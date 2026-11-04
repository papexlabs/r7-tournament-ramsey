"""Stage 4 cost sampling (Mac): random level-0 cubes of the NMH instances, solved
exactly as on the server (scripts/stream_solve.py: CaDiCaL --lrat streamed into
lrat-check), with a time limit.  Both programs run under /usr/bin/time -l
(wrappers set as stream_solve.CADICAL / LRAT_CHECK), which gives their CPU time
(user + sys) and peak RSS per cube: CPU time is what the projection uses, since
wall time on this shared Mac depends on its other load.

Cubes: the static 2^K split of scripts/make_cubes.py on the K most frequent arc
variables (<= C(n,2) in NMH's numbering), as run_stage4.sh makes them.

usage: stage4_sample.py OUT.jsonl NAME:K:SAMPLES[:SEED] ... [--timeout 600] [--workers 4] [--nice 10]
                        [--workdir DIR]
Appends one JSON line per cube to OUT.jsonl (and skips cubes already in it).
"""
import argparse
import collections
import json
import os
import random
import subprocess
import sys
import tempfile
import threading
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(HERE))
import stream_solve as SS  # noqa: E402
from stream_solve import stream_solve, split_cnf  # noqa: E402

WRAP = """#!/bin/sh
# run PROG under /usr/bin/time -l; the cube tag is taken from the ss_<tag>_ temp dir in the arguments
tag=$(printf '%s\\n' "$@" | sed -n 's|.*/ss_\\([^_/]*\\)_.*|\\1|p' | head -1)
exec /usr/bin/time -l -o "{times}/$tag.{short}.time" {prog} "$@"
"""


def make_wrappers(wd):
    times = Path(wd) / "times"
    times.mkdir(parents=True, exist_ok=True)
    for short, prog in (("cadical", subprocess.run(["which", "cadical"], capture_output=True, text=True).stdout.strip()),
                        ("lrat", SS.LRAT_CHECK)):
        w = Path(wd) / f"wrap_{short}.sh"
        w.write_text(WRAP.format(times=times, short=short, prog=prog))
        w.chmod(0o755)
        if short == "cadical":
            SS.CADICAL = str(w)
        else:
            SS.LRAT_CHECK = str(w)
    return times


def read_time(path):
    """(user + sys seconds, peak RSS GB) from macOS /usr/bin/time -l output."""
    try:
        t = Path(path).read_text().split("\n")
    except OSError:
        return None, None
    f = t[0].split()
    cpu = float(f[2]) + float(f[4])          # "<real> real <user> user <sys> sys"
    rss = next((int(l.split()[0]) for l in t if "maximum resident set size" in l), 0)
    return round(cpu, 2), round(rss / 2**30, 3)


def prepare(name, k, wd):
    cnf = ROOT / f"cnf/stage4/{name}.cnf"
    d = Path(wd) / name
    d.mkdir(parents=True, exist_ok=True)
    body = d / "body.cnf"
    if not body.exists():
        nv, nc = split_cnf(cnf, d / "body.tmp")
        os.replace(d / "body.tmp", body)
        (d / "body.meta").write_text(f"{nv} {nc}\n")
    nv, nc = map(int, (d / "body.meta").read_text().split())
    icnf = d / f"cubes_k{k}.icnf"
    if not icnf.exists():
        maxvar = 528 if name == "ST25-p-W7" else 496                           # C(n,2): arc variables
        subprocess.run([sys.executable, "-I", str(HERE / "make_cubes.py"), str(cnf), str(icnf), "--k", str(k),
                        "--maxvar", str(maxvar)], check=True, capture_output=True)
    cubes = [l.split()[1:-1] for l in icnf.read_text().splitlines() if l.startswith("a ")]
    return body, nv, nc, cubes


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("out")
    ap.add_argument("specs", nargs="+")
    ap.add_argument("--timeout", type=int, default=600)
    ap.add_argument("--workers", type=int, default=4)
    ap.add_argument("--nice", type=int, default=10)
    ap.add_argument("--workdir", default=os.path.join(tempfile.gettempdir(), "stage4_sample"))
    a = ap.parse_args()
    out = Path(a.out)
    seen = set()
    if out.exists():
        for line in out.read_text().splitlines():
            r = json.loads(line)
            seen.add((r["name"], r["k"], r["cube"]))
    tasks = []
    per = collections.defaultdict(list)
    for spec in a.specs:
        f = spec.split(":")
        name, k, m = f[0], int(f[1]), int(f[2])
        seed = int(f[3]) if len(f) > 3 else 4
        body, nv, nc, cubes = prepare(name, k, a.workdir)
        idx = random.Random(f"{name}:{k}:{seed}").sample(range(len(cubes)), m)
        for i in idx:
            if (name, k, i) not in seen:
                per[name].append((name, k, i, body, nv, nc, cubes[i]))
    # interleave instances so that the pool mixes them
    while any(per.values()):
        for name in list(per):
            if per[name]:
                tasks.append(per[name].pop(0))
    lock = threading.Lock()
    times = make_wrappers(a.workdir)

    def run(t):
        name, k, i, body, nv, nc, lits = t
        tag = f"{name.replace('-', '')}{k}c{i}"
        r = stream_solve(str(body), nv, nc, [f"{l} 0" for l in lits], str(Path(a.workdir) / "tmp"), tag,
                         timeout=a.timeout, check=True, nice=a.nice)
        cc, rc_ = read_time(times / f"{tag}.cadical.time")
        lc, rl = read_time(times / f"{tag}.lrat.time")
        rec = {"name": name, "k": k, "cube": i, "status": r["status"], "check": r.get("check"), "secs": r["secs"],
               "check_secs": r.get("check_secs"), "timeout": a.timeout,
               "cpu": {"cadical": cc, "lrat-check": lc}, "rss_gb": {"cadical": rc_, "lrat-check": rl},
               "load1": round(os.getloadavg()[0], 1), "host": "mac-m5", "t": time.strftime("%FT%T")}
        with lock, open(out, "a") as fh:
            fh.write(json.dumps(rec) + "\n")
        print(json.dumps(rec), flush=True)

    with ThreadPoolExecutor(a.workers) as ex:
        list(ex.map(run, tasks))


if __name__ == "__main__":
    main()
