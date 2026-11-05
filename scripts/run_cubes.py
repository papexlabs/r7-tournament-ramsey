"""Cube-and-conquer with streamed, checked LRAT proofs and hierarchical static splits.

Level 0: the cubes of ICNF ('a l1 .. lm 0' lines).  Each cube is solved as
CNF + cube units through scripts/stream_solve.py (CaDiCaL --lrat into
lrat-check over named pipes; nothing large on disk) with the level's time
limit.  A cube still UNKNOWN is split on the S most frequent arc variables
(<= --maxvar) that it does not fix yet, into all 2^S sign patterns (so the
children cover the parent by construction; summary.py re-checks this), and the
children run at the next level; the last level has no time limit.  A SAT cube
stops new work, and its model is saved for independent checking
(scripts/verify_model.py).

DIR/body.cnf is the CNF without its header (written once; DIR/body.meta holds "nvars nclauses"
and DIR/body.sha256 its sha256, which scripts/cnc_summary.py reports and re-checks).
Records go to DIR/results.jsonl, one JSON line per finished cube:
  {"id": "17.3.0", "lits": [...], "level": L, "status": ..., "check": ..., "secs": ...}
The run is resumable (finished ids are skipped; ids of split cubes are re-derived).

usage: run_cubes.py CNF ICNF DIR [--workers W] [--timeouts 600,1800,0]
                    [--split S] [--maxvar V] [--nice N]
"""
import argparse
import collections
import hashlib
import json
import os
import resource
import sys
import threading
import time
from concurrent.futures import ThreadPoolExecutor, FIRST_COMPLETED, wait
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from stream_solve import stream_solve, split_cnf  # noqa: E402


def mem_available_gb():
    try:
        for line in open("/proc/meminfo"):
            if line.startswith("MemAvailable:"):
                return int(line.split()[1]) / 2**20
    except OSError:
        pass
    return float("inf")


def sha256_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def read_cubes(path):
    cubes = []
    for line in open(path):
        if line.startswith("a "):
            lits = [int(x) for x in line.split()[1:]]
            assert lits[-1] == 0
            cubes.append(lits[:-1])
    return cubes


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("cnf")
    ap.add_argument("icnf")
    ap.add_argument("dir")
    ap.add_argument("--workers", type=int, default=2)
    ap.add_argument("--timeouts", default="600,1800,0")
    ap.add_argument("--split", type=int, default=4)
    ap.add_argument("--maxvar", type=int, default=0)
    ap.add_argument("--nice", type=int, default=10)
    ap.add_argument("--only", default="", help="comma-separated level-0 cube indices (testing)")
    ap.add_argument("--min-free-gb", type=float, default=8.0,
                    help="do not start a new cube while MemAvailable is below this (Linux)")
    a = ap.parse_args()
    soft, hard = resource.getrlimit(resource.RLIMIT_NOFILE)
    resource.setrlimit(resource.RLIMIT_NOFILE, (min(hard, 65536), hard))  # kobon lesson: EMFILE
    timeouts = [int(x) for x in a.timeouts.split(",")]
    out = Path(a.dir)
    out.mkdir(parents=True, exist_ok=True)
    body = out / "body.cnf"
    if not body.exists():
        tmp = out / "body.cnf.tmp"
        nv, nc = split_cnf(a.cnf, tmp)
        (out / "body.meta").write_text(f"{nv} {nc}\n")
        (out / "body.sha256").write_text(f"{sha256_file(tmp)}  body.cnf\n")
        os.replace(tmp, body)
    nv, nc = map(int, (out / "body.meta").read_text().split())
    # variable frequency for splitting (arc variables only if --maxvar)
    freq = collections.Counter()
    with open(body) as fh:
        for line in fh:
            for x in line.split()[:-1]:
                v = abs(int(x))
                if not a.maxvar or v <= a.maxvar:
                    freq[v] += 1
    order = [v for v, _ in freq.most_common()]
    cubes = read_cubes(a.icnf)
    res_path = out / "results.jsonl"
    done = {}
    if res_path.exists():
        for line in open(res_path):
            r = json.loads(line)
            done[r["id"]] = r
    lock = threading.Lock()
    stop = threading.Event()

    def children(cid, lits):
        fixed = {abs(l) for l in lits}
        new = [v for v in order if v not in fixed][: a.split]
        kids = []
        for m in range(1 << len(new)):
            kl = lits + [v if (m >> t) & 1 else -v for t, v in enumerate(new)]
            kids.append((f"{cid}.{m}", kl))
        return kids

    def solve(cid, lits, level):
        tl = timeouts[min(level, len(timeouts) - 1)]
        if level >= len(timeouts) - 1:
            tl = timeouts[-1]
        r = stream_solve(str(body), nv, nc, [f"{l} 0" for l in lits], str(out / "tmp"), cid.replace(".", "_"),
                         timeout=tl, check=True, nice=a.nice)
        rec = {"id": cid, "lits": lits, "level": level, "status": r["status"], "check": r.get("check"),
               "secs": r["secs"], "check_secs": r.get("check_secs")}
        if r["status"] == "SAT":
            (out / f"SAT_{cid}.model").write_text(" ".join(map(str, r["model"])) + "\n")
            stop.set()
        with lock, open(res_path, "a") as fh:
            fh.write(json.dumps(rec) + "\n")
        print(json.dumps({k: v for k, v in rec.items() if k != "lits"}), flush=True)
        return rec

    sel = range(len(cubes)) if not a.only else [int(x) for x in a.only.split(",")]
    frontier = [(str(i), cubes[i], 0) for i in sel]
    with ThreadPoolExecutor(a.workers) as ex:
        pending = {}
        while (frontier or pending) and not stop.is_set():
            while frontier and len(pending) < a.workers and (not pending or mem_available_gb() > a.min_free_gb):
                cid, lits, lev = frontier.pop(0)
                r = done.get(cid)
                if r:
                    if r["status"] == "UNSAT" and r.get("check") == "VERIFIED":
                        continue
                    if r["status"] == "SAT":
                        stop.set()
                        continue
                    if r["status"] == "UNKNOWN" and lev < len(timeouts) - 1:
                        frontier.extend((c, l, lev + 1) for c, l in children(cid, lits))
                        continue
                pending[ex.submit(solve, cid, lits, lev)] = (cid, lits, lev)
            if not pending:
                continue
            fin, _ = wait(pending, return_when=FIRST_COMPLETED)
            for f in fin:
                cid, lits, lev = pending.pop(f)
                rec = f.result()
                if rec["status"] == "UNKNOWN" and lev < len(timeouts) - 1:
                    frontier.extend((c, l, lev + 1) for c, l in children(cid, lits))
                elif rec["status"] == "UNSAT" and rec["check"] != "VERIFIED":
                    print(f"CHECK FAILED for cube {cid}", flush=True)
                    stop.set()
    print("stopped (SAT or failed check)" if stop.is_set() else "finished", flush=True)


if __name__ == "__main__":
    main()
