"""Sampled second proof check: re-solve a sample of the pipeline's UNSAT items and check each
streamed LRAT proof with BOTH the patched lrat-check and the formally verified cake_lpr
(scripts/audit/dualcheck.sh as scripts/stream_solve.py's LRAT_CHECK; nothing else changes).

Modes
  cubes RUN_DIR   a run_cubes.py instance directory (results/stage3/24X-p-O21s/run,
                  results/stage4/NAME/run): RUN_DIR/results.jsonl, body.cnf, body.meta.
                  Sample: --n random UNSAT leaves (seeded) plus the --slowest M slowest UNSAT
                  leaves (by recorded secs; --max-secs S leaves out slower ones).  Each leaf is
                  solved as body.cnf + its cube literals as unit clauses, exactly as run_cubes.py
                  solved it.  If RUN_DIR/body.sha256 exists, body.cnf must have that sha256 (checked
                  before anything runs).  Without body.cnf (e.g. on the Mac), --cnf CNF gives the
                  full formula: its body is split off into OUT/tmp and must match body.meta and,
                  if present, body.sha256.
  enum ENUM_DIR   a pivot enumeration directory (results/enum/k6n<n>): records.jsonl,
                  models/*.d6, certify.jsonl.  Sample: --n random jobs (seeded), plus the
                  --slowest M jobs (by certified secs) and --with-models W random jobs that have
                  recorded models; --ids FILE (a JSON list of [d, ia, ib]) adds exactly those jobs
                  (with --n 0: only those, e.g. the jobs whose proofs only lrat-check saw).  Each job's formula is rebuilt exactly as
                  scripts/certify_enum.py builds it: build/pivenum dumpcnf k A B ia ib --maxdeg,
                  plus one blocking clause per recorded model of the job (models re-checked:
                  TT_k-free, and fitting the job by scripts/audit/modelfix.py).  It must be UNSAT.

Every item must give: solver UNSAT, stream_solve check VERIFIED (dualcheck's "c VERIFIED"), and
both checkers VERIFIED in dualcheck's log.  Anything else is a failure.

Output (OUT, required): OUT/items.jsonl (one JSON line per item and attempt: id, kind, pick,
status, verdict, secs, lrat/cake verdicts, their CPU seconds and peak RSS), OUT/summary.json
(counts; "ALL VERIFIED BY BOTH": true only if every sampled item is VERIFIED by both),
OUT/dualcheck/ (dualcheck's per-call logs), OUT/tmp/ (pipes and scratch; removed when empty).
Resumable: items already in OUT/items.jsonl are skipped (--retry-failed re-runs the failed ones).

Memory: cake_lpr's heap (--heap MiB, passed as --CML_HEAP_SIZE) is the main cost per worker:
its resident size grows to the whole heap.  The smallest heap that works is set by parsing the
formula, about 10.6-12.9 bytes of heap per byte of DIMACS text (tools/cake_lpr/README.md, measured
5 Nov 2026; the proofs measured needed no more).  --heap auto (default) takes 1.25 x 12.9 bytes per
byte of the formula (cubes: body.cnf; enum: the first sampled job's formula), rounded up to
256 MiB, at least 1024 MiB: Stage 3 (1.07 GB body) about 16.1 GiB, Stage 4 (0.1 GB) 1792 MiB.
New items wait while MemAvailable < --min-free-gb (Linux).

usage: cake_sample.py cubes RUN_DIR --out OUT [--cnf CNF] [--n 40] [--slowest 10] [--max-secs 0] [--ids FILE]
                      [--seed 1] [--workers 2] [--heap auto|MiB] [--timeout 0] [--nice 10]
                      [--min-free-gb 16] [--retry-failed] [--dry-run]
       cake_sample.py enum ENUM_DIR --out OUT [--n 40] [--slowest 0] [--with-models 0] [--ids FILE] [same options]
"""
import argparse
import hashlib
import json
import math
import os
import random
import re
import resource
import socket
import subprocess
import sys
import threading
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
sys.path.insert(0, str(ROOT / "src"))
sys.path.insert(0, str(HERE))
import stream_solve as SS  # noqa: E402
from modelfix import job_mismatch  # noqa: E402  (independent audit check)
import tourn as T  # noqa: E402

DUALCHECK = str(HERE / "dualcheck.sh")
PIV = str(ROOT / "build/pivenum")
HEAP_PER_BYTE = 12.9          # cake_lpr's smallest heap / DIMACS bytes, largest measured (tools/cake_lpr/README.md)
HEAP_FACTOR = 1.25            # headroom for the proof's clauses and against GC thrashing


def sha256_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def mem_available_gb():
    try:
        for line in open("/proc/meminfo"):
            if line.startswith("MemAvailable:"):
                return int(line.split()[1]) / 2**20
    except OSError:
        pass
    return float("inf")


def read_jsonl(path):
    """JSON lines of path; a torn last line (file being appended or synced) is skipped."""
    out = []
    if not Path(path).exists():
        return out
    for line in Path(path).read_text().splitlines():
        try:
            out.append(json.loads(line))
        except ValueError:
            pass
    return out


def auto_heap(nbytes):
    return max(1024, int(math.ceil(HEAP_FACTOR * HEAP_PER_BYTE * nbytes / 2**20 / 256)) * 256)


# ---------------------------------------------------------------- cubes
def cube_items(a, out):
    run = Path(a.dir)
    recs = {}
    for r in read_jsonl(run / "results.jsonl"):
        recs[r["id"]] = r                      # latest record per id
    leaves = sorted((r for r in recs.values() if r["status"] == "UNSAT"), key=lambda r: r["id"])
    if a.max_secs:
        leaves = [r for r in leaves if r["secs"] <= a.max_secs]
    rnd = random.Random(f"cubes:{a.seed}").sample(leaves, min(a.n, len(leaves)))
    slow = sorted(leaves, key=lambda r: (-r["secs"], r["id"]))[: a.slowest]
    listed = []
    if a.ids:   # e.g. the leaves whose proofs only lrat-check saw; every listed id must be an UNSAT leaf
        unsat = {r["id"]: r for r in recs.values() if r["status"] == "UNSAT"}
        want = {str(x) for x in json.loads(Path(a.ids).read_text())}
        missing = sorted(want - set(unsat))
        if missing:
            raise SystemExit(f"--ids: {len(missing)} listed ids are not UNSAT leaves of {run}, e.g. {missing[:3]}")
        listed = [unsat[i] for i in sorted(want)]
    items = {}
    for pick, rs in (("slowest", slow), ("random", rnd), ("listed", listed)):
        for r in rs:
            it = items.setdefault(r["id"], {"kind": "cube", "id": r["id"], "pick": [], "level": r["level"],
                                            "lits": r["lits"], "orig_secs": r["secs"], "orig_check": r.get("check")})
            it["pick"].append(pick)
    info = {"leaves": len(leaves), "records": len(recs)}
    return sorted(items.values(), key=lambda it: -it["orig_secs"]), info


def cube_body(a, out):
    """(body path, nvars, nclauses, sha info); refuses on a sha256 or size mismatch."""
    run = Path(a.dir)
    nv, nc = map(int, (run / "body.meta").read_text().split())
    want = None
    if (run / "body.sha256").exists():
        want = (run / "body.sha256").read_text().split()[0]
    body = run / "body.cnf"
    if not body.exists():
        if not a.cnf:
            raise SystemExit(f"{body} is missing: give the full formula with --cnf CNF")
        body = out / "tmp" / "body.cnf"
        body.parent.mkdir(parents=True, exist_ok=True)
        tmp = body.with_suffix(".part")
        nv2, nc2 = SS.split_cnf(a.cnf, tmp)
        os.replace(tmp, body)
        if (nv2, nc2) != (nv, nc):
            raise SystemExit(f"--cnf header {nv2} {nc2} != body.meta {nv} {nc}")
    got = sha256_file(body)
    if want and got != want:
        raise SystemExit(f"body sha256 MISMATCH: {body} has {got}, {run / 'body.sha256'} says {want}")
    return body, nv, nc, {"body": str(body), "body_sha256": got, "body_sha256_expected": want,
                          "sha_check": "OK" if want else "no body.sha256 (not checked)"}


# ---------------------------------------------------------------- enum
def enum_kn(a):
    d = Path(a.dir)
    if (d / "summary.json").exists():
        s = json.loads((d / "summary.json").read_text())
        return s["k"], s["n"]
    m = re.match(r"k(\d+)n(\d+)", d.name)
    if not m:
        raise SystemExit(f"{d}: no summary.json and the name is not k<k>n<n>...")
    return int(m.group(1)), int(m.group(2))


def enum_models(d):
    models = {}
    for p in (Path(d) / "models").glob("*.d6"):
        for line in p.read_text().splitlines():
            f = line.split()
            if not f:
                continue
            if len(f) != 4:
                raise SystemExit(f"{p}: model lines must be 'd ia ib d6'")
            models.setdefault((int(f[0]), int(f[1]), int(f[2])), set()).add(f[3])
    return {key: sorted(v) for key, v in models.items()}      # as scripts/certify_enum.py


def enum_items(a, out):
    d = Path(a.dir)
    recs = {}
    for r in read_jsonl(d / "records.jsonl"):
        recs[(r["d"], r["ia"], r["ib"])] = r
    jobs = sorted(k for k, r in recs.items() if r["status"] == "complete")
    secs = {}
    for c in read_jsonl(d / "certify.jsonl"):
        if c.get("check") == "VERIFIED":
            secs[(c["d"], c["ia"], c["ib"])] = c["secs"]
    rng = random.Random(f"enum:{a.seed}")
    rnd = rng.sample(jobs, min(a.n, len(jobs)))
    withm = [j for j in jobs if recs[j]["models"] > 0]
    wm = rng.sample(withm, min(a.with_models, len(withm)))
    slow = sorted((j for j in jobs if j in secs), key=lambda j: (-secs[j], j))[: a.slowest]
    listed = []
    if a.ids:   # e.g. the jobs whose proofs only lrat-check saw; every listed job must be a complete job
        want = {tuple(x) for x in json.loads(Path(a.ids).read_text())}
        missing = sorted(want - set(jobs))
        if missing:
            raise SystemExit(f"--ids: {len(missing)} listed jobs are not complete jobs of {d}, e.g. {missing[:3]}")
        listed = sorted(want)
    items = {}
    for pick, js in (("slowest", slow), ("random", rnd), ("with-models", wm), ("listed", listed)):
        for j in js:
            key = f"{j[0]}_{j[1]}_{j[2]}"
            it = items.setdefault(key, {"kind": "enum", "id": key, "pick": [], "d": j[0], "ia": j[1], "ib": j[2],
                                        "models": recs[j]["models"], "orig_secs": secs.get(j)})
            it["pick"].append(pick)
    info = {"jobs": len(recs), "complete_jobs": len(jobs), "jobs_with_models": len(withm), "certified": len(secs)}
    return sorted(items.values(), key=lambda it: -(it["orig_secs"] or 0)), info


def enum_formula(k, n, it, models, wd):
    """(body path, nv, nc, extra clauses) exactly as scripts/certify_enum.py, or a mismatch reason."""
    d, ia, ib = it["d"], it["ia"], it["ib"]
    asz = n - 1 - d
    ms = models.get((d, ia, ib), [])
    if len(ms) != it["models"]:
        return None, f"{it['models']} models recorded, {len(ms)} found"
    for m in ms:
        why = job_mismatch(k, n, d, ia, ib, m)
        if why:
            return None, f"model does not fit its job: {why}"
    ca = ROOT / f"data/tt{k-1}free/tt{k-1}free{asz}.d6"
    cb = ROOT / f"data/tt{k-1}free/tt{k-1}free{d}.d6"
    cnf = subprocess.run([PIV, "dumpcnf", str(k), str(ca), str(cb), str(ia), str(ib), "--maxdeg"],
                         capture_output=True, text=True, check=True).stdout
    head, body = cnf.split("\n", 1)
    nv, nc = int(head.split()[2]), int(head.split()[3])
    bpath = Path(wd) / f"b_{d}_{ia}_{ib}.cnf"
    bpath.write_text(body)
    # blocking clauses: arc variables are the A x B pairs in row-major order (certify_enum.py)
    extra = []
    for m in ms:
        o = T.from_d6(m)
        if len(o) != n or T.has_tt(o, k):
            bpath.unlink()
            return None, "recorded model is not a TT_k-free tournament on n vertices"
        lits = []
        v = 0
        for i in range(asz):
            for j in range(asz + 1, n):
                v += 1
                lits.append(-v if (o[i] >> j) & 1 else v)
        extra.append(" ".join(map(str, lits)) + " 0")
    return (bpath, nv, nc, extra), None


# ---------------------------------------------------------------- run
def tag_of(it):
    return ("c" if it["kind"] == "cube" else "j") + it["id"].replace(".", "-").replace("_", "-") + "x"


def dual_log(logdir, tag, before):
    new = sorted(set(logdir.glob(f"ss_{tag}_*.json")) - before, key=lambda p: p.stat().st_mtime)
    if not new:
        return None
    try:
        return json.loads(new[-1].read_text())
    except (OSError, ValueError):
        return None


def item_record(it, r, log, extra):
    rec = {k: v for k, v in it.items() if k != "lits"}
    rec.update(status=r.get("status"), check=r.get("check"), secs=r.get("secs"), check_secs=r.get("check_secs"))
    for side in ("lrat", "cake"):
        s = (log or {}).get(side) or {}
        rec[side] = s.get("verdict", "no log")
        rec[f"{side}_exit"] = s.get("exit")
        rec[f"{side}_cpu"] = s.get("cpu")
        rec[f"{side}_rss_gb"] = s.get("rss_gb")
        if rec[side] != "VERIFIED":
            rec[f"{side}_said"] = s.get("said")
            if s.get("killed_after"):
                rec[f"{side}_killed_after"] = s["killed_after"]
    rec["verdict"] = ("VERIFIED" if rec["status"] == "UNSAT" and rec["check"] == "VERIFIED"
                      and rec["lrat"] == "VERIFIED" and rec["cake"] == "VERIFIED" else "NOT VERIFIED")
    rec.update(extra)
    return rec


def summarize(a, out, items, info, setup):
    got = {}
    for r in read_jsonl(out / "items.jsonl"):
        got[r["id"]] = r                      # latest attempt per item
    recs = [got[it["id"]] for it in items if it["id"] in got]
    ver = [r for r in recs if r["verdict"] == "VERIFIED"]
    bad = [r for r in recs if r["verdict"] != "VERIFIED"]
    rss = lambda side: max((r.get(f"{side}_rss_gb") or 0 for r in recs), default=0)
    s = {"mode": a.mode, "dir": str(Path(a.dir).resolve()), "seed": a.seed, "n_random": a.n,
         "n_slowest": a.slowest, **({"n_with_models": a.with_models} if a.mode == "enum" else {}),
         **({"max_secs": a.max_secs} if a.mode == "cubes" else {}),
         **info, **setup,
         "sampled": len(items), "done": len(recs), "missing": len(items) - len(recs),
         "unsat": sum(r["status"] == "UNSAT" for r in recs),
         "lrat_verified": sum(r["lrat"] == "VERIFIED" for r in recs),
         "cake_verified": sum(r["cake"] == "VERIFIED" for r in recs),
         "verified_by_both": len(ver),
         "not_verified": [{"id": r["id"], "status": r["status"], "lrat": r["lrat"], "cake": r["cake"],
                           "lrat_said": r.get("lrat_said"), "cake_said": r.get("cake_said"),
                           "problem": r.get("problem")} for r in bad][:50],
         "cake_heap_exhausted": sum("heap space exhausted" in (r.get("cake_said") or "") for r in bad),
         "solver_seconds": round(sum(r.get("secs") or 0 for r in recs), 1),
         "orig_seconds": round(sum(r.get("orig_secs") or 0 for r in recs), 1),
         "cpu_seconds": {"lrat-check": round(sum(r.get("lrat_cpu") or 0 for r in recs), 1),
                         "cake_lpr": round(sum(r.get("cake_cpu") or 0 for r in recs), 1)},
         "max_rss_gb": {"lrat-check": rss("lrat"), "cake_lpr": rss("cake")},
         "ALL VERIFIED BY BOTH": len(items) > 0 and len(ver) == len(items),
         "t": time.strftime("%FT%T")}
    tmp = out / "summary.json.tmp"
    tmp.write_text(json.dumps(s, indent=1) + "\n")
    os.replace(tmp, out / "summary.json")
    return s


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("mode", choices=("cubes", "enum"))
    ap.add_argument("dir")
    ap.add_argument("--out", required=True)
    ap.add_argument("--cnf", default="", help="cubes: full formula when RUN_DIR/body.cnf is absent")
    ap.add_argument("--n", type=int, default=40, help="random items")
    ap.add_argument("--slowest", type=int, default=None, help="slowest items (default: cubes 10, enum 0)")
    ap.add_argument("--max-secs", type=float, default=0, help="cubes: leave out leaves slower than this")
    ap.add_argument("--with-models", type=int, default=0, help="enum: random jobs that have models")
    ap.add_argument("--ids", default="", help="JSON file: enum, a list of [d, ia, ib]; cubes, a list of leaf ids; "
                                              "all of these too")
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--workers", type=int, default=2)
    ap.add_argument("--heap", default="auto", help="cake_lpr heap in MiB, or auto")
    ap.add_argument("--timeout", type=int, default=0, help="CaDiCaL time limit per item (0 = none)")
    ap.add_argument("--nice", type=int, default=10)
    ap.add_argument("--min-free-gb", type=float, default=16.0)
    ap.add_argument("--retry-failed", action="store_true")
    ap.add_argument("--dry-run", action="store_true", help="print the sample and the heap, solve nothing")
    a = ap.parse_args()
    if a.slowest is None:
        a.slowest = 10 if a.mode == "cubes" else 0
    out = Path(a.out)
    out.mkdir(parents=True, exist_ok=True)
    soft, hard = resource.getrlimit(resource.RLIMIT_NOFILE)
    resource.setrlimit(resource.RLIMIT_NOFILE, (min(hard, 65536), hard))
    for b in ("build/lrat-check", "build/cake_lpr") + (("build/pivenum",) if a.mode == "enum" else ()):
        if not os.access(ROOT / b, os.X_OK):
            raise SystemExit(f"{b} is missing (bash scripts/cloud/setup.sh builds it)")

    body = None
    if a.mode == "cubes":
        items, info = cube_items(a, out)
        info["instance"] = Path(a.dir).resolve().parent.name if Path(a.dir).name == "run" else Path(a.dir).name
        if a.dry_run:
            src = Path(a.dir) / "body.cnf"
            src = src if src.exists() else Path(a.cnf) if a.cnf else None
            nbytes, setup = (src.stat().st_size if src else 0), {}
        else:
            body, nv, nc, setup = cube_body(a, out)
            nbytes = Path(body).stat().st_size
        nbytes += 64 * max((len(it["lits"]) for it in items), default=0)
    else:
        items, info = enum_items(a, out)
        k, n = enum_kn(a)
        info.update(k=k, n=n)
        models = enum_models(a.dir)
        setup = {}
        nbytes = 0
        if items and a.heap == "auto":
            (out / "tmp").mkdir(exist_ok=True)
            f, _ = enum_formula(k, n, items[0], models, out / "tmp")
            if f:
                nbytes = f[0].stat().st_size + sum(len(x) + 1 for x in f[3])
                f[0].unlink()
    heap = auto_heap(nbytes) if a.heap == "auto" else int(a.heap)
    setup.update(cake_heap_mib=heap, workers=a.workers, timeout=a.timeout,
                 host=socket.gethostname(),
                 cake_lpr_sha256=sha256_file(ROOT / "build/cake_lpr"),
                 lrat_check_sha256=sha256_file(ROOT / "build/lrat-check"),
                 cadical=subprocess.run([SS.CADICAL, "--version"], capture_output=True, text=True).stdout.strip())
    print(f"{a.mode} {a.dir}: {len(items)} items ({info}), cake heap {setup['cake_heap_mib']} MiB, "
          f"{a.workers} workers", flush=True)
    if a.dry_run:
        for it in items:
            print(json.dumps({k: v for k, v in it.items() if k != "lits"}))
        return

    done = {}
    for r in read_jsonl(out / "items.jsonl"):
        done[r["id"]] = r
    todo = [it for it in items if it["id"] not in done or (a.retry_failed and done[it["id"]]["verdict"] != "VERIFIED")]
    print(f"to do: {len(todo)} (already recorded: {len(items) - len(todo)})", flush=True)

    logdir = out / "dualcheck"
    logdir.mkdir(exist_ok=True)
    tmpdir = out / "tmp"
    tmpdir.mkdir(exist_ok=True)
    os.environ["DUALCHECK_LOG_DIR"] = str(logdir)
    if heap:
        os.environ["DUALCHECK_CAKE_HEAP"] = str(heap)
    SS.LRAT_CHECK = DUALCHECK
    lock = threading.Lock()
    queue_ = list(todo)
    running = [0]
    t0 = time.time()
    count = [0]

    def run(it):
        tag = tag_of(it)
        before = set(logdir.glob(f"ss_{tag}_*.json"))
        t1 = time.time()
        extra = {}
        if it["kind"] == "cube":
            r = SS.stream_solve(str(body), nv, nc, [f"{l} 0" for l in it["lits"]], str(tmpdir), tag,
                                timeout=a.timeout, check=True, nice=a.nice)
        else:
            f, why = enum_formula(k, n, it, models, tmpdir)
            if f is None:
                r = {"status": "MODEL_MISMATCH", "secs": 0.0}
                extra["problem"] = why
            else:
                bpath, nv_, nc_, ext = f
                r = SS.stream_solve(str(bpath), nv_, nc_, ext, str(tmpdir), tag, timeout=a.timeout, check=True,
                                    nice=a.nice)
                bpath.unlink()
        log = dual_log(logdir, tag, before) if r["status"] != "MODEL_MISMATCH" else None
        extra.update(cake_heap_mib=heap, wall=round(time.time() - t1, 1), host=setup["host"], t=time.strftime("%FT%T"))
        rec = item_record(it, r, log, extra)
        with lock:
            with open(out / "items.jsonl", "a") as fh:
                fh.write(json.dumps(rec) + "\n")
            count[0] += 1
            print(json.dumps({k: rec.get(k) for k in ("id", "pick", "status", "verdict", "lrat", "cake", "secs",
                                                      "orig_secs", "cake_cpu", "cake_rss_gb")})
                  + f"  [{count[0]}/{len(todo)}, {time.time() - t0:.0f}s]", flush=True)

    def worker():
        while True:
            with lock:
                if not queue_:
                    return
                it = queue_.pop(0)
                running[0] += 1
            while True:                        # wait for memory, unless this is the only item running
                with lock:
                    alone = running[0] == 1
                if alone or mem_available_gb() >= a.min_free_gb:
                    break
                time.sleep(15)
            try:
                run(it)
            except Exception as e:             # record it (a failure), keep the other items going
                rec = item_record(it, {"status": "ERROR", "secs": 0.0}, None,
                                  {"problem": f"{type(e).__name__}: {e}"[:500], "host": setup["host"],
                                   "t": time.strftime("%FT%T")})
                with lock:
                    with open(out / "items.jsonl", "a") as fh:
                        fh.write(json.dumps(rec) + "\n")
                print(f"ERROR on {it['id']}: {rec['problem']}", flush=True)
            finally:
                with lock:
                    running[0] -= 1

    ths = [threading.Thread(target=worker) for _ in range(max(1, a.workers))]
    for th in ths:
        th.start()
        time.sleep(0.2)
    for th in ths:
        th.join()
    s = summarize(a, out, items, info, setup)
    try:
        if body and Path(body).parent == tmpdir:
            Path(body).unlink()
        tmpdir.rmdir()
    except OSError:
        pass
    print(json.dumps({k: s[k] for k in ("sampled", "done", "unsat", "lrat_verified", "cake_verified",
                                         "verified_by_both", "ALL VERIFIED BY BOTH")}), flush=True)
    sys.exit(0 if s["ALL VERIFIED BY BOTH"] else 1)


if __name__ == "__main__":
    main()
