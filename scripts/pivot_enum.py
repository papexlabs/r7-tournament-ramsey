"""Enumerate all TT_k-free tournaments on n vertices by pivot decomposition.

Every TT_k-free T on n vertices has a vertex w of maximum out-degree
d >= ceil((n-1)/2) (and d <= R(k-1) - 1); In(w), Out(w) are TT_{k-1}-free on
n-1-d and d vertices.  For each d and each pair (A, B) from the complete
catalogues data/tt{k-1}free/ (verified by scripts/a0_catalogue.py),
build/pivenum enumerates every TT_k-free completion with all out-degrees <= d
(AllSAT, CaDiCaL, every model re-checked).  The union of the models, up to
isomorphism (nauty labelg), is the complete catalogue on n vertices.

Resumable: records go to OUT/records.jsonl (one per job) and raw models to
OUT/models/<batch>.d6; jobs already recorded with status "complete" are skipped.
At the end OUT/classes.d6 holds the canonical classes and OUT/summary.json the
counts.  A job with status other than "complete" makes the result incomplete
(reported, never silently ignored).

usage: pivot_enum.py k n OUT [--sample FRAC] [--seed S] [--workers W]
                     [--batch B] [--time SEC] [--nice N]
"""
import argparse
import json
import os
import random
import subprocess
import sys
import threading
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PIV = str(ROOT / "build/pivenum")


def catalogue(k1, m):
    p = ROOT / f"data/tt{k1}free/tt{k1}free{m}.d6"
    return p, [l for l in p.read_text().splitlines() if l.strip()]


def make_jobs(k, n, sample=0.0, seed=1):
    """All pivot jobs (d, ia, ib) for TT_k-free tournaments on n vertices (optionally a seeded sample)."""
    k1 = k - 1
    # R(k-1)-1 = largest order of a TT_{k-1}-free tournament
    rmax = max(m for m in range(1, 64) if (ROOT / f"data/tt{k1}free/tt{k1}free{m}.d6").exists()
               and catalogue(k1, m)[1])
    dmin = (n - 1 + 1) // 2  # ceil((n-1)/2)
    jobs = []  # (d, ia, ib)
    for d in range(dmin, rmax + 1):
        asz = n - 1 - d
        if asz <= 0 or asz > rmax:
            continue
        _, CA = catalogue(k1, asz)
        _, CB = catalogue(k1, d)
        for ia in range(len(CA)):
            for ib in range(len(CB)):
                jobs.append((d, ia, ib))
    total = len(jobs)
    if sample:
        rng = random.Random(seed)
        jobs = sorted(rng.sample(jobs, max(1, round(sample * total))))
    return jobs, total


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("k", type=int)
    ap.add_argument("n", type=int)
    ap.add_argument("out")
    ap.add_argument("--sample", type=float, default=0.0)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--workers", type=int, default=3)
    ap.add_argument("--batch", type=int, default=10)
    ap.add_argument("--time", type=float, default=0.0, help="per-job limit (0 = none)")
    ap.add_argument("--nice", type=int, default=10)
    a = ap.parse_args()
    k1 = a.k - 1
    out = Path(a.out)
    (out / "models").mkdir(parents=True, exist_ok=True)
    jobs, total = make_jobs(a.k, a.n, a.sample, a.seed)
    rec_path = out / "records.jsonl"
    done = set()
    if rec_path.exists():
        for line in rec_path.read_text().splitlines():
            r = json.loads(line)
            if r["status"] == "complete":
                done.add((r["d"], r["ia"], r["ib"]))
    todo = [j for j in jobs if j not in done]
    print(f"k={a.k} n={a.n} jobs_total={total} selected={len(jobs)} todo={len(todo)}", flush=True)
    by_d = {}
    for j in todo:
        by_d.setdefault(j[0], []).append(j)
    batches = []
    for d, js in sorted(by_d.items()):
        for i in range(0, len(js), a.batch):
            batches.append((d, js[i:i + a.batch]))
    random.Random(a.seed).shuffle(batches)  # mix hard and easy splits across workers
    lock = threading.Lock()
    t0 = time.time()
    counter = {"jobs": 0, "models": 0}

    def run(bi, d, js):
        pa, _ = catalogue(k1, a.n - 1 - d)
        pb, _ = catalogue(k1, d)
        cmd = ["nice", "-n", str(a.nice), PIV, "enum", str(a.k), str(pa), str(pb), "--maxdeg"]
        if a.time:
            cmd += ["--time", str(a.time)]
        inp = "".join(f"{ia} {ib}\n" for _, ia, ib in js)
        r = subprocess.run(cmd, input=inp, capture_output=True, text=True)
        if r.returncode != 0:
            raise RuntimeError(f"pivenum failed (rc {r.returncode}): {r.stderr[-500:]}")
        recs, models = [], []
        cur = None
        for line in r.stdout.splitlines():
            if line.startswith("R "):
                f = line.split()
                recs.append({"d": d, "ia": int(f[1]), "ib": int(f[2]), "arcs": int(f[3]),
                             "clauses": int(f[4]), "status": f[5], "models": int(f[6]),
                             "secs": float(f[7])})
                cur = f"{d} {f[1]} {f[2]}"
            elif line.startswith("T "):
                models.append(f"{cur} {line[2:]}")  # d ia ib model  (model belongs to that job)
        if len(recs) != len(js):
            raise RuntimeError(f"batch {bi}: {len(recs)} records for {len(js)} jobs")
        if models:
            (out / "models" / f"d{d}_b{bi}_{os.getpid()}_{int(time.time()*1000)}.d6").write_text("\n".join(models) + "\n")
        with lock:
            with open(rec_path, "a") as fh:
                for rc in recs:
                    fh.write(json.dumps(rc) + "\n")
            counter["jobs"] += len(recs)
            counter["models"] += len(models)
            if counter["jobs"] % max(1, len(todo) // 20) < len(recs):
                print(f"  {counter['jobs']}/{len(todo)} jobs, {counter['models']} models, "
                      f"{time.time()-t0:.0f}s", flush=True)
        return len(recs)

    with ThreadPoolExecutor(a.workers) as ex:
        futs = [ex.submit(run, bi, d, js) for bi, (d, js) in enumerate(batches)]
        for f in as_completed(futs):
            f.result()  # re-raise failures

    # aggregate
    recs = [json.loads(l) for l in rec_path.read_text().splitlines()]
    latest = {}
    for r in recs:
        latest[(r["d"], r["ia"], r["ib"])] = r
    sel = [latest[j] for j in jobs if j in latest]
    raw = set()
    for p in (out / "models").glob("*.d6"):
        raw.update(l.split()[-1] for l in p.read_text().splitlines() if l.strip())
    classes = []
    if raw:
        rr = subprocess.run(["labelg", "-q"], input="\n".join(sorted(raw)) + "\n",
                            capture_output=True, text=True, check=True)
        classes = sorted(set(l for l in rr.stdout.splitlines() if l.strip()))
    (out / "classes.d6").write_text("\n".join(classes) + ("\n" if classes else ""))
    per_d = {}
    for r in sel:
        s = per_d.setdefault(r["d"], {"jobs": 0, "secs": 0.0, "max_secs": 0.0, "sat_jobs": 0, "models": 0,
                                      "not_complete": 0})
        s["jobs"] += 1
        s["secs"] += r["secs"]
        s["max_secs"] = max(s["max_secs"], r["secs"])
        s["sat_jobs"] += r["models"] > 0
        s["models"] += r["models"]
        s["not_complete"] += r["status"] != "complete"
    summ = {"k": a.k, "n": a.n, "jobs_total": total, "jobs_selected": len(jobs), "jobs_recorded": len(sel),
            "all_complete": all(r["status"] == "complete" for r in sel) and len(sel) == len(jobs),
            "raw_models": len(raw), "classes": len(classes), "solver_seconds": round(sum(r["secs"] for r in sel), 1),
            "per_d": per_d, "wall_seconds_this_run": round(time.time() - t0, 1)}
    (out / "summary.json").write_text(json.dumps(summ, indent=1))
    print(json.dumps(summ))


if __name__ == "__main__":
    main()
