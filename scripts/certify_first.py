"""Certify-first enumeration: one LRAT-checked solve per job when the job has no models.

Same jobs as scripts/pivot_enum.py (make_jobs).  For every job not yet
recorded as complete in OUT/records.jsonl:
  1. Solve the job's CNF (pivenum dumpcnf --maxdeg, the exact formula that
     pivenum enum uses) with CaDiCaL --lrat streamed into lrat-check
     (scripts/stream_solve.py).
  2. UNSAT and VERIFIED: the job has no TT_k-free completion.  Write a
     records.jsonl line (status complete, models 0, via certify-first) and a
     certify.jsonl line (check VERIFIED, models 0) -- the same meaning as
     pivot_enum.py followed by certify_enum.py, in one solve instead of two.
  3. Anything else (SAT, UNSAT not verified, UNKNOWN): run pivenum enum (AllSAT)
     on the job and write its records/models exactly as pivot_enum.py does;
     nothing goes to certify.jsonl, so certify_enum.py certifies the job later
     with its blocking clauses.  Every first-solve outcome is logged in
     OUT/certify_first.jsonl.
Afterwards run (unchanged tools, same flags):
  python3 scripts/pivot_enum.py k n OUT [--sample S --seed X]   # 0 jobs left: writes summary.json, classes.d6
  python3 scripts/certify_enum.py OUT                          # certifies the SAT jobs, writes certify_summary.json
so all_complete / all_jobs_verified keep their meaning and nothing is skipped.
Resumable: jobs with a complete record are skipped.

usage: certify_first.py k n OUT [--sample S] [--seed X] [--workers W] [--nice N]
"""
import argparse
import json
import os
import subprocess
import sys
import tempfile
import threading
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
from pivot_enum import make_jobs, catalogue  # noqa: E402
from stream_solve import stream_solve  # noqa: E402

PIV = str(ROOT / "build/pivenum")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("k", type=int)
    ap.add_argument("n", type=int)
    ap.add_argument("out")
    ap.add_argument("--sample", type=float, default=0.0)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--workers", type=int, default=3)
    ap.add_argument("--nice", type=int, default=10)
    a = ap.parse_args()
    k1 = a.k - 1
    out = Path(a.out)
    (out / "models").mkdir(parents=True, exist_ok=True)
    jobs, total = make_jobs(a.k, a.n, a.sample, a.seed)
    rec_path, cert_path, log_path = out / "records.jsonl", out / "certify.jsonl", out / "certify_first.jsonl"
    done = set()
    if rec_path.exists():
        for line in rec_path.read_text().splitlines():
            r = json.loads(line)
            if r["status"] == "complete":
                done.add((r["d"], r["ia"], r["ib"]))
    todo = [j for j in jobs if j not in done]
    print(f"certify-first k={a.k} n={a.n} jobs_total={total} selected={len(jobs)} todo={len(todo)}", flush=True)
    lock = threading.Lock()
    wd = tempfile.mkdtemp(prefix="cf_")
    t0 = time.time()
    stats = {"jobs": 0, "unsat_verified": 0, "fallback": 0, "secs": 0.0}

    def append(path, rec):
        with open(path, "a") as fh:
            fh.write(json.dumps(rec) + "\n")

    def run(job):
        d, ia, ib = job
        asz = a.n - 1 - d
        ca, _ = catalogue(k1, asz)
        cb, _ = catalogue(k1, d)
        cnf = subprocess.run(["nice", "-n", str(a.nice), PIV, "dumpcnf", str(a.k), str(ca), str(cb),
                              str(ia), str(ib), "--maxdeg"], capture_output=True, text=True, check=True).stdout
        head, body = cnf.split("\n", 1)
        nv, nc = int(head.split()[2]), int(head.split()[3])
        bpath = Path(wd) / f"b_{d}_{ia}_{ib}.cnf"
        bpath.write_text(body)
        res = stream_solve(str(bpath), nv, nc, [], wd, f"{d}_{ia}_{ib}", nice=a.nice)
        bpath.unlink()
        first = {"d": d, "ia": ia, "ib": ib, "status": res["status"], "check": res.get("check"), "secs": res["secs"]}
        if res["status"] == "UNSAT" and res.get("check") == "VERIFIED":
            rec = {"d": d, "ia": ia, "ib": ib, "arcs": asz * d, "clauses": nc, "status": "complete",
                   "models": 0, "secs": res["secs"], "via": "certify-first"}
            cert = {"d": d, "ia": ia, "ib": ib, "models": 0, "status": "UNSAT", "check": "VERIFIED",
                    "secs": res["secs"], "via": "certify-first"}
            with lock:
                append(log_path, first)
                append(cert_path, cert)   # certificate first, then the completion record
                append(rec_path, rec)
                stats["unsat_verified"] += 1
                stats["secs"] += res["secs"]
            return
        # fall back to the AllSAT enumeration for this job (certified later by certify_enum.py)
        r = subprocess.run(["nice", "-n", str(a.nice), PIV, "enum", str(a.k), str(ca), str(cb), "--maxdeg"],
                           input=f"{ia} {ib}\n", capture_output=True, text=True)
        if r.returncode != 0:
            raise RuntimeError(f"pivenum enum failed on {job}: {r.stderr[-300:]}")
        recs, models = [], []
        for line in r.stdout.splitlines():
            if line.startswith("R "):
                f = line.split()
                recs.append({"d": d, "ia": int(f[1]), "ib": int(f[2]), "arcs": int(f[3]), "clauses": int(f[4]),
                             "status": f[5], "models": int(f[6]), "secs": float(f[7]), "via": "allsat-fallback"})
            elif line.startswith("T "):
                models.append(f"{d} {ia} {ib} {line[2:]}")
        if len(recs) != 1:
            raise RuntimeError(f"pivenum enum gave {len(recs)} records for {job}")
        if models:
            (out / "models" / f"d{d}_cf_{ia}_{ib}_{os.getpid()}_{int(time.time()*1000)}.d6").write_text(
                "\n".join(models) + "\n")
        with lock:
            append(log_path, first)
            append(rec_path, recs[0])
            stats["fallback"] += 1
            stats["secs"] += res["secs"] + recs[0]["secs"]

    with ThreadPoolExecutor(a.workers) as ex:
        futs = [ex.submit(run, j) for j in todo]
        for i, f in enumerate(as_completed(futs), 1):
            f.result()
            if i % max(1, len(todo) // 20) == 0:
                with lock:
                    print(f"  {i}/{len(todo)} jobs: {stats['unsat_verified']} UNSAT-VERIFIED first, "
                          f"{stats['fallback']} fallback (SAT or unchecked), {time.time()-t0:.0f}s", flush=True)
    stats["jobs"] = len(todo)
    stats["wall_seconds"] = round(time.time() - t0, 1)
    stats["secs"] = round(stats["secs"], 1)
    print(json.dumps(stats), flush=True)


if __name__ == "__main__":
    main()
