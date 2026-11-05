"""Certify a pivot enumeration (scripts/pivot_enum.py) job by job with LRAT.

For every recorded job (d, ia, ib) the formula is pivenum's CNF for the job
(TT_k exclusion + degree bounds) plus one blocking clause per recorded model
of that job.  If CaDiCaL proves it UNSAT and lrat-check VERIFIES the streamed
proof, the job has no TT_k-free completion besides the recorded models.  The
models themselves are re-checked TT_k-free here (independently of pivenum).
Every recorded model must also fit its job (scripts/audit/modelfix.py, an
independent audit check): a tournament with exactly the job's fixed arcs
(A = catalogue line ia on 0..a-1, pivot a, B = line ib on a+1..n-1, A -> pivot
-> B) and all out-degrees <= d; only then does its blocking clause (its A x B
arcs) exclude that completion.  A job with a model that does not fit is
recorded as MODEL_MISMATCH (not VERIFIED, no solve), and models filed under a
job without a record make all_jobs_verified false.
Together with complete catalogues of TT_{k-1}-free tournaments this certifies
the enumeration.

usage: certify_enum.py OUT --workers W [--limit N]
Writes OUT/certify.jsonl (resumable) and prints a summary.
"""
import argparse
import json
import subprocess
import sys
import tempfile
import threading
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))
sys.path.insert(0, str(ROOT / "scripts"))
sys.path.insert(0, str(ROOT / "scripts" / "audit"))
import tourn as T  # noqa: E402
from stream_solve import stream_solve  # noqa: E402
from modelfix import job_mismatch  # noqa: E402  (independent audit check, kept separate)

PIV = str(ROOT / "build/pivenum")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("out")
    ap.add_argument("--workers", type=int, default=3)
    ap.add_argument("--limit", type=int, default=0, help="certify only N jobs (timing/testing)")
    ap.add_argument("--seed", type=int, default=0, help="with --limit: random N jobs (seeded) instead of the first N")
    a = ap.parse_args()
    out = Path(a.out)
    summ = json.loads((out / "summary.json").read_text())
    k, n = summ["k"], summ["n"]
    recs = {}
    for line in (out / "records.jsonl").read_text().splitlines():
        r = json.loads(line)
        recs[(r["d"], r["ia"], r["ib"])] = r
    models = {}
    for p in (out / "models").glob("*.d6"):
        for line in p.read_text().splitlines():
            f = line.split()
            if len(f) != 4:
                raise SystemExit(f"{p}: model lines must be 'd ia ib d6' (re-run pivot_enum.py)")
            models.setdefault((int(f[0]), int(f[1]), int(f[2])), set()).add(f[3])
    # a job re-run after an interruption may have written its (identical) model set twice
    models = {key: sorted(v) for key, v in models.items()}
    for key, r in recs.items():
        if r["models"] != len(models.get(key, [])):
            raise SystemExit(f"job {key}: {r['models']} models recorded, {len(models.get(key, []))} found")
    # every model must fit its job (fixed arcs of A, pivot and B; degree bound); see modelfix.py
    mismatch = {}
    for key, ms in models.items():
        for m in ms:
            why = job_mismatch(k, n, key[0], key[1], key[2], m)
            if why:
                mismatch[key] = why
                break
    orphans = sorted(key for key in models if key not in recs)
    if mismatch or orphans:
        print(f"MODEL MISMATCH: {len(mismatch)} job(s), e.g. {sorted(mismatch.items())[:3]}; "
              f"models without a job record: {len(orphans)} job(s) {orphans[:3]}", flush=True)
    cert_path = out / "certify.jsonl"
    done = set()
    if cert_path.exists():
        for line in cert_path.read_text().splitlines():
            c = json.loads(line)
            if c.get("check") == "VERIFIED":
                done.add((c["d"], c["ia"], c["ib"]))
    todo = sorted(k_ for k_ in recs if k_ not in done or k_ in mismatch)
    if a.limit:
        if a.seed:
            import random
            todo = sorted(random.Random(a.seed).sample(todo, min(a.limit, len(todo))))
        else:
            todo = todo[: a.limit]
    lock = threading.Lock()
    wd = tempfile.mkdtemp(prefix="cert_")

    def run(key):
        d, ia, ib = key
        asz = n - 1 - d
        if key in mismatch:
            rec = {"d": d, "ia": ia, "ib": ib, "models": len(models.get(key, [])), "status": "MODEL_MISMATCH",
                   "check": "FAILED", "problem": mismatch[key], "secs": 0.0}
            with lock, open(cert_path, "a") as fh:
                fh.write(json.dumps(rec) + "\n")
            return rec
        ca = ROOT / f"data/tt{k-1}free/tt{k-1}free{asz}.d6"
        cb = ROOT / f"data/tt{k-1}free/tt{k-1}free{d}.d6"
        cnf = subprocess.run([PIV, "dumpcnf", str(k), str(ca), str(cb), str(ia), str(ib), "--maxdeg"],
                             capture_output=True, text=True, check=True).stdout
        head, body = cnf.split("\n", 1)
        nv, nc = int(head.split()[2]), int(head.split()[3])
        bpath = Path(wd) / f"b_{d}_{ia}_{ib}.cnf"
        bpath.write_text(body)
        # blocking clauses: arc variables are the A x B pairs in row-major order
        b = d
        extra = []
        for m in models.get(key, []):
            o = T.from_d6(m)
            assert len(o) == n and not T.has_tt(o, k), "recorded model is not TT_k-free"
            lits = []
            v = 0
            for i in range(asz):
                for j in range(asz + 1, n):
                    v += 1
                    lits.append(-v if (o[i] >> j) & 1 else v)
            extra.append(" ".join(map(str, lits)) + " 0")
        res = stream_solve(str(bpath), nv, nc, extra, wd, f"{d}_{ia}_{ib}")
        bpath.unlink()
        rec = {"d": d, "ia": ia, "ib": ib, "models": len(extra), "status": res["status"],
               "check": res.get("check"), "secs": res["secs"]}
        with lock, open(cert_path, "a") as fh:
            fh.write(json.dumps(rec) + "\n")
        return rec

    with ThreadPoolExecutor(a.workers) as ex:
        res = [f.result() for f in as_completed([ex.submit(run, key) for key in todo])]
    allc = [json.loads(l) for l in cert_path.read_text().splitlines()]
    ver = {(c["d"], c["ia"], c["ib"]) for c in allc if c.get("check") == "VERIFIED"} - set(mismatch)
    s = {"jobs": len(recs), "verified": len(ver & set(recs)), "this_run": len(res),
         "failed_this_run": sum(r["check"] != "VERIFIED" for r in res),
         "solve_seconds_this_run": round(sum(r["secs"] for r in res), 1),
         "models_checked": sum(len(v) for v in models.values()),
         "model_mismatch_jobs": len(mismatch), "orphan_model_jobs": len(orphans),
         "all_jobs_verified": set(recs) <= ver and not orphans}
    (out / "certify_summary.json").write_text(json.dumps(s, indent=1))
    print(json.dumps(s))


if __name__ == "__main__":
    main()
