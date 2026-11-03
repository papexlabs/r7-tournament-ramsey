"""Crude tree-size estimate by a fixed static split (no lookahead cubing).

Pick k variables (the k most frequent arc variables of the CNF), draw S of
the 2^k assignments uniformly, solve each sub-formula (CNF + k units) with
cadical under a per-piece limit L (nice 10).  The 2^k pieces partition the
search space, so 2^k * mean(piece time) estimates the total time of a naive
k-variable split (an upper-ish reference for proper cube-and-conquer);
pieces that time out are counted as L (so the estimate is then a lower
bound of that split's cost).

usage: split_estimate.py NAME CNF --k K --samples S --limit L [--seed X] [--jobs J]
"""
import argparse
import collections
import json
import random
import statistics
import subprocess
import tempfile
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("name")
    ap.add_argument("cnf")
    ap.add_argument("--k", type=int, default=10)
    ap.add_argument("--samples", type=int, default=8)
    ap.add_argument("--limit", type=int, default=60)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--jobs", type=int, default=2)
    ap.add_argument("--maxvar", type=int, default=0, help="only consider vars <= maxvar (arc vars)")
    a = ap.parse_args()
    rng = random.Random(a.seed)
    lines = Path(a.cnf).read_text().splitlines()
    hdr = lines[0].split()
    nv, nc = int(hdr[2]), int(hdr[3])
    occ = collections.Counter()
    for line in lines[1:]:
        for x in line.split()[:-1]:
            v = abs(int(x))
            if not a.maxvar or v <= a.maxvar:
                occ[v] += 1
    split_vars = [v for v, _ in occ.most_common(a.k)]
    body = "\n".join(lines[1:]) + "\n"
    del lines
    assigns = [rng.getrandbits(a.k) for _ in range(a.samples)]
    td = tempfile.mkdtemp(prefix="split_")

    def solve(i):
        bits = assigns[i]
        units = [v if (bits >> t) & 1 else -v for t, v in enumerate(split_vars)]
        p = Path(td) / f"p{i}.cnf"
        p.write_text(f"p cnf {nv} {nc + len(units)}\n" + body + "".join(f"{u} 0\n" for u in units))
        t1 = time.time()
        rr = subprocess.run(["nice", "-n", "10", "cadical", "-q", "-t", str(a.limit), str(p)],
                            capture_output=True, text=True)
        dt = time.time() - t1
        p.unlink()
        return {"piece": i, "status": {10: "SAT", 20: "UNSAT"}.get(rr.returncode, "UNKNOWN"),
                "seconds": round(dt, 2)}

    with ThreadPoolExecutor(max_workers=a.jobs) as ex:
        rows = list(ex.map(solve, range(a.samples)))
    times = [r["seconds"] if r["status"] != "UNKNOWN" else a.limit for r in rows]
    res = {"name": a.name, "cnf": a.cnf, "k": a.k, "split_vars": split_vars,
           "samples": a.samples, "limit": a.limit,
           "solved": sum(r["status"] != "UNKNOWN" for r in rows),
           "sat": sum(r["status"] == "SAT" for r in rows),
           "mean_seconds_capped": round(statistics.mean(times), 2),
           "estimate_total_seconds": round((1 << a.k) * statistics.mean(times)),
           "estimate_is_lower_bound": any(r["status"] == "UNKNOWN" for r in rows),
           "rows": rows}
    (ROOT / f"results/split_{a.name}.json").write_text(json.dumps(res, indent=1))
    print(json.dumps({k: v for k, v in res.items() if k != "rows"}))


if __name__ == "__main__":
    main()
