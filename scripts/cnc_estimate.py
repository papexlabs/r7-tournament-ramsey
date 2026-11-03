"""Crude cube-and-conquer size estimate.

1. march_cu splits the CNF into N cubes (static depth -d D, or -n / -l).
2. S cubes are drawn uniformly at random; each is solved by cadical as
   CNF + cube-literals-as-units with a per-cube time limit L (nice 10).
3. Estimate of total conquer time = N * mean(per-cube time), where a timed
   out cube counts as L (so the estimate is a lower bound if any time out).

usage: cnc_estimate.py NAME CNF --depth D --samples S --limit L [--seed X] [--jobs J]
Writes results/cnc_NAME.json (and the per-cube table).
"""

import argparse
import json
import random
import statistics
import subprocess
import tempfile
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MARCH = ROOT / "build/march_src/march_cu"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("name")
    ap.add_argument("cnf")
    ap.add_argument("--depth", type=int, default=0)
    ap.add_argument("--nvars", type=int, default=0)
    ap.add_argument("--samples", type=int, default=20)
    ap.add_argument("--limit", type=int, default=60)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--jobs", type=int, default=2)
    a = ap.parse_args()
    rng = random.Random(a.seed)
    (ROOT / "cubes").mkdir(exist_ok=True)
    cubes_path = ROOT / f"cubes/{a.name}.icnf"
    cmd = ["nice", "-n", "10", str(MARCH), a.cnf, "-o", str(cubes_path)]
    if a.depth:
        cmd += ["-d", str(a.depth)]
    if a.nvars:
        cmd += ["-n", str(a.nvars)]
    t0 = time.time()
    r = subprocess.run(cmd, capture_output=True, text=True)
    t_cube = time.time() - t0
    cubes = []
    for line in cubes_path.read_text().splitlines():
        if line.startswith("a "):
            cubes.append([int(x) for x in line.split()[1:-1]])
    n = len(cubes)
    refuted_in_cubing = None
    for line in r.stdout.splitlines():
        if "refuted" in line.lower() or "UNSAT" in line:
            refuted_in_cubing = line.strip()
    lines = Path(a.cnf).read_text().splitlines()
    hdr = lines[0].split()
    nv, nc = int(hdr[2]), int(hdr[3])
    body = "\n".join(lines[1:]) + "\n"
    sample_idx = sorted(rng.sample(range(n), min(a.samples, n))) if n else []
    td = tempfile.mkdtemp(prefix="cnc_")

    def solve(i):
        cube = cubes[i]
        p = Path(td) / f"c{i}.cnf"
        p.write_text(f"p cnf {nv} {nc + len(cube)}\n" + body + "".join(f"{l} 0\n" for l in cube))
        t1 = time.time()
        rr = subprocess.run(["nice", "-n", "10", "cadical", "-q", "-t", str(a.limit), str(p)],
                            capture_output=True, text=True)
        dt = time.time() - t1
        p.unlink()
        st = {10: "SAT", 20: "UNSAT"}.get(rr.returncode, "UNKNOWN")
        return {"cube": i, "len": len(cube), "status": st, "seconds": round(dt, 2)}

    with ThreadPoolExecutor(max_workers=a.jobs) as ex:
        rows = list(ex.map(solve, sample_idx))
    times = [min(r_["seconds"], a.limit) if r_["status"] != "UNKNOWN" else a.limit for r_ in rows]
    res = {
        "name": a.name, "cnf": a.cnf, "march_cmd": " ".join(cmd[3:]),
        "cubing_seconds": round(t_cube, 1), "n_cubes": n,
        "mean_cube_len": round(statistics.mean(len(c) for c in cubes), 1) if cubes else 0,
        "refuted_in_cubing": refuted_in_cubing,
        "samples": len(rows), "limit": a.limit,
        "solved": sum(r_["status"] != "UNKNOWN" for r_ in rows),
        "sat_cubes": sum(r_["status"] == "SAT" for r_ in rows),
        "mean_seconds_capped": round(statistics.mean(times), 2) if times else None,
        "median_seconds": round(statistics.median(times), 2) if times else None,
        "max_seconds": max(times) if times else None,
        "estimate_total_cpu_seconds_lower": round(n * statistics.mean(times), 0) if times else None,
        "rows": rows,
    }
    (ROOT / f"results/cnc_{a.name}.json").write_text(json.dumps(res, indent=1))
    print(json.dumps({k: v for k, v in res.items() if k != "rows"}, indent=1))


if __name__ == "__main__":
    main()
