"""E3: sample TT6-free tournaments on m vertices (default 22) and test Y8.

Question: does every TT6-free tournament on 22 vertices contain Y8?  If yes,
the (in, out) = (23, 22) split of a 46-vertex TT7-free tournament is already
excluded by the 25 UNSAT instances "23X-p-Y8" of Neiman-Mackey-Heule.
Sampling cannot prove "yes"; one Y8-free sample proves "no".

Method: base CNF = TT6-free on m free vertices (3-cycle encoding), plus
random unit clauses fixing `fix` random arcs (resampled until SAT), solved by
cadical with a random seed.  Each model is checked independently (has_tt),
canonicalised (nauty), tested for Y8 and for being a subtournament of one of
the 25 known TT6-free 23-vertex tournaments.

usage: e3_sample22.py [m] [samples] [fix] [seed]
"""

import json
import random
import subprocess
import sys
import tempfile
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))
import tourn as T  # noqa: E402

m = int(sys.argv[1]) if len(sys.argv) > 1 else 22
samples = int(sys.argv[2]) if len(sys.argv) > 2 else 100
fix = int(sys.argv[3]) if len(sys.argv) > 3 else 40
seed = int(sys.argv[4]) if len(sys.argv) > 4 else 1
rng = random.Random(seed)

base_mat = ROOT / f"cnf/mat/free{m}.txt"
base_cnf = ROOT / f"cnf/TT6free{m}.cnf"
base_map = ROOT / f"cnf/TT6free{m}.map"
if not base_cnf.exists() or not base_map.exists():
    rows = [["0" if i == j else "*" for j in range(m)] for i in range(m)]
    T.write_matrix(rows, base_mat)
    subprocess.run([str(ROOT / "build/encode"), str(base_mat), "6", "1", str(base_cnf), str(base_map)],
                   check=True, capture_output=True)
lines = base_cnf.read_text().splitlines()
hdr = lines[0].split()
nv, nc = int(hdr[2]), int(hdr[3])
body = "\n".join(lines[1:]) + "\n"
arcvar = {}
for line in base_map.read_text().splitlines():
    f = line.split()
    if f[1] == "a":
        arcvar[(int(f[2]), int(f[3]))] = int(f[0])
pairs = sorted(arcvar)

Y8 = T.matrix_to_out(T.read_matrix(ROOT / "data/Y8.txt"))
Y8r = T.reverse(Y8)
known22 = set()
for p in sorted((ROOT / "data").glob("I23_*.txt")):
    o = T.matrix_to_out(T.read_matrix(p))
    subs = [T.induced(o, [v for v in range(23) if v != d]) for d in range(23)]
    known22.update(T.canon_many(subs))

stats = {"m": m, "fix": fix, "seed": seed, "solved": 0, "unsat_retries": 0,
         "timeouts": 0, "classes": 0, "with_Y8": 0, "without_Y8": 0,
         "with_revY8": 0, "sub_of_known23": 0, "solve_seconds": 0.0}
seen = {}
examples_noY8 = []
t0 = time.time()
with tempfile.TemporaryDirectory() as td:
    cnfp = Path(td) / "s.cnf"
    while stats["solved"] < samples:
        units = []
        for (i, j) in rng.sample(pairs, fix):
            v = arcvar[(i, j)]
            units.append(v if rng.random() < 0.5 else -v)
        cnfp.write_text(f"p cnf {nv} {nc + len(units)}\n" + body + "".join(f"{u} 0\n" for u in units))
        t1 = time.time()
        r = subprocess.run(["nice", "-n", "10", "cadical", "-q", "-t", "60",
                            f"--seed={rng.randrange(10**6)}", str(cnfp)],
                           capture_output=True, text=True)
        stats["solve_seconds"] += time.time() - t1
        if r.returncode == 20:
            stats["unsat_retries"] += 1
            continue
        if r.returncode != 10:
            stats["timeouts"] += 1
            continue
        val = set()
        for line in r.stdout.splitlines():
            if line.startswith("v"):
                for x in line.split()[1:]:
                    x = int(x)
                    if x > 0:
                        val.add(x)
        out = [0] * m
        for (i, j), v in arcvar.items():
            if v in val:
                out[i] |= 1 << j
            else:
                out[j] |= 1 << i
        assert not T.has_tt(out, 6), "model contains TT6 -- encoding bug"
        stats["solved"] += 1
        c = T.canon(out)
        if c in seen:
            continue
        hasY = T.contains(out, Y8)
        hasYr = T.contains(out, Y8r)
        seen[c] = hasY
        stats["classes"] += 1
        stats["with_Y8" if hasY else "without_Y8"] += 1
        stats["with_revY8"] += hasYr
        stats["sub_of_known23"] += c in known22
        if not hasY and len(examples_noY8) < 5:
            examples_noY8.append(c)
stats["wall_seconds"] = round(time.time() - t0, 1)
stats["solve_seconds"] = round(stats["solve_seconds"], 1)
stats["examples_without_Y8_d6"] = examples_noY8
out = ROOT / f"results/e3_sample{m}_fix{fix}_seed{seed}.json"
out.write_text(json.dumps(stats, indent=1))
print(json.dumps(stats, indent=1))
