"""E3c: sample TT6-free tournaments on 22 (or 21) vertices via pivot instances.

Plain CDCL does not find a TT6-free 22-vertex tournament within minutes
(results/runs.csv, val-TT6free22).  Instead: a TT6-free O on m vertices has a
vertex w with out-degree d >= ceil((m-1)/2); In_O(w), Out_O(w) are TT5-free.
So O = A -w- B with A, B TT5-free (|A| + |B| = m - 1, |B| = d).  We draw A, B
from the complete TT5-free catalogue (authors' repo, re-checked in E4),
solve "A -p- B, TT6-free" (only A x B free) with a random seed, and test each
solution for Y8 / reversed Y8 and for being a subtournament of one of the 25
known TT6-free 23-vertex tournaments.

usage: e3_pivot_sample.py m tries seed [timeout]
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
import instances as I  # noqa: E402

m, tries, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
tlim = int(sys.argv[4]) if len(sys.argv) > 4 else 30
rng = random.Random(seed)
CAT = ROOT / "refs/directed-ramsey-src/Directed-Ramsey-master/TT5-Free"
cat = {}
for s in range(8, 14):
    cat[s] = [T.matrix_to_out(T.read_matrix(p)) for p in sorted((CAT / f"{s}-Vertex").glob("Mat*.txt"))]
Y8 = T.matrix_to_out(T.read_matrix(ROOT / "data/Y8.txt"))
Y8r = T.reverse(Y8)
known = set()
for p in sorted((ROOT / "data").glob("I23_*.txt")):
    o = T.matrix_to_out(T.read_matrix(p))
    if m == 22:
        known.update(T.canon_many([T.induced(o, [v for v in range(23) if v != d]) for d in range(23)]))
    elif m == 21:
        import itertools
        known.update(T.canon_many([T.induced(o, [v for v in range(23) if v not in dd])
                                   for dd in itertools.combinations(range(23), 2)]))
splits = [(a, m - 1 - a) for a in range(8, 14) if 8 <= m - 1 - a <= 13 and m - 1 - a >= a]
stats = {"m": m, "seed": seed, "timeout": tlim, "splits": splits, "tries": 0, "sat": 0,
         "unsat": 0, "unknown": 0, "classes": 0, "with_Y8": 0, "without_Y8": 0,
         "without_Y8_and_revY8": 0, "sub_of_known23": 0, "solve_seconds": 0.0, "per_split": {}}
seen = {}
ex = []
t0 = time.time()
with tempfile.TemporaryDirectory() as td:
    for t in range(tries):
        a, b = rng.choice(splits)
        A, B = rng.choice(cat[a]), rng.choice(cat[b])
        rows = I.pivot_matrix(A, B)
        mp, cnf = Path(td) / "m.txt", Path(td) / "x.cnf"
        T.write_matrix(rows, mp)
        subprocess.run([str(ROOT / "build/encode"), str(mp), "6", "5900", str(cnf), str(Path(td) / "x.map")],
                       check=True, capture_output=True)
        vmap = {}
        for line in (Path(td) / "x.map").read_text().splitlines():
            f = line.split()
            vmap[int(f[0])] = (int(f[2]), int(f[3]))
        t1 = time.time()
        r = subprocess.run(["nice", "-n", "10", "cadical", "-q", "-t", str(tlim),
                            f"--seed={rng.randrange(10**6)}", str(cnf)], capture_output=True, text=True)
        stats["solve_seconds"] += time.time() - t1
        stats["tries"] += 1
        key = f"{a},{b}"
        ps = stats["per_split"].setdefault(key, {"sat": 0, "unsat": 0, "unknown": 0})
        if r.returncode == 20:
            stats["unsat"] += 1; ps["unsat"] += 1
            continue
        if r.returncode != 10:
            stats["unknown"] += 1; ps["unknown"] += 1
            continue
        stats["sat"] += 1; ps["sat"] += 1
        true = set()
        for line in r.stdout.splitlines():
            if line.startswith("v"):
                true.update(int(x) for x in line.split()[1:] if int(x) > 0)
        n = len(rows)
        out = [0] * n
        for i in range(n):
            for j in range(i + 1, n):
                c = rows[i][j]
                if c == "1":
                    out[i] |= 1 << j
                elif c == "0":
                    out[j] |= 1 << i
        for v, (i, j) in vmap.items():
            if v in true:
                out[i] |= 1 << j
            else:
                out[j] |= 1 << i
        assert not T.has_tt(out, 6)
        c = T.canon(out)
        if c in seen:
            continue
        y, yr = T.contains(out, Y8), T.contains(out, Y8r)
        seen[c] = y
        stats["classes"] += 1
        stats["with_Y8" if y else "without_Y8"] += 1
        stats["without_Y8_and_revY8"] += (not y) and (not yr)
        stats["sub_of_known23"] += c in known
        if not y and len(ex) < 3:
            ex.append(c)
stats["solve_seconds"] = round(stats["solve_seconds"], 1)
stats["wall_seconds"] = round(time.time() - t0, 1)
stats["examples_without_Y8_d6"] = ex
(ROOT / f"results/e3_pivot_sample{m}_seed{seed}.json").write_text(json.dumps(stats, indent=1))
print(json.dumps(stats, indent=1))
