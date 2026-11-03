"""Exhaustive cross-check of build/encode against brute force on small cases.

For random partial tournaments (n = 8..10, k = 4..5, <= 14 free arcs) every
assignment of the free arcs is evaluated (a) by brute force (does the
completed tournament contain TT_k?) and (b) by the CNF, with each 3-cycle
variable set to the actual cyclic status of its triple (the best choice,
since t occurs only positively in TT clauses and t -> cyclic is enforced).
Run: python3 tests/test_encode.py
"""

import random
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))
import tourn as T  # noqa: E402

ENC = ROOT / "build/encode"


def parse_cnf(path):
    cls = []
    for line in Path(path).read_text().splitlines():
        if not line or line[0] in "pc":
            continue
        lits = [int(x) for x in line.split()][:-1]
        cls.append(lits)
    return cls


def parse_map(path):
    m = {}
    for line in Path(path).read_text().splitlines():
        f = line.split()
        m[int(f[0])] = (f[1], tuple(int(x) for x in f[2:]))
    return m


def run_case(rng, n, k, nfree, limit):
    pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
    free = set(rng.sample(pairs, nfree))
    base = [[rng.random() < 0.5 for _ in range(n)] for _ in range(n)]
    rows = [["0"] * n for _ in range(n)]
    for i, j in pairs:
        c = "*" if (i, j) in free else ("1" if base[i][j] else "0")
        rows[i][j] = c
        rows[j][i] = "*" if c == "*" else ("0" if c == "1" else "1")
    with tempfile.TemporaryDirectory() as td:
        mp = Path(td) / "m.txt"
        T.write_matrix(rows, mp)
        cnf, mapf = Path(td) / "x.cnf", Path(td) / "x.map"
        subprocess.run([str(ENC), str(mp), str(k), str(limit), str(cnf), str(mapf)],
                       check=True, capture_output=True)
        cls = parse_cnf(cnf)
        vmap = parse_map(mapf)
    arcvars = sorted(v for v, (t, _) in vmap.items() if t == "a")
    mismatches = 0
    for mask in range(1 << len(arcvars)):
        out = [0] * n
        assign = {}
        for i, j in pairs:
            if rows[i][j] == "*":
                continue
            if rows[i][j] == "1":
                out[i] |= 1 << j
            else:
                out[j] |= 1 << i
        for b, v in enumerate(arcvars):
            i, j = vmap[v][1]
            val = bool(mask >> b & 1)
            assign[v] = val
            if val:
                out[i] |= 1 << j
            else:
                out[j] |= 1 << i
        for v, (t, tri) in vmap.items():
            if t == "t":
                a, b_, c = tri
                sub = T.induced(out, [a, b_, c])
                assign[v] = T.three_cycles(sub) == 1
        cnf_ok = all(any(assign[abs(l)] == (l > 0) for l in cl) for cl in cls)
        truth_ok = not T.has_tt(out, k)
        if cnf_ok != truth_ok:
            mismatches += 1
    return mismatches, len(cls), len(arcvars)


def main():
    rng = random.Random(20261103)
    total = 0
    cases = 0
    for trial in range(60):
        n = rng.choice([8, 9, 10])
        k = rng.choice([4, 5])
        nfree = rng.randint(6, 13)
        limit = rng.choice([1, 3, 10, 5900])
        mm, nc, nv = run_case(rng, n, k, nfree, limit)
        cases += 1 << nv
        total += mm
        if mm:
            print(f"MISMATCH trial={trial} n={n} k={k} free={nfree} limit={limit}: {mm}")
    print(f"assignments checked: {cases}, mismatches: {total}")
    sys.exit(1 if total else 0)


if __name__ == "__main__":
    main()
