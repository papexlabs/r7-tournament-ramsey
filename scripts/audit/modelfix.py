"""Independent audit check: every recorded enumeration model fits its job.

Written on 5 Nov 2026 by an external auditor apart from the repository code (its own digraph6
decoder, no src/tourn.py) and kept as a separate tool on purpose.

A job (d, ia, ib) of scripts/pivot_enum.py for TT_k-free tournaments on n vertices is the pivot
instance A -w- B: A = line ia of data/tt{k-1}free/tt{k-1}free{a}.d6 on vertices 0..a-1
(a = n-1-d), the pivot w = vertex a, B = line ib of data/tt{k-1}free/tt{k-1}free{d}.d6 on
vertices a+1..n-1; arcs inside A and inside B as in the catalogue, A -> w -> B, and (pivenum
--maxdeg) every out-degree at most d.  scripts/certify_enum.py blocks each recorded model by its
A x B arcs only, so the blocking clause excludes the job's completion with those arcs only if the
model is a tournament with exactly the job's fixed arcs.  A model that does not fit its job
therefore fails the job (scripts/certify_enum.py calls job_mismatch).

CLI: python3 scripts/audit/modelfix.py OUT [OUT ...]
  checks every line "d ia ib d6" of OUT/models/*.d6 (k and n from OUT/summary.json, else from a
  directory name k<k>n<n>...); prints the counts per OUT and exits 1 on any mismatch.
"""
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


def from_d6(s):
    n = ord(s[1]) - 63
    bits = []
    for ch in s[2:]:
        v = ord(ch) - 63
        bits += [(v >> t) & 1 for t in range(5, -1, -1)]
    out = [0] * n
    for i in range(n):
        for j in range(n):
            if bits[i * n + j]:
                out[i] |= 1 << j
    return out


_cat = {}


def catalogue_line(k1, m, i):
    if (k1, m) not in _cat:
        p = ROOT / f"data/tt{k1}free/tt{k1}free{m}.d6"
        _cat[(k1, m)] = [l for l in p.read_text().split() if l]
    return from_d6(_cat[(k1, m)][i])


def job_mismatch(k, n, d, ia, ib, model_d6):
    """'' if the model fits job (d, ia, ib), else the first reason it does not."""
    if not model_d6.startswith("&") or len(model_d6) < 2:
        return "not a digraph6 '&' string"
    o = from_d6(model_d6)
    a = n - 1 - d
    if len(o) != n:
        return f"{len(o)} vertices, not {n}"
    for i in range(n):
        if (o[i] >> i) & 1:
            return f"loop at {i}"
        for j in range(i + 1, n):
            if ((o[i] >> j) & 1) + ((o[j] >> i) & 1) != 1:
                return f"pair {i},{j} is not one arc"
    A = catalogue_line(k - 1, a, ia)
    B = catalogue_line(k - 1, d, ib)
    for i in range(a):
        for j in range(a):
            if i != j and ((o[i] >> j) & 1) != ((A[i] >> j) & 1):
                return f"arc {i},{j} inside A differs from catalogue line {ia}"
    for i in range(a):
        if not (o[i] >> a) & 1:
            return f"A vertex {i} does not point to the pivot"
    for j in range(d):
        if not (o[a] >> (a + 1 + j)) & 1:
            return f"pivot does not point to B vertex {j}"
    for i in range(d):
        for j in range(d):
            if i != j and ((o[a + 1 + i] >> (a + 1 + j)) & 1) != ((B[i] >> j) & 1):
                return f"arc {i},{j} inside B differs from catalogue line {ib}"
    if max(bin(x).count("1") for x in o) > d:
        return f"an out-degree exceeds d = {d}"
    return ""


def main():
    bad_total = 0
    for out in map(Path, sys.argv[1:]):
        if (out / "summary.json").exists():
            s = json.loads((out / "summary.json").read_text())
            k, n = s["k"], s["n"]
        else:
            m = re.match(r"k(\d+)n(\d+)", out.name)
            k, n = int(m.group(1)), int(m.group(2))
        tot = bad = 0
        for p in sorted((out / "models").glob("*.d6")):
            for line in p.read_text().splitlines():
                f = line.split()
                if not f:
                    continue
                tot += 1
                why = "malformed line" if len(f) != 4 else job_mismatch(k, n, int(f[0]), int(f[1]), int(f[2]), f[3])
                if why:
                    bad += 1
                    if bad <= 5:
                        print(f"  {p.name}: {' '.join(f[:3])}: {why}")
        print(f"{out}: k={k} n={n} models {tot}, not fitting their job: {bad}")
        bad_total += bad
    sys.exit(1 if bad_total else 0)


if __name__ == "__main__":
    main()
