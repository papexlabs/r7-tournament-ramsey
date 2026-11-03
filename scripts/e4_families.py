"""E4: forced substructures of TT6-free out-neighbourhoods and their Y8 status.

In a tournament O on m vertices some vertex w has out-degree >= ceil((m-1)/2);
if O is TT6-free, out_O(w) is TT5-free.  So O contains w -> X for some
TT5-free X on 10 (m = 21) or 11 (m = 22) vertices.  Lists the families
{w -> X} (catalogue of TT5-free tournaments from the authors' repo, which we
re-check for TT5-freeness and pairwise non-isomorphism) and counts how many
members contain Y8 (those are already excluded for in-degree-23 pivots by
the 47 paper's 25 UNSAT runs).
"""
import json, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))
import tourn as T
CAT = ROOT / "refs/directed-ramsey-src/Directed-Ramsey-master/TT5-Free"
Y8 = T.matrix_to_out(T.read_matrix(ROOT / "data/Y8.txt"))
H6 = T.matrix_to_out(T.read_matrix(ROOT / "data/H6.txt"))
W7 = T.matrix_to_out(T.read_matrix(ROOT / "data/W7.txt"))
res = {}
for m in (10, 11, 12, 13):
    files = sorted((CAT / f"{m}-Vertex").glob("Mat*.txt"), key=lambda p: int(p.stem[3:]))
    X = [T.matrix_to_out(T.read_matrix(p)) for p in files]
    assert all(not T.has_tt(x, 5) for x in X)
    can = T.canon_many(X)
    assert len(set(can)) == len(X)
    fam = []
    for x in X:  # w -> X : vertex 0 beats all of X
        o = [((1 << (m + 1)) - 1) & ~1] + [x_ << 1 for x_ in x]
        fam.append(o)
    res[m] = {"n_TT5free": len(X),
              "w->X contains Y8": sum(T.contains(o, Y8) for o in fam),
              "w->X contains H6": sum(T.contains(o, H6) for o in fam),
              "w->X contains W7": sum(T.contains(o, W7) for o in fam)}
    print(m, res[m], flush=True)
(ROOT / "results/e4_families.json").write_text(json.dumps(res, indent=1))
