"""E5: check the TT6-free catalogues in evanlohn/digraph_isolators (2022).

For n = 20..27: parse tt6free{n}.d6, verify each is a tournament, TT6-free,
pairwise non-isomorphic (nauty), closed under reversal, and that the 23/24
files match the Neiman-Mackey-Heule classes.  For n = 22 (and 21) test
containment of Y8 and of reversed Y8; for n = 21 count H6 / W7 / Y8.
Completeness of the files is NOT verified here (see FEASIBILITY.md).
"""
import json, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))
import tourn as T
CAT = ROOT / "refs/digraph-isolators-src/digraph_isolators-HEAD/tt6free_tournaments"
Y8 = T.matrix_to_out(T.read_matrix(ROOT / "data/Y8.txt")); Y8r = T.reverse(Y8)
H6 = T.matrix_to_out(T.read_matrix(ROOT / "data/H6.txt")); W7 = T.matrix_to_out(T.read_matrix(ROOT / "data/W7.txt"))
res = {}
only = [int(x) for x in sys.argv[1:]] or [27, 26, 25, 24, 23, 22, 21]
for n in only:
    lines = [l.strip() for l in (CAT / f"tt6free{n}.d6").read_text().splitlines() if l.strip()]
    outs = [T.from_d6(l) for l in lines]
    for o in outs:
        T.check_tournament(o)
    r = {"count": len(outs)}
    r["all_tt6free"] = all(not T.has_tt(o, 6) for o in outs)
    can = T.canon_many(outs)
    r["distinct_classes"] = len(set(can))
    rc = set(T.canon_many([T.reverse(o) for o in outs]))
    r["closed_under_reversal"] = rc == set(can)
    sc = [l.strip() for l in (CAT / f"tt6free{n}_sc.d6").read_text().splitlines() if l.strip()] if (CAT / f"tt6free{n}_sc.d6").exists() else []
    r["self_converse_computed"] = sum(1 for o, c in zip(outs, T.canon_many([T.reverse(o) for o in outs])) if c == T.canon(o)) if n >= 22 else None
    r["sc_file_count"] = len(sc)
    if n in (23, 24):
        ours = set(T.canon_many([T.matrix_to_out(T.read_matrix(p)) for p in sorted((ROOT / "data").glob(f"I{n}_*.txt"))]))
        r["matches_NMH_classes"] = ours == set(can)
    if n == 22:
        r["with_Y8"] = sum(T.contains(o, Y8) for o in outs)
        r["with_revY8"] = sum(T.contains(o, Y8r) for o in outs)
        r["outdegree_sets"] = sorted({tuple(sorted(set(T.outdegrees(o)))) for o in outs})
        st = T.matrix_to_out(T.read_matrix(ROOT / "data/ST27.txt"))
        import itertools
        sub22 = set()
        # 22-vertex subtournaments of the 25 known 23s
        for p in sorted((ROOT / "data").glob("I23_*.txt")):
            o = T.matrix_to_out(T.read_matrix(p))
            sub22.update(T.canon_many([T.induced(o, [v for v in range(23) if v != d]) for d in range(23)]))
        r["subs_of_known_23"] = sum(c in sub22 for c in can)
        r["not_sub_of_any_23"] = len(can) - r["subs_of_known_23"]
    if n == 21:
        import random
        r["with_H6"] = sum(T.contains(o, H6) for o in outs)
        r["with_W7"] = sum(T.contains(o, W7) for o in outs)
        r["with_H6_or_W7"] = sum(T.contains(o, H6) or T.contains(o, W7) for o in outs)
        r["with_Y8"] = sum(T.contains(o, Y8) for o in outs)
        r["max_outdeg_hist"] = {}
        for o in outs:
            k = max(T.outdegrees(o)); r["max_outdeg_hist"][k] = r["max_outdeg_hist"].get(k, 0) + 1
    res[n] = r
    print(n, json.dumps(r), flush=True)
p = ROOT / "results/e5_lohn_catalogue.json"
old = json.loads(p.read_text()) if p.exists() else {}
old.update({str(k): v for k, v in res.items()})
p.write_text(json.dumps(old, indent=1))
