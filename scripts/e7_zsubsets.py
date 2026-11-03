"""E7: subtournaments Z_m of O21* (the unique Y8-free TT6-free 21-vertex
tournament of the Lohn catalogue) with the fewest 3-cycles, m = 8..16.
Exhaustive with vertex 0 fixed for m <= 9 (O21* is vertex-transitive if
Aut acts transitively, checked below), then greedy growth + 1-swap local
search.  Writes data/O21s_Z{m}.txt.
"""
import itertools, json, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))
import tourn as T
o = T.matrix_to_out(T.read_matrix(ROOT / "data/O21star.txt"))
n = len(o)
def cyc(S):
    mask = 0
    for v in S: mask |= 1 << v
    m = len(S)
    return m*(m-1)*(m-2)//6 - sum((lambda d: d*(d-1)//2)(bin(o[v] & mask).count("1")) for v in S)
# vertex transitivity: orbit of 0 under automorphisms (embeddings of o into o)
orb = set()
import random
emb_all = []
def all_auts():
    res = []
    m = n; order = list(range(n)); full = (1<<n)-1
    inn = [0]*n
    for i in range(n):
        for j in range(n):
            if o[i]>>j&1: inn[j] |= 1<<i
    img = [0]*n
    def rec(t, used):
        if t == n: res.append(img[:]); return
        cand = full & ~used
        for u in range(t):
            cand &= o[img[u]] if (o[u]>>t&1) else inn[img[u]]
        while cand:
            x = (cand & -cand).bit_length()-1; cand &= cand-1
            img[t] = x; rec(t+1, used | (1<<x))
    rec(0, 0); return res
auts = all_auts()
vt = len({a[0] for a in auts}) == n
res = {"aut_order": len(auts), "vertex_transitive": vt, "Z": {}}
best = {}
for m in range(8, 17):
    if m <= 9 and vt:
        cands = ([0] + list(c) for c in itertools.combinations(range(1, n), m - 1))
        bestS = min(cands, key=cyc)
    else:
        prev = best[m-1]
        bestS = min((prev + [v] for v in range(n) if v not in prev), key=cyc)
        improved = True
        while improved:
            improved = False
            for i in range(m):
                for v in range(n):
                    if v in bestS: continue
                    S2 = bestS[:i] + [v] + bestS[i+1:]
                    if cyc(S2) < cyc(bestS): bestS, improved = S2, True
    best[m] = sorted(bestS)
    Z = T.induced(o, best[m])
    T.write_matrix(T.out_to_rows(Z), ROOT / f"data/O21s_Z{m}.txt")
    res["Z"][m] = {"verts": best[m], "3cycles": cyc(best[m]), "max_tt": T.max_tt(Z), "outdeg": sorted(T.outdegrees(Z), reverse=True)}
    print(m, res["Z"][m], flush=True)
(ROOT / "results/e7_zsubsets.json").write_text(json.dumps(res, indent=1))
print("aut", len(auts), "vt", vt)
