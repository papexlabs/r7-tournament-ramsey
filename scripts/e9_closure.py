"""E9: deletion-closure consistency of the Lohn TT6-free files (n = 20..23).

A complete catalogue C_n must contain every (n-1)-vertex subtournament of
every member of C_{n+1}.  We check C_22 -> C_21 (all 21-subs of the 89) and
C_23 -> C_22, and optionally C_21 -> C_20 (357,840 canonical forms).
Also: number of members of C_n that are subtournaments of a member of
C_{n+1} ("extendable") -- a complete catalogue need not have all extendable.
Necessary conditions only; they do not prove completeness.
"""
import json, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))
import tourn as T
CAT = ROOT / "refs/digraph-isolators-src/digraph_isolators-HEAD/tt6free_tournaments"
def load(n): return [l.strip() for l in (CAT / f"tt6free{n}.d6").read_text().split() if l.strip()]
res = {}
levels = [int(x) for x in sys.argv[1:]] or [23, 22]
for big in levels:
    small = big - 1
    B = [T.from_d6(l) for l in load(big)]
    S = set(T.canon_many([T.from_d6(l) for l in load(small)]))
    subs = set()
    chunk = []
    for o in B:
        for d in range(big):
            chunk.append(T.induced(o, [v for v in range(big) if v != d]))
        if len(chunk) > 20000:
            subs.update(T.canon_many(chunk)); chunk = []
    subs.update(T.canon_many(chunk))
    r = {"n_big": len(B), "distinct_subs": len(subs), "subs_missing_from_small_file": len(subs - S),
         "small_file_size": len(S), "small_members_extendable": len(S & subs)}
    res[f"{big}->{small}"] = r
    print(big, small, r, flush=True)
p = ROOT / "results/e9_closure.json"
old = json.loads(p.read_text()) if p.exists() else {}
old.update(res); p.write_text(json.dumps(old, indent=1))
