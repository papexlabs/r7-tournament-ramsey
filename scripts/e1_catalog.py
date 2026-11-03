"""E1: rebuild and cross-check the TT6-free catalogue facts used by the 47 proof.

Reads the authors' published matrices from refs/directed-ramsey-src (fetched by
scripts/fetch_refs.sh) only to compare against our own constructions.
Writes data/*.txt (our own constructions) and results/e1_catalog.json.
"""

import itertools
import json
import sys
import time
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))
import tourn as T  # noqa: E402

REPO = ROOT / "refs/directed-ramsey-src/Directed-Ramsey-master"
DATA = ROOT / "data"
DATA.mkdir(exist_ok=True)
res: dict = {}
t0 = time.time()


def load_full(path):
    return T.matrix_to_out(T.read_matrix(path))


def sub_classes(out, k):
    """Canonical classes of k-vertex subtournaments (by deleting n-k vertices)."""
    n = len(out)
    subs = []
    reps = {}
    for dele in itertools.combinations(range(n), n - k):
        keep = [v for v in range(n) if v not in dele]
        subs.append(T.induced(out, keep))
    cans = T.canon_many(subs)
    for c, s in zip(cans, subs):
        reps.setdefault(c, s)
    return reps


# --- ST27 ---------------------------------------------------------------
st = T.st27()
res["st27_outdegrees"] = sorted(set(T.outdegrees(st)))
res["st27_max_tt"] = T.max_tt(st)
theirs27 = load_full(REPO / "TT6-Free/27-Vertex/27-TT6-Free.txt")
res["st27_iso_to_published"] = T.canon(st) == T.canon(theirs27)
T.write_matrix(T.out_to_rows(st), DATA / "ST27.txt")
res["st27_reverse_iso"] = T.canon(T.reverse(st)) == T.canon(st)

# --- subtournament classes of ST27 ---------------------------------------
for k in (26, 25, 24, 23, 22):
    reps = sub_classes(st, k)
    res[f"sub_st27_{k}_classes"] = len(reps)
    if k in (24, 23):
        for idx, (c, s) in enumerate(sorted(reps.items())):
            T.write_matrix(T.out_to_rows(s), DATA / f"subST27_{k}_{idx:02d}.txt")
    if k == 22:
        sub22 = reps
    print(k, len(reps), f"{time.time()-t0:.1f}s", flush=True)

# compare with published 24A..24E and 23A..23V
pub24 = {x: load_full(REPO / f"TT6-Free/24-Vertex/24{x}.txt") for x in "ABCDE"}
pub23s = {
    x: load_full(REPO / f"TT6-Free/23-Vertex/SubST27/23{x}.txt")
    for x in "ABCDEFGHIJKLMNOPQRSTUV"
}
pub23d = {x: load_full(REPO / f"TT6-Free/23-Vertex/Doubly-Regular/23{x}.txt") for x in "WXY"}
own24 = set(sub_classes(st, 24))
own23 = set(sub_classes(st, 23))
c24 = dict(zip(pub24, T.canon_many(list(pub24.values()))))
c23s = dict(zip(pub23s, T.canon_many(list(pub23s.values()))))
c23d = dict(zip(pub23d, T.canon_many(list(pub23d.values()))))
res["published_24_match_own"] = sorted(c24.values()) == sorted(own24)
res["published_23sub_match_own"] = sorted(set(c23s.values())) == sorted(own23) and len(set(c23s.values())) == 22
res["published_23_all_tt6free"] = all(not T.has_tt(o, 6) for o in list(pub23s.values()) + list(pub23d.values()))
res["published_24_all_tt6free"] = all(not T.has_tt(o, 6) for o in pub24.values())

# reversal closure of the 25 classes of 23
all23 = {**pub23s, **pub23d}
can23 = {**c23s, **c23d}
rev_can = dict(zip(all23, T.canon_many([T.reverse(o) for o in all23.values()])))
inv = {v: k for k, v in can23.items()}
res["rev_map_23"] = {k: inv.get(rev_can[k], "NOT-IN-LIST") for k in all23}
rev24 = dict(zip(pub24, T.canon_many([T.reverse(o) for o in pub24.values()])))
inv24 = {v: k for k, v in c24.items()}
res["rev_map_24"] = {k: inv24.get(rev24[k], "NOT-IN-LIST") for k in pub24}

# --- doubly regular 23 ------------------------------------------------------
qr23 = T.qr_circulant(23)
res["qr23_tt6free"] = not T.has_tt(qr23, 6)
res["qr23_is"] = [k for k, c in c23d.items() if c == T.canon(qr23)]


def doubly_regular(o):
    n = len(o)
    d = set(T.outdegrees(o))
    if len(d) != 1:
        return False
    common = {bin(o[a] & o[b]).count("1") for a in range(n) for b in range(n) if a != b}
    return len(common) == 1


res["dr23_doubly_regular"] = {k: doubly_regular(o) for k, o in pub23d.items()}

# --- small forced structures --------------------------------------------------
def tail_block(path, m):
    rows = T.read_matrix(path)
    n = len(rows)
    blk = [r[n - m :] for r in rows[n - m :]]
    return T.matrix_to_out(blk)


H6 = tail_block(REPO / "log25/ST25-p-H6.txt", 6)
W7 = tail_block(REPO / "log25/ST25-p-W7.txt", 7)
Y8 = tail_block(REPO / "log23/23A-p-Y8.txt", 8)
for name, o in (("H6", H6), ("W7", W7), ("Y8", Y8)):
    T.write_matrix(T.out_to_rows(o), DATA / f"{name}.txt")
    res[f"{name}_outdeg"] = T.outdegrees(o)
    res[f"{name}_max_tt"] = T.max_tt(o)
    res[f"{name}_3cycles"] = T.three_cycles(o)
# H6 = TT3 => 3-cycle ; W7 (= G7 in the paper) = TT2 => regular 5-tournament
res["Y8_same_in_all_25_logs"] = len(
    set(T.canon_many([tail_block(REPO / f"log23/23{x}-p-Y8.txt", 8) for x in "ABCDEFGHIJKLMNOPQRSTUVWXY"]))
) == 1
res["Y8_in_all_25_23s"] = all(T.contains(o, Y8) for o in all23.values())
res["Y8_in_all_22sub_st27"] = sum(T.contains(o, Y8) for o in sub22.values())
res["n_22sub_st27"] = len(sub22)
res["Y8_rev_iso_Y8"] = T.canon(T.reverse(Y8)) == T.canon(Y8)

# --- counts of transitive subsets (sizes of encodings) ------------------------
tt_counts = {}
for name, o in list(pub24.items()) + [("ST25", T.induced(st, list(range(25)))), ("ST26", T.induced(st, list(range(26))))]:
    tt_counts[name] = [T.count_tt(o, a) for a in range(1, 6)]
for name in ("A", "W"):
    tt_counts["23" + name] = [T.count_tt(all23[name], a) for a in range(1, 6)]
res["tt_counts_a1..a5"] = tt_counts
res["seconds"] = round(time.time() - t0, 1)

(ROOT / "results").mkdir(exist_ok=True)
(ROOT / "results/e1_catalog.json").write_text(json.dumps(res, indent=1, sort_keys=True))
print(json.dumps(res, indent=1, sort_keys=True))
