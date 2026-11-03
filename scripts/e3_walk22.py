"""E3b: random walk on TT6-free tournaments on m vertices by single arc reversals.

Start: a TT6-free m-vertex subtournament of a known 23-vertex one.  Step:
reverse a uniformly random arc; keep the move iff the result is still
TT6-free (only TT6s through the reversed arc need checking).  Every
`every` accepted moves the current tournament is canonicalised and tested
for Y8 (and reversed Y8).  Evidence only: a Y8-free sample would show that
Y8 is avoidable at m vertices; finding none proves nothing.

usage: e3_walk22.py START(I23 letter) m steps every seed
"""
import json, random, sys, time
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))
import tourn as T

letter, m, steps, every, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
rng = random.Random(seed)
Y8 = T.matrix_to_out(T.read_matrix(ROOT / "data/Y8.txt")); Y8r = T.reverse(Y8)
big = T.matrix_to_out(T.read_matrix(ROOT / f"data/I23_{letter}.txt"))
keep = sorted(rng.sample(range(23), m))
out = T.induced(big, keep)
assert not T.has_tt(out, 6)
inn = [0] * m
for i in range(m):
    for j in range(m):
        if out[i] >> j & 1: inn[j] |= 1 << i

def tt_through(u, v, need):
    """Is there a TT_need containing the arc u->v?  Vertices before u must beat
    u and v, between u and v: beaten by u and beating v, after v: beaten by both."""
    full = (1 << m) - 1
    A = inn[u] & inn[v]            # before u
    B = out[u] & inn[v]            # between
    C = out[u] & out[v]            # after v
    # TT in A then u then TT in B then v then TT in C, with all forward arcs;
    # need a chain a1>..>ar (in A), b's (in B), c's (in C) with sizes summing to need-2
    def best(cand):  # largest transitive subtournament inside cand, capped at need
        b = 0
        def rec(c, d):
            nonlocal b
            if d > b: b = d
            if b >= need: return
            if d + bin(c).count("1") <= b: return
            x = c
            while x:
                w = (x & -x).bit_length() - 1; x &= x - 1
                rec(c & out[w], d + 1)
        rec(cand, 0); return b
    # exact: enumerate transitive chains greedily across the three blocks
    def rec2(stage, allowed, d):
        # stage 0: choose from A (then may move to stage 1), 1: from B, 2: from C
        if d >= need - 2: return True
        blocks = [A, B, C]
        for s in range(stage, 3):
            c = allowed & blocks[s]
            x = c
            while x:
                w = (x & -x).bit_length() - 1; x &= x - 1
                if rec2(s, allowed & out[w], d + 1): return True
        return False
    return rec2(0, full, 0)

acc = tried = 0
seen = {}
rows = []
t0 = time.time()
for st in range(steps):
    u, v = rng.sample(range(m), 2)
    if not (out[u] >> v & 1): u, v = v, u   # u -> v currently
    tried += 1
    # reverse to v -> u
    out[u] &= ~(1 << v); inn[v] &= ~(1 << u); out[v] |= 1 << u; inn[u] |= 1 << v
    if tt_through(v, u, 6):
        out[v] &= ~(1 << u); inn[u] &= ~(1 << v); out[u] |= 1 << v; inn[v] |= 1 << u
        continue
    acc += 1
    if acc % every == 0:
        c = T.canon(out)
        if c not in seen:
            seen[c] = (T.contains(out, Y8), T.contains(out, Y8r))
            rows.append({"acc": acc, "y8": seen[c][0], "revy8": seen[c][1], "d6": c if not seen[c][0] else ""})
assert not T.has_tt(out, 6)
res = {"start": letter, "m": m, "steps": steps, "tried": tried, "accepted": acc,
       "classes_checked": len(seen), "with_Y8": sum(a for a, b in seen.values()),
       "without_Y8": sum(not a for a, b in seen.values()),
       "without_Y8_and_revY8": sum((not a) and (not b) for a, b in seen.values()),
       "seconds": round(time.time() - t0, 1),
       "first_without_Y8": next((r["d6"] for r in rows if not r["y8"]), None)}
(ROOT / f"results/e3_walk{m}_{letter}_seed{seed}.json").write_text(json.dumps(res, indent=1))
print(json.dumps(res, indent=1))
