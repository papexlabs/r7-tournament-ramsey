"""Independent audit check: the cube tree of a run_cubes.py run is closed.

Written on 5 Nov 2026 by an external auditor apart from scripts/cnc_summary.py and kept as a
separate tool on purpose (no solver, no checker; records only).

DIR holds cubes.icnf (static level-0 split, scripts/make_cubes.py) and run/results.jsonl.
Checks:
 - the level-0 cubes are all 2^K sign patterns of one set of K distinct variables (so they cover
   every assignment by construction);
 - starting from cube i (record id "i"), every node has a record with exactly its literals; an
   UNSAT record must have check VERIFIED (a leaf); an UNKNOWN record must have children
   "id.0", "id.1", ... that extend its literals by the same S fresh variables (not fixed by
   the parent) in all 2^S sign patterns, and each child is visited in turn; any other status
   (SAT) is a problem.
The latest record of an id counts (a cube re-run after a failed check appears twice); the
number of such repeated ids and of records outside the tree is printed.
usage: python3 scripts/audit/closure.py DIR      exit 0 iff no problem and at least one leaf
"""
import itertools
import json
import sys

sys.setrecursionlimit(10000)
d = sys.argv[1].rstrip("/")
cubes = []
for line in open(d + "/cubes.icnf"):
    if line.startswith("a "):
        l = [int(x) for x in line.split()[1:]]
        assert l[-1] == 0
        cubes.append(l[:-1])
bad = []
vs = [tuple(sorted(abs(x) for x in c)) for c in cubes]
if len(set(vs)) != 1:
    bad.append(("level-0 variable sets differ",))
else:
    V = vs[0]
    pats = {tuple(sorted(c, key=abs)) for c in cubes}
    if len(set(V)) != len(V) or not (len(pats) == 2 ** len(V) == len(cubes)):
        bad.append(("level-0 cubes are not all sign patterns", len(pats), len(cubes)))
recs, repeated = {}, 0
for line in open(d + "/run/results.jsonl"):
    r = json.loads(line)
    repeated += r["id"] in recs
    recs[r["id"]] = r
used = set()
leaves = 0


def visit(cid, lits):
    global leaves
    r = recs.get(cid)
    if r is None:
        bad.append(("missing", cid))
        return
    used.add(cid)
    if r["lits"] != lits:
        bad.append(("lits mismatch", cid))
        return
    if r["status"] == "UNSAT":
        if r["check"] != "VERIFIED":
            bad.append(("unverified", cid))
        leaves += 1
        return
    if r["status"] != "UNKNOWN":
        bad.append(("status", cid, r["status"]))
        return
    kids = [k for k in recs if k.startswith(cid + ".") and k.count(".") == cid.count(".") + 1]
    if not kids:
        bad.append(("no kids", cid))
        return
    S = len(recs[kids[0]]["lits"]) - len(lits)
    if S <= 0:
        bad.append(("S", cid))
        return
    ext = [recs[k]["lits"][len(lits):] for k in kids]
    for k in kids:
        if recs[k]["lits"][:len(lits)] != lits or len(recs[k]["lits"]) != len(lits) + S:
            bad.append(("prefix", k))
    varsets = {tuple(abs(x) for x in e) for e in ext}
    if len(varsets) != 1:
        bad.append(("varsets", cid))
        return
    nv = next(iter(varsets))
    if len(set(nv)) != S or set(nv) & {abs(x) for x in lits}:
        bad.append(("fresh", cid))
    if {tuple(e) for e in ext} != {tuple(v if s else -v for v, s in zip(nv, bits))
                                   for bits in itertools.product([0, 1], repeat=S)}:
        bad.append(("not all patterns", cid))
    for k in kids:
        visit(k, recs[k]["lits"])


for i, c in enumerate(cubes):
    visit(str(i), c)
unused = set(recs) - used
maxv = max((abs(x) for r in recs.values() for x in r["lits"]), default=0)
print(d.split("/")[-1], "leaves", leaves, "bad", bad[:5], len(bad), "unused records", len(unused),
      "repeated ids", repeated, "max var in cubes", maxv)
sys.exit(0 if not bad and leaves > 0 else 1)
