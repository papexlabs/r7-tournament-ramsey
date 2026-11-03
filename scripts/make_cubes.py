"""Static level-0 split: all 2^K sign patterns of K chosen variables, as an iCNF cube file.

The K variables are the most frequent variables <= --maxvar in the CNF (arc
variables come first in our encodings), or an explicit --vars list.
usage: make_cubes.py CNF OUT.icnf --k K [--maxvar V] [--vars 1,2,3]
"""
import argparse
import collections

ap = argparse.ArgumentParser()
ap.add_argument("cnf")
ap.add_argument("out")
ap.add_argument("--k", type=int, default=10)
ap.add_argument("--maxvar", type=int, default=0)
ap.add_argument("--vars", default="")
a = ap.parse_args()
if a.vars:
    vs = [int(x) for x in a.vars.split(",")]
else:
    freq = collections.Counter()
    with open(a.cnf) as fh:
        fh.readline()
        for line in fh:
            for x in line.split()[:-1]:
                v = abs(int(x))
                if not a.maxvar or v <= a.maxvar:
                    freq[v] += 1
    vs = [v for v, _ in freq.most_common(a.k)]
with open(a.out, "w") as fh:
    fh.write(f"c static split on vars {','.join(map(str, vs))}\n")
    for m in range(1 << len(vs)):
        fh.write("a " + " ".join(str(v if (m >> t) & 1 else -v) for t, v in enumerate(vs)) + " 0\n")
print(f"{1 << len(vs)} cubes on vars {vs}")
