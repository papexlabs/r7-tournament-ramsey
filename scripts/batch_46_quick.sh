#!/bin/bash
# E6: first look at the (24,21) pivot instances I24 -p- {H6,W7} and (for
# contrast) I23 -p- {H6,W7}; 60 s cadical each, 3 in parallel, nice 10.
cd "$(dirname "$0")/.."
for L in A B C D E; do for Z in H6 W7; do echo "q-24$L-p-$Z cnf/24$L-p-$Z.cnf cadical 60"; done; done > build/.jobs46
for L in A W Y; do for Z in H6 W7; do echo "q-23$L-p-$Z cnf/23$L-p-$Z.cnf cadical 30"; done; done >> build/.jobs46
xargs -P 3 -L 1 python3 scripts/run_sat.py < build/.jobs46
rm -f build/.jobs46
