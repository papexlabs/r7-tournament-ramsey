#!/bin/bash
# E2 validation batch (run from repo root). CPU cap ~30 min total, 4 in parallel, nice 10.
cd "$(dirname "$0")/.."
cat <<'JOBS' | xargs -P 4 -L 1 python3 scripts/run_sat.py
val-TT5free13 cnf/TT5free13.cnf cadical 60
val-TT5free14 cnf/TT5free14.cnf cadical 300 --lrat
val-ST26-p-TT5 cnf/ST26-p-TT5.cnf cadical 600 --lrat
calib-ST25-p-H6-nmh cnf/ST25-p-H6.nmh.cnf cadical 600 --opts=--stabilize=false_--walk=false
val-TT6free27 cnf/TT6free27.cnf cadical 180
val-TT6free28 cnf/TT6free28.cnf cadical 180
JOBS
