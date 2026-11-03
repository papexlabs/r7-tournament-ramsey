#!/bin/bash
# E8: (24,21) pivot instances with out-structure Z_m (fewest-3-cycle
# subtournaments of O21*), 60 s cadical each, 3 in parallel, nice 10.
cd "$(dirname "$0")/.."
cat > build/.jobsz <<'JOBS'
q-24A-p-Z8 cnf/24A-p-Z8.cnf cadical 60
q-24B-p-Z8 cnf/24B-p-Z8.cnf cadical 60
q-24A-p-Z10 cnf/24A-p-Z10.cnf cadical 60
q-24B-p-Z10 cnf/24B-p-Z10.cnf cadical 60
q-24A-p-Z12tri cnf/24A-p-Z12.tri.cnf cadical 60
q-24B-p-Z12tri cnf/24B-p-Z12.tri.cnf cadical 60
JOBS
xargs -P 3 -L 1 python3 scripts/run_sat.py < build/.jobsz
