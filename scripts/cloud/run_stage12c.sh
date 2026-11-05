#!/bin/bash
# Run 2 of Stages 1-2 (after the lrat-check fix of 5 Nov 2026), on the server, in ~/tr:
#   nohup bash scripts/cloud/run_stage12c.sh WORKERS [GRACE_MIN] > results/stage12.log 2>&1 < /dev/null &
# For n = 26, 25, 24, 23, 22, 21 (TT6-free tournaments; n = 26 certifies that ST26 is unique):
#   certify_first.py (one LRAT-checked solve per job; AllSAT only for SAT jobs),
#   pivot_enum.py (aggregation: summary.json, classes.d6; enumerates nothing if certify_first finished),
#   certify_enum.py (the SAT jobs with their blocking clauses; every model must fit its job),
# with the flags of run_stage12b.sh, into results/enum/k6n<n>.  Every n must end with all_complete
# and all_jobs_verified.  Resumable: rerun the same command; finished jobs are skipped via
# records.jsonl / certify.jsonl, and an n that is already complete and verified is skipped.
# At the end: results/stage12.DONE (0 = every n complete and verified).  If GRACE_MIN (default 60)
# is less than the time left to the user-data hard stop, the power-off moves to GRACE_MIN minutes
# from now (as in run_stage12b.sh); pass a large GRACE_MIN (e.g. 99999) when the box goes on to
# Stage 4, so the hard stop stays where it is.
# On the Mac after sync: python3 scripts/stage12_check.py (classes vs Lohn, NMH, ST26/ST27; GO lines).
set -uo pipefail
cd "$(dirname "$0")/../.."
W="${1:?workers}"; GRACE="${2:-60}"; STAGE=stage12
ulimit -n 65536 2>/dev/null || ulimit -n "$(ulimit -Hn)"
log() { echo "$(date -u '+%F %T') [stage12c] $*"; }
mkdir -p results/enum

busy() { pgrep -f '^(bash scripts/cloud/run_stage(\.sh|12b\.sh)|python3 -I scripts/(pivot_enum|certify_enum|certify_first)\.py)' > /dev/null; }
if busy; then
  log "another enumeration driver or job is running: $(pgrep -fa '^(bash scripts/cloud/run_stage|python3 -I scripts/)' | cut -c1-90 | tr '\n' ';'); not starting"
  exit 2
fi
for b in build/pivenum build/lrat-check; do
  [ -x "$b" ] || { log "$b missing: run scripts/cloud/setup.sh first"; exit 2; }
done

rc=0
verified() {  # dir
  grep -q '"all_complete": true' "$1/summary.json" 2>/dev/null &&
  grep -q '"all_jobs_verified": true' "$1/certify_summary.json" 2>/dev/null
}
certify_first() {  # n
  local out="results/enum/k6n$1"
  log "n=$1: certify_first"
  python3 -I scripts/certify_first.py 6 "$1" "$out" --workers "$W" --nice 5 || return 1
  log "n=$1: pivot_enum (aggregation; enumerates nothing if certify_first finished)"
  python3 -I scripts/pivot_enum.py 6 "$1" "$out" --workers "$W" --batch 10 --nice 5 || return 1
  log "n=$1: certify_enum (the SAT jobs, with their blocking clauses)"
  python3 -I scripts/certify_enum.py "$out" --workers "$W" || return 1
}
NS="${STAGE12_NS:-26 25 24 23 22 21}"   # STAGE12_NS: a subset, for local tests only
for n in $NS; do
  if verified "results/enum/k6n$n"; then log "n=$n already complete and VERIFIED"; continue; fi
  certify_first "$n" || { log "n=$n: a step failed"; rc=1; }
done
for n in $NS; do
  if verified "results/enum/k6n$n"; then log "n=$n complete and VERIFIED: $(head -c 200 results/enum/k6n$n/summary.json | tr '\n' ' ')"
  else log "n=$n NOT complete/verified"; rc=1; fi
done

log "stage12 (run 2) finished rc=$rc"
echo "$rc" > "results/$STAGE.DONE"
# move the power-off to GRACE minutes from now, but never past the user-data hard stop
if [ -f /run/systemd/shutdown/scheduled ]; then
  hard_usec=$(sed -n 's/^USEC=//p' /run/systemd/shutdown/scheduled)
  now_usec=$(( $(date +%s) * 1000000 ))
  left_min=$(( (hard_usec - now_usec) / 60000000 ))
  [ "$left_min" -gt "$GRACE" ] && sudo shutdown -h +"$GRACE" "stage done; grace for sync"
fi
