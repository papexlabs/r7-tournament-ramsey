#!/bin/bash
# Take over stage12 from run_stage.sh without losing work (on the server, in ~/tr).
#
#   # 1) stop ONLY the old driver's bash parent (its python child keeps running):
#   kill $(pgrep -f '^bash scripts/cloud/run_stage.sh stage12')
#   # 2) start this driver (it refuses to run while that parent is alive):
#   nohup bash scripts/cloud/run_stage12b.sh WORKERS [GRACE_MIN] >> results/stage12.log 2>&1 < /dev/null &
#
# Steps (each one resumable: finished jobs are skipped via records.jsonl / certify.jsonl):
#   0. wait until no enumeration/certification python is running (the n=22
#      pivot_enum.py inherited from run_stage.sh, or a certify_enum.py);
#   1. n=22: pivot_enum.py (completes any missing job, writes summary/classes),
#      then certify_enum.py (classic path: blocking clauses per job);
#   2. n=23, then n=21: certify_first.py (one LRAT-checked solve per job; AllSAT only
#      for SAT jobs), pivot_enum.py (aggregation), certify_enum.py (SAT jobs);
#   3. every n must have all_complete and all_jobs_verified; writes results/stage12.DONE
#      (0 = ok) and moves the power-off to GRACE_MIN (default 60) minutes from now, never
#      later than the hard stop armed by user-data (same as run_stage.sh).
# After a spot reclaim: relaunch, `bash scripts/cloud/push.sh IP --results` (code + the
# results synced to the Mac, models included), setup.sh, and start this script again.
set -uo pipefail
cd "$(dirname "$0")/../.."
W="${1:?workers}"; GRACE="${2:-60}"; STAGE=stage12
ulimit -n 65536 2>/dev/null || ulimit -n "$(ulimit -Hn)"
log() { echo "$(date -u '+%F %T') [stage12b] $*"; }

if pgrep -f '^bash scripts/cloud/run_stage.sh' > /dev/null; then
  log "run_stage.sh is still alive: kill its bash parent first (see header); not starting"
  exit 2
fi
busy() { pgrep -f '^python3 -I scripts/(pivot_enum|certify_enum|certify_first)\.py' > /dev/null; }
while busy; do log "waiting for running enumeration/certification: $(pgrep -fa '^python3 -I scripts/' | cut -c1-90 | tr '\n' ';')"; sleep 300; done

rc=0
verified() {  # dir
  grep -q '"all_complete": true' "$1/summary.json" 2>/dev/null &&
  grep -q '"all_jobs_verified": true' "$1/certify_summary.json" 2>/dev/null
}
classic() {  # n
  local out="results/enum/k6n$1"
  log "n=$1: pivot_enum (resume/aggregate)"
  python3 -I scripts/pivot_enum.py 6 "$1" "$out" --workers "$W" --batch 10 --nice 5 || return 1
  log "n=$1: certify_enum"
  python3 -I scripts/certify_enum.py "$out" --workers "$W" || return 1
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
for n in 25 24; do verified "results/enum/k6n$n" || { log "n=$n not verified yet"; classic $n || rc=1; }; done
verified results/enum/k6n22 || classic 22 || rc=1
verified results/enum/k6n23 || certify_first 23 || rc=1
verified results/enum/k6n21 || certify_first 21 || rc=1
for n in 25 24 22 23 21; do
  if verified "results/enum/k6n$n"; then log "n=$n complete and VERIFIED: $(head -c 200 results/enum/k6n$n/summary.json | tr '\n' ' ')"
  else log "n=$n NOT complete/verified"; rc=1; fi
done

log "stage12 (takeover) finished rc=$rc"
echo "$rc" > "results/$STAGE.DONE"
if [ -f /run/systemd/shutdown/scheduled ]; then
  hard_usec=$(sed -n 's/^USEC=//p' /run/systemd/shutdown/scheduled)
  now_usec=$(( $(date +%s) * 1000000 ))
  left_min=$(( (hard_usec - now_usec) / 60000000 ))
  [ "$left_min" -gt "$GRACE" ] && sudo shutdown -h +"$GRACE" "stage done; grace for sync"
fi
