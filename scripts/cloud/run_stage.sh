#!/bin/bash
# On the server, in ~/tr, under nohup:
#   nohup bash scripts/cloud/run_stage.sh STAGE WORKERS [GRACE_MIN] > results/STAGE.log 2>&1 &
# STAGE: stage1 (TT6-free n=22 and n=23 enumerations + LRAT certification; n=24, n=25 re-run)
#        stage2 (TT6-free n=21 enumeration + certification)
#        stage12 (stage1 then stage2 on the same instance)
#        stage3 (the five instances I24X -p- O21*, cube-and-conquer with streamed LRAT checks)
#        stage3-XYZ (only instances X, Y, Z of A..E, e.g. stage3-ABC and stage3-DE on two boxes)
# When the stage ends (success or failure) it writes results/<STAGE>.DONE and moves the
# power-off to GRACE_MIN minutes from now (default 60) -- never later than the hard stop
# armed by user-data -- so the Mac has time to sync results back.
set -uo pipefail
cd "$(dirname "$0")/../.."
STAGE="$1"; W="$2"; GRACE="${3:-60}"
ulimit -n 65536 2>/dev/null || ulimit -n "$(ulimit -Hn)"
mkdir -p results/enum results/stage3
log() { echo "$(date -u '+%F %T') $*"; }
rc=0

enum_and_certify() {  # k n workers
  local k=$1 n=$2 w=$3 out="results/enum/k${1}n${2}"
  log "enumerate k=$k n=$n"
  python3 -I scripts/pivot_enum.py "$k" "$n" "$out" --workers "$w" --batch 10 --nice 5 || return 1
  log "certify k=$k n=$n"
  python3 -I scripts/certify_enum.py "$out" --workers "$(( w * 3 / 4 ))" || return 1
  grep -q '"all_jobs_verified": true' "$out/certify_summary.json" || { log "CERTIFY INCOMPLETE n=$n"; return 1; }
  grep -q '"all_complete": true' "$out/summary.json" || { log "ENUM INCOMPLETE n=$n"; return 1; }
  log "n=$n done: $(cat $out/summary.json | head -c 300)"
}

case "$STAGE" in
  stage1)
    for n in 25 24; do rm -rf "results/enum/k6n$n"; enum_and_certify 6 $n "$W" || rc=1; done
    enum_and_certify 6 22 "$W" || rc=1
    enum_and_certify 6 23 "$W" || rc=1
    ;;
  stage2)
    enum_and_certify 6 21 "$W" || rc=1
    ;;
  stage12)
    for n in 25 24; do rm -rf "results/enum/k6n$n"; enum_and_certify 6 $n "$W" || rc=1; done
    enum_and_certify 6 22 "$W" || rc=1
    enum_and_certify 6 23 "$W" || rc=1
    enum_and_certify 6 21 "$W" || rc=1
    ;;
  stage3|stage3-*)
    # stage3 = all five; stage3-ABC = instances A, B, C only (e.g. one of two 96-vCPU boxes)
    LIST="A B C D E"; [ "$STAGE" != stage3 ] && LIST=$(echo "${STAGE#stage3-}" | sed 's/./& /g')
    NX=$(echo $LIST | wc -w); WX=$(( W / NX ))
    for X in $LIST; do   # prepare all instances first (encode ~5 s each, 1 GB CNF each)
      d="results/stage3/24$X-p-O21s"; mkdir -p "$d"
      if [ ! -f "cnf/24$X-p-O21s.tri.cnf" ]; then
        python3 -I src/instances.py "data/I24_$X.txt" data/O21star.txt "cnf/24$X-p-O21s.txt"
        build/encode "cnf/24$X-p-O21s.txt" 7 1 "cnf/24$X-p-O21s.tri.cnf"
      fi
      [ -f "$d/cubes.icnf" ] || python3 -I scripts/make_cubes.py "cnf/24$X-p-O21s.tri.cnf" "$d/cubes.icnf" --k 10 --maxvar 504
    done
    pids=""
    for X in $LIST; do   # the instances run side by side, W/NX workers each
      d="results/stage3/24$X-p-O21s"
      log "conquer 24$X with $WX workers"
      python3 -I scripts/run_cubes.py "cnf/24$X-p-O21s.tri.cnf" "$d/cubes.icnf" "$d/run" \
        --workers "$WX" --timeouts 600,1800,0 --split 4 --maxvar 504 --nice 5 --min-free-gb 24 \
        > "$d/conquer.log" 2>&1 &
      pids="$pids $!"
    done
    for p in $pids; do wait "$p" || rc=1; done
    for X in $LIST; do
      d="results/stage3/24$X-p-O21s"
      python3 -I scripts/cnc_summary.py "cnf/24$X-p-O21s.tri.cnf" "$d/cubes.icnf" "$d/run" || rc=1
      grep -q '"ALL CLOSED"' "$d/run/summary.json" && log "24$X ALL CLOSED" || { log "24$X NOT CLOSED"; rc=1; }
    done
    ;;
  *) echo "unknown stage $STAGE"; exit 2 ;;
esac

log "stage $STAGE finished rc=$rc"
echo "$rc" > "results/$STAGE.DONE"
# move the power-off to GRACE minutes from now, but never past the user-data hard stop
if [ -f /run/systemd/shutdown/scheduled ]; then
  hard_usec=$(sed -n 's/^USEC=//p' /run/systemd/shutdown/scheduled)
  now_usec=$(( $(date +%s) * 1000000 ))
  left_min=$(( (hard_usec - now_usec) / 60000000 ))
  [ "$left_min" -gt "$GRACE" ] && sudo shutdown -h +"$GRACE" "stage done; grace for sync"
fi
