#!/bin/bash
# Stage 4: re-run NMH's long computations (arXiv 2011.00683, section 5.2) as cube-and-conquer
# with streamed, checked LRAT proofs.  On the server, in ~/tr, under nohup:
#   nohup bash scripts/cloud/run_stage4.sh STAGE WORKERS [GRACE_MIN] > results/STAGE.log 2>&1 < /dev/null &
# STAGE: stage4           all 28 instances
#        stage4-<codes>   a subset, one letter per instance:
#                           A..Y = 23X-p-Y8,  t = ST26-p-TT5,  h = ST25-p-H6,  w = ST25-p-W7
#                         e.g. stage4-SHLFGEOt and stage4-ABCDIJKMNPQRTUVWXYhw on two boxes
# Environment (optional): SLOTS (instances side by side, default: all of the stage's instances;
#   WORKERS/SLOTS workers each), TIMEOUTS (run_cubes levels, default 1800,3600,1800,7200,0, the
#   schedule that finished run 1), MINFREE (GB, default 8),
#   POLL (scheduler poll seconds, default 20), STAGE4_NAMES (explicit instance names; tests only).
# Steps: fetch NMH's repository if missing; build every CNF with NMH's encoder and require the
# sha256 recorded in data/stage4_manifest.json; static 2^K cubes; run_cubes.py per instance,
# longest expected first, SLOTS at a time; cnc_summary.py per instance must say ALL CLOSED.
# A SAT cube contradicts NMH: its model is checked with verify_model.py, the stage stops (all
# solvers killed), and results/STAGE.SAT is written.  Resumable: rerun the same command (after a
# spot reclaim: new box, push.sh IP --results); finished cubes and closed instances are skipped.
# At the end: results/STAGE.DONE (0 = every instance ALL CLOSED) and the power-off moves to
# GRACE_MIN minutes from now (default 60), never past the user-data hard stop.
set -uo pipefail
cd "$(dirname "$0")/../.."
STAGE="$1"; W="$2"; GRACE="${3:-60}"
SLOTS="${SLOTS:-0}"; TIMEOUTS="${TIMEOUTS:-1800,3600,1800,7200,0}"; MINFREE="${MINFREE:-8}"   # SLOTS 0 = all
ulimit -n 65536 2>/dev/null || ulimit -n "$(ulimit -Hn)"
mkdir -p results/stage4 cnf/stage4
log() { echo "$(date -u '+%F %T') $*"; }
rc=0
SATFLAG="results/$STAGE.SAT"
NMH=refs/directed-ramsey-src/Directed-Ramsey-master

code_name() {
  case "$1" in
    t) echo ST26-p-TT5 ;; h) echo ST25-p-H6 ;; w) echo ST25-p-W7 ;;
    [A-Y]) echo "23$1-p-Y8" ;;
    *) return 1 ;;
  esac
}

if [ -n "${STAGE4_NAMES:-}" ]; then
  ONLY=$(echo $STAGE4_NAMES | tr ' ' ',')
else
  case "$STAGE" in
    stage4) CODES="thwABCDEFGHIJKLMNOPQRSTUVWXY" ;;
    stage4-?*) CODES="${STAGE#stage4-}" ;;
    *) echo "unknown stage $STAGE"; exit 2 ;;
  esac
  ONLY=""
  for c in $(echo "$CODES" | sed 's/./& /g'); do
    nm=$(code_name "$c") || { echo "unknown instance code '$c' in $STAGE"; exit 2; }
    ONLY="$ONLY,$nm"
  done
  ONLY="${ONLY#,}"
fi
NAMES=$(python3 -I scripts/stage4_instances.py list --only "$ONLY") || exit 2   # longest expected first
NX=$(echo $NAMES | wc -w | tr -d " ")   # tr: BSD wc pads with spaces
{ [ "$SLOTS" -le 0 ] || [ "$SLOTS" -gt "$NX" ]; } && SLOTS=$NX
WX=$(( W / SLOTS )); [ "$WX" -lt 1 ] && WX=1
log "stage $STAGE: $NX instances, $SLOTS side by side with $WX workers each, timeouts $TIMEOUTS: $NAMES"

if [ ! -f "$NMH/encoding/tour-encode.c" ]; then
  log "fetching NMH's repository (encoder and inputs; every file used is checked against the manifest)"
  mkdir -p refs/directed-ramsey-src
  curl -fsSL -A 'PapexResearchBot/1.0 (+https://papex.org)' -o refs/directed-ramsey-src/repo.tar.gz \
       https://codeload.github.com/neimandavid/Directed-Ramsey/tar.gz/refs/heads/master \
    && tar xzf refs/directed-ramsey-src/repo.tar.gz -C refs/directed-ramsey-src \
    || log "FETCH FAILED: copy refs/directed-ramsey-src from the Mac (see notes/STAGE4.md)"
fi

prep() {  # build + sha256 check, cubes; writes results/stage4/NAME/prep.ok on success
  local name=$1 d="results/stage4/$1" tk ck mv inp
  mkdir -p "$d"; rm -f "$d/prep.ok"
  python3 -I scripts/stage4_instances.py build "$name" || return 1
  read -r tk ck mv inp < <(python3 -I scripts/stage4_instances.py param "$name") || return 1
  if [ ! -f "$d/cubes.icnf" ]; then
    python3 -I scripts/make_cubes.py "cnf/stage4/$name.cnf" "$d/cubes.icnf.tmp" --k "$ck" --maxvar "$mv" \
      && mv "$d/cubes.icnf.tmp" "$d/cubes.icnf" || return 1
  fi
  echo "$tk $ck $mv $inp" > "$d/prep.ok"
}
closed() { grep -q '"ALL CLOSED"' "results/stage4/$1/run/summary.json" 2>/dev/null; }

log "prepare (NMH encoder, sha256 against the manifest, cubes)"
python3 -I scripts/stage4_instances.py encoder || log "ENCODER BUILD FAILED"
for name in $NAMES; do
  closed "$name" && continue
  prep "$name" > "results/stage4/$name.prep.log" 2>&1 &
done
wait
for name in $NAMES; do
  closed "$name" && continue
  [ -f "results/stage4/$name/prep.ok" ] || { log "PREPARE FAILED for $name: $(tail -2 results/stage4/$name.prep.log | tr '\n' ' ')"; rc=1; }
done

stop_all() {  # kill every run_cubes / cadical / lrat-check of this stage
  pkill -f 'scripts/run_cubes.py cnf/stage4/' 2>/dev/null
  sleep 2
  pkill -f 'results/stage4/.*/run/tmp/' 2>/dev/null
}

conquer() {  # one instance; returns 0 (finished), 3 (SAT), 1 (other failure)
  local name=$1 d="results/stage4/$1" tk ck mv inp f
  read -r tk ck mv inp < "$d/prep.ok"
  local n0; n0=$(cat "$d/conquer.log" 2>/dev/null | wc -l)
  python3 -I scripts/run_cubes.py "cnf/stage4/$name.cnf" "$d/cubes.icnf" "$d/run" \
    --workers "$WX" --timeouts "$TIMEOUTS" --split 4 --maxvar "$mv" --nice 5 --min-free-gb "$MINFREE" \
    >> "$d/conquer.log" 2>&1
  local r=$?
  for f in "$d"/run/SAT_*.model; do
    [ -f "$f" ] || continue
    {
      echo "!!!!!!!! SAT CUBE in $name: $f -- this contradicts NMH's UNSAT result !!!!!!!!"
      python3 -I scripts/verify_model.py --numbering nmh --model "$f" --out "$d" "$inp" "cnf/stage4/$name.cnf" "$tk"
      echo "verify_model exit $?"
    } >> "$SATFLAG" 2>&1
    return 3
  done
  local cf; cf=$(tail -n +"$((n0 + 1))" "$d/conquer.log" | grep "CHECK FAILED" | tail -1)
  [ -n "$cf" ] && log "LRAT CHECK FAILED in $name (a rerun retries it): $cf"
  [ "$r" -eq 0 ] || { log "run_cubes for $name exited $r"; return 1; }
  return 0
}

# scheduler: portable (also bash 3.2 for the Mac test): every job writes NAME.status when done
RUNNING=""
nrunning() { set -- $RUNNING; echo $#; }
handle() {  # name status
  case "$2" in
    0) log "conquer $1 finished" ;;
    3) log "!!!!!!!! SAT in $1: see $SATFLAG -- STOPPING THE STAGE !!!!!!!!"; touch "results/stage4/STOP.$STAGE"; stop_all; rc=1 ;;
    *) log "conquer $1 failed (status $2)"; rc=1 ;;
  esac
}
reap() {  # wait until at least one running job has finished, handle every finished one
  local still any nm
  while :; do
    still=""; any=0
    for nm in $RUNNING; do
      if [ -f "results/stage4/$nm.status" ]; then handle "$nm" "$(cat "results/stage4/$nm.status")"; any=1
      else still="$still $nm"; fi
    done
    RUNNING=$still
    [ "$any" = 1 ] && return
    sleep "${POLL:-20}"
  done
}

rm -f "results/stage4/STOP.$STAGE"
if [ -f "$SATFLAG" ]; then
  log "$SATFLAG exists from an earlier run: not starting (inspect it first)"; rc=1
else
  for name in $NAMES; do
    [ -f "results/stage4/STOP.$STAGE" ] && break
    closed "$name" && { log "$name already ALL CLOSED"; continue; }
    [ -f "results/stage4/$name/prep.ok" ] || continue
    while [ "$(nrunning)" -ge "$SLOTS" ]; do reap; done
    [ -f "results/stage4/STOP.$STAGE" ] && break
    log "conquer $name with $WX workers"
    rm -f "results/stage4/$name.status"
    ( conquer "$name"; echo $? > "results/stage4/$name.status.tmp"; mv "results/stage4/$name.status.tmp" "results/stage4/$name.status" ) &
    RUNNING="$RUNNING $name"
  done
  while [ "$(nrunning)" -gt 0 ]; do reap; done
  wait
fi

if [ ! -f "$SATFLAG" ]; then
  for name in $NAMES; do
    d="results/stage4/$name"
    if [ -f "$d/run/results.jsonl" ] && [ -f "$d/cubes.icnf" ]; then
      python3 -I scripts/cnc_summary.py "cnf/stage4/$name.cnf" "$d/cubes.icnf" "$d/run" > "$d/summary.log" 2>&1 || rc=1
    fi
    closed "$name" && log "$name ALL CLOSED" || { log "$name NOT CLOSED"; rc=1; }
  done
else
  log "SAT found: summaries skipped; $(head -c 2000 "$SATFLAG")"
fi

log "stage $STAGE finished rc=$rc"
echo "$rc" > "results/$STAGE.DONE"
# move the power-off to GRACE minutes from now, but never past the user-data hard stop
if [ -f /run/systemd/shutdown/scheduled ]; then
  hard_usec=$(sed -n 's/^USEC=//p' /run/systemd/shutdown/scheduled)
  now_usec=$(( $(date +%s) * 1000000 ))
  left_min=$(( (hard_usec - now_usec) / 60000000 ))
  [ "$left_min" -gt "$GRACE" ] && sudo shutdown -h +"$GRACE" "stage done; grace for sync"
fi
