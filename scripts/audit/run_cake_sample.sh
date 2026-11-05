#!/bin/bash
# Sampled second proof check after the main run: scripts/audit/cake_sample.py on every Stage 3
# instance, every Stage 4 instance and every enumeration n, each item re-solved and its LRAT proof
# checked by both lrat-check and cake_lpr (scripts/audit/dualcheck.sh).  On the server, in ~/tr,
# after push.sh and setup.sh (which builds and tests build/cake_lpr), once the main stage is done:
#   nohup bash scripts/audit/run_cake_sample.sh PART > results/cake_PART.log 2>&1 < /dev/null &
# PART: stage3 | stage4 | enum | all (all = stage3, then stage4, then enum)
# Output: results/cake/<part>/<name>/{items.jsonl,summary.json,dualcheck/}, and results/cake/PART.DONE
# (0 = every summary says "ALL VERIFIED BY BOTH": true).
# A run dir without body.cnf uses the CNF (cnf/24X-p-O21s.tri.cnf, cnf/stage4/NAME.cnf) if present;
# body.sha256 is checked either way.  Resumable: rerun the same command.
# Sizes (environment; defaults sized for one 96-vCPU / 370 GiB box, tools/cake_lpr/README.md):
#   S3_N=40 S3_M=5 S3_W=3      per Stage 3 instance: random leaves, slowest leaves, workers
#                              (5 instances side by side: 15 workers, ~21 GiB each)
#   S4_N=30 S4_M=3 S4_CAP=3600 S4_W=3   per Stage 4 instance (28 side by side: 84 workers);
#                              leaves slower than S4_CAP seconds in run 2 are not sampled
#   E_W=80 E21_N=1000 E22_N=500   enumeration workers; random jobs for n = 21 and n = 22 (plus the
#                              10 slowest and up to 50 / 30 jobs with models); n = 23..26: all jobs
#   MINFREE=24                 GB of MemAvailable below which no new item starts
#   RESULTS=results CAKE_OUT=results/cake E_NS="21 22 23 24 25 26"   inputs, output, enumeration n's
set -uo pipefail
cd "$(dirname "$0")/../.."
PART="${1:?usage: run_cake_sample.sh stage3|stage4|enum|all}"
S3_N="${S3_N:-40}"; S3_M="${S3_M:-5}"; S3_W="${S3_W:-3}"
S4_N="${S4_N:-30}"; S4_M="${S4_M:-3}"; S4_CAP="${S4_CAP:-3600}"; S4_W="${S4_W:-3}"
E_W="${E_W:-80}"; E21_N="${E21_N:-1000}"; E22_N="${E22_N:-500}"; MINFREE="${MINFREE:-24}"
R="${RESULTS:-results}"; OUT="${CAKE_OUT:-$R/cake}"; E_NS="${E_NS:-21 22 23 24 25 26}"
ulimit -n 65536 2>/dev/null || ulimit -n "$(ulimit -Hn)"
log() { echo "$(date -u '+%F %T') $*"; }
mkdir -p "$OUT"
rc=0
CS=(python3 -I scripts/audit/cake_sample.py)

cubes_target() {  # part name rundir cnf n m w [extra...]
  local part=$1 name=$2 run=$3 cnf=$4 n=$5 m=$6 w=$7; shift 7
  local o="$OUT/$part/$name" extra=()
  mkdir -p "$o"
  if [ ! -f "$run/results.jsonl" ]; then log "$name: no $run/results.jsonl"; return 1; fi
  if [ ! -f "$run/body.cnf" ]; then
    [ -f "$cnf" ] || { log "$name: neither $run/body.cnf nor $cnf"; return 1; }
    extra=(--cnf "$cnf")
  fi
  "${CS[@]}" cubes "$run" --out "$o" --n "$n" --slowest "$m" --workers "$w" --min-free-gb "$MINFREE" \
    ${extra[@]+"${extra[@]}"} "$@" > "$o/run.log" 2>&1
}

part_stage3() {
  local pids=() X
  for X in A B C D E; do
    cubes_target stage3 "24$X-p-O21s" "$R/stage3/24$X-p-O21s/run" "cnf/24$X-p-O21s.tri.cnf" \
      "$S3_N" "$S3_M" "$S3_W" & pids+=($!)
  done
  for p in "${pids[@]}"; do wait "$p" || rc=1; done
}

part_stage4() {
  local pids=() d name
  for d in "$R"/stage4/*/run; do
    [ -d "$d" ] || continue
    name=$(basename "$(dirname "$d")")
    cubes_target stage4 "$name" "$d" "cnf/stage4/$name.cnf" "$S4_N" "$S4_M" "$S4_W" --max-secs "$S4_CAP" & pids+=($!)
  done
  [ ${#pids[@]} -gt 0 ] || { log "no $R/stage4/*/run"; rc=1; return; }
  for p in "${pids[@]}"; do wait "$p" || rc=1; done
}

part_enum() {
  local n d o args
  for n in $E_NS; do
    d="$R/enum/k6n$n"; o="$OUT/enum/k6n$n"
    [ -f "$d/records.jsonl" ] || { log "no $d/records.jsonl"; rc=1; continue; }
    case $n in
      21) args=(--n "$E21_N" --slowest 10 --with-models 50) ;;
      22) args=(--n "$E22_N" --slowest 10 --with-models 30) ;;
      *)  args=(--n 1000000) ;;
    esac
    mkdir -p "$o"
    log "enum n=$n: ${args[*]}"
    "${CS[@]}" enum "$d" --out "$o" "${args[@]}" --workers "$E_W" --min-free-gb "$MINFREE" > "$o/run.log" 2>&1 || rc=1
  done
}

case "$PART" in
  stage3) part_stage3 ;;
  stage4) part_stage4 ;;
  enum) part_enum ;;
  all) part_stage3; part_stage4; part_enum ;;
  *) echo "unknown part $PART"; exit 2 ;;
esac

# one line per summary; rc 0 only if every summary of this part says ALL VERIFIED BY BOTH
for s in "$OUT"/*/*/summary.json; do
  [ -f "$s" ] || continue
  case "$PART" in all) ;; *) case "$s" in "$OUT/$PART/"*) ;; *) continue ;; esac ;; esac
  python3 -I -c 'import json, sys; s = json.load(open(sys.argv[1])); print(sys.argv[1], "sampled", s["sampled"], "both", s["verified_by_both"], "lrat", s["lrat_verified"], "cake", s["cake_verified"], "ALL VERIFIED BY BOTH:", s["ALL VERIFIED BY BOTH"])' "$s"
  grep -q '"ALL VERIFIED BY BOTH": true' "$s" || rc=1
done
log "cake sample $PART finished rc=$rc"
echo "$rc" > "$OUT/$PART.DONE"
exit "$rc"
