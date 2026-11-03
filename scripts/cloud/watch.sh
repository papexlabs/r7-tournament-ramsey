#!/bin/bash
# Mac-side liveness + progress check of a stage on the server (kobon lessons: anchor
# remote pgrep patterns so they cannot match the ssh shell itself, and treat "alive but
# no progress for STALL minutes" as a failure, not as running).
# Prints one line per check; exits on DONE, failure or stall.
# usage: bash scripts/cloud/watch.sh HOST_IP STAGE [EVERY_SEC=600] [STALL_MIN=90]
set -u
HOST="ubuntu@$1"; STAGE="$2"; EVERY="${3:-600}"; STALL="${4:-90}"
SSH="ssh -i $HOME/.ssh/kobon-aws.pem -o BatchMode=yes -o StrictHostKeyChecking=accept-new -o ConnectTimeout=20 -o ServerAliveInterval=15 -o ServerAliveCountMax=4"
fails=0
while true; do
  out=$($SSH "$HOST" "cd tr; \
    alive=\$(pgrep -f '^bash scripts/cloud/run_stage' >/dev/null && echo yes || echo no); \
    done=\$(cat results/$STAGE.DONE 2>/dev/null || echo -); \
    tb=\$(grep -c Traceback results/$STAGE.log 2>/dev/null || echo 0); \
    newest=\$(find results -type f \( -name 'records.jsonl' -o -name 'certify.jsonl' -o -name 'results.jsonl' \) -printf '%T@\n' 2>/dev/null | sort -n | tail -1); \
    age=\$(( (\$(date +%s) - \${newest%.*}) / 60 )); \
    load=\$(cut -d' ' -f1 /proc/loadavg); mem=\$(free -g | awk '/Mem/{print \$7}'); \
    echo alive=\$alive done=\$done tracebacks=\$tb progress_age_min=\$age load=\$load mem_avail_gb=\$mem; \
    tail -1 results/$STAGE.log" 2>&1)
  rc=$?
  # a teardown timeout after a full answer is not an outage (seen 11-03): judge by the answer
  if [ $rc -ne 0 ] && ! echo "$out" | grep -q "alive="; then
    fails=$((fails + 1)); echo "$(date '+%F %T') ssh failed ($fails): $out"
    [ $fails -ge 3 ] && { echo "WATCH: server unreachable 3 times (spot reclaim, timer, or IP change)"; exit 1; }
  else
    fails=0; echo "$(date '+%F %T') $out" | tr '\n' ' '; echo
    case "$out" in
      *"done=0"*) echo "WATCH: $STAGE finished OK"; exit 0 ;;
      *"done=1"*) echo "WATCH: $STAGE finished WITH ERRORS"; exit 1 ;;
    esac
    echo "$out" | grep -q 'tracebacks=[1-9]' && { echo "WATCH: Traceback in log"; exit 1; }
    echo "$out" | grep -q 'alive=no' && { echo "WATCH: run_stage.sh not running and no DONE file"; exit 1; }
    age=$(echo "$out" | sed -n 's/.*progress_age_min=\([0-9-]*\).*/\1/p')
    [ -n "$age" ] && [ "$age" -gt "$STALL" ] && { echo "WATCH: no progress for $age min"; exit 1; }
  fi
  sleep "$EVERY"
done
