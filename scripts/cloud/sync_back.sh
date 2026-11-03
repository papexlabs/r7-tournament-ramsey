#!/bin/bash
# Server -> Mac every SECONDS (default 600): the stage's results (records, models,
# certificates, cube results, logs, *.DONE) and the server's process list.
# Stops by itself once results/<STAGE>.DONE has been copied (one final sync).
# usage: nohup bash scripts/cloud/sync_back.sh HOST_IP STAGE [SECONDS] > results/STAGE.sync.log 2>&1 &
set -u
cd "$(dirname "$0")/../.."
HOST="ubuntu@$1"; STAGE="$2"; EVERY="${3:-600}"
SSH="ssh -i $HOME/.ssh/kobon-aws.pem -o BatchMode=yes -o StrictHostKeyChecking=accept-new -o ConnectTimeout=20"
while true; do
  rsync -az -e "$SSH" --exclude 'body.cnf' --exclude 'tmp/' --exclude '*.fifo' \
      "$HOST:tr/results/" results/ \
    && $SSH "$HOST" 'ps -axo etime=,pcpu=,rss=,args= | grep -E "^ *[0-9:-]+ .*(pivenum|cadical|lrat-check|python3 -I scripts)" | grep -v grep | head -400' \
         > "results/$STAGE.remote_ps.tmp" \
    && mv "results/$STAGE.remote_ps.tmp" "results/$STAGE.remote_ps.txt" \
    && echo "$(date '+%F %T') synced"
  if [ -f "results/$STAGE.DONE" ]; then echo "$(date '+%F %T') $STAGE.DONE synced (rc $(cat results/$STAGE.DONE)); stopping"; exit 0; fi
  sleep "$EVERY"
done
