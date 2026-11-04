#!/bin/bash
# Mac -> server.
#   bash scripts/cloud/push.sh HOST_IP            code only (scripts, src, tests, tools, data, notes):
#                                                 safe while a stage is running (results/ untouched)
#   bash scripts/cloud/push.sh HOST_IP --results  also results/ INCLUDING enumeration models: only for a
#                                                 fresh box resuming from what sync_back.sh copied home
#   bash scripts/cloud/push.sh HOST_IP --results-sub PATH...   e.g. stage4, or stage4/23S-p-Y8 stage4/23H-p-Y8
#                                                 only these paths under results/ (a fresh box resuming one
#                                                 stage, or one box of two): its sync_back then cannot copy
#                                                 stale files of other stages or boxes home
# Never push results/ to a box whose stage is running: rsync would replace the files the running
# python appends to, and those appends would be lost.
set -euo pipefail
cd "$(dirname "$0")/../.."
HOST="ubuntu@$1"
SSH="ssh -i $HOME/.ssh/kobon-aws.pem -o BatchMode=yes -o StrictHostKeyChecking=accept-new -o ConnectTimeout=20"
$SSH "$HOST" 'mkdir -p tr'
rsync -az -e "$SSH" --exclude __pycache__/ scripts src tests tools data notes "$HOST:tr/"
if [ "${2:-}" = "--results" ]; then
  if $SSH "$HOST" "pgrep -f '^(bash scripts/cloud/run_stage|python3 -I scripts/)' > /dev/null"; then
    echo "a stage is running on $1: refusing to push results/"; exit 1
  fi
  rsync -az -e "$SSH" --exclude 'body.cnf' --exclude 'tmp/' --exclude '*.fifo' --exclude 'aws_*' results "$HOST:tr/"
fi
if [ "${2:-}" = "--results-sub" ]; then
  shift 2
  [ $# -gt 0 ] || { echo "--results-sub needs paths under results/"; exit 2; }
  for sub in "$@"; do
    case "$sub" in /*|.*|*..*) echo "bad path $sub (relative to results/, no ..)"; exit 2 ;; esac
    [ -e "results/$sub" ] || { echo "results/$sub does not exist"; exit 2; }
  done
  if $SSH "$HOST" "pgrep -f '^(bash scripts/cloud/run_stage|python3 -I scripts/)' > /dev/null"; then
    echo "a stage is running on ${HOST#ubuntu@}: refusing to push results/"; exit 1
  fi
  $SSH "$HOST" 'mkdir -p tr/results'
  (cd results && rsync -azR -e "$SSH" --exclude 'body.cnf' --exclude 'tmp/' --exclude '*.fifo' --exclude '*.status' \
    "$@" "$HOST:tr/results/")
  echo "pushed to ${HOST#ubuntu@}:tr/results/: $*"; exit 0
fi
echo "pushed to $1:tr/ ${2:-(code only)}"
