#!/bin/bash
# Mac -> server: copy the repo (code, data, small results; no CNFs, refs, proofs, build).
# usage: bash scripts/cloud/push.sh HOST_IP
set -euo pipefail
cd "$(dirname "$0")/../.."
SSH="ssh -i $HOME/.ssh/kobon-aws.pem -o BatchMode=yes -o StrictHostKeyChecking=accept-new -o ConnectTimeout=20"
rsync -az -e "$SSH" --exclude cnf/ --exclude refs/ --exclude build/ --exclude proofs/ \
  --exclude cubes/ --exclude .git/ --exclude __pycache__/ --exclude 'results/enum/*/models/' \
  ./ "ubuntu@$1:tr/"
echo "pushed to $1:tr/"
