#!/bin/bash
# On the server, in ~/tr (the repo copy pushed by scripts/cloud/push.sh):
# waits for user-data's tool build, builds our binaries, runs the quick tests.
#   bash scripts/cloud/setup.sh
set -euo pipefail
cd "$(dirname "$0")/../.."
for i in $(seq 1 120); do [ -f /opt/tr-tools/READY ] && break; sleep 10; done
[ -f /opt/tr-tools/READY ] || { echo "tools not built (see /var/log/tr-user-data.log)"; exit 1; }
mkdir -p build cnf
cc -O2 -o build/encode src/encode.c
c++ -O2 -std=c++17 -o build/pivenum src/pivenum.cpp -I/usr/local/include /usr/local/lib/libcadical.a
gcc -O2 -std=c99 -DLONGTYPE -w -o build/lrat-check tools/drat-trim/lrat-check.c
python3 tests/test_encode.py
python3 tests/test_pivenum.py
ulimit -n
echo "setup OK on $(nproc) vCPUs, $(free -g | awk '/Mem/{print $2}') GiB"
