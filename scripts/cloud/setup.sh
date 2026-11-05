#!/bin/bash
# On the server, in ~/tr (the repo copy pushed by scripts/cloud/push.sh):
# waits for user-data's tool build, builds our binaries, runs the quick tests.
#   bash scripts/cloud/setup.sh
# Gate (set -e): setup fails, and no stage may start, unless the patched lrat-check rejects the
# bogus empty-clause proofs and accepts genuine CaDiCaL proofs (tests/test_lrat_check.py) and the
# independent 3-cycle-mode soundness checker passes its tests (tests/test_tri_sound.py).
set -euo pipefail
cd "$(dirname "$0")/../.."
for i in $(seq 1 120); do [ -f /opt/tr-tools/READY ] && break; sleep 10; done
[ -f /opt/tr-tools/READY ] || { echo "tools not built (see /var/log/tr-user-data.log)"; exit 1; }
mkdir -p build cnf
cc -O2 -o build/encode src/encode.c
cc -O2 -o build/tri_sound src/tri_sound.c
c++ -O2 -std=c++17 -o build/pivenum src/pivenum.cpp -I/usr/local/include /usr/local/lib/libcadical.a
# patched 5 Nov 2026: an empty clause must end in a conflict (see the comments in the source)
gcc -O2 -std=c99 -DLONGTYPE -w -o build/lrat-check tools/drat-trim/lrat-check.c
python3 tests/test_lrat_check.py
python3 tests/test_tri_sound.py
python3 tests/test_encode.py
python3 tests/test_pivenum.py
# second proof check, run on a sample after the main run (scripts/audit/cake_sample.py): build the
# formally verified checker build/cake_lpr from tools/cake_lpr and self-test it, then test
# scripts/audit/dualcheck.sh (lrat-check and cake_lpr side by side); setup fails if either fails
bash scripts/audit/cake_build.sh
python3 tests/test_dualcheck.py
ulimit -n
echo "setup OK on $(nproc) vCPUs, $(free -g | awk '/Mem/{print $2}') GiB"
