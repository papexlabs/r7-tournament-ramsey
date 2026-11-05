#!/bin/bash
# Build build/cake_lpr (the formally verified LRAT/LPR checker, tools/cake_lpr/README.md) and
# self-test it; exits non-zero, so that scripts/cloud/setup.sh fails, unless
#   - the release files match upstream's cake_lpr.sha256 (the x64 cake_lpr.S is not kept),
#   - the upstream example proof gives exactly "s VERIFIED UNSAT" on stdout (and nothing on stderr),
#   - a bogus proof (empty clause without a conflict, "3 0 0") of the satisfiable formula
#     "1 2 / -1 2" is rejected, and so are an empty proof and the example proof cut short,
#   - the heap flag is accepted (--CML_HEAP_SIZE, used by scripts/audit/dualcheck.py).
# cake_lpr exits 0 even when a check fails, so only its output is a verdict.
#   bash scripts/audit/cake_build.sh
set -euo pipefail
cd "$(dirname "$0")/../.."
C=tools/cake_lpr
sha_check() { if command -v sha256sum > /dev/null; then sha256sum -c -; else shasum -a 256 -c -; fi; }
(cd "$C" && grep -v ' cake_lpr\.S$' cake_lpr.sha256 | sha_check)
mkdir -p build
make -s -B -C "$C" cake_lpr 2>&1 | grep -v 'reducing alignment' || true
[ -x "$C/cake_lpr" ] || { echo "cake_lpr build FAILED"; exit 1; }
mv "$C/cake_lpr" build/cake_lpr
T=$(mktemp -d)
trap 'rm -rf "$T"' EXIT
want() {  # name expected-stdout cake_lpr-args...
  local name=$1 exp=$2; shift 2
  build/cake_lpr "$@" > "$T/out" 2> "$T/err" || true
  if [ "$exp" = VERIFIED ]; then
    [ "$(cat "$T/out")" = "s VERIFIED UNSAT" ] && [ ! -s "$T/err" ] || { echo "cake_lpr self-test FAILED ($name): $(cat "$T/out" "$T/err")"; exit 1; }
  else
    ! grep -q "VERIFIED" "$T/out" || { echo "cake_lpr self-test FAILED ($name accepted): $(cat "$T/out")"; exit 1; }
  fi
  echo "cake_lpr self-test ok: $name: $(cat "$T/out" "$T/err" | head -1)"
}
printf 'p cnf 2 2\n1 2 0\n-1 2 0\n' > "$T/sat.cnf"
printf '3 0 0\n' > "$T/bogus.lrat"
: > "$T/empty.lrat"
head -n 5 "$C/example.lpr" > "$T/cut.lpr"
want "example proof" VERIFIED "$C/example.cnf" "$C/example.lpr"
want "example proof, heap flag" VERIFIED --CML_HEAP_SIZE=256 "$C/example.cnf" "$C/example.lpr"
want "empty clause without conflict on a satisfiable formula" REJECTED "$T/sat.cnf" "$T/bogus.lrat"
want "empty proof" REJECTED "$C/example.cnf" "$T/empty.lrat"
want "example proof cut short" REJECTED "$C/example.cnf" "$T/cut.lpr"
echo "cake_lpr OK: build/cake_lpr $(if command -v sha256sum > /dev/null; then sha256sum build/cake_lpr; else shasum -a 256 build/cake_lpr; fi | cut -d' ' -f1)"
