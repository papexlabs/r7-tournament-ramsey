#!/bin/sh
# Second proof check: build/lrat-check (patched) and build/cake_lpr (formally verified, CakeML)
# side by side on the same formula and the same LRAT proof; "c VERIFIED" and exit 0 only if both
# verify.  Drop-in replacement for build/lrat-check (scripts/stream_solve.py LRAT_CHECK).
#   scripts/audit/dualcheck.sh CNF PROOF      (either may be a named pipe)
# Details, environment variables and the log format: scripts/audit/dualcheck.py.
exec python3 -I "$(dirname "$0")/dualcheck.py" "$@"
