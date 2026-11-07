#!/bin/bash
# Runs a heavy command (Lean builds, the test suite) with a memory cap and one at a time:
# a second heavy job waits for the first. The cap kills the job, not the machine.
#   scripts/capped.sh <command…>        (PROOFSCRIPT_MEMORY_MAX, default 6G)
set -e
lock="${XDG_RUNTIME_DIR:-/tmp}/proofscript-heavy.lock"
exec 9>"$lock"
flock 9
exec systemd-run --user --scope --quiet -p MemoryMax="${PROOFSCRIPT_MEMORY_MAX:-6G}" -p MemorySwapMax=0 -- "$@"
