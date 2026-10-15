#!/bin/sh
# Check generated certificate modules a few at a time, then the aggregate theorem.
# Each Lean process keeps its kernel memory until it exits, so parallelism is bounded.
# The generator lists independent targets in DfsBankCertKEEP.targets (the last module
# of each chain, plus packed modules), so no two lake processes build the same module.
# Usage: sh work/run_lean_certificates.sh KEEP [PARALLEL]   (KEEP may carry a suffix, e.g. 144v2)
KEEP=${1:-160}; PAR=${2:-3}
cd "$(dirname "$0")/final_lean" || exit 1
LAKE=${LAKE:-lake}
if [ -f "DfsBankCert${KEEP}.targets" ]; then
  LIST=$(cat "DfsBankCert${KEEP}.targets")
else
  LIST=$(ls DfsBankCert${KEEP}_*.lean | sed 's/\.lean$//')
fi
printf '%s\n' $LIST |
  xargs -P "$PAR" -I{} sh -c "$LAKE build {} >/dev/null 2>&1 && echo 'ok {}' || echo 'FAILED {}'"
$LAKE build DfsBankCert${KEEP} 2>&1 | grep -E "axioms|error|completed|failed"
