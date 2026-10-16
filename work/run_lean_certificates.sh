#!/bin/sh
# Preserve the existing entry point while propagating every build/audit failure.
# Usage: sh work/run_lean_certificates.sh KEEP [PARALLEL]
# KEEP may carry a suffix, e.g. 144v2. Override PYTHON or LAKE when necessary.
SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd) || exit 1
exec "${PYTHON:-python3}" "$SCRIPT_DIR/check_lean_certificates.py" "${1:-160}" --workers "${2:-2}"
