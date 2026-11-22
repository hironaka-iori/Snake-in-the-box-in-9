#!/bin/bash
# Regenerate the cover tables and their check modules (lean/gen, not committed) and build the table data
# into lean/build. Needed on any machine that makes cover certificates or assembles the final theorem.
#   bash scripts/make_tables.sh            (~10 min; the check modules are built later, by assemble_d8.py)
set -euo pipefail
cd "$(dirname "$0")"
T=${TMPDIR:-/tmp}/m39tables.$$; mkdir -p "$T"
gcc -O3 -o enumk_raw enumk_raw.c && gcc -O3 -o enum6_raw enum6_raw.c
./enumk_raw 5 15 > "$T/raw5.txt"
./enum6_raw 6 29 y ../data/q5_15.txt > "$T/raw6.txt"
python3 gentables.py "$T/raw5.txt" "$T/raw6.txt" "$T/tables" 2000
python3 genlean_tables.py "$T/tables" 2000
python3 genlean_checks.py
(cd ../lean && bash build.sh > /dev/null)   # plain stack (idempotent)
bash build_tables.sh
rm -rf "$T"
echo "tables: $(ls ../lean/gen/T5c*.lean ../lean/gen/T6c*.lean | grep -vc Ok) data modules, $(wc -w < ../lean/gen/checks.txt) check modules"
