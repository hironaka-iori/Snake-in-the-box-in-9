#!/bin/bash
# Generate (read-only use of milestones/35-231-lean/scripts/gen_lean_*6sc.py), port and build a conditional
# 6SC chain in Lean 4.35, plus its glue modules for the assembly.
#   bash lean435/tools/chain435.sh PLAN TAG BOUND [WORKDIR]
# e.g. bash lean435/tools/chain435.sh milestones/28-combined-identities/data/certplan231_m232_541_1b.json.gz M232B541 232
set -euo pipefail
R=$(cd "$(dirname "$0")/../.." && pwd); T="$R/lean435/tools"
PLAN=$1 TAG=$2 BOUND=$3 W=${4:-$HOME/l435/chain$BOUND}
mkdir -p "$W/gen"
cd "$R"
python3 milestones/35-231-lean/scripts/gen_lean_automaton6sc.py --plan "$PLAN" --tag "$TAG" --expect-bound "$BOUND" \
  --out-stronger "$W/gen" --out-core "$W/gen" --summary "lean435/data/auto6sc_$TAG.json" --sha256 "lean435/data/shards6sc_$TAG.sha256"
python3 milestones/35-231-lean/scripts/gen_lean_chain6sc.py --tag "$TAG" --out-stronger "$W/gen" \
  --summary "lean435/data/auto6sc_$TAG.json" --ctx-shapes-per-part 4
python3 "$T/port.py" --extra-root "$W/gen" --out "$W/src" "Audit6SC$TAG" LocalWindowFamilies
python3 "$T/build.py" --keep-going --src "$W/src" --build "$W/build" --jobs "${JOBS:-3}" --rss-gb 6 "Audit6SC$TAG" LocalWindowFamilies
cat "$W/build/Audit6SC$TAG.out"
TAGP=$(basename "$PLAN" .json.gz)
python3 "$T/glue435.py" --tag "$TAG" --gen "$W/gen" --plan "$PLAN" --freederive "lean435/data/freederive_$TAGP.json.gz" --out "$W/glue"
