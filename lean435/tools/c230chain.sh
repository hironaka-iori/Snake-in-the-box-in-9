#!/bin/bash
# Spec layer of the 230 assembly (milestone 37): the ported K7 chain, the main-line modules it needs, the
# handwritten lean435/c230 modules and the generated spec modules of c230gen.py, built with build.py.
#   bash lean435/tools/c230chain.sh [WORKDIR]      (default ~/l435/c230chain; JOBS=3)
# Output: WORKDIR/src (sources), WORKDIR/build (.olean), WORKDIR/gen/glue (glue for assemble230.py).
set -euo pipefail
R=$(cd "$(dirname "$0")/../.." && pwd); T="$R/lean435/tools"
W=${1:-$HOME/l435/c230chain}
mkdir -p "$W"
cd "$R"
python3 "$T/k7src.py" --out "$W/rkroot" ${K7SRC_NO_FETCH:+--no-fetch}
python3 "$T/port.py" --extra-root "$W/rkroot" --out "$W/src" AggregateDirectionK7R34C7W16Conditional \
  DirectionWindowBridge ShareBridge LocalWindowFamilies Snake9
for f in C230Cover C230Mask C230K7 C230Final; do cp "$R/lean435/c230/$f.lean" "$W/src/$f.lean"; done
python3 "$T/c230gen.py" --out "$W/gen"
cp "$W"/gen/spec/*.lean "$W/src/"
python3 "$T/build.py" --keep-going --src "$W/src" --build "$W/build" --jobs "${JOBS:-3}" --rss-gb "${RSS_GB:-6}" \
  C230Final LocalWindowFamilies
