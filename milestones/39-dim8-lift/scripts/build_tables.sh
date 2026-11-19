#!/bin/bash
# compile the generated table data modules (lean/gen) into lean/build
cd "$(dirname "$0")/../lean"
for m in $(cat gen/modules.txt); do
  [ -f build/$m.olean ] && [ build/$m.olean -nt gen/$m.lean ] && continue
  LEAN_PATH=build /opt/lean-4.35.0-linux/bin/lean -o build/$m.olean gen/$m.lean 2>&1 | grep -m3 error && echo "FAIL $m"
done
echo TABLES BUILT
