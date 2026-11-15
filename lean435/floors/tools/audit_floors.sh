#!/bin/bash
# Audit of the 4.35 floor port.  Usage: audit_floors.sh SRC BUILD
#  1. no `sorry`, `native_decide` or `axiom` in the ported sources;
#  2. no "declaration uses 'sorry'" in any build log, and every `#print axioms` report of the
#     build within {propext, Classical.choice, Quot.sound};
#  3. the sha256 of every source and output part equal lean435/floors/data/OLEAN-MANIFEST.tsv;
#  4. a fresh module importing only `Floors233Port` restates `floors233`; its axioms are printed
#     and the .olean files it opens are listed (none of the 1,046 floor modules may appear).
set -eu
SRC=$(realpath "$1"); B=$(realpath "$2"); HERE=$(dirname "$(realpath "$0")")
LEAN=/opt/lean-4.35.0-linux/bin/lean
! grep -rlE "sorry|native_decide|^\s*axiom\b" "$SRC" --include=*.lean || { echo "FAIL 1"; exit 1; }
! grep -rl "declaration uses 'sorry'" "$B" --include=*.out || { echo "FAIL 2 sorry"; exit 1; }
python3 -I - "$B" <<'PY'
import re, sys, pathlib
ok = {'propext', 'Classical.choice', 'Quot.sound'}; n = 0
for f in pathlib.Path(sys.argv[1]).rglob('*.out'):
    for m in re.finditer(r"depends on axioms: \[([^\]]*)\]", f.read_text()):
        ax = {a.strip() for a in m.group(1).replace('\n', ' ').split(',')}
        n += 1
        if not ax <= ok: sys.exit(f'FAIL 2 {f}: {ax}')
print(f'2. {n} axiom reports, all within {sorted(ok)}')
PY
python3 -I - "$SRC" "$B" "$HERE/../data/OLEAN-MANIFEST.tsv" <<'PY'
import hashlib, os, sys
S, B, M = sys.argv[1:4]
h = lambda p: hashlib.sha256(open(p, 'rb').read()).hexdigest() if os.path.exists(p) else '-'
rows = [l.split('\t') for l in open(M).read().splitlines()[1:]]
for r in rows:
    b = B + '/' + r[0].replace('.', '/')
    got = [h(S + '/' + r[0].replace('.', '/') + '.lean')] + [h(b + e) for e in ('.olean', '.olean.server', '.olean.private', '.ir', '.ir.sig')]
    if got != r[1:]: sys.exit(f'FAIL 3 {r[0]}')
print(f'3. {len(rows)} modules: sources and outputs match the manifest')
PY
T=$(mktemp -d); cd "$T"
printf 'module\npublic import Floors233Port\npublic theorem audit_floors : Snake9.DirectionWindow6S.Floors233 :=\n  Snake9.Floors233Port.floors233\n#print axioms audit_floors\n' > Audit.lean
LEAN_PATH="$B" strace -f -qq -e trace=openat -o tr.txt "$LEAN" -R . Audit.lean
grep -o "$B/[^\"]*\.olean\"" tr.txt | sed "s|$B/||;s|\.olean\"||;s|/|.|g" | sort -u > opened.txt
echo "4. opened $(wc -l < opened.txt) module interfaces: $(tr '\n' ' ' < opened.txt)"
rm -rf "$T"
