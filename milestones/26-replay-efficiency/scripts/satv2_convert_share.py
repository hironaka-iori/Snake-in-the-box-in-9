"""Rewrite a main-format share certificate for the share checker of Sat v2 (`TagsSW`).

A measurement tool of milestones/26-replay-efficiency/README.md, "Sat v2", not a production
generator.  It reads `SRC/Data.lean`, `SRC/Structure.lean` and `SRC/Shard*.lean` of a share floor
of main (e.g. `Share7300`, layout of milestones/33-233-lean), decodes the two meaning trees
(`mtB`, `mtB64`) and writes DST/ with flat tables (`TagsW.getF`, `TagsSW.getSF`) and the checks by
`TagsW.ctrOKK`, `TagsSW.totOK` and `TagsSW.ckAllS`.

  python3 satv2_convert_share.py SRC DST NAME      # e.g. sh/Share7300 sh/S7300v 7300
"""
import re, sys, os
src, dst, name = sys.argv[1], sys.argv[2], sys.argv[3]   # e.g. sh/Share7300 v2s/Share7300 7300
def bl(x): return max(1, x.bit_length())
def walk(nv, st, leafbits, leaf):
    out = {}
    def rec(r, s, st, fuel):
        if fuel == 0: return st
        if r + s <= nv:
            st = rec(r, 2 * s, st, fuel - 1)
            return rec(r + s, 2 * s, st, fuel - 1)
        m = leaf(st & ((1 << leafbits) - 1))
        if m is not None: out[r] = m
        return st >> leafbits
    rec(0, 1, st, 64)
    return out
def leafM(x):
    k = x & 3
    if k == 0: return None
    if k == 1: return ('p', x >> 2)
    if k == 2: return ('e', x >> 2)
    return ('r', (x >> 2) & 255, (x >> 10) & 65535, x >> 26)
def leafX(x):
    k = x & 3
    if k == 0: return None
    if k == 1: return ('sq', (x >> 2) & 65535, (x >> 18) & 255, x >> 26)
    if k == 2: return ('t', (x >> 2) & 1023, (x >> 12) & 65535, (x >> 28) & 65535, x >> 44)
    return ('u', (x >> 2) & 65535, x >> 18)
d = open(os.path.join(src, 'Data.lean')).read()
mm = re.search(r'noncomputable def meaning : MT := \(mtB (\d+) 64 0 1 \(nat_lit 0x([0-9a-f]+)\)\)\.1', d)
mx = re.search(r'noncomputable def smeaning : MS := \(mtB64 (\d+) 64 0 1 \(nat_lit 0x([0-9a-f]+)\)\)\.1', d)
nv = int(mm.group(1)); M = walk(nv, int(mm.group(2), 16), 48, leafM); X = walk(int(mx.group(1)), int(mx.group(2), 16), 64, leafX)
vw = bl(max([m[1] for m in M.values() if m[0] != 'r'] + [0]))
rs = [m for m in M.values() if m[0] == 'r']
cw, iw, jw = (bl(max([m[k] for m in rs] + [0])) for k in (1, 2, 3))
W = 2 + max(vw, cw + iw + jw)
T = 0
for x, m in M.items():
    c = (1 | m[1] << 2) if m[0] == 'p' else (2 | m[1] << 2) if m[0] == 'e' else (3 | m[1] << 2 | m[2] << (2 + cw) | m[3] << (2 + cw + iw))
    assert c < 1 << W; T |= c << (x * W)
qw = bl(max([m[1] for m in X.values() if m[0] in ('sq', 'u')] + [0]))
aw = bl(max([m[2] for m in X.values() if m[0] == 'sq'] + [0]))
bw = bl(max([m[3] for m in X.values() if m[0] == 'sq'] + [0]))
tw = bl(max([m[2] for m in X.values() if m[0] == 'u'] + [0]))
iw2 = bl(max([m[1] for m in X.values() if m[0] == 't'] + [0]))
hw = bl(max([max(m[2], m[3]) for m in X.values() if m[0] == 't'] + [0]))
ccw = bl(max([m[4] for m in X.values() if m[0] == 't'] + [0]))
WX = 2 + max(qw + aw + bw, qw + tw, iw2 + 2 * hw + ccw)
TX = 0
for x, m in X.items():
    if m[0] == 'sq': c = 1 | m[1] << 2 | m[2] << (2 + qw) | m[3] << (2 + qw + aw)
    elif m[0] == 'u': c = 3 | m[1] << 2 | m[2] << (2 + qw)
    else: c = 2 | m[1] << 2 | m[2] << (2 + iw2) | m[3] << (2 + iw2 + hw) | m[4] << (2 + iw2 + 2 * hw)
    assert c < 1 << WX; TX |= c << (x * WX)
d = d.replace(mm.group(0), 'noncomputable def mtab : Nat := nat_lit 0x%x\nnoncomputable def meaning : Nat → MT := TagsW.getF mtab %d %d %d' % (T, W, cw, iw))
d = d.replace(mx.group(0), 'noncomputable def stab : Nat := nat_lit 0x%x\nnoncomputable def smeaning : Nat → MS := TagsSW.getSF stab %d %d %d %d %d' % (TX, WX, qw, aw, iw2, hw))
d = d.replace('import LocalWindowTagsSharePacked', 'import LocalWindowTagsSharePacked\nimport LocalWindowTagsSW')
os.makedirs(dst, exist_ok=True)
pkg = os.path.basename(dst)
d = d.replace('import Share%s.' % name, 'import %s.' % pkg)
open(os.path.join(dst, 'Data.lean'), 'w').write(d)
for f in sorted(os.listdir(src)):
    if f.startswith('Shard'):
        t = open(os.path.join(src, f)).read().replace('import Share%s.' % name, 'import %s.' % pkg)
        t = t.replace('theorem shard', 'theorem shard').replace(' ckAllS ', ' TagsSW.ckAllS ')
        open(os.path.join(dst, f), 'w').write(t)
t = open(os.path.join(src, 'Structure.lean')).read().replace('import Share%s.' % name, 'import %s.' % pkg)
t = t.replace('ctrs.all (ctrOK meaning (centresK window bounds))', 'TagsW.allK (TagsW.ctrOKK meaning (centresK window bounds)) ctrs')
t = t.replace('tots.all (totOK meaning', 'tots.all (TagsSW.totOK meaning')
open(os.path.join(dst, 'Structure.lean'), 'w').write(t)
print(dict(nv=nv, M=len(M), X=len(X), W=W, WX=WX, mbytes=T.bit_length() // 8, sbytes=TX.bit_length() // 8))
