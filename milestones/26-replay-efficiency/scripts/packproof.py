"""Rewrite the proof lists (and input slots) of replay data modules into packed chunks.

  python packproof.py DIR WBITS [CHUNK_BYTES] [--no-slots]

`proof<k> : List Nat := [...]` becomes `Snake9.ProofPack.unpackL W [c0, c1, ...]` (see
ProofPack.lean), `inputSlots` becomes `Snake9.NatPack.unpackL [...]`.  The decoded lists are
the same (checked here); the kernel checks test the decoded lists anyway.
"""
import os, re, sys
sys.path.insert(0, os.path.join(os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..')), 'milestones', '10-window-aggregate', 'scripts'))
import pack_checkpoints as PK
NUM = re.compile(r'nat_lit (0x[0-9a-fA-F]+|\d+)')


def enc_chunk(xs, w):
    st, pos = 0, 0
    for x in xs:
        n = -(-x.bit_length() // w)
        assert n < 65536
        st |= (n | (x << 16)) << pos
        pos += 16 + w * n
    assert len(xs) < 65536
    return len(xs) | (st << 16)


def dec_chunk(c, w):
    n, st, out = c & 65535, c >> 16, []
    for _ in range(n):
        b = w * (st & 65535)
        out.append((st >> 16) & ((1 << b) - 1))
        st >>= 16 + b
    return out


def chunks(xs, w, cbytes):
    out, cur, bits = [], [], 0
    for x in xs:
        b = 16 + w * -(-x.bit_length() // w)
        if cur and (bits + b > 8 * cbytes or len(cur) >= 65535):
            out.append(cur); cur, bits = [], 0
        cur.append(x); bits += b
    if cur:
        out.append(cur)
    return out


def rewrite(text, w, cbytes, slots=True):
    lines, out, i = text.split('\n'), [], 0
    while i < len(lines):
        m = re.match(r'noncomputable def (proof\d+|cp\d+|inputSlots) : List Nat := (List\.append \[|\[)', lines[i])
        if not m or (m.group(1) == 'inputSlots' and not slots):
            out.append(lines[i]); i += 1; continue
        j = i
        while j < len(lines) and lines[j].strip() != '':
            j += 1
        xs = [int(t, 0) for t in NUM.findall('\n'.join(lines[i:j]))]
        if m.group(1) == 'inputSlots':
            out.extend(PK.pack_def('inputSlots', xs).rstrip('\n').split('\n'))
        else:
            cs = [enc_chunk(c, w) for c in chunks(xs, w, cbytes)]
            assert [y for c in cs for y in dec_chunk(c, w)] == xs
            out.append('noncomputable def %s : List Nat := Snake9.ProofPack.unpackL %d [' % (m.group(1), w))
            out.append(',\n'.join('  nat_lit 0x%x' % c for c in cs) + ']')
        i = j
    res = '\n'.join(out)
    imp = 'import ProofPack\n' + ('import NatPack\n' if slots and 'import NatPack\n' not in res else '')
    return re.sub(r'^(import [^\n]+\n)', lambda mm: mm.group(1) + imp, res, count=1)


if __name__ == '__main__':
    d, w = sys.argv[1], int(sys.argv[2])
    cb = int(sys.argv[3]) if len(sys.argv) > 3 and sys.argv[3].isdigit() else 4096
    for f in sorted(os.listdir(d)):
        if f.startswith('Data') and f.endswith('.lean'):
            p = os.path.join(d, f)
            t = open(p).read()
            if 'ProofPack' in t:
                continue
            open(p, 'w').write(rewrite(t, w, cb, '--no-slots' not in sys.argv))

