"""Rewrite the checkpoint lists of replay data modules into packed chunks (`NatPack`).

A replay data module `LocalWindowUnsat/<W>/Data<k>.lean` defines `cp<k+1> : List Nat` as a
`List.append` of literal lists (2^16 clause words, about half of them 0).  As Lean terms
these lists take about three times their source size in the `.olean`; the packed form
`Snake9.NatPack.unpackL [c₀, c₁, …]` stores each chunk of up to 64 entries as one literal
(see `work/final_lean/NatPack.lean` for the format).  The decoded list is the same, and the
kernel checks of the next segment test it anyway.

Only modules without an up-to-date `.olean` are rewritten (built modules keep their olean).

  python pack_checkpoints.py [--dirs R01203A4623 ...] [--dry-run]
"""
import argparse, os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.abspath(os.path.join(HERE, '..', '..', '..', 'work', 'final_lean'))
UNSAT = os.path.join(LEAN, 'LocalWindowUnsat')
OLEAN = os.path.join(LEAN, '.lake', 'build', 'lib', 'lean', 'LocalWindowUnsat')
NUM = re.compile(r'nat_lit (0x[0-9a-fA-F]+|\d+)')
CHUNK = 64


def encode(xs):
    """One chunk: n + 2^8 (w + 2^16 (z + 2^n st))."""
    n = len(xs)
    assert n <= 255
    w = max([x.bit_length() for x in xs] + [1])
    assert w < 65536
    z, st, pos = 0, 0, 0
    for i, x in enumerate(xs):
        if x == 0:
            z |= 1 << i
        else:
            st |= x << pos
            pos += w
    return n + (w << 8) + (z << 24) + (st << (24 + n))


def decode(c):
    n, w = c & 255, (c >> 8) & 65535
    r = c >> 24
    z, st = r & ((1 << n) - 1), r >> n
    out = []
    for i in range(n):
        if (z >> i) & 1:
            out.append(0)
        else:
            out.append(st & ((1 << w) - 1))
            st >>= w
    return out


def pack_def(name, xs):
    chunks = [encode(xs[i:i + CHUNK]) for i in range(0, len(xs), CHUNK)]
    assert [y for c in chunks for y in decode(c)] == xs
    body = ',\n'.join('  nat_lit 0x%x' % c for c in chunks)
    return 'noncomputable def %s : List Nat := Snake9.NatPack.unpackL [\n%s]\n' % (name, body)


def rewrite(text):
    lines = text.split('\n')
    out, i, n_defs = [], 0, 0
    while i < len(lines):
        m = re.match(r'noncomputable def (cp\d+) : List Nat := (List\.append \[|\[)', lines[i])
        if not m:
            out.append(lines[i])
            i += 1
            continue
        j = i
        while j < len(lines) and lines[j].strip() != '':
            j += 1
        block = '\n'.join(lines[i:j])
        xs = [int(t, 0) for t in NUM.findall(block)]
        out.extend(pack_def(m.group(1), xs).rstrip('\n').split('\n'))
        n_defs += 1
        i = j
    if not n_defs:
        return text, 0
    res = '\n'.join(out)
    if 'import NatPack\n' not in res:
        res = re.sub(r'^(import [^\n]+\n)', r'\1import NatPack\n', res, count=1)
    return res, n_defs


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--dirs', nargs='*')
    ap.add_argument('--dry-run', action='store_true')
    a = ap.parse_args()
    dirs = a.dirs or sorted(d for d in os.listdir(UNSAT) if os.path.isdir(os.path.join(UNSAT, d)))
    tot_files = tot_before = tot_after = 0
    for d in dirs:
        for f in sorted(os.listdir(os.path.join(UNSAT, d))):
            if not (f.startswith('Data') and f.endswith('.lean')):
                continue
            src = os.path.join(UNSAT, d, f)
            ol = os.path.join(OLEAN, d, f[:-5] + '.olean')
            if os.path.exists(ol) and os.path.getmtime(ol) > os.path.getmtime(src):
                continue
            text = open(src).read()
            if 'Snake9.NatPack.unpackL' in text:
                continue
            new, k = rewrite(text)
            if not k:
                continue
            tot_files += 1
            tot_before += len(text)
            tot_after += len(new)
            if not a.dry_run:
                tmp = src + '.tmp'
                open(tmp, 'w').write(new)
                os.replace(tmp, src)
    print('rewrote %d files: %.1f MB -> %.1f MB source' % (tot_files, tot_before / 1e6, tot_after / 1e6))


if __name__ == '__main__':
    sys.exit(main())
