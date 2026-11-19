"""Generate the cover tables as Lean data (words of Aut(Q8) generators taking each raw set to its
representative), from enumk_raw / enum6_raw output.  Words act on Q8 vertices through Sym.gen:
applyW (c :: w) u = gen c (applyW w u); for an entry (R, w, rep): R.testBit (applyW w u) = rep.testBit u.
usage: python3 gentables.py raw5.txt raw6.txt outdir chunk"""
import sys, os, itertools
raw5, raw6, out, chunk = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4])
os.makedirs(out, exist_ok=True)
pairs8 = [(a, b) for a in range(8) for b in range(8) if a < b]
def gen(c, u):
    if c < 28:
        a, b = pairs8[c]
        return u ^ ((1 << a) | (1 << b)) if ((u >> a) & 1) != ((u >> b) & 1) else u
    return u ^ (1 << (c - 28))
def applyW(w, u):
    for c in reversed(w): u = gen(c, u)
    return u
def word(k, perm, t):
    # phi(u) = P_perm(u) ^ t ; want applyW w = phi^{-1} = P_{perm^{-1}} o xor t
    inv = [0] * k
    for i, j in enumerate(perm): inv[j] = i
    # decompose position permutation inv into transpositions: inv = tau1 o tau2 o ... (as maps on positions)
    cur = list(range(k)); trans = []
    target = inv[:]
    # selection: build target by composing transpositions on the left
    sigma = list(range(k))   # current sigma; we want sigma == target, sigma = tau1 o ... o taum
    ts = []
    arr = target[:]
    # standard: arr = target; find transpositions s.t. arr o t1 o t2 ... = id, then target = tm o ... o t1
    for i in range(k):
        if arr[i] != i:
            j = arr.index(i)
            arr[i], arr[j] = arr[j], arr[i]          # arr := arr o (i j)
            ts.append((min(i, j), max(i, j)))
    # arr o t1 o ... o tm = id  =>  target = tm o ... o t1
    w = [pairs8.index(p) for p in reversed(ts)]
    w += [28 + i for i in range(k) if t >> i & 1]
    return w
perms5 = list(itertools.permutations(range(5))); perms6 = list(itertools.permutations(range(6)))
def check(w, R, rep, n):
    return all(applyW(w, u) < (1 << n) and ((R >> applyW(w, u)) & 1) == ((rep >> u) & 1) for u in range(1 << n))
T5 = []
for l in open(raw5):
    if not l.startswith('R '): continue
    _, m, c, p, t = l.split(); m, c, p, t = int(m, 16), int(c, 16), int(p), int(t)
    w = word(5, perms5[p], t); assert check(w, m, c, 5), (m, c)
    T5.append((m, w, c))
T6 = []
for l in open(raw6):
    if not l.startswith('R '): continue
    _, m, c, p, t = l.split(); m, c, p, t = int(m, 16), int(c, 16), int(p), int(t)
    w = word(6, perms6[p], t); assert check(w, m, c, 6), (m, c)
    T6.append((m & 0xffffffff, m, w, c))
print('T5', len(T5), 'max word', max(len(e[1]) for e in T5), 'T6', len(T6), 'max word', max(len(e[2]) for e in T6))
def lst(w): return '[' + ', '.join(map(str, w)) + ']'
with open(os.path.join(out, 'T5.txt'), 'w') as f:
    for m, w, c in T5: f.write('%d %s %d\n' % (m, lst(w), c))
with open(os.path.join(out, 'T6.txt'), 'w') as f:
    for r5, m, w, c in T6: f.write('%d %d %s %d\n' % (r5, m, lst(w), c))
