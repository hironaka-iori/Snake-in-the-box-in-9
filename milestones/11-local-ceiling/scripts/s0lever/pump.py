"""Pumping caps from real snakes.  An automaton whose state at path position i is
(canonical shape of the last L transition directions, last K symbols) and which forbids only windows that are
locally infeasible must allow every transition a real snake performs.  If positions i<j of one bank snake have the
same state, the snake segment i+1..j is a cycle of the automaton, so its minimum cycle mean is at most the mean
symbol over that segment.  Report the minimum such segment mean (a cap on any such automaton) and the floor."""
import pickle, sys
import os
D = os.path.dirname(os.path.abspath(__file__)) + '/'
store = pickle.load(open(D + 'charges.pkl', 'rb'))
floor = lambda mu: 9214 / (35 + mu) - 1
def canon(ds):
    m = {}; return tuple(m.setdefault(x, len(m)) for x in ds)
def cap(symfn, L, K, maxlen=400):
    best = (99, None)
    for n, o in store.items():
        if not n.startswith('bank'): continue
        seq = o['seqs'][0]; v = len(seq)
        dirs = [(seq[i] ^ seq[i + 1]).bit_length() - 1 for i in range(v - 1)]  # dirs[i]: edge i -> i+1
        sym = [symfn(o['g'][x]) for x in seq]
        pref = [0.0]
        for s in sym: pref.append(pref[-1] + float(s))
        seen = {}
        # state at vertex i (internal, 1..v-2): last L directions into i, last K symbols ending at i
        for i in range(max(L, K), v - 1):
            st = (canon(dirs[i - L:i]), tuple(sym[i - K + 1:i + 1]))
            for j0 in seen.get(st, []):
                if i - j0 > maxlen: continue
                mu = (pref[i + 1] - pref[j0 + 1]) / (i - j0)
                if mu < best[0]: best = (mu, (n, j0, i))
            seen.setdefault(st, []).append(i)
    return best
lump = lambda g: min(g['alpha'], 6)
SYMS = {'lumped alpha': lump, 'alpha': lambda g: g['alpha'], 'ex (exact share, r4)': lambda g: g['ex'],
        'dom (corner rule, r3)': lambda g: g['dom'], 'c3': lambda g: g['c3'],
        'dom floored to 1/2': lambda g: int(2 * g['dom']) / 2}
cases = [(6, 3), (7, 5), (8, 6), (10, 8), (12, 10), (14, 12), (16, 14), (20, 18)]
for name, fn in SYMS.items():
    out = []
    for L, K in cases:
        mu, w = cap(fn, L, K)
        out.append(f'L{L}K{K}:{mu:.2f}' + (f'({floor(mu):.0f})' if mu < 99 else '(none)'))
    print(f'{name:22s} ' + ' '.join(out), flush=True)
