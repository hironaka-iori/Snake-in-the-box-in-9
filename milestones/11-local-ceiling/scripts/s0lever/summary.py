import pickle, statistics as st
from fractions import Fraction as F
import os
D = os.path.dirname(os.path.abspath(__file__)) + '/'
store = pickle.load(open(D + 'charges.pkl', 'rb'))
KEYS = ['alpha', 'ex', 'dom', 'c3', 'cheap']
floor = lambda mu: 9214 / (35 + mu) - 1
print('targets: mean needed to exclude v = X+2 (bound m <= X):')
for X in (238, 236, 230, 220, 210, 207, 200, 196):
    print(f'  m<={X}: mu > {(9214 - 35 * (X + 2)) / (X + 2):.3f}')
KS = [1, 2, 3, 4, 5, 6, 8, 10, 13, 16, 20, 26, 40]
def winmin(vals, k, cyclic):
    n = len(vals)
    if cyclic:
        return min(sum(vals[(s + i) % n] for i in range(k)) for s in range(n)) / k
    return min(sum(vals[s:s + k]) for s in range(0, n - k + 1)) / k
groups = {'bank': [n for n in store if n.startswith('bank')], 'adv208': ['adv208'], 'adv224': ['adv224']}
for gname, names in groups.items():
    print('=' * 20, gname)
    print(' deep empty squares:', sum(store[n]['deep'] for n in names), '| undominated mass:', sum(store[n]['undom'] for n in names),
          '| max |N(Q)∩S|:', max(store[n]['selmax'] for n in names), 'min:', min(store[n]['selmin'] for n in names),
          '| max nonempty directions of an empty square:', max(store[n]['nQmax'] for n in names))
    print(' v:', sorted({store[n]['v'] for n in names}), 'T/v:', st.mean(store[n]['T'] / store[n]['v'] for n in names),
          '2s0/v:', st.mean(2 * store[n]['s0'] / store[n]['v'] for n in names))
    for key in KEYS:
        means = []; mins1 = []; mins2 = []; ends = []; wm = {k: [] for k in KS}
        for n in names:
            o = store[n]
            for seq in o['seqs']:
                vals = [float(o['g'][x][key]) for x in seq]
                if o['cyclic']:
                    inner = vals; mins2.append(min(vals)); mins1.append(min(vals))
                else:
                    inner = vals[1:-1]; mins1.append(min(vals[1:-1])); mins2.append(min(vals[2:-2])); ends += [vals[0], vals[-1]]
                for k in KS:
                    if k <= len(inner): wm[k].append(winmin(inner, k, o['cyclic']))
            means.append(sum(float(o['g'][x][key]) for x in o['g']) / o['v'])
        mu = st.mean(means)
        print(f' {key:6s} mean {mu:6.3f} (floor {floor(mu):6.1f})  min internal {min(mins1):5.2f}  min idx2..v-3 {min(mins2):5.2f}'
              + (f'  endpoints min {min(ends):5.2f}' if ends else ''))
        print('        k-window min mean: ' + ' '.join(f'k{k}:{min(wm[k]):.2f}' for k in KS if wm[k]))
