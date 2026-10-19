import pickle, statistics as st
import os
D = os.path.dirname(os.path.abspath(__file__)) + '/'
store = pickle.load(open(D + 'charges.pkl', 'rb'))
need = {X: (9214 - 35 * (X + 2)) / (X + 2) for X in (230, 220, 210, 200, 196)}
bank = [n for n in store if n.startswith('bank')]
def gmean(names, G):
    return st.mean(sum(min(float(store[n]['g'][x]['dom']), G) for x in store[n]['g']) / store[n]['v'] for n in names)
print('minimal cap G (step 0.25) with mean of min(dom,G) above the target:')
for X, mu in need.items():
    out = []
    for names, lab in ((bank, 'bank'), (['adv208'], 'adv208'), (['adv224'], 'adv224')):
        G = 0.0
        while G < 60 and gmean(names, G) <= mu: G += 0.25
        out.append(f'{lab}: ' + (f'G>={G:.2f}' if G < 60 else 'never'))
    print(f' m<={X} (mu>{mu:.3f}): ' + ' | '.join(out))
def wins(vals, k, cyc):
    n = len(vals); p = [0.0]
    ext = vals + vals[:k] if cyc else vals
    for a in ext: p.append(p[-1] + a)
    rng = range(n) if cyc else range(n - k + 1)
    return min(p[s + k] - p[s] for s in rng) / k
print('smallest k such that every k-window of internal vertices has mean dom above the target (sliding-window necessity):')
series = {}
for lab, names in (('bank', bank), ('adv208', ['adv208']), ('adv224', ['adv224'])):
    seqs = []
    for n in names:
        o = store[n]
        for s in o['seqs']:
            vals = [float(o['g'][x]['dom']) for x in s]
            seqs.append((vals if o['cyclic'] else vals[1:-1], o['cyclic']))
    series[lab] = seqs
for X, mu in need.items():
    out = []
    for lab, seqs in series.items():
        kk = None
        for k in range(1, 191):
            if all(len(v) < k or wins(v, k, c) > mu for v, c in seqs) and any(len(v) >= k for v, c in seqs):
                kk = k; break
        out.append(f'{lab}: k={kk}')
    print(f' m<={X}: ' + ' | '.join(out))
