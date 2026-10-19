import pickle, statistics as st, collections, math
from fractions import Fraction as F
import os
D = os.path.dirname(os.path.abspath(__file__)) + '/'
store = pickle.load(open(D + 'charges.pkl', 'rb'))
floor = lambda mu: 9214 / (35 + mu) - 1
groups = {'bank': [n for n in store if n.startswith('bank')], 'adv208': ['adv208'], 'adv224': ['adv224']}
def gmean(names, f):
    return st.mean(sum(f(store[n]['g'][x]) for x in store[n]['g']) / store[n]['v'] for n in names)
print('mean of min(dom, G) and the resulting floor (edges):')
for G in (6, 8, 10, 12, 14, 16, 18, 20, 24, 99):
    row = []
    for g, names in groups.items():
        mu = gmean(names, lambda d: min(float(d['dom']), G))
        row.append(f'{g} {mu:5.2f} ({floor(mu):5.1f})')
    print(f' G={G:3d}: ' + ' | '.join(row))
print('dom share (dom - alpha) by alpha, internal vertices:')
for g, names in groups.items():
    by = collections.defaultdict(list)
    for n in names:
        o = store[n]
        for seq in o['seqs']:
            xs = seq if o['cyclic'] else seq[1:-1]
            for x in xs:
                by[o['g'][x]['alpha']].append(float(o['g'][x]['dom'] - o['g'][x]['alpha']))
    print(' ', g, ' '.join(f'a={a}:n{len(l)} min{min(l):.2f} mean{st.mean(l):.2f}' for a, l in sorted(by.items()) if a <= 8))
den = collections.Counter()
for n in groups['bank'][:20]:
    for x, d in store[n]['g'].items(): den[d['dom'].denominator] += 1
print('denominators of dom on 20 bank snakes:', sorted(den.items()))
mx = collections.Counter()
for g, names in groups.items():
    print(g, 'max dom', max(float(store[n]['g'][x]['dom']) for n in names for x in store[n]['g']),
          'max alpha', max(store[n]['g'][x]['alpha'] for n in names for x in store[n]['g']))
