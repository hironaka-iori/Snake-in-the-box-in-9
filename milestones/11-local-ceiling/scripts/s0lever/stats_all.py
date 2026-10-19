import json, sys, statistics as st, pickle
from fractions import Fraction as F
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from charges import analyse, R
OUT = os.path.dirname(os.path.abspath(__file__)) + '/'
bank = [b['vertex_sequence'] for b in json.load(open(R + 'work/bank9.json'))]
adv = {n: json.load(open(R + f'milestones/11-local-ceiling/data/adversary{n}.json')) for n in (208, 224)}
KEYS = ['alpha', 'ex', 'dom', 'c3', 'cheap']
res = {}
for n, d in adv.items():
    r = analyse(d['S'], True)
    res[f'adv{n}'] = dict(seqs=d['cycles'], cyclic=True, r=r)
for idx, s in enumerate(bank):
    r = analyse(s, False)
    res[f'bank{idx}'] = dict(seqs=[s], cyclic=False, r=r)
# strip sel / nQ to keep pickle small
store = {}
for name, o in res.items():
    r = o['r']
    store[name] = dict(seqs=o['seqs'], cyclic=o['cyclic'], v=r['v'], T=r['T'], s0=r['s0'], deep=r['deep'], undom=r['undom'],
                       g={x: {k: r['g'][x][k] for k in KEYS} for x in r['g']},
                       nQmax=max(a for a, b in r['nQ']), selmax=max(b for a, b in r['nQ']), selmin=min(b for a, b in r['nQ']))
pickle.dump(store, open(OUT + 'charges.pkl', 'wb'))
print('done')
