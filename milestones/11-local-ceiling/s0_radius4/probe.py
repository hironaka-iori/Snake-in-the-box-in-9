"""Witness descent (upper bounds on min shareN, M=12) for given 5-centre windows. usage: probe.py tl 'dirs|alphas' ..."""
import sys, json
from e1lib import ShareModel
tl = float(sys.argv[1])
for spec in sys.argv[2:]:
    ds, als = spec.split('|')
    dirs = [int(x) for x in ds.split(',')]
    al = [(6, 21) if s == '6+' else int(s) for s in als.split(',')]
    sm = ShareModel(dirs, al, 4, 12, tcap=302)
    r = sm.minimise2(Kmax=300, time_limit=tl, budget=30000)
    r.pop('sel', None); r.update(dirs=dirs, alpha_req=als, M=12)
    print(json.dumps(r), flush=True)
    with open('probe_results.jsonl', 'a') as f: f.write(json.dumps(r) + '\n')
