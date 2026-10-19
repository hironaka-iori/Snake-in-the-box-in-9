import sys, json, time
from e1lib import ShareModel
M = int(sys.argv[1]); radius = int(sys.argv[2]); syms = sys.argv[3].split(',')
tl = float(sys.argv[4]) if len(sys.argv) > 4 else 500
out = []
for s in syms:
    a = (6, 21) if s == '6+' else ((int(s.split('-')[0]), int(s.split('-')[1])) if '-' in s else int(s))
    Kmax = int(sys.argv[5]) if len(sys.argv) > 5 else 50
    sm = ShareModel([0, 1], [a], radius, M, tcap=Kmax + 2)
    print(f'M={M} r={radius} alpha={a}: vars {sm.enc.nv} ulits {len(sm.ulits)}', flush=True)
    r = sm.minimise(Kmax=Kmax, time_limit=tl, log=lambda x: print(x, flush=True))
    r['alpha_req'] = s; r['M'] = M; r['radius'] = radius
    print(json.dumps({k: v for k, v in r.items() if k != 'sel'}), flush=True)
    out.append(r)
json.dump(out, open(f'single_M{M}_r{radius}_{"_".join(syms)}.json', 'w'))
