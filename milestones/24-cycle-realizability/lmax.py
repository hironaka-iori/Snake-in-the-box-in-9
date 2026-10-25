"""L_max of every collected cycle (data/cycles.json) for every entry phase, by the exhaustive
DFS of unroll.c, re-checked by the pure-Python brute force of brute.py (no symmetry
reduction) and by an independent induced-path check of the witness.  Writes data/lmax.json.

L_max(phase) = the largest n such that some induced path of Q9 has 7 + n edges whose
consecutive 7-direction windows have the shapes states[phase], states[phase+1], ...,
states[phase+n] (cyclically), i.e. the snake stays n automaton transitions on the cycle.
Where the DFS hits LIMIT nodes the value is a lower bound (exact = false); see sat_lmax.py.
"""
import json, os, time
from shapes import unroll, check_sequence, rules_of_cycle
from brute import brute

LIMIT = 20_000_000          # DFS node limit; beyond it L_max is reported as a lower bound

HERE = os.path.dirname(os.path.abspath(__file__))
cyc = json.load(open(os.path.join(HERE, 'data', 'cycles.json')))
out = {}
for name, c in cyc.items():
    st = [tuple(s) for s in c['states']]
    p = len(st)
    res = []
    for ph in range(p):
        t = time.time()
        r = unroll(st, ph, limit=LIMIT)
        check_sequence(r['seq'], st, ph)
        nodes = None
        if r['exhaustive'] and r['nodes'] <= 200000:     # pure-Python cross-check where cheap
            b, nodes = brute(st, ph)
            assert b == r['max_transitions'], (name, ph, b, r)
        res.append(dict(phase=ph, L_max=r['max_transitions'], path_edges=r['path_edges'],
                        periods=round(r['max_transitions'] / p, 3), dfs_nodes=r['nodes'],
                        brute_nodes=nodes, exhaustive=r['exhaustive'], witness=r['seq']))
    mx = max(x['L_max'] for x in res)
    exh = all(x['exhaustive'] for x in res)
    out[name] = dict(period=p, rules=rules_of_cycle(st), states=c['states'],
                     exact=exh, L_max=mx, L_max_periods=round(mx / p, 3),
                     forbidden_run=mx + 1, phases=res)
    print(f"{name:28s} p={p:2d} rules={rules_of_cycle(st)} L_max by phase="
          f"{[x['L_max'] for x in res]} max={'' if exh else '>='}{mx} ({mx / p:.2f} periods, path {mx + 7} edges)", flush=True)
json.dump(out, open(os.path.join(HERE, 'data', 'lmax.json'), 'w'), indent=1)
