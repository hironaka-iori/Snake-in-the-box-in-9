"""Finite colour-refinement data for symmetry of each rooted allowed graph."""
from pathlib import Path
from collections import Counter
import hashlib, json
H = Path(__file__).resolve().parents[1]
p = H/'data/complement-graph.json'
data = json.loads(p.read_bytes()); reports = []
for g in data['reports']:
    V = g['allowed_vertices']; S = set(V); root = g['root']
    N = {v:sorted(v ^ (1<<k) for k in range(8) if v ^ (1<<k) in S) for v in V}
    signatures = {v:(v == root, len(N[v])) for v in V}
    palette = {key:i for i,key in enumerate(sorted(set(signatures.values())))}
    colours = {v:palette[signatures[v]] for v in V}
    rounds = [{'classes':len(palette), 'sizes':sorted(Counter(colours.values()).values()),
               'colours':[colours[v] for v in V]}]
    while True:
        signatures = {v:(colours[v], tuple(sorted(colours[w] for w in N[v]))) for v in V}
        palette = {key:i for i,key in enumerate(sorted(set(signatures.values())))}
        new = {v:palette[signatures[v]] for v in V}
        rounds.append({'classes':len(palette), 'sizes':sorted(Counter(new.values()).values()),
                       'colours':[new[v] for v in V]})
        stable = len(palette) == len(set(colours.values()))
        colours = new
        if stable: break
    reports.append({'root':root, 'vertices':V, 'rounds':rounds, 'discrete':len(palette)==len(V),
                    'nontrivial_classes':[[v for v in V if colours[v]==c] for c in sorted(palette.values())
                                         if sum(colours[v]==c for v in V)>1]})
out = {'source_sha256':hashlib.sha256(p.read_bytes()).hexdigest(), 'reports':reports,
       'scope':'Finite enumeration. A root-fixing graph automorphism preserves every refinement round. A discrete final partition would therefore force identity; no nontrivial automorphism is asserted from surviving colour classes.'}
(H/'data/graph-refinement.json').write_text(json.dumps(out,indent=2)+'\n')
for r in reports: print(r['root'], [s['classes'] for s in r['rounds']], 'discrete',r['discrete'])
