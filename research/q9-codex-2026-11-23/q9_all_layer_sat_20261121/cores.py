"""Reduce fixed conditions heuristically, then export one standalone DRAT example."""
import json, random, sys
from pathlib import Path
from pysat.solvers import Solver
from layers import Model, layer_order, seeds, BASE, verify

known = seeds()
snapshot = BASE / 'seed_paths.json'
if not snapshot.exists():
    snapshot.write_text(json.dumps(known, sort_keys=True))
known = json.loads(snapshot.read_text())
for w,p in known.items():verify(p,w)
rows = [json.loads(s) for s in (BASE/'results4.jsonl').read_text().splitlines()]
selection = sorted((r for r in rows if r['status']=='UNSAT'), key=lambda r:r['conflicts'])[:6]
best = None
for row in selection:
    word = row['word']
    m = Model(word,193)
    rng = random.Random(71031)
    path = known[word]
    mask = [{v&31 for v in path if v >> 5 == h} for h in m.order]
    assumptions = [v for i,x in enumerate(m.x) for v in rng.sample([x[k] for k in sorted(mask[i])],4)]
    with Solver(name='cadical195', bootstrap_with=m.clauses) as solver:
        solver.set_phases([v if k in mask[i] else -v for i,x in enumerate(m.x) for k,v in enumerate(x)])
        solver.conf_budget(15000)
        if solver.solve_limited(assumptions=assumptions) is not False:continue
        core = list(solver.get_core())
        for v in core.copy():
            if v not in core:continue
            trial = [x for x in core if x!=v]
            solver.conf_budget(650)
            if solver.solve_limited(assumptions=trial) is False:
                core=list(solver.get_core())
    record = dict(word=word,positive_pins=len(core), variables=sorted(core),
                  cube_vertices=[32*m.order[(x-1)//32]+(x-1)%32 for x in sorted(core)])
    print(json.dumps(record), flush=True)
    if best is None or len(core)<best['positive_pins']:best = record
if best is None:sys.exit(1)
m=Model(best['word'],193)
cnf=m.clauses + [[x] for x in best['variables']]
with (BASE/'core.cnf').open('w') as fh:
    print('p cnf',m.top,len(cnf),file=fh)
    for c in cnf:print(*c,0,file=fh)
with Solver(name='cadical195', bootstrap_with=cnf, with_proof=True) as solver:
    assert solver.solve() is False
    proof=solver.get_proof()
    (BASE/'core.drat').write_text('\n'.join(proof)+'\n')
(BASE/'certificate.json').write_text(json.dumps(best, indent=2)+'\n')
