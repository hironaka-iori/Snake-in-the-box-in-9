"""Redundant edge linearization and short-cycle cuts after path contraction."""
import argparse,itertools,json,random,time
from pathlib import Path
import contracted as base
from small_controls import all_path_sets
original_build=base.build
def build(n,seed,inside,fix_seed=False):
    m,x,starts,arcs,g=original_build(n,seed,inside,fix_seed)
    adj={v:set() for v in x}
    for v,w in g['physical']+list(g['artificial']):
        z=arcs[v,w]+arcs[w,v]
        m.add(z<=x[v]);m.add(z<=x[w])
        adj[v].add(w);adj[w].add(v)
    m.add(sum(arcs.values())==sum(x.values())-1)
    cycles=set()
    for v in adj:
        for w in adj[v]:
            if v<w:
                for z in adj[v]&adj[w]:cycles.add(frozenset((v,w,z)))
    for v,w in itertools.combinations(adj,2):
        for a,b in itertools.combinations(adj[v]&adj[w],2):
            cycles.add(frozenset((v,w,a,b)))
    for c in sorted(cycles,key=lambda c:(len(c),sorted(c))):
        m.add(sum(x[v] for v in c)<=len(c)-1)
    g['short_cycle_cuts']=len(cycles)
    return m,x,starts,arcs,g
base.build=build
def controls():
    begin=time.monotonic();rng=random.Random(192);cache={};rows=[]
    scenarios=[(2,[0,1,3],list(range(16))),(3,[0,1,3],list(range(256))),
        (3,[0,1,3,7,6],list(range(256))),
        (4,[0,1,3,7,6],sorted({0,65535,*rng.sample(range(65536),62)}))]
    for n,seed,regions in scenarios:
        if n not in cache:cache[n]=all_path_sets(n)
        full=(1<<(1<<n))-1;seedmask=sum(1<<v for v in seed)
        for region in regions:
            outside=full^region
            expected=max(p.bit_count()-1 for p in cache[n] if p&outside==seedmask&outside)
            r=base.solve(n,seed,{v for v in range(1<<n) if region>>v&1},3)
            assert r['status']=='OPTIMAL' and r['edges']==expected
            rows.append(dict(n=n,seed=seed,region_mask=region,oracle_edges=expected,model_edges=r['edges']))
    report=dict(status='PASSED',cases=rows,seconds=time.monotonic()-begin,
        script_sha256_lf=base.sha(Path(__file__)),model_sha256_lf=base.sha(Path(base.__file__)),
        oracle_sha256_lf=base.sha(base.HERE/'scripts/small_controls.py'))
    (base.HERE/'data/strengthened-controls.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(f'Passed {len(rows)} strengthened controls',flush=True)
def run(seconds):
    source=base.ROOT/'milestones/18-expanded-cells/data/aligned-seed.json'
    inventory=base.ROOT/'milestones/23-parity-compatible-faces/data/boundary-inventory.json'
    seed=json.loads(source.read_text())['path_vertices']
    report=dict(script_sha256_lf=base.sha(Path(__file__)),model_sha256_lf=base.sha(Path(base.__file__)),
        source_sha256_lf=base.sha(source),inventory_sha256_lf=base.sha(inventory),
        scope='Restricted maximization with redundant linear constraints and augmented-graph triangle and four-cycle cuts. No global exclusion.',controls=[],runs=[])
    for face in json.loads(inventory.read_text())['rows']:
        inside={v for v in range(512) if v&face['fixed_mask']==face['fixed_value']}
        c=base.solve(9,seed,inside,5,True);assert c['status']=='OPTIMAL' and c['edges']==191
        c['face_index']=face['face_index'];report['controls'].append(c)
        r=base.solve(9,seed,inside,seconds);r['face_index']=face['face_index']
        r['short_cycle_cuts']=build(9,seed,inside)[-1]['short_cycle_cuts'];report['runs'].append(r)
        (base.HERE/'data/strengthened-search.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
        print(json.dumps({k:r.get(k) for k in ('face_index','status','edges','objective_bound_edges','short_cycle_cuts')}),flush=True)
        if r.get('edges',0)>191:break
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--seconds',type=float,default=20);args=ap.parse_args()
    controls();run(args.seconds)
