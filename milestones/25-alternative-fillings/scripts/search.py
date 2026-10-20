"""Fixed-length diversity, allowing one-edge retreat before another face repair."""
import argparse,json,sys,time,random
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'milestones/24-contracted-face-search/scripts'))
from contracted import geometry,check,sha,cp_model,solve as grow
from small_controls import all_path_sets

def build(n,seed,inside,target):
    g=geometry(n,seed,inside);nodes=g['nodes'];m=cp_model.CpModel()
    x={v:m.new_bool_var(f'x{v}') for v in nodes}
    starts={v:m.new_bool_var(f's{v}') for v in nodes}
    ends={v:m.new_bool_var(f'e{v}') for v in nodes}
    arcs={};neighbors={v:[] for v in nodes};circuit=[(v,v,x[v].Not()) for v in nodes]
    for v,w in g['physical']+list(g['artificial']):
        neighbors[v].append(w);neighbors[w].append(v)
        for a,b in ((v,w),(w,v)):
            t=m.new_bool_var(f'a{a}_{b}');arcs[a,b]=t;circuit.append((a,b,t))
        z=arcs[v,w]+arcs[w,v]
        m.add(z>=x[v]+x[w]-1);m.add(z<=x[v]);m.add(z<=x[w])
    for v in nodes:
        circuit.extend([(1<<n,v,starts[v]),(v,1<<n,ends[v])])
        m.add(starts[v]+ends[v]<=x[v])
        m.add(sum(x[w] for w in neighbors[v])==2-starts[v]-ends[v]).only_enforce_if(x[v])
    for v in g['forced']:m.add(x[v]==1)
    m.add_circuit(circuit)
    m.add(sum(v*t for v,t in starts.items())<sum(v*t for v,t in ends.items()))
    m.add(sum(x.values())+len(g['internal'])==target+1)
    m.add(sum(arcs.values())==sum(x.values())-1)
    m.maximize(sum(t for v,t in x.items() if v not in seed))
    hint=None
    if target==len(seed)-1:hint=seed[:]
    elif target==len(seed)-2:
        if seed[0] in inside:hint=seed[1:]
        elif seed[-1] in inside:hint=seed[:-1]
    if hint:
        hint=[v for v in hint if v not in g['internal']]
        if hint[0]>hint[-1]:hint.reverse()
        used=set(zip(hint,hint[1:]))
        for v in nodes:
            m.add_hint(x[v],int(v in hint));m.add_hint(starts[v],int(v==hint[0]));m.add_hint(ends[v],int(v==hint[-1]))
        for e,t in arcs.items():m.add_hint(t,int(e in used))
    return m,x,starts,arcs,g

def solve(n,seed,inside,target,seconds=20):
    m,x,starts,arcs,g=build(n,seed,inside,target)
    s=cp_model.CpSolver();s.parameters.max_time_in_seconds=seconds
    s.parameters.num_search_workers=2;s.parameters.random_seed=193
    status=s.solve(m)
    r=dict(status=s.status_name(status),seconds=s.wall_time,limit_seconds=seconds,
        workers=2,random_seed=193,target_edges=target,model_vertices=len(x),
        objective_bound_new_vertices=s.best_objective_bound)
    if status in (cp_model.FEASIBLE,cp_model.OPTIMAL):
        p=[next(v for v,t in starts.items() if s.value(t))]
        while True:
            nxt=[w for (v,w),t in arcs.items() if v==p[-1] and s.value(t)]
            if not nxt:break
            assert len(nxt)==1 and nxt[0] not in p;p+=nxt
        expanded=[p[0]];used=[]
        for v,w in zip(p,p[1:]):
            key=tuple(sorted((v,w)))
            if key in g['artificial']:
                segment=g['artificial'][key];used.append(key)
                expanded.extend(segment[1:] if segment[0]==v else segment[-2::-1])
            else:expanded.append(w)
        check(expanded,n)
        assert set(used)==set(g['artificial']) and len(used)==len(set(used))
        assert set(expanded)-set(inside)==set(seed)-set(inside)
        assert len(expanded)==target+1==len(p)+len(g['internal'])
        new=set(expanded)-set(seed);removed=set(seed)-set(expanded)
        assert len(new)==round(s.objective_value)
        r.update(path_vertices=expanded,new_vertices=sorted(new),removed_vertices=sorted(removed),
            objective_new_vertices=len(new))
    return r

def controls():
    rng=random.Random(193);rows=[];cache={}
    scenarios=[(2,[0,1,3],list(range(16))),(3,[0,1,3,7,6],list(range(256))),
        (4,[0,1,3,7,6],sorted({0,65535,*rng.sample(range(65536),30)}))]
    for n,seed,regions in scenarios:
        if n not in cache:cache[n]=all_path_sets(n)
        full=(1<<(1<<n))-1;seedmask=sum(1<<v for v in seed)
        for region in regions:
            outside=full^region
            for target in (len(seed)-1,len(seed)-2):
                valid=[p for p in cache[n] if p.bit_count()==target+1 and p&outside==seedmask&outside]
                expected=max(((p&~seedmask).bit_count() for p in valid),default=None)
                r=solve(n,seed,{v for v in range(1<<n) if region>>v&1},target,3)
                if expected is None:assert r['status']=='INFEASIBLE'
                else:assert r['status']=='OPTIMAL' and r['objective_new_vertices']==expected
                rows.append(dict(n=n,seed=seed,region=region,target=target,expected=expected,
                    status=r['status'],actual=r.get('objective_new_vertices')))
    return dict(cases=rows,status='PASSED')

def run(args):
    source=ROOT/'milestones/18-expanded-cells/data/aligned-seed.json'
    inventory=ROOT/'milestones/23-parity-compatible-faces/data/boundary-inventory.json'
    seed=json.loads(source.read_text())['path_vertices']
    report=dict(script_sha256_lf=sha(Path(__file__)),source_sha256_lf=sha(source),
        inventory_sha256_lf=sha(inventory),dependencies_sha256_lf={
            name:sha(ROOT/'milestones/24-contracted-face-search/scripts'/name)
            for name in ['contracted.py','small_controls.py']},
        hypothesis='Alternative equal-length fillings, or a one-edge retreat, may enable improvement after changing the repair region.',
        controls=controls(),runs=[],regrowth=[])
    print(f"Passed {len(report['controls']['cases'])} diversity controls",flush=True)
    output=HERE/'data/results.json';output.parent.mkdir(parents=True,exist_ok=True)
    def save():output.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
    faces={r['face_index']:r for r in json.loads(inventory.read_text())['rows']}
    for fi in [3,0,4,5]:
        f=faces[fi];inside={v for v in range(512) if v&f['fixed_mask']==f['fixed_value']}
        for target in (191,190):
            r=solve(9,seed,inside,target,args.seconds);r['face_index']=fi
            report['runs'].append(r);save()
            print(json.dumps({k:r.get(k) for k in ['face_index','target_edges','status','objective_new_vertices','objective_bound_new_vertices']}),flush=True)
    # Only genuine new selected vertices justify a follow-up repair.
    candidates=[(i,r) for i,r in enumerate(report['runs']) if r.get('objective_new_vertices',0)>0]
    candidates.sort(key=lambda ir:(-ir[1]['objective_new_vertices'],-ir[1]['target_edges']))
    for ri,r in candidates[:2]:
        p=r['path_vertices']
        for fi in [3,0,4,5]:
            if fi==r['face_index']:continue
            f=faces[fi];inside={v for v in range(512) if v&f['fixed_mask']==f['fixed_value']}
            g=grow(9,p,inside,args.seconds);g.update(parent_run=ri,face_index=fi)
            report['regrowth'].append(g);save()
            print(json.dumps({'phase':'regrowth','parent_run':ri,'face':fi,'status':g['status'],'edges':g.get('edges')}),flush=True)
            if g.get('edges',0)>191:return
    save()
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--seconds',type=float,default=20)
    run(ap.parse_args())
