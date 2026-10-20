"""Maximize induced-path length after contracting fixed outside path interiors."""
import argparse,json,sys,time,hashlib
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'work'))
from exact_search import cp_model
def sha(p):return hashlib.sha256(p.read_bytes().replace(b'\r\n',b'\n')).hexdigest()
def check(p,n):
    assert len(p)==len(set(p)) and all(0<=v<1<<n for v in p)
    for j,v in enumerate(p):
        for i,w in enumerate(p[:j]):assert ((v^w).bit_count()==1)==(i+1==j)
def geometry(n,seed,inside):
    check(seed,n);inside=set(inside);outside=set(seed)-inside
    neighbors={v:[w for w in outside if (v^w).bit_count()==1] for v in outside}
    unseen=set(outside);components=[]
    while unseen:
        v=min(v for v in unseen if len(neighbors[v])<=1);p=[v];unseen.remove(v)
        while True:
            nxt=[w for w in neighbors[p[-1]] if w in unseen]
            if not nxt:break
            assert len(nxt)==1;p+=nxt;unseen.remove(nxt[0])
        components.append(p)
    internal={v for p in components for v in p[1:-1]}
    forbidden={v for v in inside if any((v^w).bit_count()==1 for w in internal)}
    nodes=sorted((inside-forbidden)|(outside-internal))
    assert not (set(seed)&forbidden)
    physical=[(v,w) for i,v in enumerate(nodes) for w in nodes[i+1:] if (v^w).bit_count()==1]
    artificial={tuple(sorted((p[0],p[-1]))):p for p in components if len(p)>=3}
    assert not (set(physical)&set(artificial))
    assert len(internal)==sum(len(p)-2 for p in artificial.values())
    return {'nodes':nodes,'forced':sorted(outside-internal),'internal':internal,'forbidden':forbidden,'components':components,'physical':physical,'artificial':artificial}
def build(n,seed,inside,fix_seed=False):
    g=geometry(n,seed,inside);nodes=g['nodes'];offset=len(g['internal'])
    m=cp_model.CpModel();x={v:m.new_bool_var(f'x{v}') for v in nodes}
    starts={v:m.new_bool_var(f's{v}') for v in nodes};ends={v:m.new_bool_var(f'e{v}') for v in nodes}
    circuit=[(v,v,x[v].Not()) for v in nodes];arcs={};neighbors={v:[] for v in nodes}
    for v,w in g['physical']+list(g['artificial']):
        neighbors[v].append(w);neighbors[w].append(v)
        for a,b in ((v,w),(w,v)):
            t=m.new_bool_var(f'a{a}_{b}');arcs[a,b]=t;circuit.append((a,b,t))
        m.add(arcs[v,w]+arcs[w,v]>=x[v]+x[w]-1)
    for v in nodes:
        circuit.extend([(1<<n,v,starts[v]),(v,1<<n,ends[v])])
        m.add(starts[v]+ends[v]<=x[v])
        m.add(sum(x[w] for w in neighbors[v])==2-starts[v]-ends[v]).only_enforce_if(x[v])
    for v in g['forced']:m.add(x[v]==1)
    if fix_seed:
        for v in nodes:m.add(x[v]==int(v in seed))
    m.add_circuit(circuit)
    m.add(sum(v*t for v,t in starts.items())<sum(v*t for v,t in ends.items()))
    m.add(sum(x.values())+offset>=len(seed))
    m.maximize(sum(x.values())+offset-1)
    hint=[v for v in seed if v not in g['internal']]
    if hint[0]>hint[-1]:hint.reverse()
    used=set(zip(hint,hint[1:]))
    for v in nodes:
        m.add_hint(x[v],int(v in hint));m.add_hint(starts[v],int(v==hint[0]));m.add_hint(ends[v],int(v==hint[-1]))
    for e,t in arcs.items():m.add_hint(t,int(e in used))
    return m,x,starts,arcs,g
def solve(n,seed,inside,seconds=20,fix_seed=False):
    m,x,starts,arcs,g=build(n,seed,inside,fix_seed)
    s=cp_model.CpSolver();s.parameters.max_time_in_seconds=seconds;s.parameters.num_search_workers=2;s.parameters.random_seed=192
    status=s.solve(m)
    row={'status':s.status_name(status),'seconds':s.wall_time,'limit_seconds':seconds,'workers':2,'random_seed':192,'fix_seed':fix_seed,'model_vertices':len(g['nodes']),'forced_vertices':len(g['forced']),'contracted_internal_vertices':len(g['internal']),'forbidden_inside':len(g['forbidden']),'components':g['components'],'objective_bound_edges':s.best_objective_bound,'branches':s.num_branches,'conflicts':s.num_conflicts}
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
        assert set(used)==set(g['artificial']) and len(used)==len(set(used))
        check(expanded,n)
        assert len(expanded)==len(p)+len(g['internal'])
        assert set(expanded)^set(seed)<=set(inside)
        assert len(expanded)-1==int(round(s.objective_value))
        row.update(edges=len(expanded)-1,path_vertices=expanded,compressed_path=p)
    return row
def run(args):
    source=ROOT/'milestones/18-expanded-cells/data/aligned-seed.json'
    seed=json.loads(source.read_text())['path_vertices']
    inventory=ROOT/'milestones/23-parity-compatible-faces/data/boundary-inventory.json'
    rows=json.loads(inventory.read_text())['rows']
    if args.indices:
        wanted={int(v) for v in args.indices.split(',')};rows=[r for r in rows if r['face_index'] in wanted];assert len(rows)==len(wanted)
    report={'script_sha256_lf':sha(Path(__file__)),'source_sha256_lf':sha(source),'inventory_sha256_lf':sha(inventory),'scope':'Maximization within each fixed-outside Q8 face. Every accepted path is expanded and pair-checked. Bounds and OPTIMAL statuses are restricted, uncertified solver results.','controls':[],'runs':[]}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    for r in rows:
        inside={v for v in range(512) if v&r['fixed_mask']==r['fixed_value']}
        control=solve(9,seed,inside,5,True);assert control['status']=='OPTIMAL' and control['edges']==191
        control['face_index']=r['face_index'];report['controls'].append(control)
        row=solve(9,seed,inside,args.seconds);row['face_index']=r['face_index']
        assert row['model_vertices']==r['contracted_model_vertices']
        report['runs'].append(row)
        args.output.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
        print(json.dumps({k:row.get(k) for k in ('face_index','status','edges','objective_bound_edges','model_vertices','seconds')}),flush=True)
        if row.get('edges',0)>191:break
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--seconds',type=float,default=20);ap.add_argument('--indices');ap.add_argument('--output',type=Path,required=True);run(ap.parse_args())
