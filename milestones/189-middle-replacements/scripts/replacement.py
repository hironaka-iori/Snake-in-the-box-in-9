from pathlib import Path
import json,sys,argparse,time,hashlib
R=Path('E:/Snake-in-a-box');H=R/'milestones/189-middle-replacements';sys.path.insert(0,str(R/'work/solver_packages'))
from ortools.sat.python import cp_model

def check(p,n):
    assert len(p)==len(set(p)) and all(0<=v<1<<n for v in p)
    for i,u in enumerate(p):
        for j in range(i+1,len(p)):assert ((u^p[j]).bit_count()==1)==(j==i+1)

def canonical(row):
    variants=[]
    for path in [row['middle'],row['middle'][::-1]]:
        names={}
        for u,v in zip(path,path[1:]):names.setdefault((u^v).bit_length()-1,len(names))
        assert len(names)==8
        def mapping(v):
            w=v^path[0];return sum(((w>>old)&1)<<new for old,new in names.items())
        variants.append((tuple(mapping(v) for v in path),tuple(sorted(mapping(v) for v in row['allowed']))))
    return min(variants)

def solve(index,seconds,target):
    data=json.loads((H/'data/replacement-contexts.json').read_text());row=data['rows'][index]
    allowed=row['retained'];s,t=row['ports'];model=cp_model.CpModel();x={v:model.new_bool_var('x'+str(v)) for v in allowed};idx={v:i for i,v in enumerate(allowed)}
    arcs=[(idx[v],idx[v],x[v].Not()) for v in allowed];directed={}
    for u in allowed:
        for k in range(8):
            v=u^(1<<k)
            if v not in x or v<=u:continue
            a=model.new_bool_var(f'a{u}_{v}');b=model.new_bool_var(f'a{v}_{u}');directed[u,v]=a;directed[v,u]=b
            arcs.extend([(idx[u],idx[v],a),(idx[v],idx[u],b)])
            model.add(a+b<=x[u]);model.add(a+b<=x[v]);model.add(a+b>=x[u]+x[v]-1)
    model.add(x[s]==1);model.add(x[t]==1);arcs.append((idx[t],idx[s],True));model.add_circuit(arcs)
    model.add(sum(x.values())==target+1)
    current=set(row['middle'])
    for v,b in x.items():model.add_hint(b,int(v in current))
    tag=f'context{index:02}-middle{target}'
    model.export_to_file(str(H/'data'/(tag+'.pbtxt')))
    solver=cp_model.CpSolver();solver.parameters.num_search_workers=1;solver.parameters.max_time_in_seconds=seconds;solver.parameters.max_memory_in_mb=512;solver.parameters.random_seed=189
    started=time.monotonic();status=solver.solve(model)
    report={'context_index':index,'bank_index':row['bank_index'],'coordinate':row['coordinate'],'target_middle_edges':target,'target_full_edges':target+row['outer_edges']+2,'allowed_vertices':len(allowed),'status':solver.status_name(status),'seconds':time.monotonic()-started,'time_limit':seconds,'branches':solver.num_branches,'conflicts':solver.num_conflicts,'model_sha256':hashlib.sha256((H/'data'/(tag+'.pbtxt')).read_bytes()).hexdigest(),'scope':'Exactly the target middle-path length, fixed ports and fixed outer components; solver exclusion has no Lean certificate.'}
    if status in [cp_model.OPTIMAL,cp_model.FEASIBLE]:
        path=[s]
        while path[-1]!=t:
            opts=[v for (u,v),a in directed.items() if u==path[-1] and solver.value(a)]
            assert len(opts)==1 and opts[0] not in path;path.append(opts[0])
        assert len(path)==target+1 and set(path)=={v for v,b in x.items() if solver.value(b)}
        check(path,8);joined=row['left']+[v+256 for v in path]+row['right'];check(joined,9)
        report.update(middle_vertices=path,joined_vertices=joined,joined_edges=len(joined)-1)
    (H/'data'/(tag+'.json')).write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if not isinstance(v,list)},indent=2),flush=True)

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--index',type=int,default=0);ap.add_argument('--seconds',type=float,default=120);ap.add_argument('--target',type=int,default=97);ap.add_argument('--classify',action='store_true');args=ap.parse_args()
    if args.classify:
        rows=json.loads((H/'data/replacement-contexts.json').read_text())['rows'];seen={};classes=[]
        for i,row in enumerate(rows):seen.setdefault(canonical(row),[]).append(i)
        for k,ids in seen.items():classes.append({'representative':ids[0],'members':ids,'middle_edges':rows[ids[0]]['middle_edges'],'canonical_digest':hashlib.sha256(repr(k).encode()).hexdigest()})
        (H/'data/context-classes.json').write_text(json.dumps(classes,indent=2)+'\n');print(json.dumps([{k:v for k,v in c.items() if k!='canonical_digest'} for c in classes],indent=2))
    else:solve(args.index,args.seconds,args.target)
