"""Search the parity lifts of saved lower-dimensional paths after0,1,2 omissions."""
from pathlib import Path
import argparse,collections,hashlib,itertools,json,sys,time
H=Path(__file__).resolve().parents[1];R=H.parents[1];sys.path.insert(0,str(R/'work/solver_packages'))
from ortools.sat.python import cp_model
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
ap=argparse.ArgumentParser();ap.add_argument('--tag',required=True);ap.add_argument('--seconds',type=float,default=240);ap.add_argument('--per-query',type=float,default=2);ap.add_argument('--start',type=int,default=0);a=ap.parse_args()
source=R/'milestones/188-dimensional-constructions/data/lower-dimensional-seeds.json';raw=json.loads(source.read_bytes());dest=H/'data'/(a.tag+'.json');assert not dest.exists()
out=dict(status='RUNNING',arguments=vars(a),source_sha256=sha(source),script_sha256=sha(__file__),results=[],witnesses=[],q9_witness=None,scope='Saved parent paths in dimensions5..8, parity lift U={(x,parity x):x retained}, deleting0,1,2parentvertices. Exact closed-neighbour contraction with free Hamiltonian endpoints, other colour class and order. Every lifted witness is checked by all pairs. Native infeasibility and finite static exclusions are not end-to-end Lean certificates.')
def save():dest.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
started=time.monotonic();ident=-1;stopped=False;save()
for n in [5,6,7,8]:
    p=raw[str(n)]['vertices'];assert len(p)==len(set(p))==raw[str(n)]['edges']+1
    assert all(((v^p[j]).bit_count()==1)==(j==i+1) for i,v in enumerate(p) for j in range(i+1,len(p)))
    closed=[sum(1<<v for v in ({y}|{y^(1<<k) for k in range(n)})) for y in range(1<<n)]
    lift=lambda x:x+((x.bit_count()%2)<<n)
    for r in [0,1,2]:
        for removed in itertools.combinations(range(len(p)),r):
            ident+=1
            if ident<a.start:continue
            if time.monotonic()-started>=a.seconds:stopped=True;break
            S=sorted(v for i,v in enumerate(p) if i not in removed);mask=sum(1<<v for v in S);edges={};adj={v:set() for v in S}
            for y,c in enumerate(closed):
                ns=c&mask
                if ns.bit_count()!=2:continue
                lo=ns&-ns;v=lo.bit_length()-1;w=(ns^lo).bit_length()-1
                label=y+((1-y.bit_count()%2)<<n);edges.setdefault((v,w),[]).append(label);adj[v].add(w);adj[w].add(v)
            row=dict(id=ident,parent_dimension=n,cube_dimension=n+1,removed_indices=list(removed),target_edges=2*(len(S)-1),edges=len(edges),leaves=[v for v in S if len(adj[v])==1]);out['results'].append(row)
            if any(not adj[v] for v in S):row.update(status='ISOLATED',certificate=[v for v in S if not adj[v]]);continue
            if len(row['leaves'])>2:row.update(status='TOO_MANY_LEAVES');continue
            reached={S[0]};stack=[S[0]]
            while stack:
                v=stack.pop()
                for w in adj[v]-reached:reached.add(w);stack.append(w)
            if len(reached)<len(S):row.update(status='DISCONNECTED',certificate=sorted(reached));continue
            index={v:i for i,v in enumerate(S)};size=len(S);m=cp_model.CpModel();arcs=[];variables={}
            for v,w in edges:
                for i,j in [(index[v],index[w]),(index[w],index[v])]:
                    x=m.new_bool_var(f'a{i}_{j}');variables[i,j]=x;arcs.append((i,j,x))
            for i in range(size):
                for u,v in [(i,size),(size,i)]:
                    x=m.new_bool_var(f'a{u}_{v}');variables[u,v]=x;arcs.append((u,v,x))
            m.add_circuit(arcs);model=H/'data'/f'{a.tag}-{ident:05d}.pbtxt';m.export_to_file(str(model));row.update(model=model.name,model_sha256=sha(model))
            solver=cp_model.CpSolver();solver.parameters.num_search_workers=1;solver.parameters.max_memory_in_mb=256;solver.parameters.max_time_in_seconds=min(a.per_query,a.seconds-(time.monotonic()-started))
            status=solver.solve(m);row.update(status=solver.status_name(status),seconds=solver.wall_time,branches=solver.num_branches,conflicts=solver.num_conflicts)
            if status in [cp_model.FEASIBLE,cp_model.OPTIMAL]:
                succ={i:j for (i,j),x in variables.items() if solver.value(x)};route=[];v=succ[size]
                while v!=size:
                    assert v not in route;route.append(v);v=succ[v]
                assert len(route)==size;order=[S[i] for i in route];path=[lift(order[0])]
                for v,w in zip(order,order[1:]):path.extend([edges[min(v,w),max(v,w)][0],lift(w)])
                assert len(path)==len(set(path))==row['target_edges']+1
                assert all(((v^path[j]).bit_count()==1)==(j==i+1) for i,v in enumerate(path) for j in range(i+1,len(path)))
                witness=dict(id=ident,cube_dimension=n+1,edges=row['target_edges'],path=path,contracted_path=order,removed_indices=list(removed));out['witnesses'].append(witness);row['status']='WITNESS'
                if n==8 and row['target_edges']>=192:out['q9_witness']=witness;stopped=True;save();break
            save()
        if stopped:break
    if stopped:break
out['status']='Q9_WITNESS' if out['q9_witness'] else 'TIME_LIMIT' if stopped else 'COMPLETE_QUERY_BATCH'
out['next_id']=out['results'][-1]['id']+1 if out['results'] else a.start;out['statuses']=dict(collections.Counter(x['status'] for x in out['results']));out['seconds']=time.monotonic()-started;save()
print(json.dumps(dict(status=out['status'],statuses=out['statuses'],seconds=out['seconds'],next_id=out['next_id'],witnesses=[(w['cube_dimension'],w['edges'],w['id']) for w in out['witnesses']],q9_witness=out['q9_witness'])),flush=True)
