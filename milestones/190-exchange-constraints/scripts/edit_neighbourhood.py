from pathlib import Path
import sys,json,time,hashlib,argparse
R=Path('E:/Snake-in-a-box');H=R/'milestones/190-exchange-constraints';sys.path.insert(0,str(R/'work/solver_packages'))
from ortools.sat.python import cp_model
ap=argparse.ArgumentParser();ap.add_argument('--edits',type=int,required=True);ap.add_argument('--seconds',type=float,default=90);ap.add_argument('--deleted-edges',type=int);args=ap.parse_args();tag=f'exact-edits{args.edits}'+(f'-deletededges{args.deleted_edges}' if args.deleted_edges is not None else '')
row=json.loads((H/'data/middle95.json').read_text());old=row['middle'];s,t=old[0],old[-1];model=cp_model.CpModel();x=[model.new_bool_var('x'+str(v)) for v in range(256)];arcs=[(v,v,x[v].Not()) for v in range(256)];directed={}
for u in range(256):
    for k in range(8):
        v=u^(1<<k)
        if v<=u:continue
        a=model.new_bool_var(f'a{u}_{v}');b=model.new_bool_var(f'a{v}_{u}');directed[u,v]=a;directed[v,u]=b;arcs.extend([(u,v,a),(v,u,b)])
        model.add(a+b<=x[u]);model.add(a+b<=x[v]);model.add(a+b>=x[u]+x[v]-1)
# Exact degree and edge accounting for a fixed-endpoint replacement.
deleted_pair=[]
for i,(u,v) in enumerate(zip(old,old[1:])):
    z=model.new_bool_var('deleted_pair'+str(i));model.add(z<=1-x[u]);model.add(z<=1-x[v]);model.add(z>=1-x[u]-x[v]);deleted_pair.append(z)
oldset=set(old)
added_edges=[b for (u,v),b in directed.items() if u not in oldset and v not in oldset]
model.add(sum(added_edges)==sum(deleted_pair)+2)
if args.deleted_edges is not None:model.add(sum(deleted_pair)==args.deleted_edges)
model.add(x[s]==1);model.add(x[t]==1);arcs.append((t,s,True));model.add_circuit(arcs);model.add(sum(x)==98);model.add(sum(x[v] for v in old)==96-args.edits)
for v,b in enumerate(x):model.add_hint(b,int(v in old))
model.export_to_file(str(H/'data'/(tag+'.pbtxt')));solver=cp_model.CpSolver();solver.parameters.num_search_workers=1;solver.parameters.max_time_in_seconds=args.seconds;solver.parameters.max_memory_in_mb=512;solver.parameters.random_seed=190
start=time.monotonic();status=solver.solve(model);out={'status':solver.status_name(status),'exchange_edge_identity_imposed':True,'deleted_internal_edges':args.deleted_edges,'seconds':time.monotonic()-start,'time_limit':args.seconds,'original_vertices_removed':args.edits,'branches':solver.num_branches,'conflicts':solver.num_conflicts,'model_sha256':hashlib.sha256((H/'data'/(tag+'.pbtxt')).read_bytes()).hexdigest(),'scope':f'A97-edgeQ8path with the same ports, retaining exactly{96-args.edits} of the96 vertices of the common95-edge path. All outside vertices are available; no Q9 outer restrictions.'}
if status in [cp_model.FEASIBLE,cp_model.OPTIMAL]:
    path=[s]
    while path[-1]!=t:
        opts=[v for (u,v),b in directed.items() if u==path[-1] and solver.value(b)];assert len(opts)==1 and opts[0] not in path;path.append(opts[0])
    assert len(path)==98 and len(set(path)&set(old))==96-args.edits
    assert all(((path[i]^path[j]).bit_count()==1)==(j==i+1) for i in range(98) for j in range(i+1,98))
    out.update(middle_vertices=path,removed_vertices=sorted(set(old)-set(path)),added_vertices=sorted(set(path)-set(old)))
(H/'data'/(tag+'.json')).write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if not isinstance(v,list)},indent=2),flush=True)
