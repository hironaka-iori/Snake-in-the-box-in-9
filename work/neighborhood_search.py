"""Exact vertex-set neighborhoods with neither endpoint fixed."""
import json,time,argparse
from pathlib import Path
from exact_search import cp_model
from check_snake import verify

def model(n,edges,seed,removed):
    size=1<<n
    m=cp_model.CpModel()
    x=[m.new_bool_var(f'x{v}') for v in range(size)]
    starts=[m.new_bool_var(f's{v}') for v in range(size)]
    ends=[m.new_bool_var(f'e{v}') for v in range(size)]
    arcs=[(v,v,x[v].Not()) for v in range(size)]
    path_arcs={}
    for v in range(size):
        arcs.extend([(size,v,starts[v]),(v,size,ends[v])])
        m.add(starts[v]+ends[v]<=x[v])
        m.add(sum(x[v^(1<<k)] for k in range(n))==2-starts[v]-ends[v]).only_enforce_if(x[v])
        for k in range(n):
            w=v^(1<<k)
            a=m.new_bool_var(f'a{v}_{w}')
            arcs.append((v,w,a))
            path_arcs[v,w]=a
    for (v,w),a in path_arcs.items():
        if v<w:m.add(a+path_arcs[w,v]>=x[v]+x[w]-1)
    m.add_circuit(arcs)
    m.add(sum(x)==edges+1)
    m.add(sum(x[v] for v in seed)>=len(seed)-removed)
    # Reversing the path preserves its vertex set and all neighborhood constraints.
    m.add(sum(v*starts[v] for v in range(size))<sum(v*ends[v] for v in range(size)))
    occupied=set(seed)
    for v in range(size):m.add_hint(x[v],int(v in occupied))
    return m,x,starts,path_arcs

def solve(n,edges,seed,removed,seconds):
    m,x,starts,arcs=model(n,edges,seed,removed)
    s=cp_model.CpSolver()
    s.parameters.max_time_in_seconds=seconds
    s.parameters.num_search_workers=4
    s.parameters.random_seed=13
    begin=time.monotonic();status=s.solve(m)
    report={'n':n,'target_edges':edges,'max_removed_seed_vertices':removed,
            'status':s.status_name(status),'elapsed_seconds':time.monotonic()-begin,
            'branches':s.num_branches,'conflicts':s.num_conflicts}
    if status in (cp_model.OPTIMAL,cp_model.FEASIBLE):
        vertices=[next(v for v,a in enumerate(starts) if s.value(a))]
        while True:
            nxt=[w for (v,w),a in arcs.items() if v==vertices[-1] and s.value(a)]
            if not nxt:break
            vertices.append(nxt[0])
        result=verify([(v^w).bit_length()-1 for v,w in zip(vertices,vertices[1:])],n)
        assert result['edges']==edges
        assert result['vertex_sequence']==[v^vertices[0] for v in vertices]
        assert len(set(seed)-set(vertices))<=removed
        report['witness']=vertices
        report['removed_vertices']=sorted(set(seed)-set(vertices))
        report['added_vertices']=sorted(set(vertices)-set(seed))
    return report

if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('--removed',type=int,default=8)
    ap.add_argument('--seconds',type=float,default=30)
    ap.add_argument('--count',type=int,default=3)
    args=ap.parse_args()
    bank=json.loads(Path('work/bank9.json').read_text())
    reports=[]
    for index,row in enumerate(bank[:args.count]):
        r=solve(9,192,row['vertex_sequence'],args.removed,args.seconds)
        r['seed_index']=index;reports.append(r)
        print(json.dumps(r),flush=True)
        Path(f'outputs/neighborhood_{args.removed}.json').write_text(json.dumps(reports,indent=2))
        if 'witness' in r:break
