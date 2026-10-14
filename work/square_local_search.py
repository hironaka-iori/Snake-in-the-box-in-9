"""Test the single-vertex square condition on actual open induced paths."""
import json,time,argparse
from itertools import combinations
from pathlib import Path
from exact_search import cp_model

def run(n,alpha_limit,seconds,connected=True,endpoint_distance=0):
    size=1<<n
    m=cp_model.CpModel()
    x=[m.new_bool_var(f'x{v}') for v in range(size)]
    starts=[m.new_bool_var(f's{v}') for v in range(size)]
    ends=[m.new_bool_var(f'e{v}') for v in range(size)]
    arcs=[(v,v,x[v].Not()) for v in range(size)]
    edge_arcs={}
    for v in range(size):
        m.add(starts[v]+ends[v]<=x[v])
        m.add(sum(x[v^(1<<k)] for k in range(n))==2-starts[v]-ends[v]).only_enforce_if(x[v])
        arcs.extend([(size,v,starts[v]),(v,size,ends[v])])
        if connected:
            for k in range(n):
                w=v^(1<<k)
                a=m.new_bool_var(f'a{v}_{w}')
                edge_arcs[v,w]=a;arcs.append((v,w,a))
    m.add(sum(starts)==1);m.add(sum(ends)==1)
    for v in range(size):
        if v.bit_count()<endpoint_distance:m.add(starts[v]+ends[v]==0)
    if connected:
        for (v,w),a in edge_arcs.items():
            if v<w:m.add(a+edge_arcs[w,v]>=x[v]+x[w]-1)
        m.add_circuit(arcs)
    else:
        # Necessary for a linear forest; longer cycle components are still allowed.
        for a,b in combinations(range(n),2):
            for v in range(size):
                if not v & ((1<<a)|(1<<b)):
                    m.add(x[v]+x[v^(1<<a)]+x[v^(1<<b)]+x[v^(1<<a)^(1<<b)]<=3)
    for v in [0,1,2]:m.add(x[v]==1)
    m.add(starts[0]+ends[0]==0)
    # The selected neighbors of 0 are exactly 1 and 2. Every other square
    # through 0 is a singleton precisely when its opposite vertex is absent.
    pairs=[(1<<a)|(1<<b) for a,b in combinations(range(2,n),2)]
    if alpha_limit<=1:
        # Coordinate permutations fixing 0,1,2 put the optional missing pair at 12.
        for v in pairs:
            if v!=12 or alpha_limit==0:m.add(x[v]==1)
    else:m.add(sum(x[v] for v in pairs)>=len(pairs)-alpha_limit)
    m.add(sum(v*starts[v] for v in range(size))<sum(v*ends[v] for v in range(size)))
    s=cp_model.CpSolver();s.parameters.num_search_workers=4
    s.parameters.max_time_in_seconds=seconds;s.parameters.random_seed=29
    t=time.monotonic();status=s.solve(m)
    r={'dimension':n,'alpha_limit':alpha_limit,'connected_path':connected,'minimum_endpoint_distance':endpoint_distance,
       'status':s.status_name(status),'seconds':time.monotonic()-t,
       'branches':s.num_branches,'conflicts':s.num_conflicts}
    if status in [cp_model.OPTIMAL,cp_model.FEASIBLE]:
        r['selected_vertices']=[v for v in range(size) if s.value(x[v])]
        r['alpha_at_zero']=len(pairs)-sum(s.value(x[v]) for v in pairs)
        r['endpoints']=[v for v in range(size) if s.value(starts[v])+s.value(ends[v])]
        if connected:
            vertices=[next(v for v in range(size) if s.value(starts[v]))]
            while True:
                nxt=[w for k in range(n) if s.value(edge_arcs[vertices[-1],w:=vertices[-1]^(1<<k)])]
                if not nxt:break
                vertices.append(nxt[0])
            assert len(vertices)==len(r['selected_vertices'])
            assert len(set(vertices))==len(vertices)
            assert all(((v^w).bit_count()==1)==(j==i+1) for i,v in enumerate(vertices) for j,w in enumerate(vertices) if i<j)
            r['path']=vertices;r['edges']=len(vertices)-1
    return r

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--n',type=int,default=9)
    ap.add_argument('--alpha',type=int,default=1);ap.add_argument('--seconds',type=float,default=30)
    ap.add_argument('--endpoint-distance',type=int,default=0)
    ap.add_argument('--relaxed',action='store_true');args=ap.parse_args()
    r=run(args.n,args.alpha,args.seconds,not args.relaxed,args.endpoint_distance)
    suffix=f'_d{args.endpoint_distance}' if args.endpoint_distance else ''
    path=Path(f'outputs/square_local_n{args.n}_a{args.alpha}_{"relaxed" if args.relaxed else "path"}{suffix}.json')
    path.write_text(json.dumps(r,indent=2));print(json.dumps(r),flush=True)
