"""Joint two-layer search; neither projected snake is fixed to a published seed."""
import argparse,json,time
from pathlib import Path
from exact_search import cp_model
from check_snake import verify


def layer(model,n,edges,label):
    size=1<<n
    x=[model.new_bool_var(f'{label}_x{v}') for v in range(size)]
    model.add(x[0]==1)
    model.add(sum(x)==edges+1)
    arcs=[(v,v,x[v].Not()) for v in range(size)]
    root=model.new_bool_var(f'{label}_root')
    model.add(root==1)
    arcs.append((size,0,root))
    directed={}
    for u in range(size):
        for k in range(n):
            v=u^(1<<k)
            if u<v:
                uv=model.new_bool_var(f'{label}_{u}_{v}')
                vu=model.new_bool_var(f'{label}_{v}_{u}')
                directed[u,v]=uv;directed[v,u]=vu
                arcs.extend([(u,v,uv),(v,u,vu)])
                model.add(uv+vu>=x[u]+x[v]-1)
                model.add(uv+vu<=1)
    ends=[]
    for v in range(1,size):
        end=model.new_bool_var(f'{label}_end{v}')
        ends.append(end);arcs.append((v,size,end))
        model.add(end<=x[v])
        model.add(sum(x[v^(1<<k)] for k in range(n))==2-end).only_enforce_if(x[v])
    model.add(sum(ends)==1)
    model.add(sum(x[1<<k] for k in range(n))==1)
    model.add_circuit(arcs)
    return x,directed


def make_model(n,left,right,symmetry=True):
    assert n>=2 and left>=1 and right>=1
    model=cp_model.CpModel()
    a,aa=layer(model,n,left,'a')
    b,bb=layer(model,n,right,'b')
    for v in range(1,1<<n):
        model.add(a[v]+b[v]<=1)
    if symmetry:
        # The first coordinate directions differ because the only common vertex is 0.
        # One common coordinate permutation can therefore map them to 0 and 1.
        model.add(aa[0,1]==1)
        model.add(bb[0,2]==1)
    return model,(a,aa),(b,bb)


def decode(solver,arcs):
    path=[0]
    while True:
        nxt=[v for (u,v),arc in arcs.items() if u==path[-1] and solver.value(arc)]
        if not nxt: return path
        assert len(nxt)==1 and nxt[0] not in path
        path.append(nxt[0])


def solve(n,left,right,seconds,seed=13,workers=4,symmetry=True,hint=None,fixed=False):
    if fixed and hint is None:
        raise ValueError("Fixing vertex sets requires an explicit hint.")
    model,(xa,aa),(xb,bb)=make_model(n,left,right,symmetry)
    if hint is not None:
        for xs,arcs,path in [(xa,aa,hint['left_path']),(xb,bb,hint['right_path'])]:
            occupied=set(path);steps=set(zip(path,path[1:]))
            for v,x in enumerate(xs):
                model.add_hint(x,int(v in occupied))
                if fixed: model.add(x==int(v in occupied))
            for edge,arc in arcs.items(): model.add_hint(arc,int(edge in steps))
    solver=cp_model.CpSolver()
    solver.parameters.max_time_in_seconds=seconds
    solver.parameters.num_search_workers=workers
    solver.parameters.random_seed=seed
    start=time.monotonic();status=solver.solve(model)
    report={'base_dimension':n,'joined_dimension':n+1,'left_edges':left,'right_edges':right,
            'joined_target_edges':left+right+1,'status':solver.status_name(status),
            'elapsed_seconds':time.monotonic()-start,'time_limit_seconds':seconds,
            'random_seed':seed,'workers':workers,'coordinate_symmetry':symmetry,
            'hint_bank_seed':hint.get('bank_seed_index') if hint else None,'fixed_to_hint':fixed,
            'branches':solver.num_branches,'conflicts':solver.num_conflicts,
            'scope':('Both vertex sets fixed to the hint; one joining edge.' if fixed else
                     'Both projected paths variable; one joining edge; intersection exactly the common endpoint 0.'),
            'certificate_status':'Solver model and infeasibility results are not Lean-certified.'}
    if status in (cp_model.OPTIMAL,cp_model.FEASIBLE):
        a,b=decode(solver,aa),decode(solver,bb)
        assert len(a)==left+1 and len(b)==right+1 and set(a)&set(b)=={0}
        for path,length in [(a,left),(b,right)]:
            result=verify([(u^v).bit_length()-1 for u,v in zip(path,path[1:])],n)
            assert result['edges']==length and result['vertex_sequence']==path
        joined=list(reversed(a))+[v+(1<<n) for v in b]
        actions=[(u^v).bit_length()-1 for u,v in zip(joined,joined[1:])]
        result=verify(actions,n+1)
        assert result['edges']==left+right+1
        assert result['vertex_sequence']==[v^joined[0] for v in joined]
        report.update({'left_path':a,'right_path':b,'joined_witness':result})
    return report


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--n',type=int,default=8)
    parser.add_argument('--left',type=int,default=98)
    parser.add_argument('--right',type=int,default=97)
    parser.add_argument('--seconds',type=float,default=120)
    parser.add_argument('--seed',type=int,default=13)
    parser.add_argument('--workers',type=int,default=4)
    parser.add_argument('--no-symmetry',action='store_true')
    parser.add_argument('--hint',type=Path)
    parser.add_argument('--fixed-to-hint',action='store_true')
    parser.add_argument('--output',required=True)
    args=parser.parse_args()
    result=solve(args.n,args.left,args.right,args.seconds,args.seed,args.workers,not args.no_symmetry,
                 json.loads(args.hint.read_text(encoding='utf-8')) if args.hint else None,args.fixed_to_hint)
    Path(args.output).write_text(json.dumps(result,indent=2),encoding='utf-8')
    print(json.dumps({k:v for k,v in result.items() if k not in ['left_path','right_path','joined_witness']},indent=2))
