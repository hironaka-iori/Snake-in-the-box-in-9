import sys,json,time,argparse
from pathlib import Path
sys.path.insert(0,str(Path('work/solver_packages').resolve()))
from ortools.sat.python import cp_model

def solve(weight,seconds,target=97):
    h=(1<<weight)-1
    generators=[1<<i for i in range(8)]+[h]
    assert weight in [2,4,6,8]
    m=cp_model.CpModel()
    x=[m.new_bool_var(f'x{v}') for v in range(256)]
    arcs=[(v,v,x[v].Not()) for v in range(256)]
    av={}
    by_gen=[[] for _ in generators]
    for u in range(256):
        for k,g in enumerate(generators):
            v=u^g
            if u<v:
                a=m.new_bool_var(f'a{u}_{v}'); b=m.new_bool_var(f'a{v}_{u}')
                arcs.extend([(u,v,a),(v,u,b)])
                av[u,v]=a;av[v,u]=b
                m.add(a+b>=x[u]+x[v]-1)
                by_gen[k].extend([a,b])
        m.add(sum(x[u^g] for g in generators)==2).only_enforce_if(x[u])
    m.add_circuit(arcs)
    m.add(sum(x)==target)
    m.add(x[0]==1)
    for k in range(9):
        parity=1 if k==8 or k<weight else 0
        z=m.new_int_var(0,target//2,f'z{k}')
        m.add(sum(by_gen[k])==2*z+parity)
    solver=cp_model.CpSolver()
    solver.parameters.max_time_in_seconds=seconds
    solver.parameters.num_search_workers=4
    solver.parameters.random_seed=13
    status=solver.solve(m)
    out={'extra_generator_weight':weight,'target_quotient_cycle_vertices':target,
         'target_lifted_cycle_vertices':2*target,'status':solver.status_name(status),
         'seconds':solver.wall_time,'branches':solver.num_branches,'conflicts':solver.num_conflicts}
    if status in [cp_model.OPTIMAL,cp_model.FEASIBLE]:
        path=[0]
        while True:
            v=next(v for (u,v),a in av.items() if u==path[-1] and solver.value(a))
            if v==0:break
            path.append(v)
        assert len(path)==target
        lift=[0]
        for _ in range(2):
            for u,v in zip(path,path[1:]+[0]):
                g=u^v
                bit=8 if g==h else g.bit_length()-1
                lift.append(lift[-1]^(1<<bit))
        assert lift[-1]==0
        lift.pop()
        assert len(set(lift))==2*target
        for i,u in enumerate(lift):
            for j in range(i+1,len(lift)):
                assert ((u^lift[j]).bit_count()==1)==(j==i+1 or (i==0 and j==len(lift)-1))
        out['quotient_cycle']=path
        out['lifted_cycle']=lift
    return out

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--seconds',type=float,default=60)
    ap.add_argument('--weight',type=int,required=True);ap.add_argument('--target',type=int,default=97)
    args=ap.parse_args()
    r=solve(args.weight,args.seconds,args.target)
    Path(f'outputs/folded_coil_w{args.weight}_n{args.target}.json').write_text(json.dumps(r,indent=2),encoding='utf-8')
    print(json.dumps(r,indent=2),flush=True)
