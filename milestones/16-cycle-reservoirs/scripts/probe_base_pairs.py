"""Constructive feasibility probes for larger disjoint degree-two base sets."""
import argparse
import hashlib
import itertools
import json
from pathlib import Path
import sys

ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'work'))
from exact_search import cp_model


def run(args):
    n,size=args.n,args.size
    assert 2<=n<=8 and 4<=size<=1<<n and size%2==0
    m=cp_model.CpModel()
    xs=[[m.new_bool_var(f'x{b}_{v}')for v in range(1<<n)]for b in range(2)]
    for row in xs:
        m.add(sum(row)==size)
        for v in range(1<<n):
            m.add(sum(row[v^(1<<k)]for k in range(n))==2).only_enforce_if(row[v])
        for a,b in itertools.combinations(range(n),2):
            for v in range(1<<n):
                if v&((1<<a)|(1<<b))==0:
                    m.add(sum(row[w]for w in (v,v^(1<<a),v^(1<<b),v^(1<<a)^(1<<b)))<=3)
    for v in range(1<<n):m.add(xs[0][v]+xs[1][v]<=1)
    for v in (0,1,2):m.add(xs[0][v]==1)
    s=cp_model.CpSolver()
    s.parameters.max_time_in_seconds=args.seconds
    s.parameters.num_search_workers=2
    s.parameters.random_seed=196
    status=s.solve(m)
    result={'n':n,'size_per_set':size,'four_cycles_excluded':True,
        'status':s.status_name(status),'seconds':s.wall_time,
        'branches':s.num_branches,'conflicts':s.num_conflicts,
        'q9_product_vertices_if_feasible':(1<<(9-n))*size,
        'scope':'Constructive probe for a specified base family; no global Q9 bound.',
        'source_sha256_lf':hashlib.sha256(Path(__file__).read_bytes().replace(b'\r\n',b'\n')).hexdigest()}
    if status in (cp_model.OPTIMAL,cp_model.FEASIBLE):
        bases=[[v for v in range(1<<n)if s.value(row[v])]for row in xs]
        assert not set(bases[0])&set(bases[1])
        lengths=[]
        for vs in bases:
            assert len(vs)==size
            adj={v:{w for w in vs if (v^w).bit_count()==1}for v in vs}
            assert all(len(adj[v])==2 for v in vs)
            unseen=set(vs);sizes=[]
            while unseen:
                part=set();todo=[min(unseen)]
                while todo:
                    v=todo.pop()
                    if v in part:continue
                    part.add(v);todo.extend(adj[v])
                unseen-=part;sizes.append(len(part))
            assert all(c>=6 and c%2==0 for c in sizes)
            lengths.append(sizes)
        result.update(base_sets=bases,component_sizes=lengths)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({k:v for k,v in result.items()if k not in ('base_sets','source_sha256_lf')}),flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--n',type=int,required=True)
    p.add_argument('--size',type=int,required=True)
    p.add_argument('--seconds',type=float,default=60)
    p.add_argument('--output',type=Path,required=True)
    run(p.parse_args())
