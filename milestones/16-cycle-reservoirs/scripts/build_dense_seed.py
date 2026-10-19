"""Replace chosen cells of the 224-vertex cycle product by one induced path."""
import argparse
import hashlib
import json
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'work'))
sys.path.insert(0,str(ROOT/'milestones/14-component-construction/scripts'))
from neighborhood_search import model
from exact_search import cp_model
from check_snake import verify
from component_search import components


def run(args):
    source=ROOT/'milestones/16-cycle-reservoirs/data/base5-size14.json'
    bases=json.loads(source.read_text())['base_sets']
    cells=[[(h<<5)|v for v in bases[h.bit_count()%2]]for h in range(16)]
    product={v for c in cells for v in c}
    parts,adj=components(product,9)
    assert len(product)==224 and len(parts)==16 and all(len(c)==14 for c in parts)
    assert all(len(adj[v])==2 for v in product)
    release={int(i)for i in args.layers.split(',')}
    frozen={v for h,c in enumerate(cells)if h not in release for v in c}
    forbidden=frozen|{v^(1<<k)for v in frozen for k in range(9)}
    target=196-len(frozen)
    hint=sorted(product-frozen)
    m,x,starts,arcs=model(9,target,hint,len(hint))
    for v in forbidden:m.add(x[v]==0)
    s=cp_model.CpSolver()
    s.parameters.max_time_in_seconds=args.seconds
    s.parameters.num_search_workers=2
    s.parameters.random_seed=196
    status=s.solve(m)
    out={'base_source':source.relative_to(ROOT).as_posix(),
        'base_source_sha256_lf':hashlib.sha256(source.read_bytes().replace(b'\r\n',b'\n')).hexdigest(),
        'released_layers':sorted(release),'frozen_vertices':sorted(frozen),
        'target_path_edges':target,'allowed_vertices':512-len(forbidden),
        'status':s.status_name(status),'seconds':s.wall_time,'branches':s.num_branches,'conflicts':s.num_conflicts,
        'scope':'Restricted cell replacement; a feasible result may still contain frozen cyclic components.'}
    if status in (cp_model.OPTIMAL,cp_model.FEASIBLE):
        path=[next(v for v,a in enumerate(starts)if s.value(a))]
        while True:
            following=[w for (v,w),a in arcs.items()if v==path[-1]and s.value(a)]
            if not following:break
            assert len(following)==1 and following[0]not in path
            path.append(following[0])
        checked=verify([(a^b).bit_length()-1 for a,b in zip(path,path[1:])],9)
        assert checked['edges']==target and checked['vertex_sequence']==[v^path[0]for v in path]
        assert not set(path)&forbidden
        selected=set(path)|frozen
        cs,a=components(selected,9)
        assert len(selected)==197 and len(cs)==17-len(release)
        out.update(seed_vertices=sorted(selected),components=cs,path_vertices=path,cuts_to_retain=[],
                   pairs_checked=checked['pairs_checked'])
    out['script_sha256_lf']=hashlib.sha256(Path(__file__).read_bytes().replace(b'\r\n',b'\n')).hexdigest()
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({k:out[k]for k in ('status','target_path_edges','allowed_vertices','seconds')}),flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--layers',required=True)
    p.add_argument('--seconds',type=float,default=30)
    p.add_argument('--output',type=Path,required=True)
    run(p.parse_args())
