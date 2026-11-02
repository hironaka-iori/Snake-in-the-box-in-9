"""One bounded cap31 probe for shape012034; no claim about complete snakes."""
from pathlib import Path
from itertools import combinations
import hashlib,json,sys,time
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[2]
sys.path.insert(0,str(ROOT/'milestones/28-direct-share-certificates/scripts'))
from tagged_share import TaggedShare,Cadical153
import tagged_share,gen_lean_sat,wincert,pysat
DS=[0,1,2,0,3,4];CAP=31;SECONDS=60.0
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
save=lambda name,obj:(HERE/name).write_text(json.dumps(obj,indent=2)+'\n',encoding='utf-8')

def independent_census(selected):
    S=set(selected);assert len(S)==len(selected)
    path=[0]
    for direction in DS:path.append(path[-1]^(1<<direction))
    assert len(path)==len(set(path)) and set(path)<=S
    assert all(((x^y).bit_count()==1)==(j==i+1) for i,x in enumerate(path) for j,y in enumerate(path) if i<j)
    centres=path[1:-1]
    B={v for v in range(512) if min((v^c).bit_count() for c in centres)<=4}
    assert S<=B
    neighbours=lambda v:{v^(1<<a) for a in range(9)}
    degree={v:len(neighbours(v)&S) for v in range(512)}
    assert all(degree[v]<=2 for v in S)
    interior={v for v in S if neighbours(v)<=B}
    assert all(degree[v]>=1 for v in interior)
    ends=sorted(v for v in interior if degree[v]==1);assert len(ends)<=2
    unseen=set(S);components=[];cycles=[]
    while unseen:
        stack=[min(unseen)];vertices=set()
        while stack:
            v=stack.pop()
            if v not in unseen:continue
            unseen.remove(v);vertices.add(v);stack.extend(neighbours(v)&unseen)
        edges=sum(degree[v] for v in vertices)//2
        assert edges in (len(vertices)-1,len(vertices))
        components.append(dict(vertices=sorted(vertices),edges=edges))
        if edges==len(vertices):cycles.append(sorted(vertices))
    pairs=list(combinations(range(9),2))
    empty={q:sum(not(S&{q,q^(1<<a),q^(1<<b),q^(1<<a)^(1<<b)}) for a,b in pairs) for q in range(512)}
    singleton=[sum(not(S&{c^(1<<a),c^(1<<b),c^(1<<a)^(1<<b)}) for a,b in pairs) for c in centres]
    assert all(0<=x<=21 for x in singleton)
    shares=[];contributions=[]
    for c in centres:
        terms=[]
        for q in sorted(neighbours(c)):
            assert degree[q]>=1
            terms.append(dict(vertex=q,selected_neighbours=degree[q],empty_squares=empty[q],integer_share=12*empty[q]//degree[q]))
        shares.append(sum(x['integer_share'] for x in terms));contributions.append(terms)
    assert sum(shares)<=CAP
    return dict(path=path,centres=centres,ball_vertices=len(B),selected_vertices=len(S),singleton_counts=singleton,centre_shares=shares,total_share=sum(shares),interior_endpoints=ends,components=components,cycles=cycles,share_contributions=contributions)

def main():
    build_start=time.monotonic();enc=TaggedShare(DS,[(0,21)]*5,CAP)
    base_count=len(enc.clauses)
    cnf=('p cnf %d %d\n'%(enc.nv,base_count)+''.join(' '.join(map(str,c))+' 0\n' for c in enc.clauses)).encode()
    out=dict(shape=DS,proposed_floor=32,test_cap=CAP,bounds=[[0,21]]*5,dimension=9,radius=4,scale=12,requested_solver_seconds=SECONDS,variables=enc.nv,base_clauses=base_count,base_cnf_sha256=hashlib.sha256(cnf).hexdigest(),encoding_seconds=time.monotonic()-build_start,status='UNKNOWN',source_hashes={str(Path(m.__file__).relative_to(ROOT)):sha(Path(m.__file__)) for m in [tagged_share,gen_lean_sat,wincert]},probe_source_sha256=sha(Path(__file__)),pysat_version=pysat.__version__,cycle_cuts=[],candidate_censuses=[],scope='Bounded local forest search only. A local forest need not extend to a complete snake. Numerical UNSAT or UNKNOWN is unproved. No Lean replay or native certificate is attempted.')
    print('encoded',out['variables'],out['base_clauses'],flush=True)
    start=time.monotonic();iterations=0;seen=set()
    with Cadical153(bootstrap_with=enc.clauses) as solver:
        while time.monotonic()-start<SECONDS:
            solver.conf_budget(1000);ok=solver.solve_limited();iterations+=1
            if ok is None:continue
            if ok is False:
                out['status']='NUMERICAL_UNSAT_UNPROVED';break
            model=solver.get_model();positive={lit for lit in model if lit>0}
            assert all(any((lit in positive) if lit>0 else (-lit not in positive) for lit in clause) for clause in enc.clauses)
            selected=sorted(v for v in enc.ball if enc.var[v] in positive)
            census=independent_census(selected)
            out['candidate_censuses'].append(dict(total_share=census['total_share'],cycle_lengths=[len(c) for c in census['cycles']],selected_vertices=len(selected)))
            if not census['cycles']:
                out.update(status='SAT_INDEPENDENTLY_CHECKED_LOCAL_FOREST',selected=selected,census=census);break
            for cycle in census['cycles']:
                key=tuple(cycle);assert key not in seen;seen.add(key)
                clause=[-enc.var[v] for v in cycle];enc.add(clause,('old',('cut',)));solver.add_clause(clause);out['cycle_cuts'].append(cycle)
        out['solver_stats']=solver.accum_stats()
    out.update(elapsed_solver_seconds=time.monotonic()-start,limited_solve_calls=iterations,final_clauses=len(enc.clauses))
    save('result.json',out)
    print(json.dumps({k:out[k] for k in ['status','elapsed_solver_seconds','limited_solve_calls','candidate_censuses']}),flush=True)
if __name__=='__main__':main()
