"""Find 190-edge mixed parents, then test any new seed at target 196."""
import json,sys
from pathlib import Path
from exchange import ROOT,HERE,parents,transforms,check,sha
sys.path.insert(0,str(ROOT/'work'))
from neighborhood_search import model
from exact_search import cp_model
def search(a,b,seconds):
    aa=set(a);bb=set(b);allowed=aa|bb
    m,x,starts,arcs=model(9,190,b,len(b))
    for v in range(512):
        if v not in allowed:m.add(x[v]==0)
    m.add(starts[41]==1);m.add(x[67]==1)
    m.add(sum(t for (v,w),t in arcs.items() if v==67)==0)
    z=m.new_int_var(0,95,'balanced_exclusive_vertices')
    m.add(z<=sum(x[v] for v in aa-bb));m.add(z<=sum(x[v] for v in bb-aa));m.maximize(z)
    used=set(zip(b,b[1:]))
    for v,t in enumerate(starts):m.add_hint(t,int(v==41))
    for e,t in arcs.items():m.add_hint(t,int(e in used))
    s=cp_model.CpSolver();s.parameters.max_time_in_seconds=seconds;s.parameters.num_search_workers=2;s.parameters.random_seed=196
    status=s.solve(m)
    row={'status':s.status_name(status),'seconds':s.wall_time,'limit_seconds':seconds,'workers':2,'random_seed':196,'objective_bound':s.best_objective_bound}
    if status in (cp_model.FEASIBLE,cp_model.OPTIMAL):
        p=[41]
        while p[-1]!=67:
            nxt=[w for (v,w),t in arcs.items() if v==p[-1] and s.value(t)]
            assert len(nxt)==1 and nxt[0] not in p;p+=nxt
        check(p);assert len(p)==191 and set(p)<=allowed
        row.update(path_vertices=p,objective=s.objective_value,from_a_only=len(set(p)&(aa-bb)),from_b_only=len(set(p)&(bb-aa)),shared_deleted=len((aa&bb)-set(p)))
    return row
def main():
    a,b=parents();selected=[243,1201,5136];qs={i:q for i,(_,_,q) in enumerate(transforms(b)) if i in selected}
    data={'script_sha256_lf':sha(Path(__file__)),'runs':[]}
    for i in selected:
        r=search(a,qs[i],30);r['alignment']=i;data['runs'].append(r)
        (HERE/'data/diversity.json').write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8')
        print(json.dumps({k:v for k,v in r.items() if k!='path_vertices'}),flush=True)
if __name__=='__main__':main()
