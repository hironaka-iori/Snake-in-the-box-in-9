"""Allow arbitrary path ordering within the union of two aligned parents."""
import argparse,json,sys,time
from pathlib import Path
from exchange import ROOT,HERE,parents,transforms,check,sha
sys.path.insert(0,str(ROOT/'work'))
from neighborhood_search import model
from exact_search import cp_model
def solve(a,b,edges,common,seconds):
    allowed=set(a)|set(b);shared=set(a)&set(b)
    m,x,starts,arcs=model(9,edges,b,len(b))
    for v in range(512):
        if v not in allowed:m.add(x[v]==0)
        elif common and v in shared:m.add(x[v]==1)
    m.add(starts[41]==1);m.add(x[67]==1)
    m.add(sum(t for (v,w),t in arcs.items() if v==67)==0)
    seed=a if edges==186 else b;used=set(zip(seed,seed[1:]))
    for v,t in enumerate(starts):m.add_hint(t,int(v==41))
    for edge,t in arcs.items():m.add_hint(t,int(edge in used))
    s=cp_model.CpSolver();s.parameters.max_time_in_seconds=seconds
    s.parameters.num_search_workers=2;s.parameters.random_seed=196
    status=s.solve(m)
    row={'edges':edges,'retain_intersection':common,'union_size':len(allowed),'intersection_size':len(shared),'status':s.status_name(status),'seconds':s.wall_time,'limit_seconds':seconds,'workers':2,'random_seed':196,'branches':s.num_branches,'conflicts':s.num_conflicts}
    if status in (cp_model.FEASIBLE,cp_model.OPTIMAL):
        p=[41]
        while p[-1]!=67:
            nxt=[w for (v,w),t in arcs.items() if v==p[-1] and s.value(t)]
            assert len(nxt)==1 and nxt[0] not in p;p+=nxt
        check(p);assert len(p)==edges+1 and set(p)<=allowed
        assert not common or shared<=set(p)
        row['path_vertices']=p
    return row
def main(args):
    a,b=parents();survey=json.loads((HERE/'data/exchanges.json').read_text())
    ranked=sorted(survey['alignments'],key=lambda r:(-r['overlap'],r['index']))
    selected=sorted(set([r['index'] for r in ranked[:6]]+[ranked[i*(len(ranked)-1)//6]['index'] for i in range(1,7)]))
    choices={i:q for i,(_,_,q) in enumerate(transforms(b)) if i in selected}
    data={'script_sha256_lf':sha(Path(__file__)),'exchange_sha256_lf':sha(HERE/'scripts/exchange.py'),'model_sha256_lf':sha(ROOT/'work/neighborhood_search.py'),'selected_alignments':selected,'controls':[],'runs':[],'scope':'Fixed endpoints 41 and 67; arbitrary induced paths inside the selected parent union. Solver exclusions are restricted and not Lean certified.'}
    out=HERE/'data/union-search.json'
    for edges,p in ((186,a),(190,b)):
        row=solve(p,p,edges,True,10);assert row['status']=='OPTIMAL';data['controls'].append(row)
    for i in selected:
        for edges,common in ((196,True),(196,False),(192,False)):
            row=solve(a,choices[i],edges,common,args.seconds);row['alignment']=i;data['runs'].append(row)
            out.write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8')
            print(json.dumps({k:v for k,v in row.items() if k!='path_vertices'}),flush=True)
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--seconds',type=float,default=6);main(ap.parse_args())
