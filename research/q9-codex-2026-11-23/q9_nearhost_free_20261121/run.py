from pathlib import Path
import argparse,json,random,sys
from collections import Counter
from prepare import D,R,CUBE,NB,components,unhex,paircheck
sys.path.insert(0,str(R))
from retry_q9_six_cube_sites_cadical import search as cd
from search_q9_anchored_sets import search as mc
def solve(solver,fixed,host,target,budget):
    if solver=='cadical':return cd(fixed,host,target,budget,CUBE)
    return mc(fixed,host,target,budget,allowed=CUBE,at_least=True)
def control(solver):
    c=json.loads((R/'q8_catalogue_lifts_verified.json').read_text())['lower_certificate']
    p=c['vertices'];paircheck(p);assert len(p)==192
    host=set(c['layers'][0]['placed_vertices'])|{v+256 for v in c['layers'][1]['placed_vertices']}
    assert set(p)<=host
    # Hold actual fragments from a real embedded 191-edge witness.
    fixed=set(p);rng=random.Random(11497)
    while len(fixed)>161:
        j=rng.randrange(190)
        for v in p[j:j+5]:
            if len(fixed)==161:break
            fixed.discard(v)
    st,w=solve(solver,fixed,host,191,25000)
    assert st=='FOUND' and len(w)>=192 and fixed<=set(w);paircheck(w)
    # Dropping enough vertices from the phase hint guarantees any 191 solution
    # must recover at least one vertex outside that smaller hint.
    damaged=set(host)
    while len(damaged)>182:damaged.remove(rng.choice(sorted(damaged-fixed)))
    st2,w2=solve(solver,fixed,damaged,191,25000)
    assert st2=='FOUND' and set(w2)-damaged and fixed<=set(w2);paircheck(w2)
    return dict(edges=len(w)-1,anchors=len(fixed),host_size=len(host),damaged_hint_size=len(damaged),outside_damaged_hint=len(set(w2)-damaged),witness=w,damaged_witness=w2)
def run():
    ap=argparse.ArgumentParser();ap.add_argument('solver');ap.add_argument('budget',type=int);ap.add_argument('--prior',type=Path);ap.add_argument('--cases',default='cases.jsonl');args=ap.parse_args()
    print(json.dumps(dict(control=control(args.solver))),flush=True)
    selected=None
    if args.prior:selected={d['row'] for l in args.prior.open() if (d:=json.loads(l)).get('status')=='UNKNOWN'}
    counts=Counter()
    for i,l in enumerate((D/args.cases).open()):
        if selected is not None and i not in selected:continue
        c=json.loads(l);fixed=unhex(c['fixed']);host=unhex(c['host'])
        st,w=solve(args.solver,fixed,host,192,args.budget);counts[st]+=1
        if w: assert len(w)>=193 and fixed<=set(w);paircheck(w)
        print(json.dumps(dict(row=i,status=st,witness=w),separators=(',',':')),flush=True)
        if w:break
    print(json.dumps(dict(counts=counts)),flush=True)
if __name__=='__main__':run()
