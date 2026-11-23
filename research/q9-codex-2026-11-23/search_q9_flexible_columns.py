"""Leave the occupancy of a Q8 subcube free and search both Q9 layers in all orders."""
import argparse
import gzip
import json
import random
from itertools import combinations
from pathlib import Path
from pysat.solvers import Minicard
from search_q9_unordered_projection import project
from verify_q9_center_avoidance import verify

def complete(hint, original, patch, goal, budget, changes=2, frozen_states=(), fixed_col_parity=None,reject=None,propagate=False):
    forced = original - patch
    domain = forced | patch
    adj = {v: {v ^ (1 << d) for d in range(8)} & domain for v in domain}
    doubles = {v for v in domain if len(adj[v] & forced) <= 2}
    gain = goal + 1 - len(forced)
    if gain > len(patch) + len(doubles):
        return "SIZE", None
    with Minicard() as s:
        def lower(lits, n):
            if n > len(lits):
                s.add_clause([])
            elif n > 0:
                s.add_atmost([-t for t in lits], len(lits)-n)
        for v in sorted(domain):
            a,b,t,o=v+1,v+257,v+513,v+769
            if v in forced:
                s.add_clause([a,b])
            else:
                s.add_clause([-a,o]);s.add_clause([-b,o]);s.add_clause([-o,a,b])
            if v in doubles:
                s.add_clause([-t,a]);s.add_clause([-t,b]);s.add_clause([-a,-b,t])
                for w in adj[v] & doubles:
                    if v<w:s.add_clause([-t,-w-513])
            else:
                s.add_clause([-a,-b])
        if propagate:
            even=[v+769 for v in patch if v.bit_count()%2==0]
            odd=[-v-769 for v in patch if v.bit_count()%2==1]
            imbalance=sum(1 if v.bit_count()%2==0 else -1 for v in forced)
            hi=len(odd)-imbalance+1
            if hi<0:s.add_clause([])
            elif hi<len(patch):s.add_atmost(even+odd,hi)
            lower(even+odd,len(odd)-imbalance-1)
            for v in doubles:
                fixed_degree=len(adj[v]&forced)
                for group in combinations(adj[v]&patch,3-fixed_degree):
                    s.add_clause([-v-513,*[-z-769 for z in group]])
            for v in sorted(domain):
                for a,b in combinations((w for w in adj[v] if w>v),2):
                    z=v^a^b
                    if z<=v or z not in domain:continue
                    for height in (0,256):
                        s.add_clause([-(x+height+1) for x in (v,a,b,z)])
        for v in frozen_states:
            for x in (v,v+256):s.add_clause([x+1 if x in hint else -x-1])
        if fixed_col_parity is not None:
            assert all(v.bit_count()%2==fixed_col_parity for v in forced)
            assert all(v.bit_count()%2!=fixed_col_parity for v in patch)
            occupancies=[v+769 for v in patch]
            lower(occupancies,len(forced)-1)
            s.add_atmost(occupancies,len(forced)+1)
        lower([v+513 for v in doubles]+[v+769 for v in patch],gain)
        lower([-(v+769) if v in original else v+769 for v in patch],changes)
        fixed_single=forced-doubles
        if fixed_single and not frozen_states:
            v=min(fixed_single);s.add_clause([v+1 if v in hint else v+257])
        ends=[]
        vertices=domain|{v+256 for v in domain}
        for x in vertices:
            a=x+1;e=x+1025;ends.append(e)
            neighbors=[(v^(x&256))+1 for v in adj[x%256]]+[(x^256)+1]
            s.add_clause([-e,a]);s.add_clause([-a,*neighbors])
            for u,v in combinations(neighbors,2):s.add_clause([-e,-u,-v])
            for u,v,w in combinations(neighbors,3):s.add_clause([-a,-u,-v,-w])
            for j in range(len(neighbors)):s.add_clause([-a,e,*neighbors[:j],*neighbors[j+1:]])
        s.add_atmost(ends,2);lower(ends,2)
        s.set_phases([x+1 if x in hint else -x-1 for x in vertices])
        while True:
            left=budget-s.accum_stats()['conflicts']
            if left<=0:return 'UNKNOWN',None
            s.conf_budget(left);ok=s.solve_limited()
            if ok is not True:return ('UNKNOWN' if ok is None else 'UNSAT'),None
            model=set(s.get_model());chosen={x for x in vertices if x+1 in model}
            nb=lambda x:{x^(1<<d) for d in range(9)}&chosen
            p=[next(x for x in chosen if len(nb(x))==1)]
            rest=chosen-set(p)
            while ns:=rest&nb(p[-1]):
                assert len(ns)==1
                v=ns.pop();p.append(v);rest.remove(v)
            if not rest:
                verify(p);S={v%256 for v in p}
                assert S-patch==forced and len(S^original)>=changes and len(p)>goal
                if reject and reject(p):
                    s.add_clause([-(x+1) if x in chosen else x+1 for x in vertices]);continue
                return 'FOUND',p
            while rest:
                comp=[rest.pop()]
                for x in comp:
                    new=rest&nb(x);comp.extend(new);rest-=new
                s.add_clause([-v-1 for v in comp])

def face(mask,base):
    free=[0]
    for d in range(8):
        if mask>>d&1:free += [v^(1<<d) for v in free]
    return {base^u for u in free}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('dim',type=int);ap.add_argument('jobs',type=int);ap.add_argument('budget',type=int)
    ap.add_argument('--retry');ap.add_argument('--propagate',action='store_true');ap.add_argument('--source',default='q9_port_followup_public191.txt.gz');a=ap.parse_args()
    reader=gzip.open if a.source.endswith('.gz') else open
    with reader(a.source,'rt') as f: bank=[list(map(int,r.split())) for r in f]
    ctrl=json.loads(Path('q9_explicit_q8_96_plus_94.json').read_text())['vertices']
    h=project(ctrl,8);S={x%256 for x in h};patch=face(15,0);damaged=S^set(sorted(patch)[:3])
    state,w=complete(h,damaged,patch,191,25000,3);assert state=='FOUND';print(json.dumps(['control',state,w]),flush=True)
    rng=random.Random(19286+a.dim);seen=set()
    if a.retry:
        jobs=(r[:4] for r in map(json.loads,open(a.retry)) if r[0]!='control' and r[4]=='UNKNOWN')
    else:
        def gen():
            while True:
                i=rng.randrange(len(bank));axis=rng.randrange(9);mask=sum(1<<d for d in rng.sample(range(8),a.dim))
                yield i,axis,mask,rng.randrange(256)&~mask
        jobs=gen()
    for i,axis,mask,base in jobs:
        h=project(bank[i],axis);S={v%256 for v in h};patch=face(mask,base)
        key=(frozenset(S),mask,base)
        if key in seen:continue
        seen.add(key);st,w=complete(h,S,patch,192,a.budget,propagate=a.propagate)
        print(json.dumps([i,axis,mask,base,st,w],separators=(',',':')),flush=True)
        if w or len(seen)>=a.jobs:break
if __name__=='__main__':main()
