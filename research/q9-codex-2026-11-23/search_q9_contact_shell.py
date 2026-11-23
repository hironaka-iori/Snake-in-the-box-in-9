"""Find an induced path inside a long record plus exterior vertices with few contacts."""
from itertools import combinations
from collections import Counter
from concurrent.futures import ProcessPoolExecutor
from pysat.solvers import Minicard
from verify_q9_center_avoidance import verify
from search_q9_free_record_slice import parents
import json

def solve(p,level,target,budget):
    old=set(p)
    neighbors=[[v^1<<i for i in range(9)] for v in range(512)]
    domain=old|{v for v in range(512) if len(old.intersection(neighbors[v]))<=level}
    nbs={v:domain.intersection(neighbors[v]) for v in domain}
    changes=len(domain)-len(old)
    with Minicard() as sat:
        for v in sorted(domain):
            ns=list(nbs[v]);end=v+513
            sat.add_clause([-end,v+1])
            inc=[w+1 for w in ns]+[end]
            for triple in combinations(inc,3):sat.add_clause([-v-1]+[-a for a in triple])
            if len(inc)<2:sat.add_clause([-v-1])
            else:
                for j in range(len(inc)):sat.add_clause([-v-1]+[t for k,t in enumerate(inc) if j!=k])
        es=[v+513 for v in domain]
        sat.add_atmost(es,2);sat.add_atmost([-e for e in es],len(es)-2)
        sel=[v+1 for v in domain]
        if len(sel)<=target:return ["SIZE",changes,0,None]
        sat.add_atmost([-s for s in sel],len(sel)-target-1)
        for colour in (0,1):
            cc=[v+1 for v in domain if v.bit_count()%2==colour]
            if len(cc)<(target+1)//2:return ["SIZE",changes,0,None]
            sat.add_atmost([-v for v in cc],len(cc)-(target+1)//2)
        sat.set_phases([v+1 if v in old else -v-1 for v in domain])
        rejected=0
        while True:
            left=budget-sat.accum_stats()["conflicts"]
            if left<=0:return ["UNKNOWN",changes,rejected,None]
            sat.conf_budget(left);res=sat.solve_limited()
            if res is not True:return ["UNKNOWN" if res is None else "UNSAT",changes,rejected,None]
            model=set(sat.get_model());sel={v for v in domain if v+1 in model}
            groups=[];unseen=sel.copy()
            while unseen:
                group=[unseen.pop()]
                for x in group:
                    for u in nbs[x]&unseen:unseen.remove(u);group.append(u)
                groups.append(group)
            if len(groups)==1:
                tip=next(v for v in sel if len(nbs[v]&sel)==1);w=[tip];unseen=sel-{tip}
                while unseen:
                    u,=nbs[w[-1]]&unseen;w.append(u);unseen.remove(u)
                verify(w);assert len(w)>target;return ["FOUND",changes,rejected,w]
            rejected+=1
            for g in groups:
                q=set(g)
                if all(len(nbs[v]&q)==2 for v in g):
                    # A selected induced cycle cannot be part of any induced path.
                    sat.add_clause([-v-1 for v in g])
def init():
    global bank
    bank=parents()
def run(args):
    i,level,t,cap=args;return [i,level,t,*solve(bank[i],level,t,cap)]
if __name__=="__main__":
    with ProcessPoolExecutor(4,initializer=init) as pool:
        jobs=[(i,1,191,4000) for i in range(0,131,11)]+[(i,c,192,100000) for c in (1,2,3) for i in range(131)]
        for r in pool.map(run,jobs,buffersize=36,chunksize=1):
            print(json.dumps(r,separators=(",",":")),flush=True)
            if r[-1] and len(r[-1])>192:break
