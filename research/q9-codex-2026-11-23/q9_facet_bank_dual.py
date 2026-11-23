"""Integer-replayable necessary bounds for a Q9 snake containing a fixed Q8 segment."""
from itertools import combinations
from pathlib import Path
from collections import defaultdict
import json, os, random, sys, warnings
import numpy as np
from scipy.optimize import linprog, OptimizeWarning
from scipy.sparse import coo_matrix
warnings.filterwarnings("ignore", category=OptimizeWarning)

def build(word,axes,export=False):
    path=[0]
    for c in word:path.append(path[-1]^(1<<int(c)))
    tips={path[0],path[-1]};inside=set(path[1:-1])
    banned=inside|{v^(1<<i) for v in inside for i in range(9)}
    pool=sorted((set(range(512))-banned)|tips)
    legal=set(pool)
    rid={};factors=[]
    def row(k):
        if k not in rid:rid[k]=len(rid)
        return rid[k]
    for key in ["end0","end1","balance"]:row(key)
    states={};compatible={}
    for v in pool:
        ds=[1<<i for i in range(9) if v^(1<<i) in legal]
        allowed=[]
        for size in (0,1) if v in tips else (1,2):
            for chosen in combinations(ds,size):
                sig=sum(chosen);is_end=(size+int(v in tips)==1)
                features=[(2,1-2*(v.bit_count()%2))]
                if is_end:features.append((v.bit_count()%2,1))
                for m in axes:features.append((row((m,v,sig&m)),-1))
                allowed.append((1,features))
        states[v]=[(sum(c)) for sz in ((0,1) if v in tips else (1,2)) for c in combinations(ds,sz)]
        for m in axes:compatible[m,v]={s&m for s in states[v]}
        if v not in tips:allowed.append((0,[]))
        factors.append(allowed)
    for m in axes:
        groups=defaultdict(list)
        for v in pool:groups[v&~m].append(v)
        for cell in groups.values():
            local={v:i for i,v in enumerate(cell)}
            local_adj=[sum(1<<local[v^(1<<i)] for i in range(9) if (m>>i)&1 and v^(1<<i) in local) for v in cell]
            mandatory=sum(1<<i for i,v in enumerate(cell) if v in tips)
            options=[]
            for picked in range(1<<len(cell)):
                if (picked&mandatory)!=mandatory:continue
                keys=[];unvisited=picked
                for i,v in enumerate(cell):
                    if not (picked>>i)&1:continue
                    neighbours=picked&local_adj[i]
                    if neighbours.bit_count()>2:break
                    sig=0
                    while neighbours:
                        bit=neighbours&-neighbours;neighbours^=bit
                        sig|=v^cell[bit.bit_length()-1]
                    if sig not in compatible[m,v]:break
                    keys.append((rid[(m,v,sig)],1))
                else:
                    while unvisited:
                        start=unvisited&-unvisited;unvisited^=start;front=start
                        size=edges=0
                        while front:
                            bit=front&-front;front^=bit;size+=1
                            n=local_adj[bit.bit_length()-1]&picked;edges+=n.bit_count()
                            front|=n&unvisited;unvisited&=~n
                        if edges!=2*(size-1):break
                    else:options.append((0,keys))
            if not options:raise ValueError("empty face")
            factors.append(options)
    # Select a convex combination in each local group. Only the shared
    # statistics need dual prices in the final integer certificate.
    nr=len(rid);rr=[];cc=[];vv=[];obj=[]
    for i,opts in enumerate(factors):
        for val,features in opts:
            col=len(obj);obj.append(-val)
            rr.append(nr+i);cc.append(col);vv.append(1)
            for j,a in features:rr.append(j);cc.append(col);vv.append(a)
    for j in range(3):
        for sign in [-1,1]:
            rr.append(j);cc.append(len(obj));vv.append(sign);obj.append(1000)
    matrix=coo_matrix((vv,(rr,cc)),shape=(nr+len(factors),len(obj))).tocsc()
    if export:
        return matrix[:,:-6],obj[:-6],nr,factors,inside,tips,pool
    def certificate(colour):
        sign=1-2*colour
        delta=sign-sum(1-2*(v.bit_count()%2) for v in inside)
        rhs=[2*int(colour==0),2*int(colour==1),delta]+[0]*(nr-3)+[1]*len(factors)
        sol=linprog(np.asarray(obj,dtype=float),A_eq=matrix,b_eq=rhs,bounds=(0,None),method="highs",options={"threads":1,"time_limit":30})
        if not sol.success:return dict(word=word,majority=colour,status=str(sol.message))
        scale=10000
        prices=[round(-y*scale) for y in sol.eqlin.marginals[:nr]]
        total=scale*len(inside)+sum(x*y for x,y in zip(rhs,prices))
        for opts in factors:
            total+=max(k*scale-sum(prices[j]*a for j,a in features) for k,features in opts)
        result=dict(word=word,majority=colour,scale=scale,axes=axes,fees=prices[:3],
                    weights=[[*k,prices[i]] for k,i in rid.items() if isinstance(k,tuple) and prices[i]],bound_scaled=total)
        if os.getenv("Q9_FACET_PRIMAL"):
            offset=0;occupancy=[]
            for j,v in enumerate(pool):
                opts=factors[j]
                value=sum(sol.x[offset+k]*val for k,(val,_) in enumerate(opts))
                occupancy.append([v,round(max(0,min(1,value))*1000)])
                offset+=len(opts)
            result["occupancy_permille"]=occupancy
        return result
    return certificate

def families(n):
    opts=[sum(1<<i for i in ds) for ds in combinations(range(8),3)]
    random.Random(7341).shuffle(opts)
    # Cover the nine axes early, including mixed cells spanning both Q8 facets.
    if os.getenv("Q9_FOUR_FACES"):
        return ([15,240,448,51,204,85,170,105,150,99,156,53,202,57,198,113,142]+opts)[:n]
    return ([7,56,448]+[m for m in opts if m not in [7,56,448]])[:n]

if __name__=="__main__":
    bank=Path("q8_catalogue_96_98.words").read_text().split()
    ids=(i for i in range(len(bank)) if i not in {606,0,200,500}) if sys.argv[2]=="remaining8" else map(int,sys.argv[2:])
    for i in ids:
        calc=build(bank[i],families(int(sys.argv[1])))
        for parity in range(2):
            result=calc(parity);result["index"]=i
            print(json.dumps(result,separators=(",",":")),flush=True)
