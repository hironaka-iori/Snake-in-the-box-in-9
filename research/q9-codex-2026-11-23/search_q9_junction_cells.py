"""Search the unresolved joins with face-specific upper bounds and their summed slack."""
import argparse
import json
from collections import deque
from itertools import combinations
from pysat.card import CardEnc,EncType
from pathlib import Path
from search_q9_junction_last_cases import Balanced, anchored, check, sources

def forest(mask):
    nbrs = [[v^(1<<d) for d in range(4) if mask>>(v^(1<<d))&1] for v in range(16)]
    left = {v for v in range(16) if mask>>v&1}
    if any(len(nbrs[v])>2 for v in left):
        return False
    while left:
        start=left.pop()
        todo=[start]
        count=0
        for v in todo:
            count+=len(nbrs[v])
            for w in nbrs[v]:
                if w in left:
                    left.remove(w)
                    todo.append(w)
        if count>=2*len(todo):
            return False
    return True

def index_masks():
    valid=[m for m in range(65536) if forest(m)]
    columns = [sum(1<<i for i,m in enumerate(valid) if m>>b&1) for b in range(16)]
    bins = {}
    for i,m in enumerate(valid):
        counts=(m.bit_count(),sum(m>>v&1 for v in range(16) if v.bit_count()%2==0))
        for part,k in enumerate((counts[0],counts[1],counts[0]-counts[1])):
            bins[part,k]=bins.get((part,k),0)|(1<<i)
    return (1<<len(valid))-1,columns,bins

def partitions():
    for axes in combinations(range(9),4):
        spread=[sum(((i>>j)&1)<<d for j,d in enumerate(axes)) for i in range(16)]
        mask=sum(1<<d for d in axes)
        yield [[base|s for s in spread] for base in range(512) if not base&mask]

def leaves():
    r=[x for x in map(json.loads,Path("q9_junction_second_omission.jsonl").read_text().splitlines()) if x["status"]=="UNKNOWN"]
    queue=deque((set(x["fixed"]),set(x["excluded"])) for x in r)
    for x in map(json.loads,Path("q9_junction_branch.jsonl").read_text().splitlines()):
        a,b=queue.popleft()
        assert (a,b)==(set(x["fixed"]),set(x["excluded"]))
        if x["status"]=="UNKNOWN":
            v=x["split"]
            queue.extend([(a|{v},b),(a,b|{v})])
    assert len(queue)==37
    return list(queue)

class CellSolver(Balanced):
    def set_phases(self,hints):
        free={abs(x)-1 for x in hints}
        all_masks,columns,bins=mask_index
        targets=(self.edges+1,self.edges//2+int(self.endpoint==0),self.edges//2+int(self.endpoint==1))
        ranks=[[] for _ in targets]
        for groups in layouts:
            plan=[[] for _ in targets]
            for group in groups:
                valid=all_masks
                for i,v in enumerate(group):
                    if v in self.fixed:valid &= columns[i]
                    elif v not in free:valid &= ~columns[i]
                if not valid:
                    self.add_clause([])
                    return
                swap=group[0].bit_count()%2
                for t in range(3):
                    part=0 if t==0 else 1+((t-1)^swap)
                    max_count=next(k for k in range(16,-1,-1) if valid & bins.get((part,k),0))
                    vs=[v for v in group if t==0 or v.bit_count()%2==t-1]
                    fixed_count=sum(v in self.fixed for v in vs)
                    lits=[v+1 for v in vs if v in free]
                    plan[t].append((lits,max_count-fixed_count))
            for t in range(3):
                need=targets[t]-sum(t==0 or v.bit_count()%2==t-1 for v in self.fixed)
                slack=sum(k for _,k in plan[t])-need
                if slack<0:
                    self.add_clause([])
                    return
                ranks[t].append((slack,plan[t]))
        for rank in ranks:
            # For each chosen parallel-face partition, a deficit in one face consumes
            # the same finite slack as a deficit in any other face.
            for slack,parts in sorted(rank,key=lambda x:x[0])[:3]:
                deficits=[]
                for lits,cap in parts:
                    self.add_atmost(lits,cap)
                    floor=max(0,cap-slack)
                    self.add_atmost([-x for x in lits],len(lits)-floor)
                    if min(cap,slack)==0:continue
                    for k in range(floor+1,cap+1):
                        self.top+=1
                        flag=self.top
                        # A true deficit flag pays for occupancy below k.
                        cnf=CardEnc.atmost(lits=[-x for x in lits],bound=len(lits)-k,
                                           top_id=self.top,encoding=EncType.totalizer)
                        self.top=max(self.top,cnf.nv)
                        for clause in cnf.clauses:self.add_clause([flag,*clause])
                        deficits.append(flag)
                self.add_atmost(deficits,slack)
        super().set_phases(hints)

if __name__=="__main__":
    ap=argparse.ArgumentParser()
    ap.add_argument("folder",type=Path)
    ap.add_argument("--budget",type=int,default=20000)
    ap.add_argument("--radii",type=int,nargs="+")
    args=ap.parse_args()
    mask_index=index_masks()
    layouts=list(partitions())
    _,_,p,joins=next(sources(args.folder))
    jobs=[("control",set(p[8:80]+p[91:138]+p[151:-5]),set(),190,p[0].bit_count()%2)]
    if args.radii:
        for radius in args.radii:
            centers=[0,*joins,len(p)-1]
            fixed={v for i,v in enumerate(p) if min(abs(i-j) for j in centers)>radius}
            for ep in (0,1):
                jobs.append((f"radius-{radius}",fixed,set(),192,ep))
    else:
        jobs.extend((i,fixed,excluded,192,0) for i,(fixed,excluded) in enumerate(leaves(),1))
    for label,fixed,excluded,n,ep in jobs:
        anchored.Minicard=lambda:CellSolver(ep,fixed,n)
        status,w=anchored.search(fixed,set(p),n,args.budget,allowed=set(range(512))-excluded)
        if w:
            check(w,n)
            assert len(w)==n+1 and fixed<=set(w) and excluded.isdisjoint(w)
        if label=="control":assert status=="FOUND"
        print(json.dumps(dict(case=label,edges=n,endpoint=ep,fixed_count=len(fixed),
                              status=status,witness=w)),flush=True)
        if n==192 and w:break
