"""Propagate mandatory vertices and endpoint quotas before searching for a path of at least the given length."""
import argparse
import json
from pathlib import Path
from search_q9_capacity_groups import GroupedSolver,anchored,cases,check

neighbors=[set(n) for n in anchored.NB]
def propagate(original,excluded,sig):
    quotas=((2,0),(0,2),(1,1))[sig]
    fixed=set(original)
    available=set(range(512))-excluded
    while True:
        fdegree={v:len(neighbors[v]&fixed) for v in available}
        adegree={v:len(neighbors[v]&available) for v in available}
        if not fixed<=available or any(fdegree[v]>2 for v in fixed):return None
        reserved=[v for v in fixed if adegree[v]==1]
        spare=[quotas[h]-sum(v.bit_count()%2==h for v in reserved) for h in (0,1)]
        if min(spare)<0:return None
        label={}
        for start in fixed:
            if start in label:continue
            todo=[start]
            label[start]=start
            edges=0
            for v in todo:
                edges+=fdegree[v]
                for w in neighbors[v]&fixed:
                    if w not in label:
                        label[w]=start
                        todo.append(w)
            if edges!=2*(len(todo)-1):return None
        saturated={v for v in fixed if fdegree[v]==2}
        take=set()
        drop=set()
        for v in available:
            minimum=1 if v in reserved or spare[v.bit_count()%2]>0 else 2
            if v in fixed:
                if adegree[v]<minimum:return None
                if adegree[v]==minimum:take.update(neighbors[v]&available)
            elif adegree[v]<minimum or fdegree[v]>2 or neighbors[v]&saturated:
                drop.add(v)
            else:
                contacts=neighbors[v]&fixed
                if len({label[w] for w in contacts})<len(contacts):drop.add(v)
        if take&drop:return None
        if take<=fixed and not drop:return fixed,available
        fixed|=take
        available-=drop

class QuotaSolver(GroupedSolver):
    def __init__(self,fixed,domain,target,sig):
        super().__init__(fixed,target)
        for h,k in enumerate(((2,0),(0,2),(1,1))[sig]):
            possible=[v+513 for v in domain if v.bit_count()%2==h and len(neighbors[v]&fixed)<2]
            self.add_atmost(possible,k)
            self.add_atmost([-v for v in possible],len(possible)-k)

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("file",type=Path)
    ap.add_argument("--budget",type=int,default=35000)
    ap.add_argument("--control",action="store_true")
    ap.add_argument("--full-obstruction",action="store_true")
    args=ap.parse_args()
    db={(f,r):(p,i,j,set(im)) for f,r,p,i,j,im in cases()}
    for row in map(json.loads,args.file.read_text().splitlines()):
        if row["status"]!=("FOUND" if args.control else "UNKNOWN"):continue
        n=row.get("target",192)
        p,i,j,image=db[row["source"],row["row"]]
        centers=[0,len(p)-1,i,j]
        excluded=set()
        if args.full_obstruction:
            original={v for k,v in enumerate(p) if v not in image and min(abs(c-k) for c in centers)>row["radius"]}
            assert len(original)==row["fixed"]
        else:
            excluded.add(row["omitted"])
            centers.append(p.index(row["omitted"]))
            original={v for k,v in enumerate(p) if min(abs(c-k) for c in centers)>row["width"]}
            assert len(original)==row["anchors"]
        for sig in range(3):
            pair=propagate(original,excluded,sig)
            if pair is None:st,w="GEOMETRY",None
            else:
                fixed,domain=pair
                anchored.Minicard=lambda:QuotaSolver(fixed,domain,n,sig)
                st,w=anchored.search(fixed,set(p),n,args.budget,allowed=domain,at_least=True)
            if w:
                check(w,n)
                assert original<=set(w) and excluded.isdisjoint(w)
                colors=sorted(v.bit_count()%2 for v in (w[0],w[-1]))
                assert colors==([0,0],[1,1],[0,1])[sig]
            print(json.dumps({**row,"sig":sig,"status":st,"witness":w}),flush=True)
            if w and len(w)>=193:return
if __name__=="__main__":main()
