"""Search with additional cardinality bounds from mutually exclusive extensions of fixed vertices."""
import argparse
from collections import defaultdict
import json
from pathlib import Path
from pysat.card import CardEnc, EncType
from pysat.solvers import Cadical195
import search_q9_anchored_sets as anchored
from search_q9_break_matched_anchors import cases,check

class GroupedSolver(Cadical195):
    def __init__(self,fixed,target):
        super().__init__()
        self.fixed=fixed
        self.target=target
        self.top=2048

    def add_atmost(self,lits,bound):
        if bound<0:
            self.add_clause([])
        elif bound<len(lits):
            enc=CardEnc.atmost(lits=list(lits),bound=bound,top_id=self.top,encoding=EncType.totalizer)
            self.top=max(self.top,enc.nv)
            self.append_formula(enc.clauses)

    def set_phases(self,hints):
        free={abs(lit)-1 for lit in hints}
        groups=[]
        for v in self.fixed:
            neighbors=set(anchored.NB[v])
            if len(neighbors & self.fixed)==1 and len(neighbors & free)>=2:
                groups.append(neighbors & free)
        # Each fixed vertex already touching one fixed neighbor permits at most one
        # further neighbor. A disjoint cover can therefore count the entire group as one.
        for reverse in (False,True):
            occupy=[]
            by_color=[[],[]]
            remaining=set(free)
            def order(g):
                return (-len(g),(-1 if reverse else 1)*min(g))
            for group in sorted(groups,key=order):
                block=group & remaining
                if len(block)<2:continue
                remaining-=block
                self.top+=1
                flag=self.top
                self.add_clause([-flag,*[x+1 for x in block]])
                for x in block:self.add_clause([flag,-(x+1)])
                occupy.append(flag)
                by_color[next(iter(block)).bit_count()%2].append(flag)
            for v in remaining:
                occupy.append(v+1)
                by_color[v.bit_count()%2].append(v+1)
            need=self.target+1-len(self.fixed)
            self.add_atmost([-k for k in occupy],len(occupy)-need)
            for h in range(2):
                need=(self.target+1)//2-sum(v.bit_count()%2==h for v in self.fixed)
                self.add_atmost([-k for k in by_color[h]],len(by_color[h])-need)
        super().set_phases(hints)

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("file",type=Path)
    parser.add_argument("--budget",type=int,default=50000)
    parser.add_argument("--control",action="store_true")
    args=parser.parse_args()
    db={(f,r):(p,i,j) for f,r,p,i,j,_ in cases()}
    for x in map(json.loads,args.file.read_text().splitlines()):
        if x["status"]!=("FOUND" if args.control else "UNKNOWN"):continue
        p,i,j=db[x["source"],x["row"]]
        missing=x["omitted"]
        centers=(0,len(p)-1,i,j,p.index(missing))
        fixed={v for k,v in enumerate(p) if min(abs(k-c) for c in centers)>x["width"]}
        assert len(fixed)==x["anchors"] and missing not in fixed
        target=x["target"]
        anchored.Minicard=lambda:GroupedSolver(fixed,target)
        st,w=anchored.search(fixed,set(p),target,args.budget,at_least=True,allowed=set(range(512))-{missing})
        if w:
            check(w,target)
            assert fixed<=set(w) and missing not in w
        if args.control:assert st!="UNSAT"
        print(json.dumps({**x,"status":st,"witness":w}),flush=True)
        if w and len(w)>=193:return
if __name__=="__main__":main()
