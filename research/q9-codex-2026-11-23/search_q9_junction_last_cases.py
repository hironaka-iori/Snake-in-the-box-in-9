"""Sharpen the six still-open anchored cases using exact bipartite counts."""
import json
import sys
from pathlib import Path
import search_q9_anchored_sets as anchored
from search_q9_parent_junctions import check, masks, sources
from search_q9_junction_portfolio import EncodedSolver

class Balanced(EncodedSolver):
    def __init__(self,endpoint,fixed,edges):
        super().__init__(endpoint)
        self.endpoint=endpoint
        self.fixed=fixed
        self.edges=edges
    def set_phases(self,hints):
        for color in (0,1):
            free=[abs(x) for x in hints if (abs(x)-1).bit_count()%2==color]
            need=self.edges//2+int(color==self.endpoint)-sum(v.bit_count()%2==color for v in self.fixed)
            if not 0<=need<=len(free):
                self.add_clause([])
            else:
                self.add_atmost(free,need)
                self.add_atmost([-v for v in free],len(free)-need)
        super().set_phases(hints)

def run():
    folder=Path(sys.argv[1])
    report=[json.loads(s) for s in Path("q9_junction_portfolio_deep.jsonl").read_text().splitlines()]
    scheduled=[r for r in report if r["status"]=="UNKNOWN"]
    for name,pair,p,joins in sources(folder):
        for row in scheduled:
            if (name,pair,joins)!=(row["source"],row["pair"],row["joins"]):continue
            for width,parity,fixed in masks(p,joins,row["width"]>=10):
                if (width,parity,len(fixed))!=(row["width"],row["parity"],row["fixed"]):continue
                ep=row["endpoint_parity"]
                anchored.Minicard=lambda:Balanced(ep,fixed,192)
                status,w=anchored.search(fixed,set(p),192,int(sys.argv[2]))
                if w:
                    check(w,192)
                    assert len(w)==193 and fixed<=set(w)
                print(json.dumps({**row,"status":status,"witness":w}),flush=True)
                if w:return
if __name__=="__main__":run()
