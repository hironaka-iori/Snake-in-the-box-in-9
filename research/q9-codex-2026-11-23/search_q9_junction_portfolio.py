"""Try exact 192-edge completions with a second cardinality encoding and endpoint parity."""
import argparse
import json
from pathlib import Path
from pysat.card import CardEnc, EncType
from pysat.solvers import Cadical195
import search_q9_anchored_sets as anchored
from search_q9_parent_junctions import check, masks, sources

class EncodedSolver(Cadical195):
    def __init__(self, endpoint_parity):
        super().__init__()
        self.top = 2048
        for v in range(512):
            if v.bit_count()%2 != endpoint_parity:
                self.add_clause([-(513+v)])

    def add_atmost(self,lits,bound):
        if bound >= len(lits):
            return
        encoded = CardEnc.atmost(lits=list(lits),bound=bound,top_id=self.top,
                                 encoding=EncType.totalizer)
        self.top = max(self.top,encoded.nv)
        self.append_formula(encoded.clauses)

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("inputs",nargs="+",type=Path)
    parser.add_argument("--folder",required=True,type=Path)
    parser.add_argument("--budget",type=int,default=2500)
    args=parser.parse_args()
    # The same pair ID can emit more than one path. Keep the records in source order.
    for file in args.inputs:
        rows = (json.loads(line) for line in file.read_text().splitlines())
        targets = (row for row in rows if row["target"] == 192)
        for name,pair,p,joins in sources(args.folder):
            seen = set()
            for width,parity,fixed in masks(p,joins,"broad" in file.name):
                if frozenset(fixed) in seen:
                    continue
                seen.add(frozenset(fixed))
                row = next(targets)
                assert (row["source"],row["pair"],row["width"],row["parity"]) == (name,pair,width,parity)
                if row["status"]!="UNKNOWN" and width!=2:continue
                for ep in (0,1):
                    anchored.Minicard=lambda: EncodedSolver(ep)
                    status,w=anchored.search(fixed,set(p),192,args.budget)
                    if w:
                        check(w,192)
                        assert len(w)==193 and fixed<=set(w)
                    print(json.dumps({**row,"endpoint_parity":ep,"status":status,"witness":w}),flush=True)
                    if w:return
        assert next(targets,None) is None
if __name__=="__main__":
    main()
