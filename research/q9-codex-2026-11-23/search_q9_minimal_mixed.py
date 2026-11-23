"""When both same-color cases are impossible, either endpoint of an odd path must be required."""
import json
from collections import defaultdict
from pathlib import Path
from search_q9_endpoint_domains import QuotaSolver,propagate,anchored,check,cases

class FixedTips(QuotaSolver):
    def __init__(self,fixed,domain,required):
        super().__init__(fixed,domain,193,2)
        for v in domain-required:
            self.add_clause([-(v+513)])

def main():
    groups=defaultdict(dict)
    for r in map(json.loads,Path("q9_endpoint_domains_r12.jsonl").read_text().splitlines()):
        groups[r["source"],r["row"],r["omitted"]][r["sig"]]=r["status"]
    db={(f,r):(p,i,j) for f,r,p,i,j,_ in cases()}
    for (name,row,missing),sigs in groups.items():
        if sigs[2]!="UNKNOWN":continue
        assert sigs[0]==sigs[1]=="UNSAT"
        p,i,j=db[name,row]
        centers=[0,len(p)-1,i,j,p.index(missing)]
        required={v for k,v in enumerate(p) if min(abs(k-t) for t in centers)>12}
        pair=propagate(required,{missing},2)
        if pair is None:status,w="GEOMETRY",None
        else:
            fixed,domain=pair
            anchored.Minicard=lambda:FixedTips(fixed,domain,required)
            status,w=anchored.search(fixed,set(p),193,90000,at_least=True,allowed=domain)
        if w:
            check(w,193)
            assert required<=set(w) and missing not in w and {w[0],w[-1]}<=required
        print(json.dumps(dict(source=name,row=row,omitted=missing,status=status,witness=w)),flush=True)
        if w:return
if __name__=="__main__":main()
