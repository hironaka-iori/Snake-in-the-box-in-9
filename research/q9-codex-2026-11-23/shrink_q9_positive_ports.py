import gzip,json,random
from pathlib import Path
from bound_q9_positive_ports import bound,crossing_edges
here=Path(__file__).resolve().parent
with gzip.open(here/"q9_port_followup_public191.txt.gz","rt") as f:
    path=list(map(int,list(f)[130].split()))
edges=crossing_edges(path,7)+crossing_edges(path,5)
def vertices(es):
    return {v for e in es for v in e}
best=edges
_,faces=bound(vertices(edges),return_faces=True)
rng=random.Random(220)
for trial in range(10):
    order=edges.copy();rng.shuffle(order)
    kept=set(edges)
    for e in order:
        kept.remove(e)
        if bound(vertices(kept),fixed_faces=faces)>220:
            kept.add(e)
    if len(kept)<len(best):
        best=sorted(kept)
        print(trial,len(best),flush=True)
for refinement in range(8):
    base=list(best)
    _,faces=bound(vertices(base),return_faces=True)
    for trial in range(12):
        order=base.copy();rng.shuffle(order)
        kept=set(base)
        for e in order:
            kept.remove(e)
            if bound(vertices(kept),fixed_faces=faces)>220:kept.add(e)
        if len(kept)<len(best):best=sorted(kept)
    print("refinement", refinement, len(best), flush=True)
    if len(best)==len(base):break
value,faces=bound(vertices(best),return_faces=True)
record=dict(row_zero_based=130,axes_zero_based=[7,5],required_edges=best,faces=faces,upper_edges=value)
out=here/"q9_positive_ports_220_certificate.json"
out.write_text(json.dumps(record,indent=1)+"\n")
print("required edges",len(best),"vertices",len(vertices(best)),"upper edges",value)
