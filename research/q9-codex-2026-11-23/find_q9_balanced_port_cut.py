"""Find a clustered two-axis certificate under an explicit per-axis port cap."""
import gzip,json,sys
from pathlib import Path
from bound_q9_positive_ports import bound,crossing_edges

here=Path(__file__).resolve().parent
with gzip.open(here/"q9_port_followup_public191.txt.gz","rt") as f:
    bank=[list(map(int,line.split())) for line in f]
best=512
for r in [130,37,0,58,94,71,13,113]:
    p=bank[r]
    es=sorted([crossing_edges(p,d) for d in range(9)],key=lambda s:-len(s))[:2]
    def vertices(groups):
        return {v for g in groups for edge in g for v in edge}
    steps=0
    while any(len(g)>25 for g in es):
        if steps%5==0:
            _,faces=bound(vertices(es),return_faces=True)
        options=[]
        for a,g in enumerate(es):
            if len(g)<=25:continue
            for e in g:
                kept=[list(t) for t in es];kept[a].remove(e)
                options.append((bound(vertices(kept),fixed_faces=faces),a,e))
        _,a,e=min(options)
        es[a].remove(e);steps+=1
    value,faces=bound(vertices(es),return_faces=True)
    print(r,[len(g) for g in es],value,flush=True)
    if value<best:
        best=value
        record=dict(row_zero_based=r,required_edges=es[0]+es[1],faces=faces,upper_edges=value)
        (here/"q9_positive_ports_balanced_certificate.json").write_text(json.dumps(record,indent=1)+"\n")
    if best<=220:break
