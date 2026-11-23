from collections import Counter
import json
from pathlib import Path
import sys

from q6_star_interfaces import check
from q9_certify_geometric_joins import make
from q9_geometry_cut_library import orientations
from q9_join_interface_masks import Catalogue
from q9_three_tight_pairs import BONDS
from verify_q9_free_dimension_cuts import deg,parts
from verify_q9_frequency_branch import geometry_screen

directory,archive,checker,output=Path(sys.argv[1]),Path(sys.argv[2]),sys.argv[3],Path(sys.argv[4])
existing=directory/"q9_verified_geometric_cut_library.json"
library=json.loads(existing.read_text())
key=lambda row:(tuple(map(tuple,row["faces"])),tuple(map(tuple,row["links"])))
patterns={key(row):row for row in library["patterns"]}
catalogue=Catalogue(directory/"q6_colour_caps/interfaces_29_step_with26_verified.jsonl")
banks={}
verified=0
with archive.open() as rows:
    for line in rows:
        record=json.loads(line)
        assert record["status"]=="VERIFIED_RELAXED_PATTERN"
        source=tuple(record["source"])
        if source not in banks:
            prefix="_".join(map(str,source))
            banks[source]=json.loads((directory/f"q9_pair_{prefix}_profiles.json").read_text())["representatives"]
        layers=set(record["layers"])
        omitted={tuple(pair) for pair in record["omitted"]}
        row=banks[source][record["index"]]
        f,_=make(row,layers,catalogue,4000,omit=omitted)
        for vertices in record["cycles"]:
            cycle=set(vertices)
            assert len(cycle)==len(vertices) and all(u>>6 in layers for u in cycle)
            assert len(parts(cycle,9))==1 and all(deg(cycle,u,9)==2 for u in cycle)
            f.append([-u-1 for u in vertices])
        check(f,record["proof"],checker)
        edges,components,crossings=row
        faces=[(v,edges[v],components[v]) for v in sorted(layers)]
        links=[(a,b,n) for (a,b),n in zip(BONDS,crossings) if a in layers and b in layers and (a,b) not in omitted]
        signature=min(orientations(faces,links))
        assert signature==key(record) and omitted
        faces,links=signature
        patterns.setdefault(signature,dict(faces=faces,links=links,source=source,index=record["index"]))
        verified+=1
output.write_text(json.dumps(dict(source_certificates=library["source_certificates"]+verified,patterns=list(patterns.values())))+"\n")
print(json.dumps(dict(status="REPLAYED",verified=verified,additional_patterns=len(patterns)-len(library["patterns"]))),flush=True)
for triple in ("8_10_11","9_9_11","9_10_10"):
    prefix=directory/f"q9_pair_{triple}"
    params=(Path(f"{prefix}_profiles.json"),Path(f"{prefix}_colour_screen.json"),
            directory/"q9_pair_9_9_10_anchor_replay.log",
            [directory/"q6_colour_caps/interfaces26_1_23_c5_r1_empty_replay.log"])
    old=geometry_screen(*params,existing)
    prior=json.loads(Path(f"{prefix}_universal_geometry_screen.json").read_text())
    previous=set(prior["indices"])
    assert previous<=set(old["indices"])
    new=geometry_screen(*params,output)
    remaining=previous & set(new["indices"])
    print(json.dumps(dict(triple=triple,old=len(previous),new=len(remaining))),flush=True)
