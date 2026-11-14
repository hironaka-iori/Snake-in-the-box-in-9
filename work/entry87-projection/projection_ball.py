"""Audit and combine all projected-support decisions inside a Hamming ball of radius three."""
import json
from collections import Counter
from math import comb
from pathlib import Path
from punctured_lift import project
from solve import BANK,BANK_HASH,sha256,defects,save

if __name__=="__main__":
    raw=BANK.read_bytes();assert sha256(raw).hexdigest()==BANK_HASH;bank=json.loads(raw);cases=[];all_shapes=0
    for source in range(25):
        path=bank[source]["vertex_sequence"];P,s=project(path,5);W=set(P);assert len(W)==191 and len(s)==1
        for remove in range(4):
            for add in range(4-remove):
                k=193-(191-remove+add)
                if k<=0:continue
                suffix=("" if remove==1 else f"-remove{remove}")+("" if k==1 else f"-cross{k}")
                prefix=f"single-hinge-exchange-{source}-"
                f=Path(prefix+"150000"+suffix+".json");r=json.loads(f.read_bytes());assert r["source"]==source and r["axis"]==5
                witnesses=[z["witness"] for z in r["control"] if z["status"]=="FOUND"]
                assert len(witnesses)==1 and len(witnesses[0])==192 and not defects(witnesses[0])
                assert len({v&255 for v in witnesses[0]})==192-k
                D={v for v in range(256) if sum((v^(1<<d)) in W for d in range(8))<=2+remove}
                rows={z["root"]:z for z in r["results"]}
                if len(D)<k:
                    assert len(rows)==1 and rows[None]["reason"] and set(rows[None]["candidates"])==D
                else:assert set(rows)==D
                unresolved={v for v,z in rows.items() if z["status"]=="OPEN"}
                if unresolved:
                    follow=json.loads(Path(prefix+"1500000"+suffix+".json").read_bytes())
                    extra={z["root"]:z for z in follow["results"]};assert set(extra)==unresolved;rows.update(extra)
                assert all(z["status"]=="EXHAUSTED" for z in rows.values())
                # Count all index choices before the bipartition and degree filters.
                shapes=comb(191,remove)*comb(65,add);all_shapes+=shapes
                cases.append(dict(source=source,removed=remove,added=add,crossings=k,shapes=shapes,
                                  control=witnesses[0],roots=list(rows.values())))
    assert len(cases)==200
    save(Path("projection-ball-three.json"),dict(sources=25,radius=3,decisions=cases,
         indexed_support_changes_with_positive_crossing=all_shapes,total_root_rows=sum(len(c["roots"]) for c in cases)))
    print(len(cases),all_shapes,Counter((r["removed"],r["added"]) for r in cases))
