"""Assemble the closure implication and check the lower-bound witnesses pair by pair."""
from collections import Counter
from math import comb
from pathlib import Path
import json
import sys
from enumerate_shell import HERE, MS, read, digest, check_path, PARTNERS, PARENTS
sys.path.insert(0,str(MS/"251-eighty-edge-segments"))
from bank_capacity import check_path as verify_cube

def main():
    prior=MS/"255-parity-exchange-arms/attainer-closure.json"
    d=read(prior)
    component=set(d["paths"])
    replay=read(HERE/"replay.json")["shells"]
    cases={}
    all_shapes=set()
    for f in sorted(HERE.glob("shell-*.json")):
        shell=read(f)
        key=shell["reference_shape"]
        if key in cases or replay[f.name]["sha256"]!=digest(f) or not set(shell["shapes"])<=component:
            raise ValueError("Independent shell correspondence failed")
        cases[key]=dict(reference_class=shell["class_id"],**shell["counts"])
        all_shapes.update(shell["shapes"])
    if set(cases)!=component or not d["closed"] or len(component)!=6:
        raise ValueError("Incomplete set of references")
    for key,p in d["paths"].items():
        check_path(p)
        for order in (p,p[::-1]):
            for j in range(8):
                v=order[-1]^(1<<j)
                if v not in order and all((v^u).bit_count()!=1 for u in order[:-1]):
                    raise ValueError("An arm can be extended")
    parents={tuple(r["case"]):r["rooted_parent"] for r in read(PARENTS)["records"]}
    joins=[]
    for row in read(PARTNERS)["records"]:
        parent=parents[row["class_id"],0]
        for idx,entry in enumerate(row["paths"]):
            joined=parent[::-1]+[256+v for v in entry["path"]]
            if len(joined)!=192 or verify_cube(joined,9)!=18336:
                raise ValueError("Attaining join failed")
            joins.append([row["class_id"],idx,len(joined)-1])
    global_file=MS.parent/"outputs/snake9_witness.json"
    p=read(global_file)["vertex_sequence"]
    result=dict(covered_radius=2,counts_by_reference=cases,
                total_cases=sum(c["all_classes"] for c in cases.values()),
                positive_reference_class_pairs=sum(c["viable_classes"] for c in cases.values()),
                output_shapes=sorted(all_shapes),closure=sorted(component),
                maximum_join_in_component=191,maximum_smaller_class_overlap=45,
                inherited_cap_source="255-parity-exchange-arms/attainer-closure.json",
                verified_joins=joins,global_witness_edges=len(p)-1,
                global_witness_pairs=verify_cube(p,9),endpoint_slots_checked=16*len(component),
                dependencies={f.name:digest(f) for f in [prior,HERE/"replay.json",PARENTS,PARTNERS,global_file]})
    if len(joins)!=25 or len(p)!=192: raise ValueError("Witness count differs")
    (HERE/"summary.json").write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8",newline="\n")
    print(result["total_cases"],len(all_shapes),len(joins))

if __name__=="__main__": main()
