"""Verify conditional Q9 optima using Q8 containment, complete port coverage and integer trees."""
import json
import re
import subprocess
from pathlib import Path
from q9_check_rigid_tables import check
from q9_rigid_witnesses import decode

def verify():
    bank=Path("q8_catalogue_96_98.words").read_text().split()
    records=[json.loads(l) for l in Path("q9_rigid_ports12.jsonl").read_text().splitlines()]
    witnesses=json.loads(Path("q9_rigid_five_witnesses.json").read_text())
    summary={}
    for key,witness in witnesses.items():
        i=int(key);donor=decode(bank[i]);p=witness["vertices"]
        assert len(p)==192==len(set(p)) and all(0<=v<512 for v in p)
        assert all(((u^v).bit_count()==1)==(j==k+1) for j,v in enumerate(p) for k,u in enumerate(p[:j]))
        assert p[witness["offset"]:witness["offset"]+len(donor)]==donor
        assert len(donor)==97 and donor[0]==0 and donor[-1].bit_count()%2==0
        assert not any(x not in donor and all((x^y).bit_count()!=1 for y in donor[1:-1]) for x in range(256))
        a,b=donor[0],donor[-1]
        needed={((a,),0),((b,),0),((a,b),0),((a,b),1)}
        covered=set();partial=[];nodes=leaves=0
        for r in (r for r in records if r["i"]==i):
            ports=tuple(r["ports"]);m=r["majority"];case=(ports,m)
            assert r["word"]==bank[i] and case in needed and case not in covered
            root=Path("q9_rigid_ports_trees")/("d%d_m%d_p%s"%(i,m,"-".join(map(str,ports))))
            saved=root.with_suffix(".deep.log")
            tree=root.with_suffix(".deep.tree") if saved.is_file() and " open 0 found 0 " in saved.read_text() else root.with_suffix(".tree")
            check(r,root,p)
            cmd=["q9_facet_priced_tree_20261121/replay",str(root.with_suffix(".tables")),str(tree),"193"]
            log=subprocess.run(cmd,check=True,capture_output=True,text=True).stdout
            assert "VERIFIED nodes " in log
            counts={k:int(v) for k,v in re.findall(r"(\w+) (\d+)",log)}
            assert counts["witnesses"]==0 and counts["invalid_full"]==0
            if counts["open"]:partial.append([list(ports),m,counts["open"]]);continue
            covered.add(case);nodes+=counts["nodes"];leaves+=counts["bound_leaves"]
        summary[key]=dict(witness_edges=191,independent_hamming_pairs=18336,closed_branches=len(covered),needed_branches=len(needed),
                          closed_tree_nodes=nodes,integer_bound_leaves=leaves,partial=partial,conditional_optimum=191 if covered==needed else None)
    return summary
if __name__=="__main__":print(json.dumps(verify(),indent=2))
