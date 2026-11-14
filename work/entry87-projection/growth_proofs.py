"""Verify all hard Hamilton cases for the 131 actual source paths and syndrome edits."""
import argparse
import json
from pathlib import Path
from bank_parity_proofs import initial,prove
from check_bank_trees import graph,verify
from syndrome import neighbour_syndrome
from solve import BANK,BANK_HASH,sha256,save


def solve_receipt(receipt):
    raw=BANK.read_bytes();assert sha256(raw).hexdigest()==BANK_HASH
    bank=json.loads(raw);rows=json.loads(receipt.read_text());proofs=[]
    case=receipt.stem.split("-")
    for row in rows:
        if "duplicate" in row:continue
        i=row["index"];p=row["parity"];source=set(bank[i]["vertex_sequence"][p::2])
        def record(edited,caps,change):
            tree=prove(*initial(sorted(edited),caps))
            count=verify(*graph(edited,p,caps),tree)
            proofs.append(dict(index=i,parity=p,cap=caps,change=change,tree=tree,nodes=count))
        if case[0]=="source":
            remove=int(case[2])
            if row["small_class"]=="Hamilton path infeasible":record(source,True,[])
            for edits in row["hard"]:
                target=source-set(edits[:remove])|set(edits[remove:])
                assert len(target)==97
                record(target,False,edits)
        else:
            radius=int(case[1])
            for edits in row["hard"]:
                assert len(edits)==radius
                target=source^neighbour_syndrome(set(edits))
                record(target,radius%2==0,edits)
    path=Path(receipt.stem+"-trees.json");save(path,proofs)
    print(path,len(proofs),sum(r["nodes"] for r in proofs),max((r["nodes"] for r in proofs),default=0))


if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("receipt",nargs="+",type=Path)
    for name in p.parse_args().receipt:solve_receipt(name)
