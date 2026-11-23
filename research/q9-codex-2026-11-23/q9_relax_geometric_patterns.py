import argparse
import json
from pathlib import Path

from q6_star_interfaces import check
from q9_certify_geometric_joins import make, omittable_crossings, trial
from q9_geometry_cut_library import orientations
from q9_join_interface_masks import Catalogue
from q9_three_tight_pairs import BONDS
from verify_q9_free_dimension_cuts import deg, parts


def main(args):
    directory=args.directory
    library=json.loads((directory/"q9_verified_geometric_cut_library.json").read_text())
    tables=Catalogue(directory/"q6_colour_caps/interfaces_29_step_with26_verified.jsonl")
    banks={}
    cases=[]
    for pattern in library["patterns"]:
        counts=tuple(pattern["source"])
        if counts not in banks:
            name="_".join(map(str,counts))
            banks[counts]=json.loads((directory/f"q9_pair_{name}_profiles.json").read_text())["representatives"]
        row=banks[counts][pattern["index"]]
        e,c,r=row
        wanted=(tuple(map(tuple,pattern["faces"])),tuple(map(tuple,pattern["links"])))
        for mask in range(1,256):
            layers={v for v in range(8) if mask>>v&1}
            if len(layers)!=len(wanted[0]):
                continue
            faces=[(v,e[v],c[v]) for v in sorted(layers)]
            bonds=[(a,b,n) for (a,b),n in zip(BONDS,r) if a in layers and b in layers]
            if min(orientations(faces,bonds))!=wanted:
                continue
            omit=omittable_crossings(row,layers,tables)
            if omit:
                cases.append((len(layers),-len(omit),counts,pattern["index"],layers,omit))
            break
    cases.sort(key=lambda x:x[:4])
    print(json.dumps(dict(status="STARTED",eligible=len(cases),sample=min(args.limit,len(cases)))),flush=True)
    for i,(_,_,counts,index,layers,omit) in enumerate(cases[:args.limit]):
        row=banks[counts][index]
        # Try deleting all crossings that support no domain first, then individual ones.
        trials=[omit]+[{bond} for bond in sorted(omit) if len(omit)>1]
        for dropped in trials:
            result=trial(row,layers,tables,4000,8000,args.checker,omit=dropped)
            message=dict(source=counts,index=index,layers=sorted(layers),omitted=sorted(dropped),status=result["status"])
            if result["status"]=="UNSAT_DRAT_VERIFIED":
                f,n=make(row,layers,tables,4000,omit=dropped)
                assert n==result["layouts"]
                for cycle in result["cycles"]:
                    s=set(cycle)
                    assert len(s)==len(cycle) and all(u>>6 in layers for u in s)
                    assert len(parts(s,9))==1 and all(deg(s,u,9)==2 for u in s)
                    f.append([-u-1 for u in cycle])
                check(f,result["proof"],args.checker)
                e,c,r=row
                faces=[(v,e[v],c[v]) for v in sorted(layers)]
                links=[(a,b,n) for (a,b),n in zip(BONDS,r) if a in layers and b in layers and (a,b) not in dropped]
                faces,links=min(orientations(faces,links))
                message.update(status="VERIFIED_RELAXED_PATTERN",faces=faces,links=links)
                with args.archive.open("a") as out:
                    out.write(json.dumps(dict(**message,proof=result["proof"],cycles=result["cycles"]))+"\n")
            print(json.dumps(message),flush=True)
            if message["status"]=="VERIFIED_RELAXED_PATTERN":
                break


if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("directory",type=Path)
    parser.add_argument("checker")
    parser.add_argument("archive",type=Path)
    parser.add_argument("--limit",type=int,default=16)
    main(parser.parse_args())
