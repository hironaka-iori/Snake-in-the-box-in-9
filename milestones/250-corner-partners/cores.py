"""Enumerate all long Q8 parents that retain one recorded contiguous core."""
from argparse import ArgumentParser
from collections import Counter
from hashlib import sha256
from pathlib import Path
import json

from partners import HERE, GEOMETRY, joins, partner, save_json
from geometry import shape, induced

N=tuple(tuple(x^(1<<j) for j in range(8)) for x in range(256))
NM=tuple(sum(1<<y for y in ns) for ns in N)


def extensions(path,left):
    sites=sum(1<<x for x in path)
    end=path[0 if left else -1]
    for v in N[end]:
        if not sites&(1<<v) and NM[v]&sites==1<<end:
            yield v


def main():
    cli=ArgumentParser(description=__doc__)
    cli.add_argument("--core",type=int,default=88)
    core_edges=cli.parse_args().core
    if not 84<=core_edges<=94:
        raise ValueError("Choose a core of 84 through 94 edges")
    inventory=json.loads(joins.INVENTORY.read_bytes())
    known={str(r["donor_index"]):r["path"] for r in inventory["rows"]}
    corners=json.loads(GEOMETRY.read_bytes())["corner_closure"]["new_shapes"]
    known.update({r["id"]:r["path"] for r in corners})
    source_keys={shape(p) for p in known.values()}
    cores={}
    for label,path in known.items():
        for start in range(len(path)-core_edges):
            core=path[start:start+core_edges+1]
            cores.setdefault(shape(core),dict(donor=label,start=start,core=core))
    records={}
    coverage=[]
    for cid,origin in enumerate(cores.values()):
        core=origin["core"]
        if not induced(core,8):
            raise ValueError("Invalid core")
        right_nodes=left_nodes=0
        total=Counter()
        def grow_right(p,left_count):
            nonlocal right_nodes
            right_nodes+=1
            length=len(p)-1
            if length>=96:
                total[length]+=1
                key=shape(p)
                if key not in records:
                    partner.verify(p,8)
                    records[key]=dict(id=sha256(key).hexdigest(),edges=length,path=p,core_id=cid,
                                      left_edges=left_count,right_edges=length-core_edges-left_count,
                                      in_previous=key in source_keys)
            if length<98:
                for v in extensions(p,False):
                    grow_right(p+[v],left_count)
        def grow_left(p,left_count):
            nonlocal left_nodes
            left_nodes+=1
            grow_right(p,left_count)
            if len(p)<=98:
                for v in extensions(p,True):
                    grow_left([v]+p,left_count+1)
        grow_left(core,0)
        coverage.append(dict(id=cid,**origin,left_nodes=left_nodes,right_nodes=right_nodes,counts=total))
    if not source_keys<=records.keys():
        raise ValueError("A source parent was lost")
    new=sorted((r for r in records.values() if not r["in_previous"]),
               key=lambda r:(r["edges"],r["core_id"],r["left_edges"],r["id"]))
    totals=Counter(r["edges"] for r in new)
    path=HERE/f"cores-{core_edges}.json"
    save_json(path,dict(core_edges=core_edges,source_sha256=partner.digest(Path(__file__)),
          inventory_sha256=partner.digest(joins.INVENTORY),geometry_sha256=partner.digest(GEOMETRY),
          original_provenances=sum(len(p)-core_edges for p in known.values()),core_classes=len(cores),
          original_classes=len(known),total_classes=len(records),new_counts=totals,cores=coverage,new_shapes=new))
    print("core edges",core_edges,"core classes",len(cores),"long parents",len(records),
          "new by length",dict(totals),"first",new[0]["id"] if new else None)


if __name__=="__main__":
    main()
