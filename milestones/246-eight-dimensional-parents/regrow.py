"""Seek an unrestricted 96-edge partner after cutting back each one-conflict arm."""
from hashlib import sha256
import json
from compare import HERE, N
from placements import permute, rooted, verify

NEAR=[sum(1<<u for u in ns) for ns in N]


def complete(prefix, avoid):
    ban=sum(1<<v for v in set(avoid)|set(prefix))
    for v in prefix[:-1]:
        ban |= NEAR[v]
    path=list(prefix)
    nodes=0
    best=len(prefix)-1
    limit=500000
    def visit(blocked):
        nonlocal nodes,best
        nodes+=1
        best=max(best,len(path)-1)
        if len(path)==97:
            return list(path)
        v=path[-1]
        free=NEAR[v]&~blocked
        while free and nodes<limit:
            bit=free&-free
            free^=bit
            path.append(bit.bit_length()-1)
            found=visit(blocked|NEAR[v]|bit)
            path.pop()
            if found:
                return found
        return None
    result=visit(ban)
    status="witness" if result else ("budget" if nodes>=limit else "excluded")
    return dict(status=status,nodes=nodes,best_edges=best,path=result)


def main():
    data=(HERE/"placements.json").read_bytes()
    entries=json.loads(data)["records"]
    donor_data=(HERE/"donors.json").read_bytes()
    donors=[r["path"] for r in json.loads(donor_data)["shapes"]]
    cache={}
    records=[]
    witness=None
    for row in entries:
        if row["scope"]!="target_192" or row["min_extra_overlap"]!=1:
            continue
        old=[permute(v,row["axis_image"]) for v in rooted(donors[row["long_donor"]],row["long_endpoint"])]
        other=rooted(donors[row["short_donor"]],row["short_endpoint"])
        conflict,=set(old[1:])&set(other[1:])
        index=old.index(conflict)
        cases=[]
        for length in sorted({index-1,80,72,64,56,48,40,32,24,16,8,0},reverse=True):
            if length>=index:
                continue
            prefix=tuple(old[:length+1])
            key=(prefix,tuple(other))
            if key not in cache:
                cache[key]=complete(prefix,other)
            result=cache[key]
            cases.append(dict(prefix_edges=length,**result))
            if result["path"]:
                witness=result["path"][::-1]+[256+v for v in other]
                if len(witness)!=193:
                    raise ValueError("Wrong join length")
                verify(witness,9)
                break
        records.append(dict(long_donor=row["long_donor"],short_donor=row["short_donor"],
                            conflict=conflict,index=index,cases=cases))
        if witness:
            break
    output=dict(input_sha256=sha256(data).hexdigest(),donors_sha256=sha256(donor_data).hexdigest(),
                node_cap=500000,unique_queries=len(cache),cases=records,witness=witness)
    (HERE/"regrow.json").write_text(json.dumps(output,separators=(",",":"))+"\n",encoding="utf-8",newline="\n")
    for row in records:
        print(row["long_donor"],[(r["prefix_edges"],r["status"]) for r in row["cases"]])


if __name__=="__main__":
    main()
