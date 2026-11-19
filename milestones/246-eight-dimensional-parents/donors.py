"""Extract Q8 donor shapes from dimension cuts and legal endpoint growth."""
from collections import Counter
from hashlib import sha256
import csv
import json
import zipfile

from compare import HERE, ROOT, extensions, signature, verify


def main():
    comp=json.loads((HERE/"comparison.json").read_bytes())
    saved=json.loads((HERE.parent/"244-190-path-construction/results.json").read_bytes())
    bank=json.loads((ROOT/"work/bank9.json").read_bytes())
    with zipfile.ZipFile(ROOT/"work/record_snakes.csv.zip") as z:
        raw=z.read("snakes_dim9_190.csv")
    if sha256(raw).hexdigest()!=saved["member_sha256"]:
        raise ValueError("Parent archive changed")
    shapes={}
    def store(path,origin):
        key=signature(path)
        if key not in shapes:
            verify(path,False)
            if min(path)<0 or max(path)>=256:
                raise ValueError("Invalid projection")
            shapes[key]={"path":path,"origin":origin}

    def windows(segment,source):
        for length in range(93,min(len(segment),99)):
            for offset in range(len(segment)-length):
                store(segment[offset:offset+length+1],source+[offset])

    windows(comp["examples"]["optimal_98"]["path"],["Q8 optimal representative"])
    paths190=(list(map(int,row["vertices"].split())) for row in csv.DictReader(raw.decode().splitlines()))
    for label,paths in (("191", (r["vertex_sequence"] for r in bank)),("190",paths190)):
        for i,path in enumerate(paths):
            for axis in range(9):
                start=0
                for end in [k for k in range(len(path)-1) if path[k]^path[k+1]==1<<axis]+[len(path)-1]:
                    if end-start>=93:
                        lower=(1<<axis)-1
                        segment=[(v&lower)|((v>>(axis+1))<<axis) for v in path[start:end+1]]
                        windows(segment,[label,i,axis,start])
                    start=end+1
    initial=Counter(len(v["path"])-1 for v in shapes.values())
    for length in range(93,98):
        for record in list(shapes.values()):
            path=record["path"]
            if len(path)!=length+1:
                continue
            for new in extensions(path):
                side,vertex=("left",new[0]) if new[0]!=path[0] else ("right",new[-1])
                store(new,["end addition",signature(path).hex(),side,vertex])
    final=Counter(len(v["path"])-1 for v in shapes.values())
    (HERE/"donors.json").write_text(json.dumps(dict(parent_member_sha256=saved["member_sha256"],
         initial=initial,final=final,shapes=list(shapes.values())),separators=(",",":"))+"\n",encoding="utf-8",newline="\n")
    print("before endpoint closure",dict(sorted(initial.items())),"after",dict(sorted(final.items())))


if __name__=="__main__":
    main()
