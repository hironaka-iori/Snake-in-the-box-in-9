"""Enumerate the complete Q7 isometry group acting on the 47-edge middle."""
from collections import Counter
from hashlib import sha256
from itertools import permutations
from pathlib import Path
import json

HERE=Path(__file__).resolve().parent
PREV=HERE.parent/"246-eight-dimensional-parents"


def mask(path):
    return sum(1<<v for v in path)


def coordinate_table(axes):
    image=[0]
    for j in axes:
        image += [v^(1<<j) for v in image]
    return image


def main():
    raw=(PREV/"middle.json").read_bytes()
    path,reference=json.loads(raw)["layouts"][0]["middles"]
    fixed=mask(path)
    counts=Counter()
    disjoint=[]
    stabilizers=[]
    low=[mask(v for v in range(128) if not(v&(1<<i))) for i in range(7)]
    for perm in permutations(range(7)):
        lut=coordinate_table(perm)
        mapped=[lut[v] for v in path]
        translations=[mask(mapped)]
        for i in range(7):
            shift=1<<i
            translations += [((s&low[i])<<shift)|((s>>shift)&low[i]) for s in translations]
        for t,s in enumerate(translations):
            size=(fixed&s).bit_count()
            counts[size]+=1
            if size==0 or size==48:
                actual=[v^t for v in mapped]
                if mask(actual)!=s:
                    raise ValueError("Translation mismatch")
                row=dict(axes=perm,translation=t,path=actual)
                (disjoint if size==0 else stabilizers).append(row)
    if sum(counts.values())!=645120 or len(path)!=48 or not any(set(r["path"])==set(reference) for r in disjoint):
        raise ValueError("Missing isometry or recorded placement")
    result=dict(input_sha256=sha256(raw).hexdigest(),source_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
                first=path,reference=reference,intersection_histogram=counts,disjoint=disjoint,stabilizers=stabilizers)
    (HERE/"orbit.json").write_text(json.dumps(result,separators=(",",":"))+"\n",encoding="utf-8",newline="\n")
    print("all",sum(counts.values()),"disjoint",len(disjoint),"distinct sets",len({mask(r["path"]) for r in disjoint}),
          "stabilizers",len(stabilizers),"one extra contact",counts[1])


if __name__=="__main__":
    main()
