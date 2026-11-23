"""Find every rooted 96-edge catalogue arm containing a proved forbidden set."""
from pathlib import Path
import sys
from masks import HERE,MS,load,save,digest,bank,groups

def placements(blocked,parent,images):
    # No translation remains after the joining vertex is normalized to zero.
    weights=[sum(v.bit_count()==w for v in parent) for w in range(9)]
    if any(sum(v.bit_count()==w for v in blocked)>weights[w] for w in range(9)): return []
    allowed=bank.allowed_maps([0]+sorted(set(range(1,256))-parent),images)
    possible=bank.ALL_MAPS
    for u in sorted(blocked,key=lambda v:allowed[v].bit_count()):
        possible &= allowed[u]
        if not possible: return []
    found=[]
    while possible:
        bit=possible&-possible
        rank=bit.bit_length()-1
        if not {images[rank][u] for u in blocked}<=parent: raise ValueError("Wrong containment")
        found.append(rank)
        possible^=bit
    return found

if __name__=="__main__":
    areas=groups()
    source=load(HERE/"groups.json")
    masks={}
    for tag,row in source.items():
        if set(row["blocked"])!=set.intersection(*areas[int(tag)].values()) or set(row["members"])!=areas[int(tag)].keys():
            raise ValueError("Group definition differs")
        if row["status"]=="excluded": masks[tag]=set(row["blocked"])
    files=[(MS/"253-repeated-segment-growth/closure.json","paths"),(MS/"254-distant-arm-partners/parity-families.json","shapes"),
        (MS/"255-parity-exchange-arms/focus-closure.json","paths"),(MS/"258-four-exchange-parents/new-arms.json","shapes"),
        (MS/"259-four-exchange-component/new-arms.json","shapes")]
    shapes={}
    for f,key in files: shapes.update(load(f)[key])
    # Use the distant shell's ordered representative for reporting endpoint numbers.
    shapes.update(load(MS/"257-three-exchange-parents/partner-input.json")["shapes"])
    maps=list(bank.permutation_images())
    covered={}
    for k,path in sorted(shapes.items()):
        if len(path)!=97: continue
        for end,root in enumerate((path[0],path[-1])):
            P={v^root for v in path if v!=root}
            for tag,F in masks.items():
                hits=placements(F,P,maps)
                if hits: covered.setdefault(k+":"+str(end),{})[tag]=hits
    save(HERE/"transfer.json",dict(source_sha256=digest(HERE/"groups.json"),source_code=digest(Path(__file__)),
        reference_paths={k:p for k,p in shapes.items() if len(p)==97},covered=covered,
        complete_roots=2*sum(len(p)==97 for p in shapes.values())))
    print("certified masks",list(masks),"rooted cases",len(covered),"both ends",sum(k.endswith(":0") and k[:-1]+"1" in covered for k in covered))
