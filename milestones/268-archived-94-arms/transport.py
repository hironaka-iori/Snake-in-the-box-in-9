"""Transport published 96-edge exclusions into first-step domains of a 97-edge partner."""
from pathlib import Path
from search import HERE, roots, bank, read, write


def sources():
    prior=HERE.parent/"267-fixed-arm-extensions"
    cases=read(prior/"cases.json")["roots"]
    covered=read(prior/"summary.json")["coverage"]
    return {k:cases[k]["parent"][1:] for k in covered if len(cases[k]["parent"])==96}


def find_transfers():
    masks=sources()
    images=list(bank.permutation_images())
    roots_data=roots()
    hits={}
    for k,r in roots_data.items():
        parent=set(r["parent"])
        steps={}
        for s in (1 << j for j in range(8)):
            if s in parent:
                continue
            blocked={v^s for v in range(256) if v in parent or (v!=s and v.bit_count()==1)}
            # A set bit means that the image of this nonzero vertex is blocked.
            maps=bank.allowed_maps([0]+sorted(set(range(1,256))-blocked),images)
            for name,mask in masks.items():
                live=bank.ALL_MAPS
                for v in mask:
                    live &= maps[v]
                    if not live:break
                if live:
                    rank=(live & -live).bit_length()-1
                    assert set(bytes(mask).translate(images[rank]))<=blocked
                    steps[str(s)]=dict(source=name,rank=rank)
                    break
        hits[k]=steps
    write(HERE/"transfers.json",hits)
    print("Rooted first-step exclusions",sum(len(v) for v in hits.values()),"of",
          sum(sum(1<<d not in r["parent"] for d in range(8)) for r in roots_data.values()),
          "affected roots",sum(bool(v) for v in hits.values()))

if __name__=="__main__":
    find_transfers()
