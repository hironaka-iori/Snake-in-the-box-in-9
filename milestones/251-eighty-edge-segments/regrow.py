"""Construct longer rooted partners by changing corners and regrowing suffixes."""
from hashlib import sha256
import json
from pathlib import Path
from random import Random

from partners251 import witness, verified_partner, rooted, read
import bank as donor_search

HERE = Path(__file__).resolve().parent
ALL=(1<<256)-1
NEIGHBOURS=[sum(1<<(x^(1<<j)) for j in range(8)) for x in range(256)]


def improve(parent, initial, seed):
    outside=ALL ^ sum(1<<x for x in parent)
    random=Random(seed)
    best=list(initial)
    total=0
    for attempt in range(180):
        p=best.copy()
        # A changed corner introduces the other common neighbour of its two flanks.
        for _ in range(attempt%4):
            i=random.randrange(1,len(p)-1)
            v=p[i-1]^p[i]^p[i+1]
            used=sum(1<<x for x in p)
            if outside&(1<<v) and not used&(1<<v) and (
                    NEIGHBOURS[v]&used)==((1<<p[i-1])|(1<<p[i+1])):
                p[i]=v
        keep=random.randrange(1,len(p))
        del p[keep:]
        free=outside
        for vertex in p[:-1]:
            free &= ~(NEIGHBOURS[vertex] | (1<<vertex))
        nodes=0
        def visit(free):
            nonlocal nodes,best
            nodes+=1
            if len(p)>len(best):
                best=p.copy()
            tip=p[-1]
            choices=NEIGHBOURS[tip]&free
            new_free=free & ~(NEIGHBOURS[tip] | (1<<tip))
            moves=[]
            while choices:
                bit=choices&-choices
                choices-=bit
                v=bit.bit_length()-1
                moves.append(((NEIGHBOURS[v]&new_free).bit_count(),random.random(),v))
            if attempt%3:
                moves.sort()
            else:
                random.shuffle(moves)
            for _,__,v in moves:
                if nodes>=3500: break
                p.append(v)
                visit(new_free)
                p.pop()
        visit(free)
        total+=nodes
    return best,total


def main():
    donors_path=HERE.parent/"246-eight-dimensional-parents"/"donors.json"
    sources=[HERE/"census-72.json",HERE/"profiles.json",HERE/"profile-audit.json",Path(__file__),
             HERE/"bank.py",donors_path]
    donors=[r["path"] for r in read(donors_path)["shapes"]]
    shapes=read(sources[0])["new_shapes"]
    profiles={(r["id"],r["end"]):r for r in read(sources[1])["roots"]}
    upper={(r["id"],r["end"]):r["partner_upper"] for r in read(sources[2])["bounds"]}
    result=[]
    for i,row in enumerate(shapes):
        for end in (0,1):
            key=row["id"],end
            parent=rooted(row["path"],end)
            bank=HERE/f"bank-capacity-{i}-{end}.json"
            sources.append(bank)
            b=read(bank)
            if (b["id"],b["end"])!=key: raise ValueError("Bank root mismatch")
            bank_max=b["witness"]["partner_edges"]
            verified_partner(parent,b["witness"],bank_max)
            words,records,tables=donor_search.library(donors,bank_max+1)
            if donor_search.first_fit(parent,words,records,tables) is not None:
                raise ValueError("Independent donor census exceeds the reported maximum")
            pr=profiles[key]
            initial=max([b["witness"],pr["initial"]]+[a for a in pr["attempts"] if a["status"]=="witness"],
                        key=lambda w:w["partner_edges"])
            verified_partner(parent,initial,initial["partner_edges"])
            path,nodes=improve(parent,initial["partner"],251+i*2+end)
            w=witness(parent,path)
            verified_partner(parent,w,w["partner_edges"])
            if w["partner_edges"]>upper[key]: raise ValueError("Witness exceeds checked cap")
            result.append(dict(id=key[0],end=end,bank_max=bank_max,
                               checked_next_length_classes=len(words),checked_axis_maps=40320,
                               initial=initial["partner_edges"],nodes=nodes,partner_upper=upper[key],**w))
            print(i,end,"bank",b["witness"]["partner_edges"],"start",initial["partner_edges"],
                  "best",w["partner_edges"],"upper",upper[key],flush=True)
    out=dict(inputs={s.name:sha256(s.read_bytes()).hexdigest() for s in sources},cases=result)
    (HERE/"regrowth-witnesses.json").write_text(json.dumps(out,indent=2)+"\n",encoding="utf-8",newline="\n")


if __name__=="__main__":
    main()
