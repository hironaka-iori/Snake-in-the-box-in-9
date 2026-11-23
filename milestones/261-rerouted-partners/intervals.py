"""Transfer compatible segments and optimise one short interval replacement per seed."""
from collections import Counter
from pathlib import Path
import sys
from regrow import HERE,MS,load,save,digest,bank,growth
sys.path.insert(0,str(MS/"252-shorter-reference-segments"))
from replay_core import word

N=[[v^(1<<d) for d in range(8)] for v in range(256)]
M=[sum(1<<u for u in row) for row in N]

def bridge(path,parent,i,j,length):
    a,b=path[i],path[j]
    if length>1 and (a^b).bit_count()==1: return None
    keep=path[:i]+path[j+1:]
    banned=sum(1<<v for v in set(parent[1:])|set(keep)|{a,b})
    for v in keep: banned|=M[v]
    def visit(tip,remaining,blocks):
        if (tip^b).bit_count()>remaining: return None
        if remaining==1: return [b] if (tip^b).bit_count()==1 else None
        options=M[tip]&~blocks
        if remaining==2: options &= M[b]
        else: options &= ~M[b]
        while options:
            edge=options&-options
            options^=edge
            u=edge.bit_length()-1
            rest=visit(u,remaining-1,blocks|edge|M[tip])
            if rest is not None: return [u]+rest
        return None
    middle=visit(a,length,banned)
    return path[:i+1]+middle+path[j+1:] if middle is not None else None

if __name__=="__main__":
    files=[HERE/"growth.json",MS/"255-parity-exchange-arms/constructive.json",MS/"257-three-exchange-parents/constructed-51.json"]
    groups=[load(f)["cases"] for f in files]
    donors=list({word(r["partner"]):r["partner"] for group in groups for r in group.values()}.values())
    words,origins=bank.donor_suffixes(donors)
    images=list(bank.permutation_images())
    cases={}
    for key,row in sorted(groups[0].items()):
        parent=row["rooted_parent"]
        allowed=bank.allowed_maps(parent,images)
        fit=bank.longest(words,allowed)
        w=bank.make_witness(donors,origins[fit[1]],fit,parent)
        seed=w["partner"]
        bank.exclude_next(donors,words,allowed,fit[0]+1)
        best=seed
        edit=None
        for increment in (6,4,2):
            for i in range(len(seed)-2):
                for j in range(i+2,min(i+9,len(seed))):
                    best=bridge(seed,parent,i,j,j-i+increment)
                    if best is not None:
                        edit=[i,j,increment]
                        break
                if edit: break
            if edit: break
        if best is None: best=seed
        record=growth.check_join(parent,best)
        record.update(seed=seed,bank_edges=fit[0],rooted_parent=parent,edit=edit,
                      prior_join=row["previous_join"],growth_join=row["joined_edges"])
        cases[key]=record
    save(HERE/"intervals.json",dict(donor_shapes=len(donors),cases=cases,
        inputs={f.name:digest(f) for f in [*files,Path(__file__)]}))
    print("best",max(r["joined_edges"] for r in cases.values()),"improved roots",
          sum(r["joined_edges"]>r["prior_join"] for r in cases.values()),
          "interval gains",Counter(r["joined_edges"]-97-r["bank_edges"] for r in cases.values()))
