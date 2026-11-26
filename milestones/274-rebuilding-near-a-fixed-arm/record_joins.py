"""Compare the longest placements and their complete Q9 tip extensions to the published 191 paths."""
from near import HERE,MS,read,write,shape,valid
from collections import Counter
def grow(p):
    used=set(p)
    for k in range(9):
        v=p[-1]^(1<<k)
        if v not in used and all((v^w).bit_count()!=1 for w in p[:-1]):yield v
def main():
    pool=read(HERE/"union-placements.json")["roots"]
    for f in (HERE/"face274").glob("*/summary.json"):
        source=f.parent.name
        for k,r in read(HERE/(source+"-placements.json"))["roots"].items():
            if r["best"]["edges"]>pool[k]["best"]["edges"]:
                pool[k]=r
    archive=read(MS.parent/"work/bank9.json")
    known={shape(r["vertex_sequence"]):i for i,r in enumerate(archive) if len(r["vertex_sequence"])==192}
    assert len(known)==131
    winners={};attaining={}
    for k,entry in pool.items():
        w=entry["best"];n=w["edges"]
        if n<191:continue
        p=w["joined"];pairs=valid(p,9);s=shape(p)
        ext=[list(grow(p[::-1])),list(grow(p))]
        row=winners.setdefault(s,dict(path=p,edges=n,root=k,parent=w["A"],partner=w["B"],pairs=pairs,
                                       bank_index=known.get(s),free_tip_extensions=ext))
        attaining[k]=s
        for left,tips in enumerate(ext):
            for v in tips:
                q=[v]+p if left==0 else p+[v]
                valid(q,9)
                write(HERE/("candidate-"+str(len(q)-1)+".json"),dict(path=q,edges=len(q)-1,root=k))
    write(HERE/"record-joins.json",dict(roots=attaining,shapes=winners,compared_191=len(known)))
    print("191+ attained roots",len(attaining),"different shapes",len(winners),"outside bank",sum(r["bank_index"] is None for r in winners.values()),"extendible",sum(any(r["free_tip_extensions"]) for r in winners.values()),flush=True)
if __name__=="__main__":main()
