"""Reconstruct every minimum-debt local candidate directly from nine-bit vertices."""
import json
from pathlib import Path
root=Path(__file__).resolve().parent
report={}
for log in sorted(root.glob('anchor_walk_[0-9]*.log')):
    results=[line.split() for line in log.read_text().splitlines() if line.startswith('BEST ')]
    if not results:
        continue
    row=min(results,key=lambda r:int(r[4]))
    anchors=list(map(int,row[8:]))
    if len(set(anchors))!=len(anchors):
        continue
    path=[anchors[0]]
    for u,v in zip(anchors, anchors[1:]):
        mid=[x for x in range(512) if (x^u).bit_count()==1 and (x^v).bit_count()==1]
        path.extend((min(mid,key=lambda m:sum((w^m).bit_count()==1 for w in anchors)),v))
    assert all((u^v).bit_count()==1 for u,v in zip(path,path[1:]))
    chords=[[i,j] for j,x in enumerate(path) for i in range(j-1) if (path[i]^x).bit_count()==1]
    report[log.name]=dict(edges=len(path)-1,distinct=len(set(path)),pairs=len(path)*(len(path)-1)//2,chords=chords,vertices=path)
    assert len(chords)==int(row[4])
print(json.dumps(report,indent=2))
