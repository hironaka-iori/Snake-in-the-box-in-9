"""Rank motif-free 189-edge seeds by their longest contiguous agreement with a 191 record."""
from pathlib import Path
import json
from offspring import canon
D=Path(__file__).resolve().parent
A=(D.parent/'q9_far189_spring_20261121/comparison191.words').read_text().split()
S=[w for w,m in json.loads((D/'motif_counts.json').read_text())['seeds'] if not m]
cache={}
def find(w,n):
    if n not in cache:cache[n]={canon(a[i:i+n]) for a in A for i in range(len(a)-n+1)}
    return any(canon(w[i:i+n]) in cache[n] for i in range(len(w)-n+1))
def length(w):
    low,high=0,len(w)+1
    while high-low>1:
        n=(low+high)//2
        if find(w,n):low=n
        else:high=n
    return low
# A suffix tree is unnecessary for this fixed catalogue; normalize each window separately.
result=sorted((length(w),w) for w in S)
(D/'ranked.json').write_text(json.dumps(result,indent=1))
(D/'distant.words').write_text(''.join(w+'\n' for _,w in result[:12]))
