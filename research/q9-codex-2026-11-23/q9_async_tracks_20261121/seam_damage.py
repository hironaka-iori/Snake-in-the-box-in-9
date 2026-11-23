from generate import D,words,defects
import random,json
rn=random.Random(50813);cs=list(map(json.loads,(D/'control_975413.jsonl').read_text().splitlines()))
kept=[]
for i,r in enumerate(cs):
    g=list(r['groups']);w=r['word'];t=list(w);modified=[]
    a,b=r['patches'];seams=[q for p in (a,b) for q in (p['at'],p['at']+p['L']) if q>1 and q<len(w)-2]
    rn.shuffle(seams)
    for j in seams:
        if g[int(t[j-1])]==g[int(t[j])]:continue
        if any(abs(j-k)<3 for k in modified):continue
        t[j-1],t[j]=t[j],t[j-1];modified.append(j)
        if len(modified)==2:break
    v=''.join(t)
    if len(modified)!=2 or not defects(v):continue
    original=words[r['a']][::-1] if r['rev'] else words[r['a']]
    def cp(w,j):return tuple(sum(g[int(x)]==k for x in w[:j]) for k in range(3))
    if not all(cp(v,j)!=cp(original,j) for j in modified):continue
    kept.append(dict(parent_control=i,raw=v,seams=sorted(modified),groups=''.join(map(str,g)),defects=defects(v)))
    if len(kept)==120:break
(D/'seam_damage.jsonl').write_text(''.join(json.dumps(z,separators=(',',':'))+'\n' for z in kept))
with (D/'seam_damage.in').open('w') as f:
    for z in kept:print(z['raw'],z['groups'],0,3,143,9,file=f)
