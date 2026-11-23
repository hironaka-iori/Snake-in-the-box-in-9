from pathlib import Path
import gzip,itertools,json,collections
D=Path(__file__).resolve().parent;R=D.parent
seen=set();out={};sources=collections.Counter()
def rem(v,a):return (v&((1<<a)-1))|((v>>(a+1))<<a)
def tryit(first,second,source):
    # Both arms begin at the common crossing. Permitted full paths use two lower endpoints.
    A0=first[:96];B0=second[:96]
    def clean(v):
        seen=set()
        for i,t in enumerate(v):
            if t in seen or (i and sum((t^(1<<j)) in seen for j in range(8))!=1):return v[:i]
            seen.add(t)
        return v
    A0=clean(A0);B0=clean(B0)
    if len(A0)+len(B0)<180:return
    for Bn in range(len(B0),max(0,len(B0)-10),-1):
        bb=B0[:Bn];blk=set(bb[1:]);end=bb[-1];near={end}|{end^(1<<i) for i in range(8)}
        A=[]
        for x in A0:
            if x in blk or x in near:break
            A.append(x)
        if len(A)<2 or len(A)+Bn<180:continue
        names={};arms=[]
        for arm in (A,bb):
            q=[0]
            for u,v in zip(arm,arm[1:]):q.append(q[-1]^(1<<names.setdefault((u^v).bit_length()-1,len(names))))
            arms.append(tuple(q))
        key=tuple(arms)
        if key not in out:out[key]=source;sources[source]+=1
        break
def handle(p,src):
    steps=tuple((a^b).bit_length()-1 for a,b in zip(p,p[1:]))
    if steps in seen:return
    seen.add(steps)
    for d in range(9):
        breaks=[j+1 for j,v in enumerate(steps) if v==d]
        ends=[0,*breaks,len(p)]
        for j in range(1,len(ends)-1):
            lo,mid,hi=ends[j-1:j+2]
            if min(mid-lo,hi-mid)<75 or min(96,mid-lo)+min(96,hi-mid)<180:continue
            arms=[[rem(v,d) for v in reversed(p[lo:mid])],[rem(v,d) for v in p[mid:hi]]];assert arms[0][0]==arms[1][0]
            tryit(*arms,src);tryit(*arms[::-1],src)
for l in gzip.open(R/'q9_port_followup_public191.txt.gz','rt'):handle(list(map(int,l.split())),'public191')
files=['q9_far189_spring_20261121/additional/comparison190.words','q9_far189_spring_20261121/additional/comparison191.words','q9_far189_spring_20261121/gap_190.words','q9_gap_known190.words','q9_gap_generations/prior190.words','q9_three_axis.in']
for fn in files:
    for l in (R/fn).read_text().splitlines():
        w=l.strip()
        if not w or set(w)-set('012345678'):continue
        p=[0]
        for z in w:p.append(p[-1]^(1<<int(z)))
        handle(p,fn)
with (D/'short_seeds.txt').open('w') as f:
    for a,b in sorted(out,key=lambda k:-(len(k[0])+len(k[1]))):print(len(a),len(b),*a,*b,file=f)
print(json.dumps(dict(sources=sources,words=len(seen),seeds=len(out),best=max(map(lambda k:len(k[0])+len(k[1]),out)))))
