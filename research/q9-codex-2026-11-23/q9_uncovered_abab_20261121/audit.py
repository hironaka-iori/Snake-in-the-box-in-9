from collections import Counter
import json,re,sys
from pathlib import Path
d=Path(__file__).resolve().parent
r=d.parent
def path(w):
    p=[0]
    for c in w:p.append(p[-1]^1<<int(c))
    return p
def canon(w):
    def norm(w):
        t={}
        return ''.join(str(t.setdefault(k,len(t))) for k in w)
    return min(norm(w),norm(w[::-1]))
def checked(p):
    assert len(p)==len(set(p)) and all(0<=v<512 for v in p)
    for i,x in enumerate(p):
        for j in range(i+1,len(p)):
            assert ((x^p[j]).bit_count()==1)==(j==i+1)
ar=(r/'q9_gap_generations/prior191.words').read_text().split()
archive={canon(w):i for i,w in enumerate(ar)}
assert len(archive)==131
for w in ar:checked(path(w))
poses=[json.loads(s) for s in (d/'poses.jsonl').read_text().splitlines()]
data=[list(map(int,s.split())) for s in (d/'poses.dat').read_text().splitlines()]
assert len(poses)==len(data)
for z,pts in zip(poses,data):
    assert z['a']!=z['b'] and pts[:192]==path(ar[z['a']])
    m,t=z['m'],z['t'];assert set(m)==set(range(9))
    assert pts[192:]==[t^sum(1<<m[j] for j in range(9) if x>>j&1) for x in path(ar[z['b']])]
    assert len(set(pts[:192])&set(pts[192:]))==z['overlap']
counts={};seen=set();records={};outside={};witnesses191=0
for name in sys.argv[1:]:
    fn=d/(name+'.witness');c=Counter();known=set()
    for line in fn.read_text().splitlines():
        n,idx,flip,l,u,*rest=map(int,line.split());ends=rest[:8];bridges=rest[8:11];pp=rest[11:]
        assert len(pp)==n+1;checked(pp); c['verified']+=1
        src=[data[idx][:192],data[idx][192:]];z=poses[idx]
        S=set(src[0]);T=set(src[1]); seq=[]; arcs=[];order=[]
        for i in range(4):
            s,e=ends[2*i:2*i+2];bank=flip^(i%2);direction=1 if s<e else -1
            v=[src[bank][k] for k in range(s,e+direction,direction)]
            assert len(v)>=7 and set(v)-set(src[1-bank]);arcs.append(v)
            order.append((s,e))
            seq+=v
            if i<3 and bridges[i]>=0:
                assert bridges[i] not in S|T
                seq.append(bridges[i])
        for i in range(2):
            a,b=order[i];s,e=order[i+2]
            assert max(min(a,b),min(s,e))>min(max(a,b),max(s,e))+1
        def monotone(i):
            a,b=order[i];s,e=order[i+2]
            return a<b<s<e or a>b>s>e
        assert not monotone(0) or not monotone(1)
        assert pp[l:len(pp)-u]==seq
        w=canon(''.join(str((x^y).bit_length()-1) for x,y in zip(pp,pp[1:])))
        if n>=191:
            witnesses191+=1; seen.add(w);record=archive.get(w)
            if record is not None:known.add(record)
            else:outside[w]=pp
            nb=sum(x>=0 for x in bridges);intr=sum(v not in S|T for v in pp)
            c['long']+=1;c['long_neither_parent']+=record not in (z['a'],z['b'])
            c['long_with_free_bridge']+=nb>0
            c['long_with_two_free_bridges']+=nb>=2
            val=(record not in (z['a'],z['b']),nb,intr,min(map(len,arcs)))
            if w not in records or val>records[w][0]:
                records[w]=(val,dict(run=name,a=z['a'],b=z['b'],row=record,pose=idx,flip=flip,arcs=order,bridges=bridges,caps=[l,u],outside_both=intr,normalized=w,vertices=pp))
    if name=='recovered':
        assert 35 in known and all(poses[int(z.split()[1])]['a']==63 and poses[int(z.split()[1])]['b']==93 for z in fn.read_text().splitlines())
    counts[name]=dict(c,archive_class_count=len(known))
best=sorted(records.values(),key=lambda z:z[0],reverse=True)
summary=dict(pose_count=len(poses),pair_count=len({(z['a'],z['b']) for z in poses}),distinct_parents=len({z[k] for z in poses for k in ('a','b')}),runs=counts,verified191plus_rows=witnesses191,distinct191plus=len(seen),outside_131=len(outside),best={k:v for k,v in best[0][1].items() if k not in ('normalized','vertices')})
(d/'audit.json').write_text(json.dumps(summary,indent=2)+'\n')
(d/'long.jsonl').write_text(''.join(json.dumps(v,separators=(',',':'))+'\n' for _,v in best))
(d/'outside_131.words').write_text(''.join(w+'\n' for w in sorted(outside)))
print(json.dumps(summary,indent=2))
