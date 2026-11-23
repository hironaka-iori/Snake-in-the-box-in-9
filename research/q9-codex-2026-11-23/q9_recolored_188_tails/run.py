from bank import *
from solver import solve
import sys
collection,number,seed,cap=sys.argv[1:];rng=random.Random(int(seed));cap=int(cap)
real=(r/'q9_gap_generations/prior191.words').read_text().split()
assert all(len(w)==191 and valid(ax(map(int,w))) for w in real)
q8=json.loads((d/'q8_bank.json').read_text())
explicit=trans(json.loads((r/'q9_explicit_q8_96_plus_94.json').read_text())['vertices'])
def parts(ds):
    if not ds:yield ();return
    a,*rest=ds
    for b in rest:
        for tail in parts([v for v in rest if v!=b]):yield ((a,b),)+tail
allparts=[(pr,s) for s in range(9) for pr in parts([v for v in range(9) if v!=s])]
used=set()
for t in range(int(number)):
    target=(192,195,196,192,192,195,196,192)[t%8]
    if target==192:corelen=188;l,rh=2,2
    elif target==195:
        corelen=188 if t%16==1 else 191;l,rh=(3,4) if corelen==188 else (2,2)
    else:
        corelen=188 if t%16==2 else (192 if collection=='q8' else 191)
        l,rh={188:(4,4),191:(2,3),192:(2,2)}[corelen]
    if rng.randrange(2):l,rh=rh,l
    while True:
        if collection=='public':
            idx=rng.randrange(len(real));offset=rng.randrange(192-corelen);w=real[idx][offset:offset+corelen]
        elif collection=='knownq8':
            idx=0;offset=rng.randrange(192-corelen);w=explicit[offset:offset+corelen]
        else:
            idx=rng.randrange(len(q8[str(corelen)]));offset=0;w=q8[str(corelen)][idx]['word']
        pi=rng.randrange(len(allparts));ps,s=allparts[pi];key=(w,pi,l,rh)
        if key not in used:used.add(key);break
    st,path,k=solve(list(map(int,w)),ps,s,l,rh,cap)
    rec=dict(collection=collection,idx=idx,offset=offset,group=pi,ps=ps,s=s,left=l,right=rh,target=target,w=w,status=st,conflicts=k)
    if path:
        assert len(path)==target+1 and valid(path)
        rec['path']=path
    print(json.dumps(rec,separators=(',',':')),flush=True)
    if path:break
