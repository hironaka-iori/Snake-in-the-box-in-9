"""Independent verification of candidates, saved state and actual elapsed time."""
import json,sys,time
from pathlib import Path
from collections import Counter
root=Path(__file__).resolve().parent
bank=set((root/'known191.txt').read_text().split());assert len(bank)==131
def verify(vertices):
    assert vertices and len(set(vertices))==len(vertices) and all(0<=x<512 for x in vertices)
    assert all(((x^y).bit_count()==1)==(j==i+1) for i,x in enumerate(vertices) for j,y in enumerate(vertices) if j>i)
    steps=[x^y for x,y in zip(vertices,vertices[1:])]
    def canonical(s):
        m={};return ''.join(str(m.setdefault(d,len(m))) for d in s)
    signature=min(canonical(steps),canonical(steps[::-1]))
    counts=sorted(Counter(steps).values(),reverse=True)
    return len(steps),signature,counts+[0]*(9-len(counts))
def check(label):
    old=(root/(label+'.log')).read_text().splitlines()
    seed=list(map(int,(root/(label+'.txt')).read_text().split()));seed_edges,_,_=verify(seed)
    accepted=[];rejected=[];targets=[];ext=[];end={};elapsed=None
    for ln in old:
        f=ln.split()
        if f[0]=='START':assert int(f[1])>=0
        elif f[0]=='END':end={f[i]:int(f[i+1]) for i in range(1,len(f),2)}
        elif f[0]=='ELAPSED':elapsed=float(f[1])
        elif f[0] in ('SNAKE','KNOWN_CANDIDATE','TARGET','EXTENDED'):
            v=list(map(int,f[5:] if f[0]=='SNAKE' else f[3:]));n,s,counts=verify(v);assert n==int(f[2]);step=int(f[1]);known=s in bank
            rec=dict(step=step,edges=n,dcv=counts,known191=known,vertices=v)
            if f[0]=='SNAKE':
                assert int(f[3])==counts[0] and bool(int(f[4]))==known;accepted.append(rec)
            elif f[0]=='KNOWN_CANDIDATE':
                assert known and n==191;rejected.append(rec)
            elif f[0]=='TARGET':
                assert n>=192 or n==191 and not known;targets.append(rec)
            else:assert n>=192;ext.append(rec)
    f=(root/(label+'.ckpt')).read_text().split()
    assert f[0]=='Q9S1';step=int(f[1]);wall=float(f[3]);occ=set(map(int,f[11:]));assert len(occ)==int(f[10])
    rem=set(occ);cc=0;maxcomp=0
    while rem:
        group=[rem.pop()];edges=0
        for x in group:
            nb={x^(1<<i) for i in range(9)}&occ
            assert len(nb)<=2;edges+=len(nb)
            for y in nb&rem:rem.remove(y);group.append(y)
        assert edges//2==len(group)-1;cc+=1;maxcomp=max(maxcomp,len(group))
    best=max(accepted,key=lambda x:x['edges']) if accepted else None
    if end:
        assert end['best']==(best['edges'] if best else -1) and end['proposals']==step
    for hit in targets:
        if hit['edges']!=191:continue
        p=hit['vertices'];possible=[]
        for rev in (False,True):
            q=p[::-1] if rev else p
            for i in range(9):
                w=q[-1]^(1<<i)
                if w not in q and all((v^w).bit_count()!=1 for v in q[:-1]):possible.append((rev,i))
        assert len(possible)==len(ext)
    return dict(label=label,seed_edges=seed_edges,step=step,checkpoint_elapsed=wall,checkpoint_components=cc,largest_component_edges=maxcomp-1,best=best,first_rejected=rejected,targets=targets,extended=ext,end=end,reported_elapsed=elapsed)
if __name__=='__main__':
    states=[check(n) for n in ['A','B']]
    if '--save' in sys.argv:
        completion=json.loads((root/'completed.json').read_text());assert len(completion)==2
        for state,record in zip(states,completion):
            assert state['label']==record['id'] and (state['end'] or state['targets'])
            if not state['targets']:assert record['end_unix']-record['start_unix']>=3899
        (root/'results.json').write_text(json.dumps(dict(runs=states,completion=completion),indent=1)+'\n')
    print([(s['label'],s['step'],round(s['checkpoint_elapsed']),s['best']['edges'] if s['best'] else None,len(s['targets']),len(s['extended'])) for s in states])
