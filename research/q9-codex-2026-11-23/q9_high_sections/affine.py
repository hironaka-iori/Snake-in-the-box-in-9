"""Two to four affine parity equations select a nine-dimensional section of a longer parent."""
from pathlib import Path
from itertools import combinations
from collections import defaultdict
from random import Random
from subprocess import run,TimeoutExpired
import sys,json
D=Path(__file__).resolve().parent;R=D.parent
sys.path.insert(0,str(R/'q9_change_basis'))
from check import audit

def setup(dim,forms):
    piv={}
    for h in forms:
        for p,v in sorted(piv.items(),reverse=True):
            if h&(1<<p):h^=v
        if not h:return None
        piv[h.bit_length()-1]=h
    visible=[a for a in range(dim) if a not in piv]
    assert len(visible)==9
    return [sum(((x>>a)&1)<<b for b,a in enumerate(visible)) for x in range(1<<dim)]

def main():
    dim,n,trials,seed=map(int,sys.argv[1:]);rng=Random(seed);data='donors.txt' if dim==11 else 'donors'+str(dim)+'.txt'
    bank=[list(map(int,line.split())) for line in (R/'q9_via_q10'/data).read_text().splitlines()]
    bank=[p[1:] for p in bank if p[0]==dim]
    # All vertices and all edges of the original high-dimensional path are checked once before sampling.
    for p in bank:
        ix={x:i for i,x in enumerate(p)};assert len(ix)==len(p) and min(ix)>=0 and max(ix)<1<<dim
        for i,x in enumerate(p):
            assert sorted(ix[x^(1<<d)] for d in range(dim) if x^(1<<d) in ix)==[j for j in (i-1,i+1) if 0<=j<len(p)]
    tested=set()
    for case in range(trials):
        j=rng.randrange(len(bank));parities=[]
        for i in range(dim-9):
            weight=rng.choice((1,1,1,2,2,3,4)) if i else rng.choice((2,2,3,4,dim))
            parities.append(sum(1<<a for a in rng.sample(range(dim),weight)))
        mapping=setup(dim,parities)
        if mapping is None:continue
        row=bank[j];slices=defaultdict(list)
        for v in row:slices[sum(((h&v).bit_count()%2)<<k for k,h in enumerate(parities))].append(mapping[v])
        possible=[(k,s) for k,s in slices.items() if n-6<=len(s)<=n+8]
        rng.shuffle(possible)
        for k,orig in possible[:3]:
            assert len(set(orig))==len(orig)
            cut=max(0,len(orig)-(n+1));st=rng.randrange(cut+1)
            pts=orig[st:len(orig)-(cut-st)] if cut>st else orig[st:]
            canon=tuple(sorted(pts))
            if canon in tested:continue
            tested.add(canon)
            try:
                cmd=[str(R/'q9_change_basis/focus'),str(n),'300000','0','grow']
                out=run(cmd,input='points '+' '.join(map(str,canon))+'\n',text=True,capture_output=True,timeout=8,check=True).stdout.splitlines()
                hit=next((l for l in out if l.startswith('FOUND')),None)
                stat='FOUND' if hit else ('UNKNOWN' if any('UNKNOWN' in l for l in out) else 'CLOSED')
            except TimeoutExpired:hit=None;stat='TIME_LIMIT'
            path=None
            if hit:
                path,b=audit(hit);inv=[0]
                for a in b:inv.extend([z^a for z in inv])
                assert set(canon)<={inv[x] for x in path} and len(path)==n+1
            print(json.dumps(dict(parent=j,dimension=dim,forms=parities,coset=k,skip_front=st,skip_back=cut-st,points=len(canon),target=n,status=stat,path=path,record=hit)),flush=True)
            if hit:return
if __name__=='__main__':main()
