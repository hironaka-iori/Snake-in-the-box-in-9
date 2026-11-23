"""Independently check every emitted local table against the price certificate."""
import json
import sys
from pathlib import Path
from itertools import combinations
sys.path.insert(0,str(Path(__file__).resolve().parent.parent))
import q9_facet_dual_replay as original

B=Path(__file__).resolve().parent

def check(tag):
    c=json.loads((B/(tag+'.json')).read_text())
    root=original.replay(c)
    donor=original.donor(c['word'])
    majority=c['majority'];scale=c['scale'];tip={donor[0],donor[-1]};fixed=set(donor[1:-1])
    pool=(set(range(512))-{v^d for v in fixed for d in (0,1,2,4,8,16,32,64,128,256)})|tip
    dirs=[1<<i for i in range(9)]
    available={v:sum(d for d in dirs if v^d in pool) for v in pool}
    axes=c['axes'];fee=c['fees'];prices={tuple(row[:3]):row[3] for row in c['weights']}
    initial=(len(fixed)*scale+2*fee[majority]+(1-2*majority-sum(original.sign(v) for v in fixed))*fee[2])
    qs=[('star',v) for v in sorted(pool)]
    for m in axes:
        bases=dict.fromkeys(v&~m for v in sorted(pool))
        qs.extend((m,b) for b in bases)
    with (B/(tag+'.tables')).open() as f:
        first=list(map(int,f.readline().split()))
        assert first==[initial,scale,root,len(qs),len(pool),len(fixed),majority]
        assert set(map(int,f.readline().split()))==pool and set(map(int,f.readline().split()))==fixed
        nopts=0
        for typ,b in qs:
            width,n,*scope=map(int,f.readline().split());assert len(scope)==width
            table=dict(tuple(map(int,f.readline().split())) for _ in range(n))
            assert len(table)==n
            if typ=='star':
                assert scope[0]==b and set(scope[1:])=={b^d for d in dirs if available[b]&d}
                for k in range(1<<width):
                    expected=None
                    if k&1:
                        sig=sum(b^x for i,x in enumerate(scope[1:],1) if k>>i&1)
                        deg=sig.bit_count()+int(b in tip)
                        if deg in (1,2):
                            expected=(scale-fee[2]*original.sign(b)-(fee[b.bit_count()%2] if deg==1 else 0)
                                      +sum(prices.get((m,b,sig&m),0) for m in axes))
                    elif b not in tip:expected=0
                    assert table.get(k)==expected
            else:
                m=typ
                assert set(scope)=={v for v in pool if v&~m==b}
                full=original.linear_forests(m.bit_count());bits=list(original.directions(m));size=1<<len(bits)
                embed=[sum(d for i,d in enumerate(bits) if j>>i&1) for j in range(size)]
                local=[embed.index(x^b) for x in scope];must=sum(1<<j for j,x in enumerate(scope) if x in tip)
                lift=[0]*(1<<width)
                for k in range(1<<width):
                    low=k&-k
                    if k:lift[k]=lift[k^low]|(1<<local[low.bit_length()-1])
                    expected=None; sigs=full[lift[k]]
                    if sigs is not None and k&must==must:
                        score=0
                        for code in sigs:
                            v=b|embed[code//size];z=embed[code%size]
                            vdeg=z.bit_count()+int(v in tip)
                            if vdeg>2 or vdeg+(available[v]&~m).bit_count()<1:break
                            score-=prices.get((m,v,z),0)
                        else:expected=score
                    assert table.get(k)==expected
            nopts+=n
        assert not f.read().strip()
    return {'tag':tag,'bound_scaled':root,'options':nopts,'factors':len(qs),'result':'ALL_ASSIGNMENTS_MATCH'}

if __name__=='__main__':
    for tag in sys.argv[1:]:print(json.dumps(check(tag)),flush=True)
