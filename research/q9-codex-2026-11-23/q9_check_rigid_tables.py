"""Check all local assignments, without rebuilding or optimizing the dual LP."""
from itertools import combinations
from pathlib import Path
import json

def directions(x):
    while x:
        d=x&-x;yield d;x-=d

def signs(v):return 1-2*(v.bit_count()%2)
def check(rec,root,witness):
    cert=rec["cert"];scale=cert["scale"];p=[0]
    for c in rec["word"]:p.append(p[-1]^1<<int(c))
    assert len(set(p))==len(p)
    assert all(((u^v).bit_count()==1)==(i+1==j) for i,u in enumerate(p) for j,v in enumerate(p) if i<j)
    if "lower_vertices" in rec:
        assert set(rec["lower_vertices"])==set(p[1:])
        p=p[1:]
    required=set(rec["ports"]);lower=set(p);pool=set(range(256))-(lower-required)
    if "lower_vertices" not in rec:
        assert all(v in lower or any((v^x).bit_count()==1 for x in p[1:-1]) for v in range(256))
    full=rec["majority"];lowends={p[0],p[-1]}-required
    assert required and required<={p[0],p[-1]} and all(v.bit_count()%2==full for v in lowends)
    ends=[(2-len(lowends))*int(c==full) for c in (0,1)]
    delta=sum(map(signs,lower))-signs(full)
    assert ends==rec["upper_endpoint_counts"] and delta==rec["upper_delta"]
    fees=cert["end_weights"];balance=cert["balance_weight"]
    axes=[sum(1<<d for d in a) for a in cert["axes"]]
    prices={(m,v,z):y for m,v,z,y in cert["weights"]}
    base=len(lower)*scale+sum(x*y for x,y in zip(fees,ends))+delta*balance
    expected_faces=[(m,b) for m in axes for b in sorted({v&~m for v in pool})]
    # Restrict the phase-specific positive check to witnesses covered by this branch.
    candidates=[]
    for short in (witness[1:],witness[:-1]):
        low={v for v in short if v<256};up={v-256 for v in short if v>=256}
        if low==lower and low&up==required and all(v.bit_count()%2==full for v in (short[0],short[-1])):
            candidates.append((up,len(short)))
    pos_scores=[base]*len(candidates)
    def accepts(v,total):
        return total==2 or total==1 and ends[1-v.bit_count()%2]>0
    with root.with_suffix(".tables").open() as f:
        b,s,baked,nf,nv,ni,maj=map(int,next(f).split())
        assert (b,s,baked,nf,nv,ni,maj)==(base,scale,rec["total_scaled"],len(pool)+len(expected_faces),len(pool),len(lower),full)
        assert set(map(int,next(f).split()))=={v+256 for v in pool}
        assert set(map(int,next(f).split()))==lower
        total=base;nopts=0;observed=set()
        for group in range(nf):
            width,n,*sc=map(int,next(f).split());sc=[v-256 for v in sc];assert len(sc)==len(set(sc))==width
            data=dict(tuple(map(int,next(f).split())) for _ in range(n))
            assert len(data)==n
            expected={}
            if group<len(pool):
                v=sorted(pool)[group];assert sc[0]==v and set(sc[1:])=={v^b for b in directions(255) if v^b in pool}
                for k in range(1<<width):
                    if not k&1:
                        if v not in required:expected[k]=0
                        continue
                    ns=[u for j,u in enumerate(sc[1:],1) if k>>j&1];deg=len(ns)+int(v in required)
                    if accepts(v,deg):
                        mask=sum(v^u for u in ns)
                        expected[k]=scale-signs(v)*balance-int(deg==1)*fees[1-v.bit_count()%2]+sum(prices.get((m,v,m&mask),0) for m in axes)
            else:
                mask,_=expected_faces[group-len(pool)]
                face=sc[0]&~mask
                assert (mask,face) not in observed
                observed.add((mask,face))
                assert set(sc)=={v for v in pool if v&~mask==face}
                for k in range(1<<width):
                    pick={v for j,v in enumerate(sc) if k>>j&1}
                    if required.intersection(sc)-pick:continue
                    value=0;parent={v:v for v in pick}
                    def rep(a):
                        while a!=parent[a]:a=parent[a]
                        return a
                    ok=True
                    for v in pick:
                        sig=sum(b for b in directions(mask) if v^b in pick)
                        deg=int(v in required)+sig.bit_count()
                        external=sum(v^b in pool for b in directions(255^mask))
                        if not any(accepts(v,d) for d in range(deg,deg+external+1)):
                            ok=False;break
                        for bit in directions(sig):
                            u=v^bit
                            if u<v:
                                x,y=rep(u),rep(v)
                                if x==y:ok=False;break
                                parent[x]=y
                        if not ok:break
                        value-=prices.get((mask,v,sig),0)
                    if ok:expected[k]=value
            assert expected==data
            for j,(up,length) in enumerate(candidates):
                pos_scores[j]+=data[sum(1<<h for h,u in enumerate(sc) if u in up)]
            total+=max(data.values());nopts+=len(data)
        assert observed==set(expected_faces)
        assert not f.read().strip() and total==rec["total_scaled"]
        assert all(score==length*scale for score,(_,length) in zip(pos_scores,candidates))
    return nopts,len(candidates)

if __name__=="__main__":
    witnesses=json.loads(Path("q9_rigid_five_witnesses.json").read_text())
    for line in Path("q9_rigid_ports12.jsonl").read_text().splitlines():
        r=json.loads(line);tag="d%d_m%d_p%s"%(r["i"],r["majority"],"-".join(map(str,r["ports"])))
        root=Path("q9_rigid_ports_trees")/tag
        if not root.with_suffix(".log").exists():continue
        n,c=check(r,root,witnesses[str(r["i"])]["vertices"])
        print(tag,n,c,"ALL_OPTIONS_MATCH",flush=True)
