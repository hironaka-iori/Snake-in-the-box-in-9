"""Replace a middle by a different shape and rebuild both free ends of the source."""
import argparse,json,subprocess
from pathlib import Path
from bank_pivots import canonical_word
from double_cross_bank import cases
from punctured_lift import project
from two_eight_layers import decode
from solve import BANK,BANK_HASH,sha256,defects,save

def sources():
    raw=BANK.read_bytes();assert sha256(raw).hexdigest()==BANK_HASH;bank=json.loads(raw);rows=[]
    for pos in cases()[0]["occurrences"]:
        P,sw=project(bank[pos["entry"]]["vertex_sequence"],pos["axis"]);a,b=sw;root=P[a];delta=root^P[b]
        axes=sorted(range(8),key=lambda j:not bool(delta>>j&1));assert delta.bit_count()==3
        def norm(x):return sum(((x^root)>>j&1)<<i for i,j in enumerate(axes))
        A=list(map(norm,P[:a+1][::-1]));M=list(map(norm,P[a:b+1]));B=list(map(norm,P[b:]))
        assert A[0]==0 and B[0]==7 and len(M)==96 and not defects(A[::-1]+[v|256 for v in M]+B)
        rows.append((A,M,B))
    return rows

def run(sr,ms,trim,target):
    lines=[f"{len(sr)} {len(ms)} {trim} {target}"]
    def path(q):lines.append(" ".join(map(str,[len(q),*q])))
    for a,_,b in sr:path(a);path(b)
    for m in ms:path(m)
    r=subprocess.run([str(Path("anchored-middle-trade.exe").resolve())],input="\n".join(lines),text=True,capture_output=True,check=True)
    rows=[]
    for line in r.stdout.splitlines():
        tag,*xs=line.split();values=list(map(int,xs));index=values[0]
        if tag=="rank":
            _,trials,best,source,l,r,n,*m=values;a,_,b=sr[source]
            assert n==len(m) and canonical_word(m)==canonical_word(ms[index]) and (m[0],m[-1])==(0,7)
            for arm,removed in ((a,l),(b,r)):
                first=next((j for j,x in enumerate(arm[1:],1) if x in m),len(arm))
                assert len(arm)-first==removed
            assert best==l+r
            rows.append(dict(index=index,status="RANKED",comparisons=trials,minimum_trim=best,source=source,left=l,right=r,middle=m));continue
        if tag=="done":rows.append(dict(index=index,comparisons=values[1],matches=values[2],states=values[3],status="EXHAUSTED"));continue
        assert tag=="found";i=2;arms=[]
        for _ in range(3):
            n=values[i];arms.append(values[i+1:i+1+n]);i+=n+1
        assert i==len(values);a,m,b=arms;q=a[::-1]+[v|256 for v in m]+b
        assert len(q)==target and not defects(q) and canonical_word(m)==canonical_word(ms[index])
        rows.append(dict(index=index,source=values[1],status="FOUND",vertices=q))
    return rows

if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("--trim",type=int,default=6);p.add_argument("--target",type=int,choices=(192,193),default=193)
    p.add_argument("--start",type=int,default=0);p.add_argument("--stop",type=int,default=595);p.add_argument("--new",action="store_true");a=p.parse_args()
    src=sources();ctrl=run(src[:1],[src[0][1]],a.trim,192)
    assert (ctrl[0]["minimum_trim"]==0 if a.trim<0 else ctrl[0]["status"]=="FOUND")
    forms=json.loads(Path("eight-regrow-96-32-160000000.json").read_bytes())["forms"];ms=[];indices=[]
    known=canonical_word(src[0][1])
    for i,w in enumerate(sorted(forms)):
        q=decode(w.encode())
        if q[-1].bit_count()!=3 or (a.new and canonical_word(q)==known):continue
        ms.append(q);indices.append(i)
    sl=slice(a.start,a.stop);rows=run(src,ms[sl],a.trim,a.target)
    if rows[-1]["status"]=="FOUND" and a.new and a.target==192:
        assert canonical_word(rows[-1]["vertices"]) not in {canonical_word(r["vertex_sequence"]) for r in json.loads(BANK.read_bytes())}
    save(Path(f"anchored-middle-trade-{a.trim}-{a.target}-{int(a.new)}-{a.start}-{a.stop}.json"),
         dict(trim=a.trim,target=a.target,source_count=len(src),indices=indices[sl],control=ctrl,rows=rows))
    print(len(rows),rows[-1]["status"],sum(r.get("matches",0) for r in rows),flush=True)
