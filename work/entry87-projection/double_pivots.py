"""Coordinate permutations of three consecutive pieces about two hinges."""
import argparse,json,subprocess
from pathlib import Path
from solve import BANK,BANK_HASH,defects,save,sha256


def scan(q,lo,hi,exe):
    cmd=[str(exe),str(lo),str(hi)]
    if "indexed" in exe.name:cmd.append("index")
    p=subprocess.run(cmd,input=" ".join(map(str,q)),text=True,capture_output=True,check=True)
    status,*fields=p.stdout.split();vals=list(map(int,fields))
    if status=="FOUND":
        l,r,*path=vals;assert len(path)==len(q) and not defects(path)
        assert path[l:r+1]==q[l:r+1] and lo<=r-l+1<=hi
        for a,b in ((q[:l+1],path[:l+1]),(q[r:],path[r:])):
            mapping={}
            for x,y in zip((u^v for u,v in zip(a,a[1:])),(u^v for u,v in zip(b,b[1:]))):
                assert mapping.setdefault(x,y)==y
            assert len(set(mapping.values()))==len(mapping)
        return dict(status=status,left=l,right=r,vertices=path)
    assert status=="EXHAUSTED" and len(vals)==5
    return dict(status=status,**dict(zip(("pairs","intrinsic","nodes","images","arm_tests"),vals)))


def control(source,exe):
    for l in range(3,19):
        for a in range(9):
            for b in range(a):
                def perm(v):
                    if ((v>>a)^(v>>b))&1:v^=(1<<a)|(1<<b)
                    return v
                q=[source[l]^perm(v^source[l]) for v in source[:l]]+source[l:]
                if len(defects(q))!=1:continue
                assert scan(q,len(q)-1-l,len(q)-1-l,exe)["status"]=="FOUND";return
    raise AssertionError("positive control unavailable")


if __name__=="__main__":
    p=argparse.ArgumentParser()
    for k in ("lo","hi","first","stop"):p.add_argument(k,type=int)
    p.add_argument("--indexed",action="store_true");a=p.parse_args()
    exe=Path("double-pivots-indexed.exe" if a.indexed else "double-pivots.exe").resolve();raw=BANK.read_bytes()
    assert sha256(raw).hexdigest()==BANK_HASH;bank=json.loads(raw);control(bank[0]["vertex_sequence"],exe)
    items=json.loads(Path("bank-pivots.json").read_text());rows=[]
    suffix="-indexed" if a.indexed else ""
    file=Path(f"double-pivots-{a.lo}-{a.hi}-{a.first}-{a.stop}{suffix}.json")
    for i in range(a.first,min(a.stop,len(items))):
        rec=items[i];t=rec["insertion"];bit=1<<rec["flip"];q=bank[rec["entry"]]["vertex_sequence"]
        path=q[:t+1]+[v^bit for v in q[t:]]
        assert len(path)==193 and list(defects(path)[0])==rec["chord"]
        r=scan(path,a.lo,a.hi,exe);rows.append(dict(index=i,**r));save(file,rows)
        if r["status"]=="FOUND":break
    print(len(rows),sum(r.get("arm_tests",0) for r in rows),flush=True)
