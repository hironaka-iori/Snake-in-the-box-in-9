"""Rebuild translated-splice instances and check any proposed snake on all pairs."""
import argparse
from hashlib import sha256
import json
from math import comb
from pathlib import Path
import subprocess
from solve import BANK,BANK_HASH,defects,save


def search(q,low,high,weight,exe):
    run=subprocess.run([str(exe),str(low),str(high),str(weight)],check=True,
                       input=" ".join(map(str,[len(q),*q])),text=True,capture_output=True)
    lines=run.stdout.splitlines()
    if lines[0].startswith("witness"):
        k,i,delta,*w=map(int,lines[0].split()[1:])
        assert len(w)==len(q)+1 and not defects(w)
        assert w[:i+1]==q[:i+1] and w[i+k+2:]==[x^delta for x in q[i+k+1:]]
        return dict(k=k,cut=i,translation=delta,witness=w)
    table=[list(map(int,l.split())) for l in lines]
    count=sum(comb(9,w) for w in range(1,weight+1,2))
    assert [r[0] for r in table]==list(range(low,high+1))
    assert all(r[1]==count*(len(q)-r[0]-1) for r in table)
    return dict(table=table)


def run(a):
    raw=BANK.read_bytes();assert sha256(raw).hexdigest()==BANK_HASH
    paths=[r["vertex_sequence"] for r in json.loads(raw)]
    exe=a.exe.resolve()
    # Deliberately delete a transition from an induced path, and check that the
    # search rediscovers an induced path of the original length.
    p=paths[0];t=59;bit=p[t]^p[t-1]
    shorter=p[:t]+[v^bit for v in p[t+1:]]
    assert search(shorter,0,0,1,exe).get("witness")
    rows=[]
    for entry in range(a.first,min(a.stop,len(paths))):
        q=paths[entry];assert len(q)==192 and not defects(q)
        result=search(q,a.low,a.high,a.weight,exe)
        rows.append(dict(entry=entry,**result))
        if "witness" in result:
            print("WITNESS",entry,result["k"],flush=True);break
    save(Path(f"translated-splice-{a.low}-{a.high}-{a.weight}-{a.first}-{a.stop}.json"),rows)
    print("entries",len(rows),"witnesses",sum("witness" in row for row in rows),flush=True)


if __name__=="__main__":
    parser=argparse.ArgumentParser()
    for name in ("low","high","weight","first","stop"):parser.add_argument(name,type=int)
    parser.add_argument("--exe",type=Path,default=Path("translated-splice.exe"))
    run(parser.parse_args())
