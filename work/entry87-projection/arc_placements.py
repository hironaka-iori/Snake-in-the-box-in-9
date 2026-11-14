import argparse,json,subprocess
from pathlib import Path
from solve import BANK,BANK_HASH,sha256,save,defects
from translated_splice import search


def scan(path,k,orientation,exe,first=0,stop=192):
    cmd=[str(exe),str(k),str(first),str(stop),str(orientation)]
    proc=subprocess.run(cmd,input=" ".join(map(str,path)),text=True,capture_output=True,check=True)
    tag,*fields=proc.stdout.split()
    if tag=="witness":
        cut,reversed,*q=map(int,fields);assert len(q)==len(path)+1 and not defects(q)
        L=path[:cut+1];R=path[cut+k+1:]
        if reversed:L,R=R[::-1],L[::-1]
        assert q[:len(L)]==L
        tail=q[-len(R):]
        translate={}
        for (x,y),(u,v) in zip(zip(R,R[1:]),zip(tail,tail[1:])):
            b=x^y;c=u^v
            assert translate.setdefault(b,c)==c
        assert len(set(translate.values()))==len(translate)
        return dict(cut=cut,reversed=reversed,witness=q)
    assert tag=="count"
    return dict(zip(("positions","placements","orientation_nodes","bridge_searches","bridge_nodes"),map(int,fields)))


if __name__=="__main__":
    p=argparse.ArgumentParser()
    for s in ("k","start","stop"):p.add_argument(s,type=int)
    p.add_argument("--first",type=int,default=0);p.add_argument("--last",type=int,default=192)
    p.add_argument("--exe",type=Path,default=Path("arc-placements.exe"));a=p.parse_args()
    raw=BANK.read_bytes();assert sha256(raw).hexdigest()==BANK_HASH
    records=json.loads(raw);exe=a.exe.resolve()
    q=records[0]["vertex_sequence"];t=59
    short=q[:t]+[v^q[t]^q[t-1] for v in q[t+1:]]
    assert "witness" in scan(short,0,0,exe)
    # Compare with the separately implemented complete translation-only census.
    for k in (0,3,8):
        one=scan(q,k,1,exe)
        two=search(q,k,k,9,Path("translated-splice.exe").resolve())
        assert "witness" not in one and "witness" not in two
        assert one["placements"]==two["table"][0][3]
    rows=[]
    for i in range(a.start,a.stop):
        q=records[i]["vertex_sequence"]
        r=scan(q,a.k,0,exe,a.first,a.last);rows.append(dict(index=i,**r))
        if "witness" in r:break
    save(Path(f"arc-placements-{a.k}-{a.start}-{a.stop}-{a.first}-{a.last}.json"),rows)
    print(len(rows),sum(r.get("placements",0) for r in rows),sum("witness" in r for r in rows),flush=True)
