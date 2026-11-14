"""Close the known 22-site kernel shell for either of the first two signature distances."""
import argparse,json,subprocess
from itertools import combinations
from pathlib import Path
from math import comb
from solve import BANK,BANK_HASH,defects,sha256,save
from star_repairs import ball,is_path
from triple_star import connected


def run(sets,d,target,signature):
    single=signature==10;exe=Path("star-repairs.exe" if single else "triple-star.exe").resolve()
    stream=[f"{d} {target} 3 {len(sets)}"]+[" ".join(map(str,[len(s),*sorted(s)])) for s in sets]
    p=subprocess.run([str(exe)],input="\n".join(stream),text=True,capture_output=True,check=True)
    rows=[]
    for i,line in enumerate(p.stdout.splitlines()):
        index,*a=map(int,line.split());assert i==index
        if not single:shapes=a.pop(0)
        classes,examined,degree,hits=(a[j:j+4] for j in range(0,16,4))
        assert classes[:3]==[1,1<<d,comb(1<<d,2)]
        if d==9:assert classes[3]==384000
        if not single:assert shapes==classes[3]
        width=1 if single else 3
        edit=a[16:16+width];stars=a[16+width:19+width];n,*q=a[19+width:]
        if n:
            s=sets[i]^set(edit)
            for v in stars:
                if v>=0:s^=ball(v,d)
            assert len(q)==target and n==target and set(q)==s and not defects(q)
        rows.append(dict(classes=classes,examined=examined,degree_models=degree,solutions=hits,
                         edit=edit if n else None,stars=stars if n else None,path=q or None))
    assert len(rows)==len(sets)
    return rows


if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("signature",type=int,choices=(10,22))
    p.add_argument("first",type=int);p.add_argument("stop",type=int);a=p.parse_args()
    triples=[set(t) for t in combinations(range(8),3) if connected(t)]
    edits=[{v} for v in range(8)] if a.signature==10 else triples
    sample=[{v for v in range(8) if mask>>v&1} for mask in range(0,256,17)]
    for s,row in zip(sample,run(sample,3,5,a.signature)):
        count=0
        for kernel in triples:
            y=s.copy()
            for v in kernel:y^=ball(v,3)
            for edit in edits:
                q=y^edit
                if len(q)==5 and is_path(q,3):count+=1
        assert count==row["solutions"][3]
    raw=BANK.read_bytes();assert sha256(raw).hexdigest()==BANK_HASH
    bank=[set(r["vertex_sequence"]) for r in json.loads(raw)];rows=[]
    # The sole comparison needed for each base is its translated Hamming geometry.
    for start in range(a.first,min(len(bank),a.stop),4):
        chunk=run(bank[start:min(start+4,a.stop)],9,193,a.signature)
        rows.extend(dict(source=j,**r) for j,r in enumerate(chunk,start))
        save(Path(f"kernel22-shell-{a.signature}-{a.first}-{a.stop}.json"),rows)
        if any(r["path"] for r in chunk):break
    print(a.signature,len(rows),sum(r["solutions"][3] for r in rows),flush=True)
