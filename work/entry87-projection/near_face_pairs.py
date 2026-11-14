"""Count all near-compatible placements of two Q8 paths in opposite faces."""
import argparse,json,subprocess
from itertools import permutations
from pathlib import Path
from four_layer_bank import menus
from two_eight_layers import decode
from solve import defects,save


def scan(L,R,max_contacts,sample):
    stream=b"\n".join([f"{len(L)} {len(R)}".encode(),*L,*R])
    cmd=[str(Path("near-face-pairs.exe").resolve()),"0","opposite-faces",str(max_contacts),str(sample)]
    p=subprocess.run(cmd,input=stream,capture_output=True,check=True)
    rows=[];stats=None;counts=None
    for line in p.stdout.splitlines():
        kind,*raw=line.split();nums=list(map(int,raw))
        if kind==b"complete":stats=nums;continue
        if kind==b"counts":counts=nums;continue
        assert kind==b"sample";hits,l,r,*perm=nums
        A=decode(L[l]);B=[0]
        for d in R[r]:B.append(B[-1]^(1<<perm[d-48]))
        cross=sorted((set(A)&set(B))-{0});q=A[::-1]+[v|256 for v in B]
        assert len(cross)==hits and len(defects(q))==hits
        rows.append(dict(contacts=cross,left=A,right=B))
    assert stats is not None and counts is not None and sum(counts)==stats[1]
    return dict(counts=counts,states=stats[0],trie=stats[2],samples=rows)


if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("--contacts",type=int,default=2)
    p.add_argument("--samples",type=int,default=30);p.add_argument("--expanded",action="store_true")
    a=p.parse_args();bank=json.loads(Path("eight-face-catalogue.json").read_text())["forms"]
    if a.expanded:
        for f in sorted(Path().glob("eight-regrow-*-160000000.json")):bank.update(json.loads(f.read_text())["forms"])
    bank={s.encode():v for s,v in bank.items()}
    # Independent exhaustive injection-of-labels test on a small two-axis path.
    L=[b"01"];R=[b"01"];ctrl=scan(L,R,3,8);cnt=[0]*4
    for i,j in permutations(range(8),2):
        q={1<<i,(1<<i)^(1<<j)};cnt[len(set(decode(L[0]))&q)]+=1
    assert cnt==ctrl["counts"]
    rows=[]
    for l,r in ((99,94),(98,95),(97,96)):
        left=sorted(menus(bank,l));right=sorted(menus(bank,r));ans=scan(left,right,a.contacts,a.samples)
        rows.append(dict(sizes=[l,r],menus=[len(left),len(right)],**ans))
    save(Path(f"near-face-pairs-{int(a.expanded)}-{a.contacts}-{a.samples}.json"),rows)
    print([(r["sizes"],r["counts"]) for r in rows],flush=True)
