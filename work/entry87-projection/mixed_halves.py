"""Join two long subpaths from any two independent sources, with any relative orientation."""
import argparse, json, subprocess
from pathlib import Path
from solve import BANK, BANK_HASH, defects, save, sha256
from projection_seeds190 import seeds


def words(paths, length, interior):
    forms={}
    for i,q in enumerate(paths):
        moves=[(v^w).bit_length()-1 for v,w in zip(q,q[1:])]
        for rev,order in enumerate((moves,moves[::-1])):
            for j in range(len(order)-length+1 if interior else 1):
                names={}; key=bytes(48+names.setdefault(x,len(names)) for x in order[j:j+length])
                forms.setdefault(key,(i,rev,j))
    return forms


def vertices(seq,perm=tuple(range(9))):
    q=[0]
    for c in seq: q.append(q[-1]^(1<<perm[c-48]))
    return q


def join(left,right,exe):
    ls=list(left); rs=list(right)
    data=b"\n".join([f"{len(ls)} {len(rs)}".encode(),*ls,*rs])
    ans=subprocess.run([str(exe)],input=data,capture_output=True,check=True).stdout.split()
    if ans[0]==b"found":
        l,r,n,*tail=map(int,ans[1:]); perm=tail[:n]
        a=vertices(ls[l]); b=vertices(rs[r],perm); q=a[::-1]+b[1:]
        assert len(q)==len(ls[l])+len(rs[r])+1 and not defects(q)
        return dict(status="FOUND",left=left[ls[l]],right=right[rs[r]],states=tail[-1],vertices=q)
    assert ans[0]==b"complete" and ans[2]==b"0"
    return dict(status="exhausted",states=int(ans[1]),trie_nodes=int(ans[3]))


if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("left",type=int); p.add_argument("right",type=int)
    p.add_argument("--interior",action="store_true"); p.add_argument("--extended",action="store_true")
    p.add_argument("--exe",type=Path,default=Path("mixed-halves.exe"))
    a=p.parse_args()
    assert sha256(BANK.read_bytes()).hexdigest()==BANK_HASH
    paths=[r["vertex_sequence"] for r in json.loads(BANK.read_bytes())]
    if a.extended: paths+=list(seeds())
    exe=a.exe.resolve()
    # Two differently labelled halves of a known record recover a valid record.
    mid=96; q=paths[0]
    ls=words([q[:mid+1][::-1]],mid,False); rs=words([q[mid:]],len(q)-1-mid,False)
    assert len(join(ls,rs,exe)["vertices"])==192
    ls=words(paths,a.left,a.interior)
    rs=ls if a.left==a.right else words(paths,a.right,a.interior)
    print("Arms",len(ls),len(rs),flush=True)
    out=dict(left_length=a.left,right_length=a.right,interior=a.interior,sources=len(paths),
             left_classes=len(ls),right_classes=len(rs),**join(ls,rs,exe))
    save(Path(f"mixed-halves-{a.left}-{a.right}-{int(a.interior)}-{len(paths)}.json"),out)
    print(out["status"],out["states"],flush=True)
