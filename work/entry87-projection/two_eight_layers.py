"""Join two arbitrary rooted Q8 subpaths of public snakes across a single Q9 crossing."""
import argparse,csv,io,json,subprocess
from collections import Counter
from hashlib import sha256
from pathlib import Path
from tempfile import TemporaryFile
from zipfile import ZipFile
from four_layer_bank import menus
from projection_seeds190 import seeds
from partner93 import source_parent
from solve import BANK,BANK_HASH,defects,save


def decode(word):
    q=[0]
    for c in word:q.append(q[-1]^(1<<(c-48)))
    assert max(q)<256 and not defects(q)
    return q


def catalogue():
    archive=Path("public-records.zip")
    assert sha256(archive.read_bytes()).hexdigest()=="7bd8ca971a52e6534670b6802d885f53bad0c31a6ba7117f2ba84ee458acb58e"
    data=BANK.read_bytes();assert sha256(data).hexdigest()==BANK_HASH
    nine=[r["vertex_sequence"] for r in json.loads(data)]+list(seeds())
    parents=[source_parent()]+[json.loads(Path(f"fixed-face-long97-{i}-checked.json").read_text())["parent"]
                               for i in range(5)]
    counts=Counter({8:len(parents),9:len(nine)})
    with TemporaryFile() as stream,ZipFile(archive) as z:
        for i,q in enumerate(parents):
            assert not defects(q) and len(q) in (98,99)
            word=bytes(65+(v^w).bit_length()-1 for v,w in zip(q,q[1:]))
            stream.write(f"8 {i} ".encode()+word+b"\n")
        for i,q in enumerate(nine):
            word=bytes(65+(v^w).bit_length()-1 for v,w in zip(q,q[1:]))
            stream.write(f"9 {i} ".encode()+word+b"\n")
        for row in csv.DictReader(io.TextIOWrapper(z.open("record_snakes.csv"))):
            d=int(row["n"])
            if d==9 or d<8:continue
            word=bytes(65+int(s) for s in row["actions"].split());i=counts[d];counts[d]+=1
            stream.write(f"{d} {i} ".encode()+word+b"\n")
        stream.seek(0);proc=subprocess.run([str(Path("extract-eight.exe").resolve()),"92","8"],
                                            stdin=stream,capture_output=True,check=True)
    forms={}
    for line in proc.stdout.splitlines():
        word,d,i,start=line.split();q=decode(word);assert len(q)>=93
        forms[word.decode()]=list(map(int,(d,i,start)))
    save(Path("eight-face-catalogue.json"),dict(source_counts=counts,forms=forms))
    return forms


def join(left,right):
    if not left or not right:return dict(status="empty menu")
    L=list(left);R=list(right)
    src=b"\n".join([f"{len(L)} {len(R)}".encode(),*L,*R])
    proc=subprocess.run([str(Path("join-eight.exe").resolve()),"0","opposite-faces"],
                        input=src,capture_output=True,check=True)
    status,*words=proc.stdout.split();nums=list(map(int,words))
    if status==b"complete":return dict(status="EXHAUSTED",states=nums[0],matches=nums[1],trie=nums[2])
    assert status==b"found";l,r,dim,*tail=nums;perm=tail[:dim];states,bridge=tail[dim:];assert not bridge
    a=decode(L[l]);b=[0]
    for digit in R[r]:b.append(b[-1]^(1<<perm[digit-48]))
    assert set(a)&set(b)=={0}
    q=a[::-1]+[v|256 for v in b]
    assert not defects(q)
    return dict(status="FOUND",vertices=q,left=L[l].decode(),right=R[r].decode(),states=states)


if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("--build",action="store_true");p.add_argument("--extra",type=Path,nargs="*")
    a=p.parse_args();forms=catalogue() if a.build else json.loads(Path("eight-face-catalogue.json").read_text())["forms"]
    for f in a.extra or []:forms.update(json.loads(f.read_text())["forms"])
    bank={w.encode():ref for w,ref in forms.items()}
    # A 191-edge one-crossing bank path supplies a 97+95 positive control.
    menu={n:menus(bank,n) for n in range(93,100)}
    control=join(menu[97],menu[95]);assert control["status"]=="FOUND" and len(control["vertices"])==192
    rows=[]
    for l,r in ((99,94),(98,95),(97,96)):
        rows.append(dict(sizes=[l,r],classes=[len(menu[l]),len(menu[r])],**join(menu[l],menu[r])))
    out="two-eight-layers"+("-expanded" if a.extra else "")+".json"
    save(Path(out),dict(menus={n:len(m) for n,m in menu.items()},control=control,rows=rows))
    print(len(forms),[(r["sizes"],r["classes"],r["status"]) for r in rows])
