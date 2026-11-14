"""Extract Q7 snakes from all public higher-dimensional record paths and search for four compatible layers."""
import argparse,csv,io,json,subprocess
from collections import Counter
from hashlib import sha256
from pathlib import Path
from zipfile import ZipFile
from four_layer_bank import menus,test,words
from projection_seeds190 import seeds
from solve import BANK,BANK_HASH,defects,save


def extract(minimum,exe):
    file=Path("public-records.zip");assert sha256(file.read_bytes()).hexdigest()=="7bd8ca971a52e6534670b6802d885f53bad0c31a6ba7117f2ba84ee458acb58e"
    from tempfile import TemporaryFile
    counts=Counter()
    with TemporaryFile() as stream,ZipFile(file) as z:
        rd=csv.DictReader(io.TextIOWrapper(z.open("record_snakes.csv")))
        for r in rd:
            dim=int(r["n"])
            if dim<10:continue
            index=counts[dim];counts[dim]+=1
            tokens=bytes(65+int(v) for v in r["actions"].split())
            stream.write(f"{dim} {index} ".encode()+tokens+b"\n")
        stream.seek(0);proc=subprocess.run([str(exe),str(minimum-1)],stdin=stream,capture_output=True,check=True)
    forms={}
    for line in proc.stdout.splitlines():
        word,d,i,j=line.split();q=[0]
        for c in word:q.append(q[-1]^(1<<(c-48)))
        assert max(q)<128 and len(q)>=minimum and not defects(q)
        forms[word]=(int(d),int(i),int(j))
    return forms,counts


if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("action",choices=("build","join"))
    p.add_argument("--minimum",type=int,default=39);p.add_argument("--sizes",nargs=4,type=int,default=[49,48,48,48])
    p.add_argument("--nodes",type=int,default=2500000000);a=p.parse_args()
    file=Path(f"highdim-seven-{a.minimum}.json")
    if a.action=="build":
        raw=BANK.read_bytes();assert sha256(raw).hexdigest()==BANK_HASH
        lower=[r["vertex_sequence"] for r in json.loads(raw)]+list(seeds())
        bank,counts=extract(a.minimum,Path("extract-seven.exe").resolve())
        for word,origin in words(lower,a.minimum).items():bank.setdefault(word,("nine",origin))
        save(file,dict(minimum=a.minimum,higher_counts=counts,forms={w.decode():src for w,src in bank.items()}))
        print(len(bank),Counter(map(len,bank)),flush=True)
    else:
        bank={s.encode():v for s,v in json.loads(file.read_text())["forms"].items()}
        ms=[menus(bank,n) for n in a.sizes];assert all(ms)
        r=test(ms,Path("four-layer-bank.exe").resolve(),a.nodes);r.update(sizes=a.sizes,classes=list(map(len,ms)))
        save(Path(f"highdim-four-{'-'.join(map(str,a.sizes))}-{a.nodes}.json"),r)
        print(r["status"],r["nodes"],r["classes"],flush=True)
