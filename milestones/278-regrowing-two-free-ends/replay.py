"""Re-extract each chart, independently grow in reverse order and compare every size count."""
from collections import Counter
from hashlib import sha256
from pathlib import Path
from tempfile import TemporaryDirectory
import subprocess, sys
from archive import HERE, cases, code, read, write

width, minimum, budget = map(int,sys.argv[1:4])
full="--cube" in sys.argv
tag = "%d-%d"%(minimum,width)+("-cube" if full else "")
original = read("cases-"+tag+".json")
seeds, bank, report = cases(width,minimum,full)
complete=0; nodes=0; histograms=0; comparable=[]; disagreements=0
with TemporaryDirectory(prefix="q9-replay-") as scratch:
    temp=Path(scratch);src=temp/"source";dest=temp/"result";exe=temp/"rerun.exe"
    items=[]; bykey={}
    for key,row in seeds.items():
        ident=sha256(key).hexdigest()
        assert original[ident]["source"]==row["source"] and original[ident]["axis"]==row["axis"]
        items.append("\t".join([ident]+[",".join(map(str,row[part])) for part in ("a","m","b")]))
        bykey[ident]=row
    src.write_text("\n".join(items)+"\n",encoding="ascii")
    subprocess.run(["C:/Windows/Microsoft.NET/Framework64/v4.0.30319/csc.exe","/nologo","/optimize+","/out:"+str(exe),str(HERE/"Replay.cs")],check=True)
    subprocess.run([str(exe),str(src),str(dest),str(budget),"full" if full else "lower"],check=True)
    found={}
    for line in dest.read_text().splitlines():
        ident,closed,visits,counts=line.split("\t"); n=int(visits);nodes+=n
        hist=list(map(int,counts.split(",")))
        o=original[ident]
        if closed=="1": complete+=1
        if closed=="1" and o["closed"]:
            assert hist==o["histogram"],ident
            histograms+=len(hist); comparable.append(ident)
        found[ident]=dict(complete=closed=="1",visited=n,histogram=hist)
    assert found.keys()==original.keys()==bykey.keys()
for k,w in read("paths-"+tag+".json").items():
    path=w["vertices"]; assert len(set(path))==len(path) and all(0<=v<512 for v in path)
    assert all(((x^y).bit_count()==1)==(j==i+1) for i,x in enumerate(path) for j,y in enumerate(path[i+1:],i+1))
    word=code(path)
    assert k==sha256(word).hexdigest() and bank.get(word)==w["archive"]
write("replay-"+tag+".json",dict(complete=complete,cases=len(found),double_checked=len(comparable),
    size_counts_compared=histograms,visits=nodes,maximum_visits=budget,results=found))
print("Independently complete",complete,"of",len(found),"matching complete histograms",len(comparable),"size counts",histograms,"visits",nodes)

