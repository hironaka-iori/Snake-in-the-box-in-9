"""Classify every Q7 snake of 48 or more edges with a once-crossed coordinate."""
from argparse import ArgumentParser
from pathlib import Path
from tempfile import TemporaryDirectory
from collections import Counter
from hashlib import sha256
import gzip,subprocess
from parents import HERE,read,write,unrooted,paircheck,ordered,wordof
from primer_census import CSC

def main():
    ap=ArgumentParser();ap.add_argument("engine",choices=["mask","contacts"]);a=ap.parse_args()
    with TemporaryDirectory() as folder:
        tmp=Path(folder);exe=tmp/"SixCube.exe";parents=tmp/"parents.txt";pairs=tmp/"pairs.txt"
        subprocess.run([str(CSC),"/nologo","/optimize+","/out:"+str(exe),str(HERE/"SixCube.cs")],capture_output=True,check=True)
        log=subprocess.run([str(exe),a.engine,str(parents),str(pairs)],capture_output=True,text=True,check=True)
        core_count,large_count,max6,partner_nodes=map(int,log.stdout.split())
        large=[bytes(map(int,line.split(","))) for line in parents.read_text().splitlines()]
        assert len(large)==len(set(large))==large_count and max(len(q)-1 for q in large)==max6
        for q in large:
            paircheck(q,6);assert q[0]==0 and ordered(wordof(q))==wordof(q)
        found={}
        source=set(large);records=[]
        for line in pairs.read_text().splitlines():
            s,t=(bytes(map(int,x.split(","))) for x in line.split(";"))
            assert s in source and t[0]==0 and len(s)>=len(t) and set(s)&set(t)=={0}
            q=list(s[::-1])+[64+v for v in t];paircheck(q,7)
            k=unrooted(q);found[k]=len(q)-1;records.append(s.hex()+"/"+t.hex())
        assert len(set(records))==len(records)
    small="\n".join(sorted(p.hex() for p in large)).encode()
    got="\n".join(sorted(records)).encode()
    final=dict(larger_q6_rooted_parents=Counter(len(q)-1 for q in large),maximum_q6=max6,
               q6_prefix_visits=core_count,partner_visits=partner_nodes,
               labelled_q7=len(records),q7_counts=Counter(found.values()),q7_shapes=sorted(found),
               parents=sorted(k for k,n in found.items() if n==49),
               q6_data_sha256=sha256(small).hexdigest(),q7_data_sha256=sha256(got).hexdigest())
    if a.engine=="mask":
        (HERE/"q6-parents.hex.gz").write_bytes(gzip.compress(small,mtime=0));(HERE/"q7-layer-joins.hex.gz").write_bytes(gzip.compress(got,mtime=0))
        write(HERE/"q7-single-crossings.json",final)
    else:
        assert small==gzip.decompress((HERE/"q6-parents.hex.gz").read_bytes()) and got==gzip.decompress((HERE/"q7-layer-joins.hex.gz").read_bytes())
        assert read(HERE/"q7-single-crossings.json")["q7_shapes"]==final["q7_shapes"]
        write(HERE/"q7-single-crossings-replay.json",final)
    print({k:v for k,v in final.items() if k not in ("q7_shapes","parents")})
if __name__=="__main__":main()
