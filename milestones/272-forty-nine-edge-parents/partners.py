"""Enumerate the unrestricted opposite Q7 paths at both ends of every selected 49-edge parent."""
from argparse import ArgumentParser
from collections import Counter
from hashlib import sha256
from tempfile import TemporaryDirectory
import subprocess
from parents import HERE,R270,read,points,paircheck,unrooted
from primer_census import CSC,write

def enumerate_roots(catalogue,mode):
    cases=read(catalogue)["parents"]
    main=HERE/"partners.json"; replay=HERE/"partner-replay.json"
    results=read(main if mode=="mask" else replay) if (main if mode=="mask" else replay).exists() else {}
    problem=R270/"PrimerPartners.cs"
    with TemporaryDirectory() as direct:
        from pathlib import Path
        tmp=Path(direct); exe=tmp/"Census.exe"; out=tmp/"paths.csv"
        subprocess.run([str(CSC),"/nologo","/optimize+","/platform:x64","/out:"+str(exe),str(problem)],capture_output=True,check=True)
        for word in cases:
            for end in range(2):
                key=word+"/"+str(end)
                if results.get(key,{}).get("complete"):continue
                p=points(bytes.fromhex(word)[::1 if end==0 else -1])
                paircheck(p,7)
                command=[str(exe),mode,"46","900000000","75",str(out)]
                r=subprocess.run(command,input=",".join(map(str,p))+"\n0\n",text=True,capture_output=True,check=True)
                status,nodes,total,parity,component=r.stdout.split()
                found=sorted(bytes(map(int,line.split(","))).hex() for line in out.read_text(encoding="ascii").splitlines())
                assert len(found)==len(set(found))==int(total)
                for q in found:
                    part=list(bytes.fromhex(q))
                    assert part[0]==0 and len(part)>=47 and set(p)&set(part)=={0}
                    paircheck(p[::-1]+[128|v for v in part],8)
                digest=sha256(("\n".join(found)+"\n").encode()).hexdigest()
                row=dict(complete=status=="complete",nodes=int(nodes),parity_cuts=int(parity),component_cuts=int(component),
                         partner_lengths=Counter(len(q)//2-1 for q in found),partners_sha256=digest)
                if mode=="array" and row["complete"]:
                    previous=read(main)[key]
                    assert previous["complete"] and found==previous["partners"] and digest==previous["partners_sha256"]
                elif mode=="mask":
                    row["partners"]=found
                results[key]=row
                write(main if mode=="mask" else replay,results)
                print(mode,word[:14],end,status,len(found),dict(row["partner_lengths"]),flush=True)

if __name__=="__main__":
    ap=ArgumentParser();ap.add_argument("catalogue");ap.add_argument("mode",choices=["mask","array"]);a=ap.parse_args()
    enumerate_roots(HERE/a.catalogue,a.mode)
