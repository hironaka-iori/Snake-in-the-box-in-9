"""Enumerate all coordinate permutations and translations, retaining a nearest distinct image."""
from tempfile import TemporaryDirectory
from pathlib import Path
import os,subprocess,math
from inputs276 import HERE,read,save,valid,canonical
from collections import Counter

def main():
    p=read(HERE/"input-arms.json")["known_endpoints"]["0"]["parent"]
    with TemporaryDirectory(prefix="q9-orbit276-") as t:
        exe=Path(t)/"Orbit.exe";csc=Path(os.environ["WINDIR"])/"Microsoft.NET/Framework64/v4.0.30319/csc.exe"
        subprocess.run([str(csc),"/nologo","/optimize+","/out:"+str(exe),str(HERE/"Orbit.cs")],capture_output=True,check=True)
        r=subprocess.run([str(exe)],input=",".join(map(str,p))+"\n",text=True,capture_output=True,check=True).stdout.splitlines()
        counts=dict((i,n) for i,n in enumerate(map(int,r[0].split(","))) if n)
        permutation=list(map(int,r[1].split(",")));offset=int(r[2])
        assert sorted(permutation)==list(range(8)) and sum(counts.values())==256*math.factorial(8)
        def image(v):return offset^sum(1<<permutation[i] for i in range(8) if v&(1<<i))
        q=[image(v) for v in p];d=len(set(p)-set(q))
        assert valid(q,8)==4851 and canonical(q)==canonical(p) and d==min(i for i in counts if i)
        assert counts[0] in (1,2) and all(n%counts[0]==0 for n in counts.values())
        save(HERE/"isometry-orbit.json",dict(histogram=counts,orbit=len(range(256))*math.factorial(8)//counts[0],
             stabilizer=counts[0],minimum_positive=d,permutation=permutation,translation=offset,path=q,
             removed=sorted(set(p)-set(q)),added=sorted(set(q)-set(p))))
        print("Nearest nonidentity occupied-set image",d,"replacements, multiplicity",counts[d]//counts[0],"stabilizer",counts[0],flush=True)
if __name__=="__main__":main()
