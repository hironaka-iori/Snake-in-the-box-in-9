"""Extract the stated paths from pdftotext -layout output for the three cited primary sources."""
from pathlib import Path
from hashlib import sha256
import json, re, sys, gzip
from itertools import combinations
BASE=Path(sys.argv[1])
destination=Path(sys.argv[2])
def read(n):return (BASE/("snake9-"+n+".txt")).read_text(encoding="utf-8")
def vertices(word):
    result=[0]
    for axis in word:result.append(result[-1]^(1<<axis))
    return result
def norm(word):
    def form(w):
        chars=list(dict.fromkeys(w))
        return bytes(chars.index(c) for c in w)
    return min(form(word),form(word[::-1])).hex()
def check(path,d):
    assert len(set(path))==len(path) and all(0<=v<1<<d for v in path)
    for i,j in combinations(range(len(path)),2):
        assert ((path[i]^path[j]).bit_count()==1)==(i+1==j),(d,i,j)
def digits(text):return list(map(int,re.sub(r"\s","",text)))
def edges(p):return [(a^b).bit_length()-1 for a,b in zip(p,p[1:])]
all_paths={}
s=read("casella2005").split("A.1   dim 9 : 186")[-1].split("A.2")[0]
w=digits(s)
assert len(w)==186
check(vertices(w),9)
assert w.index(8)==97 and w.count(8)==1
all_paths["Casella-A1"]=w[:97]
q9={"Casella-A1":w}
s=read("bitterman2004").split("D.1   New Lower Bounds")[-1]
b9=s.split("New Lower Bound of s(9)=182:")[1].split("New Lower Bound of c(9)")[0]
w=[int(v)-1 for v in re.findall(r"\d+",b9)]
assert len(w)==182 and w.index(8)==97 and w.count(8)==1
check(vertices(w),9)
all_paths["Bitterman-D1"]=w[:97]
q9["Bitterman-D1"]=w
s=s.split("D.2   More Long Snakes from s(8)")[-1].split("Bibliography")[0]
s=re.sub(r"\x0c[ \t]+\d+\s*","",s)
for i,chunk in enumerate(re.findall(r"\[([1-8,\s*]+)\]",s),1):
    w=[int(v)-1 for v in re.findall(r"\d+",chunk)]
    all_paths["Bitterman-D2-"+str(i)]=w
s=read("atluri2009").split("sequence of zeros and ones below")[-1]
bits=digits(s.split("Bit Representation:")[1].split("Converted to Node")[0])
p=list(map(int,re.findall(r"\d+",s.split("Converted to Node Representation:")[1].split("\x0c")[0])))
assert len(bits)==256 and len(p)==99 and set(p[:98]) <= {i for i,v in enumerate(bits) if v}
assert [i for i,u in enumerate(p[:-2]) if (u^p[-1]).bit_count()==1]==[45,75]
all_paths["Atluri-p147-prefix"]=edges(p[:98])
for k,w in all_paths.items():
    assert len(w)==97,(k,len(w))
    check(vertices(w),8)
paths={k:{"word":"".join(map(str,w)),"canonical":norm(w)} for k,w in all_paths.items()}
urls={"casella2005":"https://www.ai.uga.edu/sites/default/files/inline-files/theses/casella_darren.pdf",
      "bitterman2004":"https://openscholar.uga.edu/record/19672","atluri2009":"https://openscholar.uga.edu/record/21280"}
docs={k:dict(url=v,pdf_sha256=sha256((BASE/("snake9-"+k+".pdf")).read_bytes()).hexdigest()) for k,v in urls.items()}
destination.write_bytes((json.dumps(dict(documents=docs,paths=paths,nine_dimensional={k:"".join(map(str,w)) for k,w in q9.items()}),indent=2)+"\n").encode())
print("Literal paths",len(paths),"symmetry classes",len({r["canonical"] for r in paths.values()}))
print("Counts of eighth-coordinate crossings", {k:v.count(7) for k,v in all_paths.items()})
