from pathlib import Path
from hashlib import sha256
import json,re,sys,subprocess
dir=Path(__file__).resolve().parent
source=Path(sys.argv[1])
target=Path(sys.argv[2]) if len(sys.argv)>2 else dir/"palani-q7.json"
pages=subprocess.check_output(["pdftotext","-layout","-f","54","-l","56",str(source),"-"]).decode("utf8").split("\f")[:3]
def rows(page,num):
    lines=page.splitlines()
    start=next(i for i,l in enumerate(lines) if re.match(r"^7\s+1\s+1\s",l))
    listed=[]
    for i,line in enumerate(lines[start:start+12]):
        ns=list(map(int,line.split()))
        if i==0: assert ns.pop(0)==7
        assert ns[0]==i+1
        listed.append(ns[-num:])
    return listed
words=rows(pages[0],50)
a,b=rows(pages[1],27),rows(pages[2],24)
names=[]
result={}
for i,word in enumerate(words):
    path=[0]
    for k in word: path.append(path[-1]^(1<<k))
    assert path==a[i]+b[i] and len(set(path))==51 and all(0<=v<128 for v in path)
    assert all(((x^y).bit_count()==1)==(j==i+1) for i,x in enumerate(path) for j,y in enumerate(path[i+1:],i+1))
    w="".join(map(str,word))
    assert w not in names;names.append(w)
    result["Palani-"+str(i+1)]=dict(word=w,q7_parent=path)
def rename(w):
    return "".join(str(list(dict.fromkeys(w)).index(ch)) for ch in w)
orbits={w:min(w,rename(w[::-1])) for w in names}
rec=dict(url="https://ai.uga.edu/sites/default/files/inline-files/theses/palani_ananta.pdf",pdf_pages=[54,55,56],printed_pages=[41,42,43],
         tables="5.1 and 5.2",pdf_sha256=sha256(source.read_bytes()).hexdigest(),paths=result,
         reversal_pairs={str(i+1):names.index(rename(w[::-1]))+1 for i,w in enumerate(names)})
print(len(orbits),len(set(orbits.values())),rec['reversal_pairs'])
target.write_text(json.dumps(rec,indent=2)+"\n",encoding="utf8",newline="\n")

