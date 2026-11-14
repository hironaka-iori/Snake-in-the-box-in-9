"""Supply all unique bank parities to the coordinate-face syndrome survey."""
import argparse
from collections import Counter
import json
from pathlib import Path
import subprocess
from solve import BANK,BANK_HASH,sha256,save
from syndrome import neighbour_syndrome
from source_growth import check


if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("first",type=int);parser.add_argument("stop",type=int)
    parser.add_argument("--patterns",type=Path,default=Path("syndrome-face-patterns.txt"))
    parser.add_argument("--exe",type=Path,default=Path("syndrome-face.exe"))
    a=parser.parse_args()
    raw=BANK.read_bytes();assert sha256(raw).hexdigest()==BANK_HASH
    records=json.loads(raw);seeds={};originals={}
    for i,r in enumerate(records):
        for p in (0,1):
            anchors=tuple(sorted(r["vertex_sequence"][p::2]))
            if anchors not in seeds:seeds[anchors]=len(seeds);originals[seeds[anchors]]=[i,p]
    groups=list(seeds)[a.first:a.stop]
    patterns=a.patterns.read_text().splitlines()
    lines=[f"{len(patterns)} {len(groups)}",*patterns]
    for anchors in groups:
        i=seeds[anchors];geo=originals[i][1]
        lines.append(" ".join(map(str,[i,geo,*anchors])))
    proc=subprocess.run([str(a.exe.resolve())],input="\n".join(lines),text=True,capture_output=True,check=True)
    details={};counts={};tags=[]
    for line in proc.stdout.splitlines():
        tag,*values=line.split();i,p,*rest=map(int,values)
        assert originals[i][1]==p
        if tag=="count":
            assert rest[0]==len(patterns) and rest[2]==len(details.get(i,[]))
            counts[i]=rest
        else:
            assert tag=="pass" and len(rest)==1
            j=rest[0];n,*changes=map(int,patterns[j].split())
            if p==0:changes=[v^1 for v in changes]
            anchors=list(seeds)[i]
            target=set(anchors)^neighbour_syndrome(set(changes))
            assert len(target)==(96 if n%2==0 else 97)
            why,w=check(target,n%2==0);tags.append(why)
            details.setdefault(i,[]).append(dict(pattern=j,reason=why,witness=w))
    assert len(counts)==len(groups)
    save(Path(f"syndrome-faces-{a.first}-{a.stop}.json"),dict(counts=counts,details=details,originals=originals,
         pattern_sha256=sha256(a.patterns.read_bytes()).hexdigest()))
    print(len(groups),sum(v[1] for v in counts.values()),Counter(tags),flush=True)
