"""Every Q8 93-edge window in all 131 source snakes, placed at each parent endpoint."""
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path
import subprocess
from partner93 import source_parent
from solve import BANK,BANK_HASH,defects,save


def canonical(word):
    names={}
    return tuple(names.setdefault(b,len(names)) for b in word)


def windows():
    raw=BANK.read_bytes();assert sha256(raw).hexdigest()==BANK_HASH
    seeds=json.loads(raw);classes={}
    for seed,record in enumerate(seeds):
        path=record["vertex_sequence"];moves=[(a^b).bit_length()-1 for a,b in zip(path,path[1:])]
        for t in range(len(moves)-92):
            seq=moves[t:t+93]
            if len(set(seq))>8:continue
            for rev,order in ((False,seq),(True,seq[::-1])):
                key=canonical(order)
                classes.setdefault(key,[seed,t,rev,0])[3]+=1
    return classes


def scan(exe):
    parent=source_parent()
    keys=windows()
    results=[]
    for root in (0,78):
        forbidden=set(parent)-{root}
        header=[root,94,len(keys),len(forbidden),*sorted(forbidden)]
        data=" ".join(map(str,header))+"\n"+"\n".join(" ".join(map(str,k)) for k in keys)
        run=subprocess.run([str(exe)],input=data,text=True,capture_output=True,check=True)
        lines=run.stdout.splitlines();assert len(lines)==len(keys)
        rows=[]
        for (moves,source),line in zip(keys.items(),lines):
            score,attain,*perm=map(int,line.split())
            path=[root]
            for b in moves:path.append(path[-1]^(1<<perm[b]))
            assert not defects(path) and score==len(set(path)&forbidden)
            row=dict(source=source,score=score,number=attain,permutation=perm)
            if score==0:
                q=parent if parent[-1]==root else parent[::-1]
                witness=q+[v|256 for v in path]
                assert len(witness)==193 and not defects(witness)
                row["witness"]=witness
            rows.append(row)
        results.append(dict(root=root,rows=rows))
        print(root,len(rows),sum(v[3] for v in keys.values()),Counter(r["score"] for r in rows),flush=True)
    save(Path("partner-orbits.json"),results)


if __name__=="__main__":
    import argparse
    p=argparse.ArgumentParser();p.add_argument("--exe",type=Path,default=Path("partner-orbits.exe"))
    scan(p.parse_args().exe.resolve())
