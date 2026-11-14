"""Compare every truth value in a sample of locks to explicit four-path joins in Q3 times Q2."""
from collections import defaultdict
from pathlib import Path
import random,subprocess,sys
from solve import defects,save


def paths():
    seq=[]
    def grow(q):
        if len(q)>=2:seq.append(tuple(q))
        for b in range(3):
            w=q[-1]^(1<<b)
            if w not in q and all((v^w).bit_count()!=1 for v in q[:-1]):grow(q+[w])
    for v in range(8):grow([v])
    return seq


if __name__=="__main__":
    seq=paths();assert max(map(len,seq))==5
    sets={q:set(q) for q in seq}
    after={q:[r for r in seq if q[-1]==r[0] and sets[q]&sets[r]=={r[0]}] for q in seq}
    truth={m:defaultdict(set) for m in ("prefix","middle","outer")};examples={}
    for a in seq:
        for b in after[a]:
            for c in after[b]:
                for d in after[c]:
                    if sets[a]&sets[d]:continue
                    record=(a,b,c,d);n=sum(map(len,record))
                    for name,key in (("prefix",(a,b)),("middle",(b,c)),("outer",(a,d))):
                        truth[name][key].add(n);examples[name,key]=record
    rng=random.Random(14);tests=positive=negative=0
    exe=Path(sys.argv[1] if len(sys.argv)>1 else "adjacent-tree.exe").resolve()
    for mode in truth:
        keys=rng.sample(sorted(truth[mode]),min(250,len(truth[mode])))
        rows=[examples[mode,k] for k in keys];stdin=[]
        for i,row in enumerate(rows):
            toks=[i]
            for q in row:toks.extend((len(q),*q))
            stdin.append(" ".join(map(str,toks)))
        flips=[(0,0),(1,0),(0,1),(1,1)] if mode=="outer" else [(0,0)]
        for f,g in flips:
            for target in range(9,21):
                cmd=[str(exe),str(target),"1000000",mode]
                if mode=="outer":cmd.extend(map(str,(f,g)))
                out=subprocess.run([*cmd,"q3"],input="\n".join(stdin),text=True,capture_output=True,check=True)
                lines=out.stdout.splitlines();assert len(lines)==len(keys)
                for i,line in enumerate(lines):
                    idx,status,*rest=line.split();assert int(idx)==i and status in ("FOUND","EXHAUSTED")
                    k=keys[i]
                    if f or g:k=(k[0][::-1] if f else k[0],k[1][::-1] if g else k[1])
                    expected=target in truth[mode].get(k,set());assert expected==(status=="FOUND"),(mode,i,k,target,status)
                    tests+=1;positive+=expected;negative+=not expected
    save(Path("adjacent-tree-control.json"),dict(Q3_paths=len(seq),truth_values=tests,positive=positive,negative=negative))
    print(len(seq),tests,positive,negative)
