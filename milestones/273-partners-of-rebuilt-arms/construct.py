"""Place and regrow donor paths against the new 49-edge-primer arms."""
from argparse import ArgumentParser
from collections import Counter
from hashlib import sha256
from pathlib import Path
from tempfile import TemporaryDirectory
import subprocess
import sys

HERE=Path(__file__).resolve().parent
MS=HERE.parent
R272=MS/"272-forty-nine-edge-parents"
R271=MS/"271-rebuilt-historical-partners"
R270=MS/"270-optimal-seven-dimensional-arms"
sys.path.insert(0,str(R270))
from place_historical import bank,checked,word,physical,rename,library,segments,identifier,CSC,read,write
from align import counter

def source_shapes():
    rows=read(R272/"q8-arms.json")
    old=set(library())
    old.update(bytes.fromhex(r["shape"]) for r in read(R270/"opposite-constructions.json")["roots"].values())
    old.update(word(r["path"]) for r in read(MS/"246-eight-dimensional-parents/donors.json")["shapes"])
    fresh={}
    for name,r in rows.items():
        code=bytes.fromhex(name)
        # Keep the earlier whole shape as a control.
        p=r["joined_q8"]
        assert code==word(p) and len(p)-1==r["q8_edges"] and 96<=len(code)<=98
        bank.check_path(p,8)
        fresh[code]=r
    return fresh,old

def donor_words(fresh):
    archive=read(MS/"266-rebuilding-one-arm/parents.json")["parents"]
    oldroots=read(R270/"opposite-constructions.json")["roots"]
    primary=set()
    banked=set(library())|set(fresh)
    banked.update(word(r["path"]) for r in read(MS/"246-eight-dimensional-parents/donors.json")["shapes"])
    for r in archive.values():
        donors=[r["parent"],*r["partners"].values()]
        banked.update(word(p) for p in donors)
        if r["from_191"]:primary.update(word(p) for p in donors)
    for r in oldroots.values():
        banked.add(word(r["parent"]))
        banked.add(word(r["best"]["B"]))
        banked.update(word(p) for p in r["history"].values())
    for r in read(R271/"long-joins.json")["witnesses"]:
        for p in (r["parent"],r["partner"]):
            primary.add(word(p))
    for r in read(R271/"retained-site-replay.json").values():
        joined=r["joined"]
        primary.add(word([v-256 for v in joined if v>=256]))
    primary.update(w for w in banked if len(w)==98)
    return sorted(w for w in banked|primary if len(w)>=84),primary

def near_miss(parent,allowed,images,shortlist,target):
    best=None
    for w in sorted({rename(s[:target]) for code in shortlist for s in (code,code[::-1]) if len(s)>=target-4}):
        sites=physical(w)
        live=bank.ALL_MAPS;value=0
        for level,column in reversed(list(enumerate(counter.columns(bank.ALL_MAPS^allowed[u] for u in sites[1:])))):
            clear=live&~column
            if clear:live=clear
            else:
                live &= column
                value += 1<<level
        rank=(live&-live).bit_length()-1
        candidate=list(sites.translate(images[rank]))
        extra=sorted(set(candidate[1:])&set(parent))
        assert len(extra)==value
        score=(target-len(w)+value,value,w,rank)
        if best is None or score<best[0]:
            best=(score,dict(word=w.hex(),rank=rank,donor=candidate,intersections=extra,
                             needed_new_sites=score[0],ties=live.bit_count()))
    return best[1]

def main():
    ap=ArgumentParser()
    ap.add_argument("--iterations",type=int,default=3200)
    ap.add_argument("--top",type=int,default=24)
    args=ap.parse_args()
    fresh,old=source_shapes();donors,shortlist=donor_words(fresh)
    words_map=segments(donors,84,98);words=sorted(words_map)
    paths=[list(physical(w)) for w in donors]
    images=list(bank.permutation_images())
    targets={191-len(w) for w in fresh}
    target_words={t:sorted({w[:t] for w in words if len(w)>=t}) for t in targets}
    backwards={t:[physical(w)[:0:-1] for w in pool] for t,pool in target_words.items()}
    roots={}
    for code in sorted(fresh,key=lambda w:(-len(w),w)):
        for w in (code,code[::-1]):
            A=list(physical(rename(w)));k=identifier(A)
            if k in roots:continue
            allowed=bank.allowed_maps(A,images)
            placed=bank.longest(words,allowed)
            joined=bank.make_witness(paths,words_map[placed[1]],placed,A)
            t=192-len(A)
            hits=0
            for seq in backwards[t]:
                live=bank.ALL_MAPS
                for u in seq:
                    live&=allowed[u]
                    if not live:break
                hits+=live.bit_count()
            assert bool(hits)==(joined["joined_edges"]>=192)
            near=near_miss(A,allowed,images,shortlist,t)
            roots[k]=dict(parent=A,shape=code.hex(),history={},placement=joined,best=checked(A,joined["partner"]),
                          target_placements=hits,repair_start=near)
            if hits:write(HERE/"candidate-192.json",roots[k])
    ranked=sorted(roots,key=lambda k:(roots[k]["repair_start"]["needed_new_sites"],-roots[k]["best"]["edges"],k))
    by_score=sorted(roots,key=lambda k:(-roots[k]["best"]["edges"],k))
    selected=list(dict.fromkeys(key for pair in zip(ranked,by_score) for key in pair))[:args.top]
    with TemporaryDirectory() as dirname:
        exe=Path(dirname)/"Regrow.exe"
        subprocess.run([str(CSC),"/nologo","/optimize+","/out:"+str(exe),str(MS/"265-joint-arm-regrowth/JoinedSearch.cs")],check=True,capture_output=True)
        for i,k in enumerate(selected):
            r=roots[k];p=r["parent"];q=r["best"]["B"];seed=273101+i
            proc=subprocess.run([str(exe),str(seed),str(args.iterations),"fixed"],input="".join(",".join(map(str,b))+"\n" for b in (p,q)),capture_output=True,text=True,check=True)
            a,b=(list(map(int,l.split(","))) for l in proc.stdout.splitlines()[:2])
            assert a==p and len(b)>=len(q)
            r["regrowth"]=dict(seed=seed,iterations=args.iterations,before=r["best"]["edges"])
            r["best"]=checked(a,b)
            if r["best"]["edges"]>=192:write(HERE/"candidate-192.json",r)
    for k,r in roots.items():
        assert r["best"]["A"]==r["parent"] and identifier(r["parent"])==k
        p=r["best"]["joined"];sel=set(p)
        for j,u in enumerate(p):
            assert {u^(1<<i) for i in range(9)}&sel==set(p[max(0,j-1):j]+p[j+1:j+2])
    result=dict(roots=roots,source_sha256=sha256((R272/"q8-arms.json").read_bytes()).hexdigest(),
                fixed_shapes=dict(Counter(map(len,fresh))),earlier_whole_controls=len(set(fresh)&old),source_shapes=len(read(R272/"q8-arms.json")),earlier_shapes=len(old),
                donor_shapes=len(donors),donor_words=len(words),target_words={t:len(ws) for t,ws in target_words.items()},
                near_donors=len(shortlist),placements=sum(r["target_placements"] for r in roots.values()),
                before_regrowth=max((r["placement"]["joined_edges"] for r in roots.values()),default=0),
                after_regrowth=max((r["best"]["edges"] for r in roots.values()),default=0),
                overlap_shortfalls=Counter(r["repair_start"]["needed_new_sites"] for r in roots.values()))
    write(HERE/"opposite-constructions.json",result)
    print({k:v for k,v in result.items() if k!="roots"},flush=True)

if __name__=="__main__":main()
