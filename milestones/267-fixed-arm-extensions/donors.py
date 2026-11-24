"""Generate candidate opposite arms near long Q8 donors, then place them against fixed parents."""
from argparse import ArgumentParser
from collections import Counter
from functools import lru_cache
from hashlib import sha256
from pathlib import Path
import gzip
import sys

from prepare import HERE, MS, LAST, bank, read, write
sys.path.insert(0,str(MS/"265-joint-arm-regrowth"))
from exchange import variants
from growth import checked

def rename(steps):
    letters=bytes(dict.fromkeys(steps))
    return steps.translate(bytes.maketrans(letters,bytes(range(len(letters)))))

@lru_cache(maxsize=8192)
def unrooted(arm):
    bits=bytes((v^w).bit_length()-1 for v,w in zip(arm,arm[1:]))
    return min(rename(bits),rename(bits[::-1]))

def physical(word):
    p=[0]
    for j in word:
        p.append(p[-1]^(1<<j))
    return bytes(p)

def seeds():
    files=[("246-eight-dimensional-parents/donors.json","shapes"),("253-repeated-segment-growth/closure.json","paths"),
           ("255-parity-exchange-arms/focus-closure.json","paths"),("259-four-exchange-component/new-arms.json","shapes"),
           ("266-rebuilding-one-arm/windows.json","paths")]
    source={}
    inputs=set()
    for file,field in files:
        path=MS/file
        source[file]=sha256(path.read_bytes()).hexdigest()
        data=read(path)[field]
        seqs=data.values() if isinstance(data,dict) else (r["path"] for r in data)
        for seq in seqs:
            if len(seq)>=96:
                inputs.add(unrooted(bytes(seq)))
    return sorted(inputs,key=lambda w:(-len(w),w)),source

def generate(limit):
    starts,sources=seeds()
    words=list(starts)
    parents=[-1]*len(words)
    index=set(words)
    i=0
    while i<len(words) and len(words)<limit:
        q=physical(words[i])
        for order in (q,q[::-1]):
            arm=bytes(v^order[0] for v in order)
            for group in variants(arm):
                for moved,_ in group:
                    if len(moved)<96:
                        continue
                    word=unrooted(moved)
                    if word not in index:
                        index.add(word)
                        words.append(word)
                        parents.append(i)
        i+=1
    rows=[[w.hex(),pred] for w,pred in zip(words,parents)]
    import json
    path=HERE/"donor-paths.json.gz"
    with gzip.GzipFile(str(path),"wb",mtime=0) as f:
        f.write(json.dumps(rows,separators=(",",":")).encode())
    data=dict(start=len(starts),expanded=i,states=len(words),closed=i==len(words),threshold=95,limit=limit,
              start_lengths=Counter(map(len,starts)),lengths=Counter(map(len,words)),sources=sources,sha256=sha256(path.read_bytes()).hexdigest())
    write(HERE/"donors.json",data)
    print(data,flush=True)

def placement():
    import json
    data=read(HERE/"cases.json")
    donors=read(HERE/"donors.json")
    raw=(HERE/"donor-paths.json.gz").read_bytes()
    assert sha256(raw).hexdigest()==donors["sha256"]
    states=[bytes.fromhex(w) for w,_ in json.loads(gzip.decompress(raw))]
    paths=[list(physical(w)) for w in states]
    # A 95- or 96-edge subpath of a longer donor may start in its interior.
    libraries=[]
    for portion in (states[:donors["start"]],states):
        word_origins={}
        for i,w in enumerate(portion):
            for direction,seq in ((1,w),(-1,w[::-1])):
                for start in range(len(seq)-94):
                    word=rename(seq[start:start+96])
                    origin=start if direction==1 else len(seq)-start
                    word_origins.setdefault(word,(i,origin,direction))
        libraries.append((sorted(word_origins),word_origins))
    images=list(bank.permutation_images())
    dest=HERE/"placements.json"
    out=read(dest) if dest.exists() else dict(donors_sha256=donors["sha256"],words=[len(z[0]) for z in libraries],roots={})
    assert out["donors_sha256"]==donors["sha256"]
    order=sorted(data["roots"],key=lambda k:(not bool(data["roots"][k]["partners"]),not data["roots"][k]["window"],k))
    for k in order:
        if k in out["roots"]:
            continue
        case=data["roots"][k]
        p=case["parent"]
        allowed=bank.allowed_maps(p,images)
        best=[]
        for words,origins in libraries:
            fit=bank.longest(words,allowed)
            w=bank.make_witness(paths,origins[fit[1]],fit,p)
            best.append(w)
        assert best[1]["joined_edges"]>=best[0]["joined_edges"]
        row=dict(original_donors=best[0]["joined_edges"],expanded_placement=best[1])
        out["roots"][k]=row
        if best[1]["joined_edges"]>=192:
            write(HERE/"candidate-192.json",best[1])
            write(dest,out)
            return
        if len(out["roots"])%10==0:
            write(dest,out)
    write(dest,out)
    print("Rooted placements",len(out["roots"]),"best",max(r["expanded_placement"]["joined_edges"] for r in out["roots"].values()),flush=True)

if __name__=="__main__":
    ap=ArgumentParser()
    ap.add_argument("--generate",type=int)
    args=ap.parse_args()
    if args.generate:
        generate(args.generate)
    else:
        placement()
