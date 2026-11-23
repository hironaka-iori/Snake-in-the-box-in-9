"""Minimise extra common vertices of a 96-edge parent and a rooted 95-edge donor."""
from hashlib import sha256
from pathlib import Path
import json
import sys

HERE = Path(__file__).resolve().parent
MS = HERE.parent
R257 = MS/"257-three-exchange-parents"
sys.path.insert(0,str(MS/"251-eighty-edge-segments"))
import bank_capacity as bank

def load(p): return json.loads(p.read_bytes())
def digest(p): return sha256(p.read_bytes()).hexdigest()
def save(p,v): p.write_text(json.dumps(v,separators=(",",":"))+"\n",encoding="utf-8",newline="\n")

def inputs():
    sources=[(MS/"253-repeated-segment-growth/closure.json","paths"),
             (MS/"254-distant-arm-partners/parity-families.json","shapes"),
             (MS/"255-parity-exchange-arms/focus-closure.json","paths"),
             (MS/"258-four-exchange-parents/new-arms.json","shapes"),
             (MS/"259-four-exchange-component/new-arms.json","shapes"),
             (MS/"255-parity-exchange-arms/partner-pool.json","shapes")]
    donors={}
    for f,k in sources: donors.update(load(f)[k])
    words={}
    for shape,path in sorted(donors.items()):
        bank.check_path(path,8)
        for end,order in enumerate((path,path[::-1])):
            for start in range(len(order)-95):
                segment=order[start:start+96]
                axes=[(a^b).bit_length()-1 for a,b in zip(segment,segment[1:])]
                first=list(dict.fromkeys(axes))
                if len(first)!=8: raise ValueError("Missing direction")
                word=bytes(first.index(a) for a in axes)
                words.setdefault(word,[shape,end,start])
    src=R257/"summary.json"
    arms=R257/"partner-input.json"
    stats=load(src)
    all_paths=load(arms)["shapes"]
    parents={k:all_paths[k] for k in sorted(set(stats["distant_two"]["unresolved"]+stats["distant_three"]["unresolved"]))}
    return words,parents,[p for p,_ in sources]+[src,arms],len(donors)

def vertices(word):
    path=[0]
    for a in word: path.append(path[-1]^(1<<a))
    return path

def census(words,allowed,limit):
    # Entry j contains the coordinate permutations with exactly j collisions so far.
    states=[(0,[bank.ALL_MAPS]+[0]*limit)]
    previous=b""
    best=limit
    minima=[]
    for word in words:
        while len(states)>1 and previous[:len(states)-1]!=word[:len(states)-1]:
            states.pop()
        v,counts=states[-1]
        for axis in word[len(states)-1:]:
            if not any(counts[:best+1]): break
            v^=1<<axis
            good=allowed[v]
            bad=bank.ALL_MAPS^good
            counts=[counts[0]&good]+[(counts[k]&good)|(counts[k-1]&bad) for k in range(1,best+1)]
            states.append((v,counts))
        previous=word
        if len(states)!=96: continue
        for k,perms in enumerate(counts[:best+1]):
            if not perms: continue
            if k<best:
                minima=[]
                best=k
            while perms:
                bit=perms & -perms
                minima.append([word.hex(),bit.bit_length()-1])
                perms^=bit
            break
    return best,minima

if __name__=="__main__":
    words,parents,files,donors=inputs()
    maps=list(bank.permutation_images())
    manifest=dict(donors=donors,words={w.hex():v for w,v in sorted(words.items())},parents=parents,
                  sources={f.relative_to(MS).as_posix():digest(f) for f in files})
    save(HERE/"catalogue.json",manifest)
    rows={}
    for shape,p in parents.items():
        for end,order in enumerate((p,p[::-1])):
            parent=[v^order[0] for v in order]
            allowed=bank.allowed_maps(parent,maps)
            for cap in (2,5,9,16,95):
                best,winners=census(sorted(words),allowed,cap)
                if winners: break
            for word,rank in winners:
                image=[maps[rank][v] for v in vertices(bytes.fromhex(word))]
                if len(set(image)&set(parent))!=1+best: raise ValueError("Incorrect intersection")
                if best==0: bank.check_path(parent[::-1]+[v+256 for v in image],9)
            rows[shape+":"+str(end)]=dict(parent=parent,minimum=best,winners=winners)
        print(shape[:9],[(r["minimum"],len(r["winners"])) for r in list(rows.values())[-2:]],flush=True)
    save(HERE/"minimum.json",dict(catalogue_sha256=digest(HERE/"catalogue.json"),rows=rows,
        placements_per_root=len(words)*len(maps),total_placements=len(rows)*len(words)*len(maps)))
