"""Construct a two-crossing lift of selected long eight-dimensional middles by alternating donor placements."""
from argparse import ArgumentParser
from hashlib import sha256
import sys
from archive import HERE, MS, read, write, code
from grow import independent_check
sys.path.insert(0,str(next(MS.glob("270-*"))))
from place_historical import library, segments, physical, bank
import json

def earlier(round_num, filename):
    return json.loads((next(MS.glob(str(round_num)+"-*"))/filename).read_bytes())

def input_middles(limit):
    result={}
    def add(p,note):
        assert all(0<=v<256 for v in p)
        key=code(p).hex()
        if key not in result: result[key]=(p,note)
    for item in earlier(246,"donors.json")["shapes"]:
        if len(item["path"])==99: add(item["path"],"Round 246 published 98-edge shape")
    direct=earlier(277,"q8-new.json")
    for key,row in sorted(direct.items(),key=lambda kv:(-len(kv[0]),kv[0])):
        if len(result)>=limit:break
        add(row["joined_q8"],"Round 277 q8-new.json")
    options = []
    files = ("nearby-direct-single-parents.json", "nearby-direct-double-parents.json", "nearby-shortened-single-parents.json", "q8-new.json", "q8-arms.json")
    for priority, filename in enumerate(files):
        path=next(MS.glob("277-*"))/filename
        if not path.exists(): continue
        rows=json.loads(path.read_bytes())
        for k,v in rows.items():
            if len(k)<190:continue
            p=v["joined_q8"]
            assert code(p).hex()==k
            known=bool(v.get("in_previous_pool", False)) if filename.startswith("nearby-") else filename=="q8-arms.json"
            options.append((-len(k),known,priority,k,p,filename))
    for _,_,_,k,p,filename in sorted(options,key=lambda row:row[:4]):
        if len(result)>=limit:break
        add(p,"Round 277 "+filename)
    placements=earlier(274,"union-placements.json")["roots"]
    for k,r in sorted(placements.items(),key=lambda kv:(-len(kv[1]["parent"]),-kv[1]["best"]["edges"],kv[0])):
        if len(result)>=limit: break
        add(r["parent"],"Round 274 "+k)
    return result

def run(opt):
    middles=input_middles(opt.limit)
    pool=set(library())|{bytes.fromhex(k) for k in middles}
    parents=earlier(274,"union-placements.json")["roots"]
    for r in parents.values():
        pool.add(code(r["parent"]));pool.add(code(r["best"]["B"]))
    words=sorted(segments(sorted(pool),84,98))
    images=list(bank.permutation_images())
    rows={}; prior={}
    for r in parents.values(): prior.setdefault(code(r["parent"]),[]).append((r["parent"],r["best"]["B"]))
    def extend(mid,side,other):
        pivot=mid[0]
        fixed={v^pivot for v in mid[1:]}
        for v in other:
            fixed.add(v^pivot)
            fixed.update((v^pivot)^(1<<j) for j in range(8))
        assert 0 not in fixed
        allowed=bank.allowed_maps([0,*fixed],images)
        n,word,index=bank.longest(words,allowed)
        new=[x^pivot for x in physical(word[:n]).translate(images[index])]
        return new if len(new)>len(side) else side
    for k,(source,note) in middles.items():
        m=list(source)
        states=[([m[0]],[m[-1]],"from ports")]
        for seed,partner in prior.get(bytes.fromhex(k),[]):
            # Transfer the donor using the unique axis map fixed by the directed middle.
            for x in (m,m[::-1]):
                f={i^j:u^v for i,j,u,v in zip(seed,seed[1:],x,x[1:])}
                if len(f)!=8 or len(set(f.values()))!=8: continue
                def image(v): return x[0]^sum(b for a,b in f.items() if v&a)
                if [image(v^seed[0]) for v in seed]!=x: continue
                arm=[]
                for v in partner:
                    u=image(v)
                    if (u^x[-1]).bit_count()<=1: break
                    arm.append(u)
                if not arm:continue
                states.append((arm,[x[-1]],"one-crossing donor") if x==m else ([x[-1]],arm,"one-crossing donor"))
        starts=list(states)
        for side in (0,1):
            x=m if side==0 else m[::-1]
            for d in range(8):
                v=x[0]^(1<<d)
                if v in m or (v^x[-1]).bit_count()<=1: continue
                if side==0: states.append(([x[0],v],[x[-1]],"one prescribed edge"))
                else: states.append(([x[-1]],[x[0],v],"one prescribed edge"))
        seen=set(); best=None; examined=0; steps=0
        for a,b,label in states:
            for leftfirst in ([False,True] if label!="one prescribed edge" else [len(b)>1]):
                workA,workB=a[:],b[:]
                for i in range(opt.passes):
                    flip=leftfirst if i%2==0 else not leftfirst
                    token=(tuple(workA),tuple(workB),flip)
                    if token in seen: break
                    seen.add(token)
                    if flip: workA=extend(m,workA,workB)
                    else: workB=extend(m[::-1],workB,workA)
                    steps+=1
                    path=workA[::-1]+[256+v for v in m]+workB
                    independent_check(path)
                    if best is None or len(path)>len(best["path"]):
                        best=dict(path=path,arm_lengths=[len(workA)-1,len(workB)-1],start=label)
                examined+=1
        assert best is not None
        rows[k]=dict(source=note,middle=m,starts=examined,placements=steps,edges=len(best["path"])-1,**best)
        write("lift-placements.json",dict(pool=len(pool),words=len(words),permutations=len(images),results=rows))
        print(note,len(m)-1,len(best["path"])-1,steps,flush=True)
        if len(best["path"])-1>=192: write("candidate-192.json",rows[k]);return

if __name__=="__main__":
    ap=ArgumentParser();ap.add_argument("--limit",type=int,default=10);ap.add_argument("--passes",type=int,default=4)
    run(ap.parse_args())



