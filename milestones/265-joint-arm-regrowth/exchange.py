"""Explore long one-crossing joins by vertex replacements, suffix reversal and endpoint edits."""
from argparse import ArgumentParser
from collections import Counter
from functools import lru_cache
from hashlib import sha256
from io import TextIOWrapper
from zipfile import ZipFile
import csv,gzip,json
from conditional import code
from tails import HERE,MS,BANK,load,save,digest,checked

N=[tuple(v^(1<<j) for j in range(8)) for v in range(256)]
M=[sum(1<<x for x in nb) for nb in N]
def mask(p):return sum(1<<v for v in p)
def key(a,b):
    sa=bytes(u^v for u,v in zip(a,a[1:]));sb=bytes(u^v for u,v in zip(b,b[1:]))
    def canon(x,y):
        w=x+b"\0"+y
        dims=bytes(dict.fromkeys(w))
        return w.translate(bytes.maketrans(dims,bytes(range(len(dims)))))
    # The separator position explicitly identifies the distinguished crossing.
    if len(sa)!=len(sb):return bytes([min(len(sa),len(sb))])+ (canon(sa,sb) if len(sa)<len(sb) else canon(sb,sa))
    return bytes([len(sa)])+min(canon(sa,sb),canon(sb,sa))

def choices(v):
    while v:
        bit=v&-v;yield bit.bit_length()-1;v-=bit

@lru_cache(maxsize=512)
def variants(p):
    # Reach every equal-length induced arm differing in at most one occupied site.
    s=mask(p);neutral={p:s}
    for i in range(1,len(p)):
        prev=p[i-1];remain=s^(1<<p[i])
        if i==len(p)-1:
            for w in choices(M[prev]&~s):
                if M[w]&remain==1<<prev:neutral[p[:i]+bytes([w])]=remain|(1<<w)
            continue
        for reverse in (False,True):
            nxt=p[-1] if reverse else p[i+1]
            for w in choices(M[prev]&M[nxt]&~s):
                if M[w]&remain!=(1<<prev)|(1<<nxt):continue
                suffix=p[i+1:][::-1] if reverse else p[i+1:]
                neutral[p[:i]+bytes([w])+suffix]=remain|(1<<w)
    out=[{},neutral,{}]
    for q,selected in neutral.items():
        tip=q[-1]
        out[0][q[:-1]]=selected^(1<<tip)
        if len(q)>=99:continue
        for v in choices(M[tip]&~selected):
            if M[v]&selected==1<<tip:out[2][q+bytes([v])]=selected|(1<<v)
    return [list(group.items()) for group in out]

def input_paths():
    archive=MS.parent/"work/record_snakes.csv.zip"
    with ZipFile(archive) as z:
        raw=z.read("snakes_dim9_190.csv")
        if sha256(raw).hexdigest()!=load(MS/"244-190-path-construction/results.json")["member_sha256"]:raise ValueError("190 source differs")
        with z.open("snakes_dim9_190.csv") as f:
            for i,row in enumerate(csv.DictReader(TextIOWrapper(f,encoding="utf8"))):
                yield "190-"+str(i),[int(v) for v in row["vertices"].split()]
    for i,r in enumerate(load(BANK)):yield "191-"+str(i),r["vertex_sequence"]

def charts(p):
    steps=[x^y for x,y in zip(p,p[1:])]
    for bit in dict.fromkeys(steps):
        if steps.count(bit)!=1:continue
        cut=steps.index(bit)
        def proj(seq):
            t=seq[0]
            return bytes(((v^t)&(bit-1))|(((v^t)//(bit*2))*bit) for v in seq)
        yield bit.bit_length()-1,proj(p[:cut+1][::-1]),proj(p[cut+1:])

def main():
    ap=ArgumentParser();ap.add_argument("--limit",type=int,default=6000);config=ap.parse_args()
    known={};starts={};chart_counts=Counter()
    for name,p in input_paths():
        known[code(p)]=name
        for axis,a,b in charts(p):
            k=key(a,b);starts.setdefault(k,(a,b,name,axis));chart_counts[str(len(p)-1)]+=1
    states=[(a,b,-1) for a,b,_,_ in starts.values()];seed_count=len(states);index={k:i for i,k in enumerate(starts)}
    moved=set();longest={};progress=0;links=0;edits=Counter();shapes=Counter();outside={};newBest=None
    fp=HERE/"exchange-states.json.gz"
    hit=False
    while progress<len(states) and len(states)<config.limit and not hit:
        a,b,_=states[progress]
        va,vb=variants(a),variants(b)
        for da in (1,0,-1):
            for db in (1,0,-1):
                length=len(a)+len(b)-1+da+db
                if length<190:continue
                for na,ma in va[1+da]:
                    for nb,mb in vb[1+db]:
                        if ma&mb!=1:continue
                        links+=1
                        k=key(na,nb)
                        if k in index:continue
                        dest=len(states);index[k]=dest;states.append((na,nb,progress))
                        edits[str((da,db))]+=1
                        if na!=a and nb!=b:moved.add(dest)
                        if length>=192:hit=True;break
                    if hit:break
                if hit:break
            if hit:break
        progress+=1
    depths=[]
    physical=Counter()
    for i,(a,b,prev) in enumerate(states):
        depths.append(0 if prev<0 else depths[prev]+1)
        seq=list(a[::-1])+[v+256 for v in b];word=code(seq)
        length=len(seq)-1;physical[length]+=1
        if word in known:continue
        ident=sha256(word).hexdigest();outside.setdefault(ident,i)
        if newBest is None or length>newBest[0]:newBest=(length,i)
    # Store the exact labelled paths for an independent all-pairs and move audit.
    with gzip.GzipFile(filename=str(fp),mode="wb",mtime=0) as f:
        f.write(json.dumps([[a.hex(),b.hex(),pred] for a,b,pred in states],separators=(",",":")).encode())
    summary=dict(input_chart_occurrences=chart_counts,start_charts=seed_count,visited=len(states),expanded=progress,
        closed=progress==len(states) and not hit,budget=config.limit,pair_visits=links,states_by_edges=physical,discovery_edits=edits,
        both_arms_changed=len(moved),max_depth=max(depths),outside_shapes=outside,
        outside_by_length=Counter(len(states[i][0])+len(states[i][1])-1 for i in outside.values()),
        states_sha256=digest(fp),source_sha256=digest(HERE/"exchange.py"),bank_sha256=digest(BANK),
        starts=[dict(name=name,axis=axis) for a,b,name,axis in starts.values()])
    if newBest:
        _,i=newBest;a,b,_=states[i]
        summary["best_outside"]=dict(state=i,**checked(list(a),list(b)))
    save(HERE/"exchange.json",summary)
    print({k:v for k,v in summary.items() if k not in ("starts","outside_shapes","best_outside")})
if __name__=="__main__":main()
