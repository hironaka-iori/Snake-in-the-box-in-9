"""Enumerate surviving affine patches after verified whole-half exclusions."""
import argparse
from collections import Counter
from concurrent.futures import ProcessPoolExecutor
import hashlib,json,math
from pathlib import Path
from search_q9_free_record_slice import parents,search,verify


def indices():
    groups={9:["q9_cut_fullparity_atleast192.jsonl"],8:["q9_cut_edges_atleast192.jsonl"],
           7:["q9_cut_squares_atleast192.jsonl","q9_cut_squares_atleast_vertex.jsonl"],
           6:["q9_cut_eight_all_atleast192.jsonl","q9_cut_eight_all_deep_atleast192.jsonl"],
           5:["q9_cut_weight5_atleast192.jsonl","q9_cut_weight5_deep_atleast192.jsonl","q9_cut_weight5_last_atleast192.jsonl"]}
    for w in (1,2,3,4):groups[w]=[f"q9_cut_weight{w}_atleast192.jsonl"]
    return groups

def read_cuts(required=None):
    ruled=[set() for _ in range(131)];logs={}
    for weight,files in indices().items():
        pending={(i,m,s) for i in range(131) for m in range(1,512)
                 if m.bit_count()==weight for s in (0,1)}
        for f in files:
            if required is not None and f not in required:break
            p=Path(f)
            if not p.exists():break
            data=p.read_bytes();rows=data.splitlines()
            if len(rows)!=len(pending):break
            seen=set();again=set()
            for row in rows:
                i,m,s,st,w=json.loads(row);k=i,m,s
                assert k in pending and k not in seen and w is None
                seen.add(k)
                if st=="UNSAT":ruled[i].add(m|((1-s)<<9))
                else:assert st=="UNKNOWN";again.add(k)
            assert seen==pending
            pending=again;logs[f]=hashlib.sha256(data).hexdigest()
        if weight>=5:assert not pending
    if required is not None:assert required==logs
    return ruled,logs

def spaces(ruled,dim):
    # A row (m,b) constrains every changed vertex x to m.x=b.
    # RREF is imposed only on m. This enumerates each affine flat once.
    allowed=[z for z in range(1024) if z&511 and z not in ruled]
    candidates=[(z,(z&511).bit_length()-1) for z in allowed]
    def dfs(basis,span,piv,last):
        if len(basis)==dim:
            yield tuple(basis);return
        maxcol=9-(dim-len(basis))
        for z,col in candidates:
            if not last<col<=maxcol or z&piv:continue
            block=[s^z for s in span]
            if any(v in ruled for v in block):continue
            yield from dfs(basis+[z],span+block,piv|1<<col,col)
    yield from dfs([],[0],0,-1)

def init():
    global bank
    bank=parents()

def solve(job):
    i,basis,cap=job;p=bank[i]
    patch={v for v in range(512) if all(((v&(m&511)).bit_count()%2)==(m>>9) for m in basis)}
    assert len(patch)==1<<(9-len(basis))
    fixed=set(p)-patch
    st,w=search(fixed,set(p),192,cap,allowed=fixed|patch,at_least=True)
    if w:
        verify(w);assert len(w)>=193 and set(w)^set(p)<=patch
    return [i,basis,st,w]

if __name__=="__main__":
    ap=argparse.ArgumentParser()
    ap.add_argument("dim",type=int)
    ap.add_argument("--count",action="store_true")
    ap.add_argument("--budget",type=int,default=10000)
    ap.add_argument("--parents",type=int,default=131)
    ap.add_argument("--manifest")
    args=ap.parse_args()
    chosen=json.load(open(args.manifest))["inputs"] if args.manifest else None
    cuts,logs=read_cuts(chosen)
    jobs=((i,b,args.budget) for i in range(args.parents) for b in spaces(cuts[i],args.dim))
    if args.count:
        counts=Counter(i for i,b,c in jobs)
        print(json.dumps(dict(codimension=args.dim,total=sum(counts.values()),counts=counts,inputs=logs)))
    else:
        with ProcessPoolExecutor(4,initializer=init) as pool:
            for r in pool.map(solve,jobs,chunksize=16,buffersize=32):
                print(json.dumps(r,separators=(",",":")),flush=True)
                if r[-1]:break
