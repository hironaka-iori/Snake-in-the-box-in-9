"""Partition each unknown family by fixing one more mutable projected visit."""
import json
import sys
from search_q9_flexible_corners import solve
from search_q9_two_flexible_ends import verify

def partition(q, ids, focus):
    neighbors = [q[j] for j in (focus-1,focus+1) if 0<=j<len(q)]
    for b in range(7):
        v=neighbors[0]^(1<<b)
        if all((v^u).bit_count()==1 for u in neighbors):
            yield b,q[:focus]+bytes([v])+q[focus+1:], [i for i in ids if i!=focus]

def tasks(mode):
    if mode=="single":
        for s,key,_ in map(json.loads,open("q9_one_end_split_192.jsonl")):
            if s!="UNKNOWN":continue
            raw,off,last=key
            p=bytes.fromhex(raw)
            q=p[:-1]+bytes([p[-2]^(1<<last)])
            ids=list(range(off,len(q)-1,2))
            def width(i):
                return 7 if i==0 or q[i-1]==q[i+1] else 2
            pos=max(ids,key=lambda i:(width(i),-abs(i-len(q)//2)))
            yield key,q,ids,pos
    else:
        for s,key,_ in map(json.loads,open("q9_two_ends_192.jsonl")):
            if s!="UNKNOWN":continue
            raw,off=key
            p=bytes.fromhex(raw)
            q=bytes([p[0]^1])+p+bytes([p[-1]^1])
            ids=[0,*range(2+off,len(q)-2,2),len(q)-1]
            yield key,q,ids,0

if __name__=="__main__":
    mode=sys.argv[1]
    for key,q,ids,focus in tasks(mode):
        for bit,p,rest in partition(q,ids,focus):
            s,w=solve(p,[],rest,192,40000 if mode=="single" else 7500,True)
            if w:verify(w,192)
            print(json.dumps([s,key,focus,bit,w],separators=(",",":")),flush=True)
            if w:sys.exit(0)
