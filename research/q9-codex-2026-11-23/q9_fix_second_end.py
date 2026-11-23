"""Enumerate the remaining end directions for unresolved two-ended families."""
import json
from q9_partition_ends import partition
from search_q9_flexible_corners import solve
from search_q9_two_flexible_ends import verify

for s,key,first,bit,_ in map(json.loads,open("q9_two_end_split_192.jsonl")):
    if s!="UNKNOWN":continue
    raw,off=key
    p=bytes.fromhex(raw)
    q=bytes([p[0]^(1<<bit)])+p+bytes([p[-1]^1])
    ids=[*range(2+off,len(q)-2,2),len(q)-1]
    for k,r,rest in partition(q,ids,len(q)-1):
        status,w=solve(r,[],rest,192,12500,True)
        if w:verify(w,192)
        print(json.dumps([status,key,bit,k,w],separators=(",",":")),flush=True)
        if w:raise SystemExit
