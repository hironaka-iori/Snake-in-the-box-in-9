"""Recheck an unresolved direction pair by recursive, complete splits of mutable visits."""
import json
from q9_partition_ends import partition
from search_q9_flexible_corners import solve
from search_q9_two_flexible_ends import verify

def search(q,ids,depth,trace):
    st,w=solve(q,[],ids,192,30000,True)
    if w:verify(w,192)
    if st!="UNKNOWN" or depth==0 or not ids:
        trace.append(st)
        return st,w
    def priority(i):
        # Prefer visits in crowded projected cells with two alternatives.
        alt=q[i-1]^q[i+1]^q[i]
        return (q[i-1]!=q[i+1],q.count(alt)+q.count(q[i]),-abs(i-len(q)//2))
    pivot=max(ids,key=priority)
    any_open=False
    for _,sub,rest in partition(q,ids,pivot):
        s,w=search(sub,rest,depth-1,trace)
        if w:return s,w
        any_open|=s=="UNKNOWN"
    return ("UNKNOWN" if any_open else "UNSAT"),None

for status,key,b,k,_ in map(json.loads,open("q9_two_end_directions_192.jsonl")):
    if status!="UNKNOWN":continue
    raw,off=key
    p=bytes.fromhex(raw)
    q=bytes([p[0]^(1<<b)])+p+bytes([p[-1]^(1<<k)])
    ids=list(range(2+off,len(q)-2,2));trace=[]
    s,w=search(q,ids,5,trace)
    print(json.dumps([s,key,b,k,trace,w]),flush=True)
    if w:break
