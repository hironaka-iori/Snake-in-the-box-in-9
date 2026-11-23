"""Reconcile monotone 191-edge exclusions and retry the genuinely open families."""
import sys,json
from search_q9_flexible_corners import solve
from search_q9_two_flexible_ends import verify
from q9_partition_ends import partition

def split(q,ids,depth,trace):
    status,w=solve(q,[],ids,192,12000,True)
    if status!="UNKNOWN" or not ids or not depth:
        trace.append(status)
        if w:verify(w,192)
        return status,w
    def order(i):
        alt=q[i-1]^q[i+1]^q[i]
        return (q[i-1]!=q[i+1],q.count(q[i])+q.count(alt),-abs(i-len(q)//2))
    pivot=max(ids,key=order);open_branch=False
    for _,p,rest in partition(q,ids,pivot):
        status,w=split(p,rest,depth-1,trace)
        if w:return status,w
        open_branch|=(status=="UNKNOWN")
    return ("UNKNOWN" if open_branch else "UNSAT"),None

if __name__=="__main__":
    easier={r[1]:r[0] for r in map(json.loads,open("q9_reversal_191_seeds.jsonl"))}
    for prior,_,_,_,key,_ in map(json.loads,open("q9_projected_reversal_192.jsonl")):
        if prior!="UNKNOWN":continue
        if easier.get(key)=="UNSAT":
            out=["UNSAT",key,"191 threshold",[],None]
        else:
            q=bytes.fromhex(key);ids=list(range(1,len(q)-1,2));trace=[]
            st,w=split(q[::-1],[len(q)-1-i for i in ids],2,trace)
            out=[st,key,"reverse split",trace,w]
        print(json.dumps(out,separators=(",",":")),flush=True)
        if out[-1]:break
