"""Prove groups of windows infeasible by solving their common contiguous subword."""
import json,sys,time
from collections import Counter
from pathlib import Path
from bench import lift
from lazy import solve
from select import key,readranges
D=Path(__file__).resolve().parent
G=192
records={}; stats=Counter(); start_time=time.monotonic()
def search(word,positions,out,row,layout):
    if not positions:return
    left,right=positions[-1],positions[0]+G
    raw=word[left:right]
    grouped=''.join(str(int(c)//2) for c in raw)
    k=key(grouped)
    if k not in records:
        s,p,c=lift(list(map(int,raw)),((0,1),(2,3),(4,5),(6,7)),8,3000)
        if s=='UNKNOWN' and len(positions)==1:
            s,p,_,_=solve(raw,100000)
        records[k]=s
        print(json.dumps(dict(word=raw,status=s,conflicts_initial=c,**({'path':p} if p and len(p)>=193 else {})),separators=(',',':')),file=out)
        if p and len(p)>=193:out.flush();raise RuntimeError('192 FOUND')
    s=records[k]
    if s=='UNSAT':stats['excluded']+=len(positions);return
    if len(positions)==1:stats[s]+=1;return
    half=len(positions)//2
    search(word,positions[:half],out,row,layout);search(word,positions[half:],out,row,layout)
def main():
    with (D/'cover192.jsonl').open('w') as out:
        for i,line in enumerate((D/'all192.logtmp').open(),1):
            row,layout,_,w,ranges=line.split();p=list(readranges(ranges));j=0
            while j<len(p):
                end=j+1
                while end<len(p) and p[end]-p[j]<=26:end+=1
                search(w,p[j:end],out,row,layout);j=end
            if i%1000==0:print(i,len(records),dict(stats),round(time.monotonic()-start_time,2),flush=True);out.flush()
    print('DONE',i,len(records),dict(stats),round(time.monotonic()-start_time,2),flush=True)
if __name__=='__main__':main()
