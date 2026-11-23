"""Identify usable near-record seeds against explicitly enumerated center exclusions."""
import csv,gzip,json
from pathlib import Path
from collections import Counter
from search_q9_two_flexible_ends import verify

def signature(steps):
    seen={}
    return bytes(seen.setdefault(x,len(seen)) for x in steps)
def code(steps):
    return min(signature(steps),signature(steps[::-1]))
def windows(w,k):
    steps=[a^b for a,b in zip(w,w[1:])]
    return [code(steps[i:i+k]) for i in range(len(w)-k)]
def reference(k):
    bank=set()
    for line in open('/tmp/q9_domain_all190_centers20.txt'):
        w=list(map(int,line.split()))
        bank.update(windows(w,k))
    for line in gzip.open('q9_free_bridge_join_inputs.txt.gz','rt'):
        w=list(map(int,line.split()))
        bank.update(windows(w,k))
    return bank

if __name__=='__main__':
    k=142
    bank=reference(k)
    examined=set();freq=Counter()
    for file,key in [('q9_189_outside_reference_component.jsonl','vertices'),('q9_novel189_seeds.jsonl','path')]:
        for r in map(json.loads,open(file)):
            w=r[key];verify(w,189)
            shape=windows(w,len(w)-1)[0]
            if shape in examined:continue
            examined.add(shape)
            hits=sum(s in bank for s in windows(w,k));freq[hits]+=1
            if not hits:print(json.dumps(['SEED',len(w)-1,w]),flush=True)
    print(json.dumps(['SUMMARY',dict(freq),len(bank),len(examined)]))
