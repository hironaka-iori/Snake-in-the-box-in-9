"""Re-encode two prescribed anchor sets per input in MiniCard and compare after completion."""
from collections import Counter
from itertools import accumulate
from operator import xor
import sys
import json
from run import ROOT,HERE,CUBE,inspect,regions
from search_q9_anchored_sets import search

def work():
    cache={}
    for i,line in enumerate(open(ROOT/'q9_new189_nearmisses.words')):
        label,word=line.split()
        if label!='2':continue
        p=list(accumulate([1<<int(d) for d in word],xor,initial=0))
        chords=inspect(p)
        assert len(chords)==2
        for fixed,params in regions(p,chords):
            if "--all" not in sys.argv and params not in ([[0,0],2,2,0],[[1,1],2,3,2],[[0,1],3,3,0]):continue
            if fixed in cache:continue
            status,w=search(set(fixed),set(p),192,12000,at_least=True)
            if w:assert len(w)>=193 and not inspect(w) and fixed<=set(w)
            cache[fixed]=status
            print(json.dumps(dict(row=i,params=params,status=status,witness=w)),flush=True)
            if w:return
    print(json.dumps(dict(counts=dict(Counter(cache.values())))),flush=True)
if __name__=='__main__':work()
