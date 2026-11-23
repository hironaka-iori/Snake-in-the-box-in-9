from one_soft import lift
from search import partition,D,axes
from relay import defects,shape
from collections import Counter
import random,json
words=sorted(set((D.parent/'q9_via_q10/monotone_near.words').read_text().split()))
bank=[list(map(int,w)) for w in words if len(w)==192 and len(defects(axes(list(map(int,w)))))==2]
parts=[(ps,s) for s in range(9) for ps in partition(tuple(i for i in range(9) if i!=s))]
jobs=[(a,j,pair) for a,w in enumerate(bank) for j in range(len(parts)) for pair in sorted(defects(axes(w)))]
random.Random(714759).shuffle(jobs);stats=Counter();known=set((D.parent/'q9_via_q10/all_near_registered.words').read_text().split());hits=set()
for a,j,permit in jobs:
    ps,s=parts[j];st,p,c=lift(bank[a],ps,s,4000,permit);stats[st]+=1
    row=dict(seed=a,partition=j,permit=permit,status=st)
    if p:
        defect=defects(p);key=shape([(i^j).bit_length()-1 for i,j in zip(p,p[1:])])
        row.update(word=key,chords=len(defect),new_to_archive=key not in known);hits.add(key)
        if not defect:row['found']=p
    print(json.dumps(row,separators=(',',':')),flush=True)
    if p and not defect:break
print(json.dumps(dict(done=True,counts=stats,distinct=len(hits))),flush=True)
