from one_soft import lift
from search import D,axes,partition
from relay import defects,shape
import json
from collections import Counter
bank=[list(map(int,w)) for w in sorted(set((D.parent/'q9_via_q10/monotone_near.words').read_text().split())) if len(w)==192 and len(defects(axes(list(map(int,w)))))==2]
parts=[(ps,s) for s in range(9) for ps in partition(tuple(i for i in range(9) if i!=s))]
pending=[q for r in (D/'remove_one.jsonl').read_text().splitlines() if (q:=json.loads(r)).get('status')=='UNKNOWN'];counts=Counter()
for r in pending:
    ps,s=parts[r['partition']];pair=tuple(r['permit'])
    st,p,c=lift(bank[r['seed']],ps,s,120000,pair);counts[st]+=1;out=dict(seed=r['seed'],partition=r['partition'],permit=pair,status=st)
    if p:out.update(candidate=shape([(a^b).bit_length()-1 for a,b in zip(p,p[1:])]),chords=len(defects(p)))
    print(json.dumps(out),flush=True)
print(json.dumps(dict(done=True,counts=counts)),flush=True)
