"""Transport a dual under a cube isometry, then evaluate it on a different Q8 mother."""
import gzip
import json
import sys
from pathlib import Path
from verify_dual import check
root=Path(__file__).resolve().parent
table={}
for line in gzip.open(root/'fresh24_duals.jsonl.gz','rt'):
    r=json.loads(line);table[r['word'],r['outer_parity']]=r['certificate']
words=(root/'q9_fresh24_rank20.words').read_text().split()
cutoff=int(sys.argv[2]) if len(sys.argv)>2 else 12
for line in Path(sys.argv[1]).read_text().splitlines():
    diff,idx,reverse,perm,w=line.split()
    if not 0<int(diff)<=cutoff:continue
    seed=words[int(idx)];mapping=[sum(((x>>i)&1)<<int(j) for i,j in enumerate(perm)) for x in range(256)]
    end=0
    for digit in seed:end^=1<<int(digit)
    shift=mapping[end] if int(reverse) else 0
    for parity in (0,1):
        old=table[seed,parity]
        cert=dict(scale=old['scale'],end_weight=old['end_weight'],balance_weight=old['balance_weight']*(-1 if shift.bit_count()&1 else 1),
            axes=[[int(perm[d]) for d in axes] for axes in old['axes']],
            weights=[[mapping[m],mapping[v]^shift,mapping[i],a] for m,v,i,a in old['weights']])
        ep=parity^(shift.bit_count()%2)
        b,s,t=check(dict(word=w,outer_parity=ep,certificate=cert),compare_saved=False)
        print(json.dumps(dict(word=w,outer_parity=ep,source_row=int(idx),source_parity=parity,difference=int(diff),reverse=int(reverse),permutation=perm,numerator=b,scale=s,required=t,excluded=b<t*s)),flush=True)
