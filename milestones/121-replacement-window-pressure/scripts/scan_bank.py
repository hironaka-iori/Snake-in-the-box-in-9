"""Check actual bank paths and compare the new restriction and replacement cycle."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
source=R/'work/bank9.json';out=H/'data/bank-scan.json'
assert not out.exists()
bank=json.loads(source.read_text(encoding='utf-8-sig'))
def canon(ds):
    labels={}
    return tuple(labels.setdefault(d,len(labels)) for d in ds)
targets=[(2511,(0,1,2,0,3,1,0,4,1),(4,4,3,5,4,4)),
 (1101529,(0,1,2,3,0,2,4,0,1),(4,3,5,4,4,4)),
 (2186371,(0,1,2,3,1,4,3,0,1),(3,5,4,4,4,3)),
 (121059,(0,1,2,0,3,2,4,0,2),(5,4,4,4,3,5)),
 (2140357,(0,1,2,3,1,4,2,1,0),(4,4,4,3,5,4))]
matches={str(e):[] for e,_,_ in targets};shape_counts={str(e):0 for e,_,_ in targets}
outer=[];pairs=0;small=[];attaining=[]
for bi,row in enumerate(bank):
    vs=row['vertex_sequence'];ds=row['transition_sequence'];S=set(vs)
    assert len(S)==len(vs)==len(ds)+1==row['edges']+1
    assert all(0<=v<512 for v in vs)
    assert all(vs[i]^vs[i+1]==1<<d for i,d in enumerate(ds))
    for i,u in enumerate(vs):
        for j in range(i+1,len(vs)):
            assert ((u^vs[j]).bit_count()==1)==(j==i+1)
            pairs+=1
    counts=[sum(all(z not in S for z in (v^(1<<a),v^(1<<b),v^(1<<a)^(1<<b)))
                for a in range(9) for b in range(a+1,9)) for v in vs]
    for r in range(len(ds)-5):
        if canon(ds[r:r+6])!=(0,1,2,0,3,2):continue
        c=counts[r+1:r+6];maximum=c[1]+c[3];outer.append(maximum)
        assert c[1]>=2 and c[3]>=2 and maximum>=8
        if maximum==8:small.append(dict(bank_index=bi,start=r,counts=c))
        if maximum==min(outer):attaining.append(dict(bank_index=bi,start=r,counts=c))
    for r in range(len(ds)-8):
        word=canon(ds[r:r+9]);c=tuple(min(6,x) for x in counts[r+3:r+9])
        for e,w,q in targets:
            if word==w:
                shape_counts[str(e)]+=1
                if c==q:matches[str(e)].append(dict(bank_index=bi,start=r,counts=counts[r+3:r+9]))
record=dict(status='PASS_BANK_PATHS_AND_WINDOW_COUNTS',bank_sha256=sha(source),script_sha256=sha(Path(__file__)),
 paths=len(bank),pairs_checked=pairs,pair_window_occurrences=len(outer),minimum_pair_sum=min(outer) if outer else None,
 pair_sum_eight=small,minimum_attainments=[x for x in attaining if x["counts"][1]+x["counts"][3]==min(outer)],replacement_direction_occurrences=shape_counts,replacement_exact_count_matches=matches,
 scope='Finite bank check only. No absence claim for all snakes and no upper bound follows. Count matches do not certify the additional history or share data of a graph key.')
out.write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
print(json.dumps(record))
