"""Audit printed paths independently of the C++ search; count edges, not vertices."""
from collections import Counter
from pathlib import Path
import json
root=Path(__file__).resolve().parent
def shape(word):
    def labels(w):
        names={}
        return ''.join(names.setdefault(ch,str(len(names))) for ch in w)
    return min(labels(word),labels(word[::-1]))
archive={shape(w) for w in (root.parent/'q9_gap_generations/prior191.words').read_text().split()}
assert len(archive)==131
out={}
for pattern in ['outer_*.log','registered_outer_*.log','registered_parity_*.log','near_registered_*.log','jitter_parity_*.log','revisit_flex_*.log','release_control_*.log','release_cross_*.log','anneal_cross_*.log','monotone_release_*.log','monotone_anneal_*.log']:
    for f in sorted(root.glob(pattern)):
        best=-1;sample=None;done=None;keys=set();count=0
        for line in f.read_text().splitlines():
            s=line.split()
            if not s:continue
            if s[0]=='DONE':done=s[1:];continue
            if s[0] not in ['BEST','FOUND'] or 'bad' in s:continue
            idx=2 if s[0]=='FOUND' and f.name.startswith('outer_') else 1
            n=int(s[idx]);p=list(map(int,s[idx+1:]))
            assert len(p)==n+1==len(set(p)) and all(0<=v<512 for v in p)
            for j,v in enumerate(p):
                for i,u in enumerate(p[:j]):
                    assert ((v^u).bit_count()==1)==(i+1==j)
            key=shape(''.join(str((a^b).bit_length()-1) for a,b in zip(p,p[1:])))
            count+=1
            if n==191:keys.add(key)
            if n>best:best=n;sample=p
        out[f.name]=dict(done=done,n_witnesses=count,maximum_observed=best if count else None,classes_at_191=len(keys),outside_archive=len(keys-archive),longest_verified=sample)
print(json.dumps(out,indent=1))
