from pathlib import Path
from collections import Counter
import json
D=Path(__file__).resolve().parent
def trace(w):
    pts=[0]
    for a in w:pts.append(pts[-1]^2**int(a))
    return pts
def norm(w):
    def ren(t):
        indices={}
        for c in t:
            if c not in indices:indices[c]=str(len(indices))
        return ''.join(indices[x] for x in t)
    return min(ren(w),ren(list(reversed(w))))
def induced(a,d):
    assert len(set(a))==len(a) and all(0<=v<2**d for v in a)
    for j,v in enumerate(a):
        for k,u in enumerate(a[:j]):assert ((v^u).bit_count()==1)==(k+1==j)
archive=(D.parent/'q8_catalogue_96_98.words').read_text().split()
seen=set()
for s in archive:
    for n in (94,95):
        for i in range(len(s)-n+1):seen.add(norm(s[i:i+n]))
base=(D/'donors.words').read_text().split();assert len(base)==len(set(base)) and not set(base)&seen
assert norm(json.loads((D.parent/'q9_frequent_95_audit.json').read_text())['core_word']) not in base
for w in base:assert w==norm(w);induced(trace(w),8)
refs=json.loads((D/'references.json').read_text())
for idx,(length,row,axis,rev,a,b) in refs.items():
    ix=int(idx);old=(D.parent/f'q9_far189_spring_20261121/comparison{length}.words').read_text().split()[row];raw=old[::-1] if rev else old
    pref,mid,suf=raw.split(str(axis));assert norm(mid)==base[ix]
    q=trace(base[ix]);left=trace(a);right=[v^q[-1] for v in trace(b)];recovered=[256+t for t in left[::-1]]+q+[256+t for t in right];induced(recovered,9)
    assert len(recovered)-1==length
records={}
neww=(D/'reroutes/donors.words').read_text().split();assert len(neww)==len(set(map(norm,neww)))==2 and not {norm(w) for w in neww}&(set(base)|seen)
for f in sorted(D.rglob('*.paths')):
    scores=[]
    for l in f.read_text().splitlines():
        edges,i,*a=map(int,l.split());induced(a,9);assert edges+1==len(a)
        diff=[(u^v).bit_length()-1 for u,v in zip(a,a[1:])];j,k=[n for n,b in enumerate(diff) if b==8];assert a[0]>=256 and a[-1]>=256 ;observed=norm(diff[j+1:k])
        if f.name.startswith(("port","trim")):assert len(observed) in (94,95)
        elif f.parent==D:assert observed==base[i]
        else:assert observed==norm(neww[i])
        scores.append(edges)
    records[str(f.relative_to(D))]={'rows':len(scores),'max':max(scores,default=None)}
print(json.dumps(dict(donors=len(base),lengths=Counter(map(len,base)),forbidden=len(seen),historical_donors=len(archive),paths=records),sort_keys=True))
