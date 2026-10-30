"""Select count assumptions for a sufficient potential on the enriched graph."""
from pathlib import Path
from fractions import Fraction
import collections,gzip,hashlib,json,sys,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'work/solver_packages'))
import numpy as np
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'));sha=lambda b:hashlib.sha256(b).hexdigest()
start=time.monotonic();old='--old' in sys.argv;tag='old-' if old else ''
P=ROOT/'milestones/68-proof-dependency-pressure' if old else HERE
res=read(P/('data/share-clean-analysis.json' if old else 'data/analysis.json'))
raw=gzip.decompress((P/('data/share-clean-potential.i64.gz' if old else 'data/potential.i64.gz')).read_bytes())
assert sha(raw)==res['potential_sha256'];pi=np.frombuffer(raw,dtype='<i8')
mu=Fraction(res['integer_mean']);d=mu.denominator;R=int(max(pi)-min(pi));p=(111960*d+R)//227+1
assert p<=mu.numerator
sm=read(ROOT/'milestones/59-extended-share-window/extended/data/model.json')
prior=ROOT/'milestones/70-proof-supported-share-model';meta=read(prior/'data/enriched-model.json')
with np.load(prior/'build/enriched-graph.npz') as z:a={k:z[k] for k in z.files}
for k,h in meta['arrays_sha256'].items():assert sha(a[k].tobytes())==h
basis=json.loads(gzip.decompress((ROOT/'milestones/68-proof-dependency-pressure/data/count-subsumption.json.gz').read_bytes()))['needed']
def canon(w):
    names=list(dict.fromkeys(w));return tuple(names.index(x) for x in w)
def encode(c):
    n=0
    for x in c:n=6*n+x-1
    return n
lookup={}
for k,(w,c) in enumerate(basis):
    for ww,cc in [(w,c),(w[::-1],c[::-1])]:
        word=canon(ww)
        if word not in lookup:lookup[word]=np.full(6**len(c),-1,dtype=np.int32)
        v=encode(cc);assert lookup[word][v] in (-1,k);lookup[word][v]=k
slack=d*a['weight'].astype(np.int64)+pi[a['U']]-pi[a['V']]-p
clauses=collections.Counter();examples={};negative=np.flatnonzero(slack<0)
for di,ds in enumerate(sm['extensions']):
    ix=negative[a['direction'][negative]==di];code=a['count_code'][ix];matches=[]
    for offset in range(5):
        for width in range(2,7-offset):
            word=canon(ds[2+offset:3+offset+width])
            if word in lookup:matches.append(lookup[word][code//6**(6-offset-width)%6**width])
    rows=np.stack(matches,axis=1) if matches else np.empty((len(ix),0),dtype=np.int32)
    for edge,row in zip(ix,rows):
        clause=tuple(sorted(set(int(k) for k in row if k>=0)))
        assert clause,('uncovered',int(edge))
        clauses[clause]+=1
        if clause not in examples:examples[clause]=dict(edge=int(edge),direction=di,history=int(a['history'][edge]),count_code=int(a['count_code'][edge]),slack=int(slack[edge]))
forced={c[0] for c in clauses if len(c)==1};selected=set(forced)
remaining=[c for c in clauses if not selected.intersection(c)]
while remaining:
    scores=collections.Counter(k for c in remaining for k in c);k=min(scores,key=lambda k:(-scores[k],k))
    selected.add(k);remaining=[c for c in remaining if k not in c]
out=dict(status='SUFFICIENT_FIXED_POTENTIAL_COVER',potential_numerator=p,potential_denominator=d,potential_range=R,potential_sha256=sha(raw),candidate_edges=len(slack),violating_edges=len(negative),distinct_clauses=len(clauses),mandatory_keys=len(forced),selected_keys=len(selected),unique_least_cover=selected==forced,selected_ids=sorted(selected),keys=[basis[k] for k in sorted(selected)],clauses=[dict(keys=c,edges=n,example=examples[c]) for c,n in sorted(clauses.items())],bound_coefficient=p+4200*d,bound_constant=1098960*d+8*p+R,margin_at_235=227*p-111960*d-R,seconds=time.monotonic()-start,scope='Count keys remain premises. Minimality, when established, fixes this graph, basis and potential.')
(HERE/f'data/{tag}selection.json.gz').write_bytes(gzip.compress(json.dumps(out,separators=(',',':')).encode(),mtime=0))
summary={k:v for k,v in out.items() if k not in ['selected_ids','keys','clauses']}
(HERE/f'data/{tag}summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(summary,flush=True)
