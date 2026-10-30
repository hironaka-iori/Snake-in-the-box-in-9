"""Independent interval matching and complete finite-model potential checks."""
from pathlib import Path
from fractions import Fraction
import gzip,hashlib,json,sys,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'work/solver_packages'));import numpy as np
read=lambda p:json.loads(p.read_text());sha=lambda b:hashlib.sha256(b).hexdigest();started=time.monotonic()
tag='proved-' if '--proved-only' in sys.argv else ''
md=read(HERE/f'data/{tag}model.json');result=read(HERE/f'data/{tag}analysis.json')
prior=ROOT/'milestones/70-proof-supported-share-model';source=read(prior/'data/enriched-model.json')
with np.load(prior/'build/enriched-graph.npz') as z:a={k:z[k] for k in z.files}
for k,h in source['arrays_sha256'].items():assert sha(a[k].tobytes())==h
cases=read(HERE/'data/cases.json');cases=[c for c in cases if c['number'] in md['applied_cases']]
if tag:assert set(md['applied_cases'])<=set(read(HERE/'data/proof-audit.json')['completed_cases'])
shapes=read(ROOT/'milestones/59-extended-share-window/extended/data/model.json')['extensions']
def canon(w):
    labels=list(dict.fromkeys(w));return tuple(labels.index(x) for x in w)
codes=np.arange(6**6);C=np.stack([codes//6**j%6+1 for j in range(5,-1,-1)],axis=1);high=np.where(C==6,21,C)
keep=np.ones(len(a['U']),dtype=bool)
for di,w in enumerate(shapes):
    forbidden=np.zeros(len(codes),dtype=bool)
    for c in cases:
        for offset in range(5):
            if offset<2:continue
            piece=w[offset:offset+5]
            for word,bs in [(c['dirs'],c['bounds']),(c['dirs'][::-1],c['bounds'][::-1])]:
                if canon(piece)!=canon(word):continue
                test=np.ones(len(codes),dtype=bool)
                for k,(lo,hi) in enumerate(bs):
                    col=offset-2+k;test&=(C[:,col]>=lo)&(high[:,col]<=hi)
                forbidden|=test
    rows=np.flatnonzero(a['direction']==di);keep[rows]=~forbidden[a['count_code'][rows]]
with np.load(HERE/f'build/{tag}graph.npz') as z:
    for k in a:
        assert np.array_equal(a[k][keep],z[k]);assert sha(z[k].tobytes())==md['arrays_sha256'][k]
    U,V,W=z['U'],z['V'],z['weight'].astype(np.int64)
assert len(U)==md['edges'] and len(a['U'])-len(U)==md['removed']
raw=gzip.decompress((HERE/f'data/{tag}potential.i64.gz').read_bytes());assert sha(raw)==result['potential_sha256']
pi=np.frombuffer(raw,dtype='<i8');mu=Fraction(result['integer_mean']);assert len(pi)==md['states']
assert np.all(mu.numerator+pi[V]<=mu.denominator*W+pi[U])
cycle=[c['edge'] for c in result['cycle']]
assert all(V[e]==U[cycle[(i+1)%len(cycle)]] for i,e in enumerate(cycle))
assert sum(int(W[e]) for e in cycle)*mu.denominator==len(cycle)*mu.numerator
out=dict(status='PASS',edges=len(U),removed=md['removed'],applied_cases=md['applied_cases'],exact_mean=str(mu),potential_range=int(max(pi)-min(pi)),attaining_cycle=len(cycle),seconds=time.monotonic()-started,scope='Independent exact interval and bucket matching on the previously verified source graph; all potential inequalities and attaining cycle checked. Global snake interpretation remains pending.')
(HERE/f'data/{tag}graph-verification.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
