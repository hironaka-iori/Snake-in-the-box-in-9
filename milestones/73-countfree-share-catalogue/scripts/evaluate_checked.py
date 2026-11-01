"""Evaluate only the completed local catalogue; retain the global proof boundary."""
from pathlib import Path
from fractions import Fraction
import gzip,hashlib,json,sys,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
OLD=ROOT/'milestones/72-four-count-proof-closure/critical-current'
sys.path.insert(0,str(ROOT/'milestones/42-six-count-state-model/scripts'))
sys.path.insert(0,str(ROOT/'milestones/51-exact-bucket-pressure/scripts'))
import analyze_share
np=analyze_share.np;alg,algsha=analyze_share.algorithms()
sha=lambda b:hashlib.sha256(b).hexdigest();read=lambda p:json.loads(p.read_text())
start=time.monotonic();meta=read(OLD/'data/source-proved-model.json')
with np.load(OLD/'build/source-graph.npz') as z:a={k:z[k] for k in z.files}
for k,h in meta['arrays_sha256'].items():assert sha(a[k].tobytes())==h
support={};floors={(0,1,2,3,4,5):12}
old_audit=OLD/'share-proof/data/proof-audit.json';assert read(old_audit)['status']=='PASS_LOCAL_SHARE_THEOREM'
support[old_audit.relative_to(ROOT).as_posix()]=sha(old_audit.read_bytes())
for f in sorted((HERE/'cases').glob('*/data/proof-audit.json')):
    case=read(f);assert case['status']=='PASS_LOCAL_SHARE_THEOREM'
    assert any(r['theorem'].endswith('.share_bound_rev') for r in case['theorem_audits'])
    support[f.relative_to(ROOT).as_posix()]=sha(f.read_bytes())
    d=tuple(case['directions']);floors[d]=max(floors.get(d,0),case['share_lower'])
assumptions=[]
for argument in sys.argv[1:]:
    assert argument.startswith('--assume=')
    word,value=argument.split('=',1)[1].split(':');shape=tuple(map(int,word));lower=int(value)
    assert len(shape)==6 and lower>=0
    assumptions.append(dict(shape=list(shape),share=lower))
    floors[shape]=max(floors.get(shape,0),lower)
prefix='assumed-'+ '-'.join(''.join(map(str,r['shape']))+'x'+str(r['share']) for r in assumptions) if assumptions else 'proved'
def canon(word):
    d={};return tuple(d.setdefault(x,len(d)) for x in word)
extensions=read(ROOT/'milestones/59-extended-share-window/extended/data/model.json')['extensions']
U,V,W=a['U'],a['V'],a['weight'].astype(np.int64).copy();base=W.copy()
for di,ds in enumerate(extensions):
    shape=min(canon(ds[-6:]),canon(ds[-6:][::-1]))
    if shape in floors:
        ix=a['direction']==di
        W[ix]=np.maximum(W[ix],120*(a['count_code'][ix]%6+1)+floors[shape])
N=meta['states'];pool=np.flatnonzero(alg['prune'](N,U,V));active=np.unique(np.concatenate([U[pool],V[pool]]))
index=np.full(N,-1,dtype=np.int32);index[active]=np.arange(len(active))
_,cycle=alg['howard'](len(active),index[U[pool]],index[V[pool]],W[pool],iters=400)
ci=pool[np.asarray(cycle)];mu=Fraction(int(W[ci].sum()),len(ci));p,d=mu.numerator,mu.denominator
assert all(int(V[ci[i]])==int(U[ci[(i+1)%len(ci)]]) for i in range(len(ci)))
pi=np.zeros(N,dtype=np.int64)
for it in range(1500):
    nxt=pi.copy();np.minimum.at(nxt,V,pi[U]+d*W-p)
    if np.array_equal(nxt,pi):break
    pi=nxt
else:raise AssertionError('Potential did not converge')
assert np.all(p+pi[V]<=d*W+pi[U]);pi-=min(pi);R=int(max(pi))
raw=pi.astype('<i8').tobytes();(HERE/f'data/{prefix}-potential.i64.gz').write_bytes(gzip.compress(raw,mtime=0))
bound=Fraction(1098960*d+8*p+R,p+4200*d)
out=dict(status='EXACT_CONDITIONAL_LOCAL_MODEL' if assumptions else 'EXACT_PROOF_SUPPORTED_LOCAL_MODEL',states=N,edges=len(U),mean=str(mu),potential_range=R,
    improved_edges=int(np.sum(W>base)),weight_sha256=sha(W.tobytes()),potential_sha256=sha(raw),
    countfree_floors=[dict(shape=list(s),share=f) for s,f in sorted(floors.items())],
    audited_local_sources=support,source_arrays_sha256=meta['arrays_sha256'],
    additional_share_assumptions=assumptions,
    cycle=[dict(edge=int(e),u=int(U[e]),v=int(V[e]),weight=int(W[e])) for e in ci],
    all_edge_potential_verified=True,conditional_bound=str(bound),conditional_integer_bound=bound.numerator//bound.denominator,
    algorithm_sha256=algsha,seconds=time.monotonic()-start,
    scope='Exact finite-model result. Any additional_share_assumptions are unproved premises; all other added floors have local Lean audits. Arbitrary-snake graph interpretation and potential replay remain pending. No new global upper bound.')
(HERE/f'data/{prefix}-model.json').write_text(json.dumps(out,indent=2)+'\n')
print({k:out[k] for k in ['status','edges','mean','potential_range','improved_edges','conditional_bound','conditional_integer_bound','seconds']},flush=True)
