"""Reconstruct lift transitions and check exact potentials, independently of generators."""
from pathlib import Path
from fractions import Fraction
import gzip,hashlib,itertools,json,sys,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'work/solver_packages'))
import numpy as np
read=lambda p:json.loads(p.read_text())
SOURCE=ROOT/'milestones/59-extended-share-window/extended';sm=read(SOURCE/'data/model.json')
with np.load(SOURCE/'build/graph.npz') as z:source={k:z[k] for k in z.files}
for k,h in sm['arrays_sha256'].items():assert hashlib.sha256(source[k].tobytes()).hexdigest()==h
B=6**5;N=sm['states']
def canon(w):
    order=list(dict.fromkeys(w));return tuple(order.index(x) for x in w)
def all_words(prefix=(),vertices=(0,)):
    if len(prefix)==11:yield prefix;return
    for d in range(min(9,max(prefix,default=-1)+2)):
        v=vertices[-1]^(1<<d)
        if v in vertices or any((v^x).bit_count()==1 for x in vertices[:-1]):continue
        yield from all_words(prefix+(d,),vertices+(v,))
ids={tuple(w):i for i,w in enumerate(sm['extensions'])};words=list(all_words());assert len(words)==11162
signatures={}
for w in words:signatures.setdefault(tuple(ids[canon(w[j:j+9])] for j in range(3)),[]).append(w)
reports=[]
for name in (sys.argv[1:] or ['terminal','shares']):
    assert name in ['terminal','shares','pressured']
    start=time.monotonic();meta=read(HERE/f'data/{name}-model.json');result=read(HERE/f'data/{name}-analysis.json')
    with np.load(HERE/f'build/{name}-graph.npz') as z:a={k:z[k] for k in z.files}
    for k,h in meta['arrays_sha256'].items():assert hashlib.sha256(a[k].tobytes()).hexdigest()==h
    if name=='terminal':
        sig=tuple(meta['pattern_ids']);prefixes=[(),sig[:1],sig[:2]]
        patterns=[dict(signature=sig,directions=meta['pattern'],caps={'5':2},mode='exclusion')]
    else:prefixes=[tuple(p) for p in meta['prefixes']];patterns=meta['patterns']
    for p in patterns:assert signatures[tuple(p['signature'])]==[tuple(p['directions'])]
    for p in meta.get('ambiguous_patterns',[]):assert signatures[tuple(p['signature'])]==[tuple(w) for w in p['matching_directions']]
    cursor=0;excluded=improved=0
    for q,prefix in enumerate(prefixes):
        # Rebuild each source block, its emitted share and its destination history.
        candidates=np.arange(len(source['U'])) if q==0 else np.flatnonzero(source['U']//B==meta['compatible_shapes'][q])
        countcode=source['count_code'][candidates];credit=source['share_lower'][candidates].copy()
        reject=np.zeros(len(candidates),dtype=bool);nextq=np.zeros(len(candidates),dtype=np.int16)
        for d in np.unique(source['direction'][candidates]):
            mask=source['direction'][candidates]==d;word=prefix+(int(d),)
            possible=[(len(p),i) for i,p in enumerate(prefixes) if p and len(p)<=len(word) and word[-len(p):]==p]
            nextq[mask]=max(possible)[1] if possible else 0
            for p in patterns:
                if len(word)<3 or word[-3:]!=tuple(p['signature']):continue
                allowed=mask.copy()
                for k,cap in p['caps'].items():allowed&=(countcode//6**(5-int(k)))%6+1<=cap
                if p['mode']=='exclusion':reject|=allowed
                else:
                    credit[mask]=np.maximum(credit[mask],p['geometric_lower'])
                    credit[allowed]=np.maximum(credit[allowed],p['lower'])
        ix=candidates[~reject];n=len(ix);sl=slice(cursor,cursor+n);cursor+=n
        assert np.array_equal(a['source_edge'][sl],ix) and np.all(a['history'][sl]==q)
        expectedU=source['U'][ix] if q==0 else N+(q-1)*B+source['U'][ix]%B
        t=nextq[~reject].astype(np.int64)
        expectedV=np.where(t==0,source['V'][ix],N+(t-1)*B+source['V'][ix]%B)
        assert np.array_equal(a['U'][sl],expectedU) and np.array_equal(a['V'][sl],expectedV)
        assert np.array_equal(a['weight'][sl],120*source['count'][ix].astype(np.int64)+credit[~reject])
        excluded+=int(reject.sum());improved+=int((credit[~reject]>source['share_lower'][ix]).sum())
    assert cursor==len(a['U'])==meta['edges']
    raw=gzip.decompress((HERE/f'data/{name}-potential.i64.gz').read_bytes())
    assert hashlib.sha256(raw).hexdigest()==result['potential_sha256']
    pi=np.frombuffer(raw,dtype='<i8');assert len(pi)==meta['states'] and min(pi)==0 and max(pi)==result['potential_range']
    mu=Fraction(result['integer_mean']);p,d=mu.numerator,mu.denominator
    assert np.all(p+pi[a['V']]<=d*a['weight'].astype(np.int64)+pi[a['U']])
    cycle=result['cycle'];ci=[r['edge'] for r in cycle]
    assert ci and all(a['V'][e]==a['U'][ci[(i+1)%len(ci)]] for i,e in enumerate(ci))
    assert d*int(a['weight'][ci].astype(np.int64).sum())==p*len(ci)
    assert Fraction(result['conditional_bound'])==Fraction(1099680*d+8*p+max(pi),p+4200*d)
    reports.append(dict(name=name,status='PASS',states=len(pi),edges=cursor,excluded=excluded,improved=improved,
        integer_mean=str(mu),cycle_length=len(ci),seconds=time.monotonic()-start))
    print(reports[-1],flush=True)
out=dict(status='PASS',canonical_eleven_shapes=11162,models=reports,
    scope='Independent finite computation, not Lean replay or a completed global snake bound.')
(HERE/('data/pressured-verification.json' if sys.argv[1:]==['pressured'] else 'data/model-verification.json')).write_text(json.dumps(out,indent=2)+'\n')
