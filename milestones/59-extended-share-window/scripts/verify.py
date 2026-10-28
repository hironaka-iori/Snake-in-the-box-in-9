"""Separate exhaustive geometry and integer-potential verification."""
from pathlib import Path
from fractions import Fraction
import gzip,hashlib,itertools,json,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'work/solver_packages'))
import numpy as np
read=lambda p:json.loads(p.read_text())
sha=lambda b:hashlib.sha256(b).hexdigest()
def canon(word):
    labels={};return tuple(labels.setdefault(x,len(labels)) for x in word)
def path(word):
    out=[0]
    for d in word:out.append(out[-1]^(1<<d))
    return out
def words(w=(),v=(0,)):
    if len(w)==9:yield w;return
    for d in range(min(9,max(w,default=-1)+2)):
        q=v[-1]^(1<<d)
        if q in v or any((q^x).bit_count()==1 for x in v[:-1]):continue
        yield from words(w+(d,),v+(q,))
NB=[{x^(1<<d) for d in range(9)} for x in range(512)]
faces=[];inc=[[] for _ in range(512)]
for a,b in itertools.combinations(range(9),2):
    mask=(1<<a)|(1<<b)
    for x in range(512):
        if x&mask:continue
        f=frozenset([x,x|(1<<a),x|(1<<b),x|mask]);faces.append(f)
        for q in f:inc[q].append(f)
assert len(set(faces))==4608
rows=read(HERE/'data/geometry.json')['patterns'];assert len(rows)==505
assert {tuple(r['directions']) for r in rows}==set(words())
prior_rows=read(ROOT/'milestones/58-share-pressure/data/forced-geometry.json')['patterns']
prior_lookup={tuple(r['directions']):r['share_lower'] for r in prior_rows}
for r in rows:
    W=path(r['directions']);assert r['vertices']==W
    S=set(W)
    D={q for q in range(512) if any(len(NB[x]&(S|{q}))>2 for x in S)}
    assert sorted(D)==r['forced_absent'] and not D&S
    C=W[4:9];assert C==r['centres']
    terms=[]
    for c in C:
        for q in sorted(NB[c]):
            e=sum(f<=D for f in inc[q]);upper=len(NB[q]-D)
            assert 0<len(NB[q]&S)<=upper
            value=12*e//upper
            if value:terms.append(dict(centre=c,corner=q,empty=e,degree_upper=upper,credit=value))
    assert terms==r['terms']
    assert r['share_lower']==sum(t['credit'] for t in terms)
    assert r['suffix_lower']==prior_lookup[canon(r['directions'][1:])]<=r['share_lower']

def load(folder):
    md=read(folder/'data/model.json')
    with np.load(folder/'build/graph.npz') as z:a={k:z[k] for k in z.files}
    for k,h in md['arrays_sha256'].items():assert sha(a[k].tobytes())==h
    return md,a
base_md,base=load(ROOT/'milestones/58-share-pressure/geometry')
base_shapes={tuple(ds):i for i,ds in enumerate(base_md['extensions'])}
results=[]
for name in ['lifted','extended']:
    md,a=load(HERE/name);assert md['states']==132*6**5
    assert md['extensions']==[r['directions'] for r in rows]
    assert md['direction_shapes']==base_md['extensions']
    pos=0;strengthened=0
    for di,r in enumerate(rows):
        ds=r['directions'];si=base_shapes[canon(ds[1:])];pi=base_shapes[canon(ds[:8])]
        l,h=np.searchsorted(base['direction'],[si,si+1]);n=int(h-l)
        sl=slice(pos,pos+n);ix=slice(l,h);codes=base['count_code'][ix]
        assert np.all(a['direction'][sl]==di)
        assert np.array_equal(a['count_code'][sl],codes)
        assert np.array_equal(a['U'][sl],pi*6**5+codes//6)
        assert np.array_equal(a['V'][sl],si*6**5+codes%(6**5))
        assert np.array_equal(a['count'][sl],codes%6+1)
        expected=base['share_lower'][ix]
        if name=='extended':expected=np.maximum(expected,r['share_lower'])
        strengthened+=int((expected>base['share_lower'][ix]).sum())
        assert np.array_equal(a['share_lower'][sl],expected)
        pos+=n
    assert pos==len(a['U'])==md['edges']==11594078
    assert strengthened==md['strengthened_transitions']
    result=read(HERE/name/'data/analysis-share.json')
    raw=gzip.decompress((HERE/name/'data/potential-share.i64.gz').read_bytes())
    assert sha(raw)==result['potential_sha256']
    pot=np.frombuffer(raw,dtype='<i8');mu=Fraction(result['integer_weight_mean']);p,q=mu.numerator,mu.denominator
    weight=120*a['count'].astype(np.int64)+a['share_lower']
    assert len(pot)==md['states']
    assert np.all(q*weight+pot[a['U']]-pot[a['V']]>=p)
    span=int(pot.max()-pot.min());assert span==result['potential_range']
    cycle=result['cycle']
    for j,e in enumerate(cycle):
        di=md['extensions'].index(e['directions']);code=0
        for c in e['counts']:code=6*code+c-1
        l,h=np.searchsorted(a['direction'],[di,di+1]);hit=np.flatnonzero(a['count_code'][l:h]==code)
        assert len(hit)==1;i=l+int(hit[0])
        assert e['state']==int(a['U'][i]) and e['next_state']==int(a['V'][i])==cycle[(j+1)%len(cycle)]['state']
        assert e['weight']==int(weight[i]) and e['share_lower']==int(a['share_lower'][i])
    assert Fraction(sum(e['weight'] for e in cycle),len(cycle))==mu
    bound=Fraction(1099680*q+8*p+span,p+4200*q)
    assert str(bound)==result['conditional_edge_bound']
    results.append(dict(name=name,states=md['states'],edges=pos,mean=str(mu/120),cycle_length=len(cycle),
                        cycle_share=sum(e['share_lower'] for e in cycle),potential_range=span,
                        bound=str(bound),integer_bound=bound.numerator//bound.denominator,strengthened=strengthened))
    del a,weight,pot

lookup={tuple(r['directions']):r['share_lower'] for r in rows}
bank=read(ROOT/'work/bank9.json');nwin=npositive=0;minmargin=None;seen=set()
for r in bank:
    W=r['vertex_sequence'];S=set(W)
    assert len(S)==len(W) and all(0<=x<512 for x in W)
    assert all((W[i]^W[i+1]).bit_count()==1 for i in range(len(W)-1))
    assert all((W[i]^W[j]).bit_count()!=1 for i in range(len(W)) for j in range(i+2,len(W)))
    empty=[sum(not(f&S) for f in inc[q]) for q in range(512)]
    deg=[len(NB[q]&S) for q in range(512)]
    shares={c:sum(12*empty[q]//deg[q] for q in NB[c]) for c in S}
    for V in [W,W[::-1]]:
        dirs=[(V[i]^V[i+1]).bit_length()-1 for i in range(len(V)-1)]
        for i in range(len(dirs)-8):
            shape=canon(dirs[i:i+9]);seen.add(shape);lo=lookup[shape]
            margin=sum(shares[x] for x in V[i+4:i+9])-lo;assert margin>=0
            minmargin=margin if minmargin is None else min(minmargin,margin)
            nwin+=1;npositive+=lo>0
probe=read(HERE/'data/centering-probe.json')
saved_cycle=read(HERE/'extended/data/analysis-share.json')['cycle']
by_word={tuple(r['directions']):r for r in rows}
rules=base_md['share_rules'];centre_total=0
for edge,given in zip(saved_cycle,probe['rows']):
    r=by_word[tuple(edge['directions'])];D=set(r['forced_absent']);value=0
    for c in r['vertices'][3:8]:
        for q in NB[c]:value+=12*sum(f<=D for f in inc[q])//len(NB[q]-D)
    shape=canon(edge['directions'][2:8]);counts=edge['counts'][:5]
    inherited=max([0]+[t['lower'] for t in rules if tuple(t['directions'])==shape and t['counts']==counts])
    assert value==given['centred_geometry'] and inherited==given['inherited_lower']
    w=120*edge['counts'][-1]+max(value,inherited);assert w==given['weight'];centre_total+=w
centred_mean=Fraction(centre_total,len(saved_cycle));threshold=Fraction(112680,227)
assert centred_mean==Fraction(probe['centred_cycle_mean'])==Fraction(9891,20)
assert threshold==Fraction(probe['required_mean_at_zero_range']) and centred_mean<threshold
out=dict(status='PASS',shapes=len(rows),positive=sum(r['share_lower']>0 for r in rows),
         improved_shapes=sum(r['share_lower']>r['suffix_lower'] for r in rows),maximum=max(r['share_lower'] for r in rows),
         models=results,bank=dict(paths=len(bank),windows=nwin,positive_windows=npositive,shapes=len(seen),minimum_margin=minmargin),
         centering_probe=dict(cycle_length=len(saved_cycle),cycle_mean=str(centred_mean),threshold=str(threshold),scope='Saved cycle only; no complete centred-model minimum asserted.'),
         scope='Separate exact computations check geometry, suffix lifts, every potential inequality and attaining cycles. Lean results are audited separately. Inherited numerical premises and full graph-to-snake assembly remain pending.')
(HERE/'data/verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
