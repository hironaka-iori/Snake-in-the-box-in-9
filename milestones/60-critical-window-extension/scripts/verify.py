"""Separate face-incidence and exhaustive-extension checks for the restricted probe."""
from pathlib import Path
from fractions import Fraction
import hashlib,itertools,json,re
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text())
def canon(ds):
    m={};return tuple(m.setdefault(d,len(m)) for d in ds)
def path(ds):
    w=[0]
    for d in ds:w.append(w[-1]^(1<<d))
    return w
def induced(w):
    return len(w)==len(set(w)) and all((w[i]^w[j]).bit_count()==1 if j==i+1 else (w[i]^w[j]).bit_count()!=1 for i in range(len(w)) for j in range(i+1,len(w)))
NB=[{x^(1<<d) for d in range(9)} for x in range(512)]
faces=[];inc=[[] for _ in range(512)]
for a,b in itertools.combinations(range(9),2):
    mask=(1<<a)|(1<<b)
    for x in range(512):
        if x&mask:continue
        f=frozenset([x,x|(1<<a),x|(1<<b),x|mask]);faces.append(f)
        for v in f:inc[v].append(f)
assert len(set(faces))==4608
def check_geometry(r):
    w=path(r['directions']);assert induced(w) and w==r['vertices']
    s=set(w);d={q for q in range(512) if any(len(NB[x]&(s|{q}))>=3 for x in s)}
    assert sorted(d)==r['forced_absent'] and r['centres']==w[-6:-1]
    terms=[]
    for c in r['centres']:
        for q in sorted(NB[c]):
            empty=sum(f<=d for f in inc[q]);upper=len(NB[q]-d)
            assert upper>=1
            credit=12*empty//upper
            if credit:terms.append(dict(centre=c,corner=q,empty=empty,degree_upper=upper,credit=credit))
    assert terms==r['terms'] and sum(t['credit'] for t in terms)==r['geometric_lower']
    assert r['weight']==120*r['counts'][-1]+max(r['geometric_lower'],r['inherited_lower'])
source=ROOT/'milestones/59-extended-share-window/extended/data/analysis-share.json'
base=read(source)['cycle'];probe=read(HERE/'data/probe.json');rs=probe['records']
assert len(base)==len(rs)==20
for i,e in enumerate(base):
    assert e['next_state']==base[(i+1)%20]['state']
    assert e['counts'][1:]==base[(i+1)%20]['counts'][:5]
    assert canon(e['directions'][1:])==canon(base[(i+1)%20]['directions'][:8])
    # Enumerate all nine actual coordinate choices, then quotient unused labels.
    candidates={canon(e['directions']+[d]) for d in range(9)}
    candidates={ds for ds in candidates if canon(ds[1:])==tuple(base[(i+1)%20]['directions']) and induced(path(ds))}
    actual=[r for r in rs if r['phase']==i]
    assert {tuple(r['directions']) for r in actual}==candidates and len(actual)==1
    r=actual[0];check_geometry(r)
    assert r['counts']==base[(i+1)%20]['counts'] and r['inherited_lower']==base[(i+1)%20]['share_lower']
    assert probe['phases'][i]['options']==[i] and probe['phases'][i]['minimum_weight']==r['weight']
assert probe['chosen']==list(range(20))
mu=Fraction(sum(r['weight'] for r in rs),20)
threshold=Fraction(1099560-235*4200,235-9)
assert mu==Fraction(probe['integer_weight_mean'])==Fraction(2478,5)
assert threshold==Fraction(probe['required_mean_zero_range'])==Fraction(56280,113)
assert mu<threshold and probe['cycle_still_prevents_234']
deep=read(HERE/'data/deeper-probe.json')['levels'];assert len(deep)==1
layer=deep[0];assert layer['length']==11;counts=[]
for i,r in enumerate(rs):
    nxt=rs[(i+1)%20]
    candidates={canon(r['directions']+[d]) for d in range(9)}
    candidates={ds for ds in candidates if canon(ds[1:])==tuple(nxt['directions']) and induced(path(ds))}
    actual=[a for a in layer['records'] if a['phase']==i]
    assert {tuple(a['directions']) for a in actual}==candidates
    for a in actual:
        check_geometry(a)
        assert a['counts']==nxt['counts'] and a['inherited_lower']==max(nxt['geometric_lower'],nxt['inherited_lower'])
    counts.append(len(candidates))
assert counts==layer['extension_counts']
controls=read(HERE/'data/validity-controls.json');assert [r['phase'] for r in controls]==[14,15,16]
for r in controls:
    i=r['phase'];w=path(r['directions']);assert w==r['vertices'] and len(set(w))==12
    compatible={canon(rs[i]['directions']+[d]) for d in range(9)
                if canon(rs[i]['directions'][1:]+[d])==tuple(rs[(i+1)%20]['directions'])}
    assert compatible=={tuple(r['directions'])}
    assert canon(r['directions'][:10])==tuple(rs[i]['directions'])
    assert canon(r['directions'][1:])==tuple(rs[(i+1)%20]['directions'])
    chords=[(a,b) for a in range(12) for b in range(a+2,12) if (w[a]^w[b]).bit_count()==1]
    assert chords==[(0,11)]
    assert all(len(NB[x]&set(w))==2 for x in w)
out=dict(status='PASS',source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
         ten_transition_extensions=len(rs),positive_ten_bounds=sum(r['geometric_lower']>0 for r in rs),
         integer_weight_mean=str(mu),normalized_mean=str(mu/120),zero_range_threshold=str(threshold),
         eleven_transition_option_counts=counts,validity_controls=[14,15,16],
         scope='Complete extensions of the single recorded cycle only. Eleven-step missing windows close twelve-cycles. No full ten- or eleven-transition model and no global upper-bound improvement.')
(HERE/'data/verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
