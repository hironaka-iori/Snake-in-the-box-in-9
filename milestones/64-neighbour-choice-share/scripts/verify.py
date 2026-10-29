from pathlib import Path
from fractions import Fraction
import itertools,json,hashlib,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text())
NB=[{y for y in range(512) if (x^y).bit_count()==1} for x in range(512)]
NM=[sum(1<<q for q in ns) for ns in NB];incident=[[] for _ in range(512)]
for a,b in itertools.combinations(range(9),2):
    for x in range(512):
        if x&(1<<a) or x&(1<<b):continue
        face={x,x+(1<<a),x+(1<<b),x+(1<<a)+(1<<b)};mask=sum(1<<v for v in face)
        for q in face:incident[q].append(mask)
def forced(q,T):
    S=set(T)|{q}
    return any(len(NB[v]&S)>=3 for v in S)
def credit(C,D):
    mask=sum(1<<q for q in D)
    return sum(12*sum(f&mask==f for f in incident[q])//(9-(NM[q]&mask).bit_count()) for c in C for q in NB[c])
rows=read(HERE/'data/choices.json')['rows'];old=read(ROOT/'milestones/63-long-window-splits/data/analysis.json');g=read(HERE/'data/analysis.json')
assert len(rows)==len(old['edges'])==len(g['edges'])==218
seen={};branches=contradictions=0;start=time.monotonic()
for i,(r,e,p) in enumerate(zip(rows,g['edges'],old['edges'])):
    assert r['edge']==i and r['directions']==e['directions']==p['directions'] and e['counts']==p['counts']
    assert e['u']==p['u'] and e['v']==p['v']
    assert r['old']==p['weight']-120*p['counts'][-1]
    assert e['weight']==120*e['counts'][-1]+max(r['old'],r['lower'])
    ds=tuple(r['directions'])
    if ds in seen:
        assert all(r[k]==seen[ds][k] for k in ['vertices','centres','A','B','D','branches','lower']);continue
    seen[ds]=r;W=[0]
    for d in ds:W.append(W[-1]^(1<<d))
    assert W==r['vertices'] and r['centres']==W[6:11] and len(set(W))==12
    assert all((W[j]^W[k]).bit_count()!=1 for j in range(12) for k in range(j+2,12))
    D={q for q in range(512) if q not in W and forced(q,W)};A=set(r['A']);B=set(r['B'])
    assert D==set(r['D']) and A==NB[W[0]]-set(W)-D and B==NB[W[-1]]-set(W)-D
    for X in [A,B]:
        assert all(any(len(NB[v]&(set(W)|{a,b}))>=3 for v in set(W)|{a,b}) for a,b in itertools.combinations(X,2))
    expected=list(itertools.product([None]+sorted(A),[None]+sorted(B)))
    assert [tuple(b['choices']) for b in r['branches']]==expected
    values=[]
    for br,(a,b) in zip(r['branches'],expected):
        branches+=1;T=set(W)|{v for v in [a,b] if v is not None}
        K=(A-({a} if a is not None else set()))|(B-({b} if b is not None else set()))
        assert not T&K
        if br['status']=='CONTRADICTION':
            contradictions+=1;assert any(len(NB[v]&T)>2 for v in T);continue
        assert all(len(NB[v]&T)<=2 for v in T)
        F={q for q in range(512) if q not in T and forced(q,T)}
        assert F==set(br['forced']) and D<=F
        absent=F|K;assert absent==set(br['absent']) and not absent&T
        assert br['mask']==sum(1<<v for v in absent) and br['lower']==credit(r['centres'],absent)
        values.append(br['lower'])
    assert values and r['lower']==min(values)
compact=read(HERE/'data/compact-certificates.json')['rows'];compressed_cases=0
assert {r['edge'] for r in compact}=={r['edge'] for r in rows if r['lower']>r['old']}
for entry in compact:
    r=rows[entry['edge']];assert len(entry['cases'])==len(r['branches'])
    for br,small in zip(r['branches'],entry['cases']):
        compressed_cases+=1;assert br['choices']==small['choices']
        a,b=br['choices'];T=set(r['vertices'])|{v for v in [a,b] if v is not None}
        K=(set(r['A'])-({a} if a is not None else set()))|(set(r['B'])-({b} if b is not None else set()))
        F=set(small['forced']);D=set(small.get('absent',[]))
        assert all(forced(q,T) for q in F) and D<=F|K
        assert small['mask']==sum(1<<v for v in D) and credit(r['centres'],D)>=r['lower']
mu=Fraction(g['integer_mean']);p,d=mu.numerator,mu.denominator;pi=g['potential'];es=g['edges']
assert all(p+pi[e['v']]<=d*e['weight']+pi[e['u']] for e in es)
cy=[es[i] for i in g['cycle']];assert cy and all(e['v']==cy[(i+1)%len(cy)]['u'] for i,e in enumerate(cy))
assert d*sum(e['weight'] for e in cy)==p*len(cy)
out=dict(status='PASS',unique_shapes=len(seen),branches=branches,degree_contradictions=contradictions,compressed_certificates=compressed_cases,improved_bounds=sum(r['lower']>r['old'] for r in rows),
    states=g['states'],edges=len(es),integer_mean=str(mu),threshold_gap=str(Fraction(112440,225)-mu),seconds=time.monotonic()-start,
    scope='Independent geometric and exact-integer check of full neighbour choices and restricted graph. Lean status is recorded separately; no global bound.',
    hashes={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [HERE/'data/choices.json',HERE/'data/analysis.json',HERE/'data/compact-certificates.json']})
(HERE/'data/verification.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
