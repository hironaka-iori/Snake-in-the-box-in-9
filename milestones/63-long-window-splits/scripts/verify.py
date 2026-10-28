"""Independent check of geometry, exhaustive split coverage and the finite minimum."""
from pathlib import Path
from fractions import Fraction
import itertools,json,hashlib,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text())
NB=[{y for y in range(512) if (x^y).bit_count()==1} for x in range(512)]
NM=[sum(1<<q for q in ns) for ns in NB];incident=[[] for _ in range(512)];facecount=0
for a,b in itertools.combinations(range(9),2):
    for x in range(512):
        if x&(1<<a) or x&(1<<b):continue
        vertices={x,x+(1<<a),x+(1<<b),x+(1<<a)+(1<<b)}
        mask=sum(1<<v for v in vertices);facecount+=1
        for q in vertices:incident[q].append(mask)
assert facecount==4608 and all(len(fs)==36 for fs in incident)
def forced(q,W):
    T=set(W)|{q}
    return any(len(NB[v]&T)>=3 for v in T)
def credit(C,D):
    mask=sum(1<<v for v in D);total=0
    for c in C:
        for q in NB[c]:
            den=9-(NM[q]&mask).bit_count();assert den>0
            total+=12*sum(f&mask==f for f in incident[q])//den
    return total
old=next(g for g in read(ROOT/'milestones/62-count-conditioned-share/data/graph-analyses.json') if g['length']==11)
rows=read(HERE/'data/splits.json')['rows'];g=read(HERE/'data/analysis.json')
assert len(rows)==len(old['edges'])==len(g['edges'])==218
cache={};alltrials=pruned=0;start=time.monotonic()
for i,(r,e,prev) in enumerate(zip(rows,g['edges'],old['edges'])):
    assert r['edge']==i and r['directions']==e['directions']==prev['directions']
    assert e['u']==prev['u'] and e['v']==prev['v'] and e['counts']==prev['counts']
    assert r['old']==prev['weight']-120*prev['counts'][-1]
    assert e['weight']==120*e['counts'][-1]+max(r['old'],r['lower'])
    ds=tuple(r['directions']);W=[0]
    for d in ds:W.append(W[-1]^(1<<d))
    assert W==r['vertices'] and len(set(W))==12 and r['centres']==W[6:11]
    assert all((W[j]^W[k]).bit_count()!=1 for j in range(12) for k in range(j+2,12))
    if ds in cache:
        ref=cache[ds]
        assert all(r[k]==ref[k] for k in ['lower','split','absent0','absent1','credit0','credit1','trials'])
        continue
    cache[ds]=r;C=r['centres'];D={q for q in range(512) if q not in W and forced(q,W)}
    assert r['base']==credit(C,D) and r['lower']>=r['base']
    assert len(r['trials'])==len({t['split'] for t in r['trials']})
    assert {t['split'] for t in r['trials']}==set(range(512))-set(W)-D
    best=-1
    for t in r['trials']:
        alltrials+=1;q=t['split'];a=credit(C,D|{q});assert a==t['credit0']
        if 'pruned_by' in t:
            pruned+=1;assert a<=t['pruned_by']==best
        else:
            D1={v for v in range(512) if v not in W+[q] and forced(v,W+[q])}
            b=credit(C,D1);assert b==t['credit1'] and t['lower']==min(a,b)
            best=max(best,min(a,b))
    assert best==r['lower']
    q=r['split'];assert set(r['absent0'])==D|{q}
    assert set(r['absent1'])=={v for v in range(512) if v not in W+[q] and forced(v,W+[q])}
    assert credit(C,set(r['absent0']))==r['credit0'] and credit(C,set(r['absent1']))==r['credit1']
    assert r['lower']==min(r['credit0'],r['credit1'])
mu=Fraction(g['integer_mean']);p,d=mu.numerator,mu.denominator;pi=g['potential'];es=g['edges']
assert all(p+pi[e['v']]<=d*e['weight']+pi[e['u']] for e in es)
cycle=[es[i] for i in g['cycle']];assert len(cycle)>0
assert all(e['v']==cycle[(i+1)%len(cycle)]['u'] for i,e in enumerate(cycle))
assert d*sum(e['weight'] for e in cycle)==p*len(cycle)
assert Fraction(112440,225)-mu==Fraction(73,30)
adj=read(HERE/'data/adjacent-splits.json')['rows'];assert all(a['lower']==b['lower'] for a,b in zip(adj,rows))
out=dict(status='PASS',unique_shapes=len(cache),geometric_split_trials=alltrials,pruned_trials=pruned,improved_bounds=sum(r['lower']>r['old'] for r in rows),
    graph_states=g['states'],graph_edges=len(es),integer_mean=str(mu),faces=facecount,seconds=time.monotonic()-start,
    scope='Independent reconstruction of all single-vertex choices under the specified degree-forcing rule, improved local numbers and the restricted finite graph minimum. No global bound.',
    hashes={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [HERE/'data/splits.json',HERE/'data/analysis.json']})
(HERE/'data/verification.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
