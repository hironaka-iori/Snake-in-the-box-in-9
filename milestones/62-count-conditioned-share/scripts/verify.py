"""Separate reconstruction using Hamming-distance adjacency and global faces."""
from pathlib import Path
from fractions import Fraction
import itertools,json,hashlib
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text())
NB=[{y for y in range(512) if (x^y).bit_count()==1} for x in range(512)]
faces=[];incident=[[] for _ in range(512)]
for a,b in itertools.combinations(range(9),2):
    for x in range(512):
        if x&(1<<a) or x&(1<<b):continue
        f={x,x+(1<<a),x+(1<<b),x+(1<<a)+(1<<b)}
        faces.append(f)
        for q in f:incident[q].append(f)
assert len(faces)==4608 and all(len(fs)==36 for fs in incident)
def forced(q,W):
    T=set(W)|{q}
    return any(len(NB[v]&T)>=3 for v in T)
def credit(C,D):
    return sum(12*sum(f<=D for f in incident[q])//len(NB[q]-D) for c in C for q in NB[c])
def canon(ds):
    names={};return tuple(names.setdefault(x,len(names)) for x in ds)
critical=read(ROOT/'milestones/61-critical-family-share/data/critical-edges.json')
branches=steps=0
for i,e in enumerate(critical):
    c=read(HERE/f'data/cases/e{i:02d}.json');W=[0]
    for d in e['directions']:W.append(W[-1]^(1<<d))
    assert c['vertices']==W and c['directions']==e['directions'] and c['counts']==e['counts']
    for k,t in enumerate(c['constraints']):
        j=k+3;ds=e['directions'];free=set(range(9))-{ds[j-1],ds[j]}
        K={W[j]^(1<<a)^(1<<b) for a,b in itertools.combinations(free,2)}
        assert set(t['corners'])==K and len(K)==21 and t['lo']==e['counts'][k]
        assert t['hi']==(21 if t['lo']==6 else t['lo'])
    for trial in c['trials']:
        k=trial['site']
        assert [b['missing'] for b in trial['branches']]==(c['constraints'][k]['corners'] if k is not None else [None])
        for b in trial['branches']:
            branches+=1;S=set(W);D=set()
            if k is not None:
                assert c['constraints'][k]['lo']==c['constraints'][k]['hi']==1
                S|=set(c['constraints'][k]['corners'])-{b['missing']};D.add(b['missing'])
            for t in b['trace']:
                steps+=1;rule=t['rule'];A=set(t.get('absent',[]));B=set(t.get('selected',[]))
                if rule=='crowded':assert all(len(NB[v]&S)>=3 for v in A)
                elif rule=='saturated':assert all(any(v in NB[u] and len(NB[u]&S)==2 for u in S) for v in A)
                else:
                    con=c['constraints'][t['constraint']];K=set(con['corners'])
                    if rule=='count_upper':assert len(K&D)==con['hi'] and B<=K-D
                    elif rule=='count_lower':assert len(K&S)==21-con['lo'] and A<=K-S
                    else:raise AssertionError(rule)
                S|=B;D|=A
            if b['status']=='CLOSED':
                assert S==set(b['selected']) and D==set(b['absent']) and not S&D
                assert all(len(NB[v]&S)<=2 for v in S)
                assert all(len(set(t['corners'])&D)<=t['hi'] and len(set(t['corners'])&S)<=21-t['lo'] for t in c['constraints'])
                assert b['lower']==credit(W[4:9],D)
            else:
                rule,v=b['reason']
                if rule=='conflict':assert v in S&D
                elif rule=='degree':assert v in S and len(NB[v]&S)>2
                elif rule=='count_upper':assert len(set(c['constraints'][v]['corners'])&D)>c['constraints'][v]['hi']
                elif rule=='count_lower':assert len(set(c['constraints'][v]['corners'])&S)>21-c['constraints'][v]['lo']
                else:raise AssertionError(rule)
rows=read(HERE/'data/split-share.json')['rows'];trials=0
for i,r in enumerate(rows):
    assert r['directions']==critical[i]['directions'] and r['old']==critical[i]['share_lower']
    W=r['vertices'];C=r['centres'];assert C==W[4:9]
    assert len(set(W))==len(W) and all((W[j]^W[k]).bit_count()!=1 for j in range(len(W)) for k in range(j+2,len(W)))
    for t in r['trials']:
        trials+=1;q=t['split'];D0=set(t['absent0']);D1=set(t['absent1'])
        assert q in D0 and q not in W
        assert all(forced(v,W) for v in D0-{q}) and all(forced(v,W+[q]) for v in D1)
        assert credit(C,D0)==t['credit0'] and credit(C,D1)==t['credit1']
        assert t['lower']==min(t['credit0'],t['credit1'])
    assert r['lower']==max(t['lower'] for t in r['trials'])
    assert any(all(r[k]==t[k] for k in ['split','absent0','absent1','credit0','credit1','lower']) for t in r['trials'])
credits={tuple(r['directions']):r['lower'] for r in rows if r['lower']>r['old']}
graphs=read(HERE/'data/graph-analyses.json')
for g in graphs:
    n=g['length'];prior=critical if n==9 else read(ROOT/f'milestones/61-critical-family-share/data/lift-{n}.json')['edges']
    nodes=sorted({e['u'] for e in prior}|{e['v'] for e in prior});idx={v:i for i,v in enumerate(nodes)}
    es=g['edges'];assert len(es)==len(prior) and g['states']==len(nodes)
    for e,p in zip(es,prior):
        assert e['u']==idx[p['u']] and e['v']==idx[p['v']] and e['directions']==p['directions'] and e['counts']==p['counts']
        assert e['weight']==120*p['counts'][-1]+max(p['share_lower'],credits.get(canon(p['directions'][-9:]),0))
    mu=Fraction(g['integer_mean']);a,b=mu.numerator,mu.denominator;pi=g['potential']
    assert all(a+pi[e['v']]<=b*e['weight']+pi[e['u']] for e in es)
    cycle=[es[i] for i in g['cycle']];assert cycle
    assert all(e['v']==cycle[(i+1)%len(cycle)]['u'] for i,e in enumerate(cycle))
    assert b*sum(e['weight'] for e in cycle)==a*len(cycle)
out=dict(status='PASS',count_branch_traces=branches,deduction_steps=steps,critical_edges=74,split_trials=trials,
    improved_geometric_bounds=len(credits),finite_graphs=3,faces=4608,
    scope='Independent integer reconstruction. Count-based candidates and floating LP results remain outside Lean-checked bounds.',
    hashes={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [HERE/'data/split-share.json',HERE/'data/graph-analyses.json']})
(HERE/'data/verification.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
