"""Independent finite reconstruction; does not import search or certificate generators."""
from pathlib import Path
from fractions import Fraction
import hashlib,itertools,json,re,time
HERE=Path(__file__).resolve().parents[1]; ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
start=time.monotonic()
NB=[{y for y in range(512) if (x^y).bit_count()==1} for x in range(512)]
faces=[];incident=[[] for _ in range(512)]
for a,b in itertools.combinations(range(9),2):
    for x in range(512):
        if x&(1<<a) or x&(1<<b):continue
        F={x,x^(1<<a),x^(1<<b),x^(1<<a)^(1<<b)}
        mask=sum(1<<v for v in F);faces.append(mask)
        for v in F:incident[v].append(mask)
assert len(faces)==4608 and all(len(fs)==36 for fs in incident)
def bad(T):return any(len(NB[v]&T)>2 for v in T)
def forced(T,q):return bad(T|{q})
def credit(C,D):
    mask=sum(1<<q for q in D);total=0
    for c in C:
        for q in NB[c]:
            den=9-len(NB[q]&D);assert den>0
            total+=12*sum(f&mask==f for f in incident[q])//den
    return total
base=read(ROOT/'milestones/64-neighbour-choice-share/data/choices.json')['rows']
old=read(ROOT/'milestones/64-neighbour-choice-share/data/analysis.json')
pack=read(HERE/'data/compact-certificates.json')['rows']
assert {x['edge'] for x in pack}=={7,10,11,24,44,45,57,58,91,115}
branches=steps=0;used_caps={};gains={}
for entry in pack:
    i=entry['edge'];r=read(HERE/f'data/cases/e{i:03d}.json');origin=base[i]
    W=[0]
    for d in r['directions']:W.append(W[-1]^(1<<d))
    assert W==r['vertices']==origin['vertices']
    assert r['centres']==W[6:11] and len(set(W))==12
    assert all((W[j]^W[k]).bit_count()!=1 for j in range(12) for k in range(j+2,12))
    assert r['directions']==old['edges'][i]['directions'] and r['counts']==old['edges'][i]['counts']
    assert entry['lower']==(r['lower'] or 0)
    A=set(r['A']);B=set(r['B']);knownW=set(W)
    D0={q for q in range(512) if q not in knownW and forced(knownW,q)}
    assert A==NB[W[0]]-knownW-D0 and B==NB[W[-1]]-knownW-D0
    for X in [A,B]:assert all(bad(knownW|{a,b}) for a,b in itertools.combinations(X,2))
    for k,c in enumerate(r['constraints']):
        j=k+5;free=set(range(9))-{r['directions'][j-1],r['directions'][j]}
        K={W[j]^(1<<a)^(1<<b) for a,b in itertools.combinations(free,2)}
        assert c['position']==j and K==set(c['corners']) and len(K)==21
        assert c['hi']==(21 if r['counts'][k]==6 else r['counts'][k])
    expected=list(itertools.product([None]+sorted(A),[None]+sorted(B)))
    assert [tuple(b['choices']) for b in entry['certificates']]==expected
    used=set()
    for cert,(a,b) in zip(entry['certificates'],expected):
        branches+=1;T=knownW|{q for q in (a,b) if q is not None}
        D=set(cert['forced']);assert all(forced(T,q) for q in D)
        D|=(A-({a} if a is not None else set()))|(B-({b} if b is not None else set()))
        for t in cert['steps']:
            steps+=1;Q=set(t['add'])
            if t['kind']=='degree':
                assert all(forced(T,q) for q in Q);D|=Q
            else:
                assert t['kind']=='select';k=t['condition'];used.add(k);c=r['constraints'][k]
                assert all(c['hi']<len(set(c['corners'])&(D|{q})) for q in Q);T|=Q
        e=cert['ending']
        if e['kind']=='share':
            assert entry['mode']=='share';M=set(e['absent'])
            assert M<=D and e['mask']==sum(1<<q for q in M)
            assert credit(r['centres'],M)>=entry['lower']
        elif e['kind']=='degree':assert bad(T)
        else:
            assert e['kind']=='upper';k=e['condition'];used.add(k);c=r['constraints'][k]
            assert c['hi']<len(set(c['corners'])&D)
    used_caps[str(i)]=sorted(used)
    # Connect the independently checked premises to the replayed instance source.
    bounds=[(0,21)]*10
    for k in used:bounds[k+4]=(0,r['constraints'][k]['hi'])
    source=(HERE/f'lean/Edge{i:03d}.lean').read_text(encoding='utf-8')
    assert f'def bounds : List (Nat × Nat) := {bounds}' in source
    assert f'def W : List Nat := {W}' in source
    if entry['mode']=='share':gains[i]=entry['lower'];assert entry['lower']>r['old']
assert used_caps['24']==[5]
# Direct three-corner obstruction, independently of all count deductions.
W=[0,1,3,7,15,14,30,22,18,50,34,42];D={6,33,39}
assert all(forced(set(W),q) for q in D)
K={34^(1<<a)^(1<<b) for a,b in itertools.combinations(set(range(9))-{4,3},2)}
assert D<=K and len(D)==3
g=next(x for x in read(HERE/'data/candidate-analyses.json') if x['mode']=='shares_only')
mu=Fraction(g['integer_mean']);p,d=mu.numerator,mu.denominator;pi=g['potential'];es=g['edges']
assert len(es)==218 and g['states']==118
for i,(e,o) in enumerate(zip(es,old['edges'])):
    assert (e['u'],e['v'],e['directions'],e['counts'])==(o['u'],o['v'],o['directions'],o['counts'])
    assert e['weight']==max(o['weight'],120*e['counts'][-1]+gains.get(i,0))
    assert p+pi[e['v']]<=d*e['weight']+pi[e['u']]
cy=[es[i] for i in g['cycle']];assert cy
assert all(e['v']==cy[(i+1)%len(cy)]['u'] for i,e in enumerate(cy))
assert d*sum(e['weight'] for e in cy)==p*len(cy) and mu==Fraction(9961,20)
dag=read(HERE/'data/acyclic-family.json');rank=dag['rank'];walk=dag['attaining_walk']
assert dag['edges']==[[e['u'],e['v']] for i,e in enumerate(old['edges']) if i!=24]
assert len(rank)==118 and min(rank)>=0 and max(rank)==19
assert all(rank[u]<rank[v] for u,v in dag['edges'])
assert len(walk)==20 and all([u,v] in dag['edges'] for u,v in zip(walk,walk[1:]))
record=read(HERE/'logs/build-record.json');build=Path(record['build']);audit=[]
assert {p.stem for p in (HERE/'lean').glob('*.lean')}=={r['module'] for r in record['records']}
for r in record['records']:
    name=r['module'];source=HERE/f'lean/{name}.lean';s=source.read_text(encoding='utf-8')
    assert r['exit_code']==0 and sha(source)==r['source_sha256']
    assert (build/f'{name}.olean').exists()
    assert not re.search(r'\b(sorry|admit|native_decide)\b',s)
    log=(HERE/f'logs/{name}.log').read_text(encoding='utf-8')
    assert 'error:' not in log and 'sorryAx' not in log
    names=re.findall(r'^#print axioms (\w+)',s,re.M)
    found=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",log,re.S)
    found+= [(n,'') for n in re.findall(r"'([^']+)' does not depend on any axioms",log)]
    assert sorted(n.rsplit('.',1)[-1] for n,_ in found)==sorted(names),(name,names,found)
    assert all(set(re.findall(r'[A-Za-z][\w.]*',a))<={'propext','Classical.choice','Quot.sound'} for _,a in found)
    audit.append(dict(module=name,checks=len(names),source_sha256=sha(source)))
out=dict(status='PASS',branch_certificates=branches,propagation_steps=steps,improved_bounds=len(gains),
    upper_premises_used=used_caps,integer_mean=str(mu),normalized_mean=str(mu/120),
    improvement=str(mu/120-Fraction(1991,480)),retained_edges=len(dag['edges']),maximum_walk=19,
    seconds=time.monotonic()-start,
    scope='Independent compact-certificate geometry and restricted graph checks; no new global bound.',
    hashes={str(f.relative_to(ROOT)):sha(f) for f in [HERE/'data/compact-certificates.json',HERE/'data/candidate-analyses.json',HERE/'data/acyclic-family.json']})
(HERE/'data/verification.json').write_text(json.dumps(out,indent=2)+'\n')
lean=dict(status='PASS',modules=len(audit),theorem_audits=sum(x['checks'] for x in audit),records=audit,
    scope='Current milestone modules and printed theorem dependencies; imported earlier modules are reused.')
(HERE/'data/lean-audit.json').write_text(json.dumps(lean,indent=2)+'\n')
print(json.dumps(out,indent=2));print('Lean modules',lean['modules'],'audits',lean['theorem_audits'])
