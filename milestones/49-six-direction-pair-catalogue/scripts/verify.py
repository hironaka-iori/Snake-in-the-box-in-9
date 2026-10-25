"""Audit proof provenance, Lean dependencies, controls and the exact graph mean."""
from pathlib import Path
from fractions import Fraction
import gzip,hashlib,itertools,json,re,sys
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'milestones/29-overlapping-share-windows/scripts'))
from joint import TaggedEncoding,window
import gen_lean_sat as gen
sys.path.insert(0,str(ROOT/'work/solver_packages'));import numpy as np

def sha(b):return hashlib.sha256(b).hexdigest()
def read(p):return json.loads((HERE/p).read_text())
def raw(name):
    p=HERE/'certificates'/name
    return p.read_bytes() if p.exists() else gzip.decompress(p.with_name(p.name+'.gz').read_bytes())
def cnf(name):return [list(map(int,l.split()))[:-1] for l in raw(name).decode().splitlines() if l and not l.startswith(('c','p'))]
cases=read('data/cases.json');return_case=read('data/return-case.json');proofs=[]
for case in cases+[return_case]:
    n=case['number'];name=f'{case["kind"]}{n}';meta=read(f'data/{name}.json');W=window(case['dirs'])
    e=TaggedEncoding(W,case['bounds'],radius=4)
    if case['kind']=='sum':
        lits=[-e.var[W[j]^(1<<a)^(1<<b)] for j in case['positions'] for a,b in itertools.combinations(range(9),2) if a not in (case['dirs'][j-1],case['dirs'][j]) and b not in (case['dirs'][j-1],case['dirs'][j])]
        e.atmost(lits,case['cap'],('ends',))
    for cc in meta['cycle_cuts']:
        assert gen.is_cycle_set(cc) and set(cc)<=e.B
        e.add([-e.var[v] for v in cc],('cut',))
    assert e.clauses==cnf(name+'.full.cnf')
    rename={int(k):v for k,v in meta['original_to_new'].items()}
    core=[[(-1 if v<0 else 1)*rename[abs(v)] for v in e.clauses[j-1]] for j in meta['source_original_clause_ids']]
    assert core==cnf(name+'.cnf')
    assert 's VERIFIED' in (HERE/f'logs/{name}-drat-check.txt').read_text()
    export=read(f'logs/{name}-export.txt');assert export['simulated']
    proofs.append(dict(case=n,clauses=len(core),active_variables=meta['active_variables'],derived_clauses=export['lemmas'],hints=export['hints'],added_cycle_cuts=len(meta.get('cycle_cuts',[]))))
audits=[]
for name,expected in [(f"CycleExclusion{c['number']}",2) for c in cases]+[(f"PairBasis{c['number']}",1) for c in cases]+[('SurveyCatalogue',50),('LocalWindowSat-JointIntervening4934',1),('SumWindow4934',3),('WitnessReturn',5),('ReturnSharpConstant',1)]:
    log=(HERE/f'logs/{name}.log').read_text(encoding='utf-8')
    assert not any(x in log for x in ['sorryAx','error:','Lean.ofReduceBool'])
    rows=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",log,re.S)
    assert len(rows)==expected,(name,rows)
    for theorem,axioms in rows:
        assert set(x.strip() for x in axioms.split(','))<={'propext','Classical.choice','Quot.sound'}
        audits.append(theorem)
build=Path((HERE/'build/latest.txt').read_text().strip());sources={}
for p in (HERE/'lean').rglob('*.lean'):
    relative=p.relative_to(HERE/'lean');o=build/relative.with_suffix('.olean')
    assert o.exists() and o.stat().st_mtime>=p.stat().st_mtime,relative
    sources[relative.as_posix()]=sha(p.read_bytes())
records=read('logs/build-record.json')['records']+read('logs/return-build-record.json')['records']+read('logs/witness-build-record.json')['records'];assert len(records)==len(sources)
for r in records:assert r['exit_code']==0 and sources[r['module']+'.lean']==r['source_sha256']
for r in read('data/archives.json'):
    assert sha(raw(r['file']))==r['sha256']
    assert sha((HERE/'certificates'/(r['file']+'.gz')).read_bytes())==r['archive_sha256']
controls=read('data/geometry-controls.json')
for r in controls['local_checks']:assert sha((HERE/'data'/r['file']).read_bytes())==r['sha256']
assert controls['bank_paths_checked']==131
assert sha((ROOT/'work/bank9.json').read_bytes())==controls['bank_sha256']

def canon(ds):
    labels={};return tuple(labels.setdefault(d,len(labels)) for d in ds)
def encode(ds):
    n=0
    for x in ds:n=6*n+x-1
    return n
witness=read('data/witness-return.json');full=read('data/full-return-five.json')
assert sha((HERE/'data/full-return-five.json').read_bytes())==witness['source_sha256']
vs=witness['vertex_sequence'];S=set(vs);assert len(vs)==147 and len(S)==147
assert all(((vs[i]^vs[j]).bit_count()==1)==(j==i+1) for i in range(147) for j in range(i+1,147))
r=witness['start'];directions=[(a^b).bit_length()-1 for a,b in zip(vs,vs[1:])]
assert directions[r:r+4]==[0,1,2,0]
counts=[sum(not({vs[r+j]^(1<<a),vs[r+j]^(1<<b),vs[r+j]^(1<<a)^(1<<b)}&S) for a,b in itertools.combinations(range(9),2)) for j in [1,3]]
assert counts==witness['pair_counts'] and sum(counts)==5
assert vs==full['vertex_sequence'] and full['status']=='SAT'
survey=read('data/survey.json');assert len(survey)==360
# Direct product enumeration is independent of the recursive survey generator.
shape_set=set()
for ds in itertools.product(range(6),repeat=6):
    if ds[0]!=0 or canon(ds)!=ds:continue
    vs=[0]
    for d in ds:vs.append(vs[-1]^(1<<d))
    if len(set(vs))!=7:continue
    if any((vs[i]^vs[j]).bit_count()==1 for i in range(7) for j in range(i+2,7)):continue
    shape_set.add(min(ds,canon(ds[::-1])))
assert shape_set==set(map(tuple,read('data/shapes.json'))) and len(shape_set)==9
expected={(si,a,b,u,v) for si in range(9) for a,b in itertools.combinations(range(1,6),2) for u,v in itertools.product([2,3],repeat=2)}
actual={(r['shape'],*r['positions'],*r['caps']) for r in survey}
assert actual==expected and len(actual)==360
positive={r['file'] for r in controls['local_checks']}
assert sum(r['status']=='SAT' for r in survey)==310
assert sum(r['status']=='UNSAT' for r in survey)==50
coverage=read('data/coverage.json');assert {r['row'] for r in coverage}=={r['name'] for r in survey if r['status']=='UNSAT'}
for row in survey:
    record=read('data/'+row['name']+'.json')
    assert record['status']==row['status'] and record['directions']==row['dirs']
    expected_caps=[21]*5
    for j,v in zip(row['positions'],row['caps']):expected_caps[j-1]=v
    assert record['caps']==expected_caps
    if row['status']=='SAT':assert row['name']+'.json' in positive
    else:
        cover=next(c for c in coverage if c['row']==row['name']);basis=next(c for c in cases if c['number']==cover['basis']);start=cover['start'];L=len(basis['dirs'])
        assert canon(row['dirs'][start:start+L])==tuple(basis['dirs'])
        assert [start+j for j in basis['positions']]==row['positions']
        assert all(a<=b for a,b in zip(row['caps'],basis['caps']))
scout=read('data/next-pairs.json');assert len(scout)==104 and all(r['status']=='SAT' for r in scout)
assert sum(len(r['occurrences']) for r in scout)==330
cycle_source=read('data/analysis.json')['cycle'];covered=set()
for row in scout:
    assert row['name']+'.json' in positive
    record=read('data/'+row['name']+'.json');expected_caps=[21]*5
    for j,v in zip(row['positions'],row['caps']):expected_caps[j-1]=v
    assert record['directions']==row['dirs'] and record['caps']==expected_caps
    for phase,start in row['occurrences']:
        cr=cycle_source[phase]
        assert canon(cr['directions'][start:start+6])==tuple(row['dirs'])
        assert [cr['counts'][start+j-1] for j in row['positions']]==row['caps']
        covered.add((phase,start,*row['positions']))
assert covered=={(ph,st,a,b) for ph in range(11) for st in range(3) for a,b in itertools.combinations(range(1,6),2)}
comparison=read('data/context-comparison.json')
assert len(comparison)==331
for row in comparison:
    record=read('data/'+row['name']+'.json')
    assert record['status']==row['status'] and record['directions']==row['dirs']
    if row['status']=='SAT':assert row['name']+'.json' in positive
    expected_caps=[21]*(row['length']-1)
    for j,v in zip(row['positions'],row['caps']):expected_caps[j-1]=v
    assert record['caps']==expected_caps
    for phase,start in row['occurrences']:
        cr=cycle_source[phase]
        assert canon(cr['directions'][start:start+row['length']])==tuple(row['dirs'])
        assert [cr['counts'][start+j-1] for j in row['positions']]==row['caps']
assert read('data/next-three-fours-sum12.json')['status']=='UNKNOWN'
assert read('data/next-three-fours-sum11.json')['status']=='UNSAT'

meta=read('data/model.json');result=read('data/analysis.json')
g=np.load(HERE/'build/graph.npz');prior=np.load(ROOT/'milestones/48-low-count-compatibility/build/graph.npz')
for name,digest in meta['arrays_sha256'].items():assert sha(g[name].tobytes())==digest
extra=np.zeros(len(g['U']),dtype=bool)
# Reconstruct rule applications directly from every subsegment, without using saved rule lists.
for i,ds in enumerate(meta['extensions']):
    mask=g['direction']==i;codes=g['count_code'][mask];bad=np.zeros(len(codes),dtype=bool)
    for r in cases:
        L=len(r['dirs'])
        for start in range(9-L):
            for reverse in [False,True]:
                piece=ds[start:start+L]
                if canon(piece[::-1] if reverse else piece)!=tuple(r['dirs']):continue
                pos=[start+L-j if reverse else start+j for j in r['positions']]
                values=[codes//6**(7-j)%6+1 for j in pos]
                # All excluded values are below six; the capped symbol six cannot be mistaken for an exact count.
                if r['kind']=='sum':
                    violation=sum(values)<=r['cap']
                    assert all(np.all(v[violation]<6) for v in values)
                else:violation=(values[0]<=r['caps'][0])&(values[1]<=r['caps'][1])
                bad|=violation
    extra[mask]=bad
assert np.array_equal(g['excluded'],prior['excluded']|extra)
assert int((extra&~prior['excluded']).sum())==528610
for name in prior.files:
    if name!='excluded':assert np.array_equal(prior[name],g[name])
keep=~g['excluded'];U=g['U'][keep];V=g['V'][keep]
weights=168*g['count'][keep].astype(np.int64)+24*g['demand'][keep]+42*g['share'][keep]
encoded=gzip.decompress((HERE/'data/potential.i64.gz').read_bytes());pi=np.frombuffer(encoded,dtype='<i8')
mean=Fraction(result['integer_weight_mean']);p,q=mean.numerator,mean.denominator
assert sha(encoded)==result['potential_sha256'] and len(pi)==meta['states']
assert len(U)==3855773 and np.all(p+pi[V]<=q*weights+pi[U])
cycle=result['cycle'];shapes={tuple(s):i for i,s in enumerate(meta['direction_shapes'])}
for i,row in enumerate(cycle):
    d,c=row['directions'],row['counts'];u=shapes[canon(d[:7])]*6**6+encode(c[:6]);v=shapes[canon(d[1:])]*6**6+encode(c[1:])
    assert u==row['state'] and v==row['next_state']==cycle[(i+1)%len(cycle)]['state']
    indices=np.flatnonzero(keep&(g['U']==u)&(g['V']==v))
    assert any(meta['extensions'][int(g['direction'][j])]==d and int(g['count_code'][j])==encode(c) and int(g['demand'][j])==row['demand'] and int(g['share'][j])==row['share_event'] for j in indices)
    assert row['weight']==168*c[-1]+24*row['demand']+42*row['share_event']
assert Fraction(sum(r['weight'] for r in cycle),len(cycle))==mean
assert mean/168==Fraction(42,11)
# The stronger four-step sum also leaves this same attaining cycle available.
for row in cycle:
    for start in range(5):
        if canon(row['directions'][start:start+4])==(0,1,2,0):
            assert row['counts'][start]+row['counts'][start+2]>=5

out=dict(status='PASS',sharp_return_edges=146,sharp_return_counts=counts,sharp_return_start=witness['start'],survey_cases=360,survey_sat=310,survey_unsat=50,basis_cases=33,six_direction_shapes=9,next_cycle_pair_controls=104,lean_audits=len(audits),audited_theorems=audits,proofs=proofs,local_checks=len(controls['local_checks']),bank_paths=131,bank_occurrences=len(controls['bank_occurrences']),newly_excluded_graph_edges=528610,remaining_graph_edges=len(U),normalized_minimum_mean='42/11',sources_sha256=sources,scope='All 50 negative survey rows and a stronger four-step sum checked in Lean. All positive controls and the exact finite graph mean checked independently in Python. No improved global bound; complete Lean graph-to-snake bridge pending.')
(HERE/'data/verification.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k not in ['audited_theorems','sources_sha256']},indent=2))
