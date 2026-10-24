"""Audit proof provenance, current Lean builds, and every retained graph edge."""
from pathlib import Path
from fractions import Fraction
import gzip,hashlib,itertools,json,re,sys
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'milestones/29-overlapping-share-windows/scripts'))
from joint import TaggedEncoding,window
sys.path.insert(0,str(ROOT/'work/solver_packages'));import numpy as np
def sha(b):return hashlib.sha256(b).hexdigest()
def read(p):return json.loads((HERE/p).read_text())
def raw(name):
    p=HERE/'certificates'/name
    return p.read_bytes() if p.exists() else gzip.decompress(p.with_name(p.name+'.gz').read_bytes())
def cnf(name):return [list(map(int,l.split()))[:-1] for l in raw(name).decode().splitlines() if l and not l.startswith(('c','p'))]
cases=read('data/cases.json');proofs=[]
for case in cases:
    n=case['number'];name=f'cycle{n}';meta=read(f'data/{name}.json')
    e=TaggedEncoding(window(case['dirs']),case['bounds'],radius=4)
    assert e.clauses==cnf(name+'.full.cnf')
    rename={int(k):v for k,v in meta['original_to_new'].items()}
    core=[[(-1 if v<0 else 1)*rename[abs(v)] for v in e.clauses[j-1]] for j in meta['source_original_clause_ids']]
    assert core==cnf(name+'.cnf')
    assert 's VERIFIED' in (HERE/f'logs/{name}-drat-check.txt').read_text()
    export=read(f'logs/{name}-export.txt');assert export['simulated']
    proofs.append(dict(case=n,clauses=len(core),active_variables=meta['active_variables'],derived_clauses=export['lemmas'],hints=export['hints']))
audits=[]
for name,expected in [(f'CycleExclusion{n}',2) for n in [471,472,473]]+[('SingletonPatterns',6)]:
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
for r in read('logs/build-record.json')['records']:
    assert r['exit_code']==0 and sources[r['module']+'.lean']==r['source_sha256']
for r in read('data/archives.json'):
    assert sha(raw(r['file']))==r['sha256']
    assert sha((HERE/'certificates'/(r['file']+'.gz')).read_bytes())==r['archive_sha256']
controls=read('data/geometry-controls.json')
for r in controls['local_checks']:assert sha((HERE/'data'/r['file']).read_bytes())==r['sha256']
assert controls['bank_paths_checked']==131

def canon(ds):
    labels={};return tuple(labels.setdefault(d,len(labels)) for d in ds)
def encode(ds):
    n=0
    for x in ds:n=6*n+x-1
    return n
gmeta=read('data/model.json');result=read('data/analysis.json')
g=np.load(HERE/'build/graph.npz');prior=np.load(ROOT/'milestones/44-critical-window-generalization/build/graph.npz')
for name,digest in gmeta['arrays_sha256'].items():assert sha(g[name].tobytes())==digest
extra=np.zeros(len(g['U']),dtype=bool)
for i,ds in enumerate(gmeta['extensions']):
    positions=set()
    for r in cases:
        L=len(r['dirs']);j=r['position']
        for start in range(9-L):
            piece=ds[start:start+L]
            if canon(piece)==tuple(r['dirs']):positions.add(start+j)
            if canon(piece[::-1])==tuple(r['dirs']):positions.add(start+L-j)
    if not positions:continue
    mask=g['direction']==i;codes=g['count_code'][mask];bad=np.zeros(len(codes),dtype=bool)
    for j in positions:bad|=((codes//6**(7-j))%6==0)
    extra[mask]=bad
assert np.array_equal(g['excluded'],prior['excluded']|extra)
assert int((extra&~prior['excluded']).sum())==57837
for name in prior.files:
    if name!='excluded':assert np.array_equal(prior[name],g[name])
keep=~g['excluded'];U=g['U'][keep];V=g['V'][keep]
weights=168*g['count'][keep].astype(np.int64)+24*g['demand'][keep]+42*g['share'][keep]
encoded=gzip.decompress((HERE/'data/potential.i64.gz').read_bytes());pi=np.frombuffer(encoded,dtype='<i8')
assert sha(encoded)==result['potential_sha256'] and len(pi)==gmeta['states']
assert len(U)==4493893 and np.all(7056+pi[V]<=11*weights+pi[U])
cycle=result['cycle'];shapes={tuple(s):i for i,s in enumerate(gmeta['direction_shapes'])}
for i,row in enumerate(cycle):
    d,c=row['directions'],row['counts'];u=shapes[canon(d[:7])]*6**6+encode(c[:6]);v=shapes[canon(d[1:])]*6**6+encode(c[1:])
    assert u==row['state'] and v==row['next_state']==cycle[(i+1)%len(cycle)]['state']
    indices=np.flatnonzero(keep&(g['U']==u)&(g['V']==v))
    assert any(gmeta['extensions'][int(g['direction'][j])]==d and int(g['count_code'][j])==encode(c) and int(g['demand'][j])==row['demand'] and int(g['share'][j])==row['share_event'] for j in indices)
    assert row['weight']==168*c[-1]+24*row['demand']+42*row['share_event']
assert Fraction(sum(r['weight'] for r in cycle),168*len(cycle))==Fraction(42,11)
assert min(min(r['counts']) for r in cycle)==2
out=dict(status='PASS',lean_audits=len(audits),audited_theorems=audits,proofs=proofs,local_checks=len(controls['local_checks']),bank_paths=131,
    bank_occurrences=len(controls['bank_occurrences']),newly_excluded_graph_edges=57837,remaining_graph_edges=len(U),normalized_minimum_mean='42/11',
    new_cycle_has_no_count_one=True,sources_sha256=sources,scope='Three arbitrary-coordinate singleton exclusions checked in Lean. Exact finite graph mean independently checked; no improved global bound or complete Lean graph-to-snake bridge.')
(HERE/'data/verification.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k not in ['audited_theorems','sources_sha256']},indent=2))
