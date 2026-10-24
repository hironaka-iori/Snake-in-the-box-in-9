"""Verify proof provenance, Lean audits, witnesses, and the all-edge graph result."""
from pathlib import Path
from fractions import Fraction
import gzip,hashlib,itertools,json,re,sys
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'milestones/29-overlapping-share-windows/scripts'))
from joint import TaggedEncoding,window
sys.path.insert(0,str(ROOT/'work/solver_packages'))
import numpy as np
def sha(b):return hashlib.sha256(b).hexdigest()
def read(p):return json.loads((HERE/p).read_text())
def raw(name):
    path=HERE/'certificates'/name
    return path.read_bytes() if path.exists() else gzip.decompress(path.with_name(path.name+'.gz').read_bytes())
def cnf(name):return [list(map(int,l.split()))[:-1] for l in raw(name).decode().splitlines() if l and not l.startswith(('c','p'))]
meta=read('data/sum441.json');ds=meta['dirs'];W=window(ds)
enc=TaggedEncoding(W,[(0,21)]*7,radius=4)
lits=[-enc.var[W[j]^(1<<a)^(1<<b)] for j in [2,6] for a,b in itertools.combinations(range(9),2) if a not in (ds[j-1],ds[j]) and b not in (ds[j-1],ds[j])]
enc.atmost(lits,6,('ends',))
assert meta['cycle_cuts']==[] and enc.clauses==cnf('sum441.full.cnf')
rename={int(k):v for k,v in meta['original_to_new'].items()}
core=[[(-1 if v<0 else 1)*rename[abs(v)] for v in enc.clauses[j-1]] for j in meta['source_original_clause_ids']]
assert core==cnf('sum441.cnf') and len(core)==1076
assert 's VERIFIED' in (HERE/'logs/sum441-drat-check.txt').read_text()
assert read('logs/sum441-export.txt')['hints']==34159
audits=[]
for name,number in [('LocalWindowSat-JointIntervening441',1),('SumWindow441',3),('WitnessSharp',5),('WitnessShort',5),('SharpConstant',2)]:
    log=(HERE/f'logs/{name}.log').read_text(encoding='utf-8')
    assert not any(x in log for x in ['sorryAx','error:','Lean.ofReduceBool'])
    rows=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",log,re.S)
    assert len(rows)==number,(name,rows)
    for theorem,axioms in rows:
        assert set(x.strip() for x in axioms.split(',')) <= {'propext','Classical.choice','Quot.sound'}
        audits.append(theorem)
build=Path((HERE/'build/latest.txt').read_text().strip());sources={}
for p in (HERE/'lean').rglob('*.lean'):
    relative=p.relative_to(HERE/'lean');o=build/relative.with_suffix('.olean')
    assert o.exists() and o.stat().st_mtime>=p.stat().st_mtime,relative
    sources[relative.as_posix()]=sha(p.read_bytes())
for receipt in ['logs/build-record.json','logs/witness-build-record.json']:
    for r in read(receipt)['records']:
        assert r['exit_code']==0 and sources[r['module']+'.lean']==r['source_sha256']
for r in read('data/archives.json'):
    assert sha(raw(r['file']))==r['sha256']
    assert sha((HERE/'certificates'/(r['file']+'.gz')).read_bytes())==r['archive_sha256']
controls=read('data/geometry-controls.json')
for r in controls['local_and_full_checks']:assert sha((HERE/'data'/r['file']).read_bytes())==r['sha256']
assert controls['bank_paths_checked']==131 and len(controls['bank_occurrences'])==6

# Saved graph verification does not invoke its optimizer.
gmeta=read('data/model.json');result=read('data/analysis.json')
g=np.load(HERE/'build/graph.npz');prior=np.load(ROOT/'milestones/42-six-count-state-model/build/graph.npz')
for name,digest in gmeta['arrays_sha256'].items():assert sha(g[name].tobytes())==digest
def canon(word):
    labels={};return tuple(labels.setdefault(x,len(labels)) for x in word)
def encode(word):
    n=0
    for x in word:n=6*n+x-1
    return n
extra=np.zeros(len(g['U']),dtype=bool)
for i,word in enumerate(gmeta['extensions']):
    if canon(word)==tuple(ds) or canon(word[::-1])==tuple(ds):
        mask=g['direction']==i;codes=g['count_code'][mask]
        extra[mask]=((codes//6**5)%6+1+(codes//6)%6+1<7)
assert np.array_equal(g['excluded'],prior['excluded']|extra)
assert int((extra&~prior['excluded']).sum())==9496
for name in prior.files:
    if name!='excluded':assert np.array_equal(prior[name],g[name])
keep=~g['excluded'];U=g['U'][keep];V=g['V'][keep]
weights=168*g['count'][keep].astype(np.int64)+24*g['demand'][keep]+42*g['share'][keep]
encoded=gzip.decompress((HERE/'data/potential.i64.gz').read_bytes());pi=np.frombuffer(encoded,dtype='<i8')
assert sha(encoded)==result['potential_sha256'] and len(pi)==gmeta['states']
assert len(U)==4551730 and np.all(7056+pi[V]<=11*weights+pi[U])
cycle=result['cycle'];shapes={tuple(s):i for i,s in enumerate(gmeta['direction_shapes'])}
for i,row in enumerate(cycle):
    d,c=row['directions'],row['counts']
    u=shapes[canon(d[:7])]*6**6+encode(c[:6]);v=shapes[canon(d[1:])]*6**6+encode(c[1:])
    assert u==row['state'] and v==row['next_state']==cycle[(i+1)%len(cycle)]['state']
    indices=np.flatnonzero(keep&(g['U']==u)&(g['V']==v))
    assert any(gmeta['extensions'][int(g['direction'][j])]==d and int(g['count_code'][j])==encode(c) and int(g['demand'][j])==row['demand'] and int(g['share'][j])==row['share_event'] for j in indices)
    assert row['weight']==168*c[-1]+24*row['demand']+42*row['share_event']
assert Fraction(sum(r['weight'] for r in cycle),168*len(cycle))==Fraction(42,11)
out=dict(status='PASS',lean_audits=len(audits),audited_theorems=audits,proof_clauses=len(core),proof_hints=34159,
    sharp_witness_edges=140,shorter_context_counterexample_edges=146,independent_geometry_checks=len(controls['local_and_full_checks']),
    bank_paths=131,bank_occurrences=6,newly_excluded_graph_edges=9496,remaining_graph_edges=len(U),normalized_minimum_mean='42/11',
    sources_sha256=sources,scope='Sharp universal pattern inequality and complete witnesses checked in Lean. Finite graph checked by integer arithmetic; no improved global bound and no complete Lean graph-to-snake bridge.')
(HERE/'data/verification.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k not in ['audited_theorems','sources_sha256']},indent=2))
