"""Audit native proofs, Lean receipts, explicit geometry, and finite potentials."""
from pathlib import Path
from fractions import Fraction
import gzip,hashlib,itertools,json,re,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
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
case=read('data/cases.json')[0];meta=read('data/sum501.json');W=window(case['dirs']);e=TaggedEncoding(W,case['bounds'],radius=4)
lits=[-e.var[W[j]^(1<<a)^(1<<b)] for j in case['positions'] for a,b in itertools.combinations(range(9),2) if a not in (case['dirs'][j-1],case['dirs'][j]) and b not in (case['dirs'][j-1],case['dirs'][j])]
e.atmost(lits,case['cap'],('ends',))
for cc in meta['cycle_cuts']:
 assert gen.is_cycle_set(cc) and set(cc)<=e.B
 e.add([-e.var[v] for v in cc],('cut',))
assert e.clauses==cnf('sum501.full.cnf')
rename={int(k):v for k,v in meta['original_to_new'].items()}
core=[[(-1 if v<0 else 1)*rename[abs(v)] for v in e.clauses[j-1]] for j in meta['source_original_clause_ids']]
assert core==cnf('sum501.cnf')
assert 's VERIFIED' in (HERE/'logs/sum501-drat-check.txt').read_text()
export=read('logs/sum501-export.txt');assert export['simulated']
audits=[]
for name,expected in [('LocalWindowSat-JointIntervening501',1),('SumWindow501',3),('TripleWitness',6),('TripleDemand',10),('RangeTargets',4)]:
 log=(HERE/f'logs/{name}.log').read_text(encoding='utf-8')
 assert not any(x in log for x in ['sorryAx','error:','Lean.ofReduceBool'])
 rows=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",log,re.S)
 rows += [(name,'') for name in re.findall(r"'([^']+)' does not depend on any axioms",log)]
 assert len(rows)==expected,(name,rows)
 for theorem,axioms in rows:
  assert set(x.strip() for x in axioms.split(',') if x.strip())<={'propext','Classical.choice','Quot.sound'}
  audits.append(theorem)
build=Path((HERE/'build/latest.txt').read_text().strip());sources={}
for p in (HERE/'lean').rglob('*.lean'):
 relative=p.relative_to(HERE/'lean');o=build/relative.with_suffix('.olean')
 assert o.exists() and o.stat().st_mtime>=p.stat().st_mtime,relative
 sources[relative.as_posix()]=sha(p.read_bytes())
records=read('logs/build-record.json')['records'];assert len(records)==len(sources)
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
def encode(cs):
 v=0
 for c in cs:v=6*v+c-1
 return v
witness=read('data/witness.json');vs=witness['vertex_sequence'];S=set(vs)
assert len(vs)==len(S)==144 and all(0<=v<512 for v in vs)
assert all(((vs[i]^vs[j]).bit_count()==1)==(j==i+1) for i in range(len(vs)) for j in range(i+1,len(vs)))
r=witness['start'];directions=[(a^b).bit_length()-1 for a,b in zip(vs,vs[1:])]
assert directions[r:r+6]==[0,1,2,3,4,0]
counts=[sum(not({vs[r+j]^(1<<a),vs[r+j]^(1<<b),vs[r+j]^(1<<a)^(1<<b)}&S) for a,b in itertools.combinations(range(9),2)) for j in [1,4,5]]
assert counts==witness['counts']==[3,5,5] and sum(counts)==13
assert vs==read('data/full-triple-thirteen.json')['vertex_sequence']

meta=read('data/model.json');result=read('data/analysis.json')
with np.load(HERE/'build/graph.npz') as z:g={k:z[k] for k in z.files}
with np.load(ROOT/'milestones/49-six-direction-pair-catalogue/build/graph.npz') as z:prior={k:z[k] for k in z.files}
for name,digest in meta['arrays_sha256'].items():assert sha(g[name].tobytes())==digest
extra=np.zeros(len(g['U']),dtype=bool);demand=prior['demand'].copy()
for i,ds in enumerate(meta['extensions']):
 mask=g['direction']==i;codes=g['count_code'][mask];bad=np.zeros(len(codes),dtype=bool);req=demand[mask].copy()
 for start in range(3):
  for rev in [False,True]:
   word=ds[start:start+6]
   if canon(word[::-1] if rev else word)!=(0,1,2,3,4,0):continue
   positions=[start+6-j if rev else start+j for j in [1,4,5]]
   values=[codes//6**(7-j)%6+1 for j in positions]
   exact=np.logical_and.reduce([v<6 for v in values]);deficit=np.maximum(0,13-sum(values))
   bad|=exact&(deficit>0);req=np.maximum(req,np.where(exact,0,deficit))
 extra[mask]=bad;demand[mask]=req
assert np.array_equal(g['excluded'],prior['excluded']|extra)
assert np.array_equal(g['demand'],demand)
assert int((extra&~prior['excluded']).sum())==430797
assert int(((demand>prior['demand'])&~g['excluded']).sum())==148609
for name in prior:
 if name not in ['excluded','demand']:assert np.array_equal(prior[name],g[name])

def check_potential(folder,arrays,metadata):
 result=json.loads((folder/'data/analysis.json').read_text());keep=~arrays['excluded'];U=arrays['U'][keep];V=arrays['V'][keep]
 weights=168*arrays['count'][keep].astype(np.int64)+24*arrays['demand'][keep]+42*arrays['share'][keep]
 encoded=gzip.decompress((folder/'data/potential.i64.gz').read_bytes());pi=np.frombuffer(encoded,dtype='<i8')
 mean=Fraction(result['integer_weight_mean']);p,q=mean.numerator,mean.denominator
 assert sha(encoded)==result['potential_sha256'] and len(pi)==metadata['states']
 assert np.all(p+pi[V]<=q*weights+pi[U])
 cycle=result['cycle'];shapes={tuple(s):i for i,s in enumerate(metadata['direction_shapes'])}
 for i,row in enumerate(cycle):
  d,c=row['directions'],row['counts'];u=shapes[canon(d[:7])]*6**6+encode(c[:6]);v=shapes[canon(d[1:])]*6**6+encode(c[1:])
  assert u==row['state'] and v==row['next_state']==cycle[(i+1)%len(cycle)]['state']
  indices=np.flatnonzero(keep&(arrays['U']==u)&(arrays['V']==v))
  assert any(metadata['extensions'][int(arrays['direction'][j])]==d and int(arrays['count_code'][j])==encode(c) and int(arrays['demand'][j])==row['demand'] and int(arrays['share'][j])==row['share_event'] for j in indices)
  assert row['weight']==168*c[-1]+24*row['demand']+42*row['share_event']
 assert Fraction(sum(r['weight'] for r in cycle),len(cycle))==mean
 return result
check_potential(HERE,g,meta)
survey=read('data/critical-survey.json');family=read('data/critical-family.json')
assert len(survey)==len(family['windows'])==381
positive={r['file'] for r in controls['local_checks']}
for row,window in zip(survey,family['windows']):
 rec=read('data/critical-survey/'+row['name']+'.json')
 assert row['directions']==window['directions'] and row['counts']==window['counts']
 assert row['caps']==[21 if x==6 else x for x in row['counts']]
 assert row['status']==rec['status']
 if row['status']=='SAT':assert 'critical-survey/'+row['name']+'.json' in positive
for name in ['empty18-at-237','empty18-universal']:assert read('data/'+name+'.json')['status']=='UNKNOWN'
exploratory=[]
for folder in ['screen','excess-screen']:
 path=HERE/folder;gm=json.loads((path/'data/model.json').read_text())
 with np.load(path/'build/graph.npz') as z:ga={k:z[k] for k in z.files}
 for name,digest in gm['arrays_sha256'].items():assert sha(ga[name].tobytes())==digest
 gr=check_potential(path,ga,gm)
 exploratory.append(dict(model=folder,mean=gr['normalized_charge_mean'],remaining_edges=gr['edges'],potential_range=gr['potential_range']))
assert exploratory[0]['mean']=='42/11' and exploratory[1]['mean']=='23/6'
cover=read('data/pressure-cover.json');assert cover['selected_count']==160 and cover['violating_edges']==72306
for row in read('data/excess-survey.json'):
 rec=read('data/excess-survey/'+row['name']+'.json')
 assert rec['status']==row['status'] and rec['directions']==row['directions']
 assert rec['joint']==[row['positions'],6*len(row['positions'])+row['excess_cap']]
 if row['status']=='SAT':assert 'excess-survey/'+row['name']+'.json' in positive
out=dict(status='PASS',lean_audits=len(audits),audited_theorems=audits,lean_modules=len(records),sharp_triple_edges=143,sharp_triple_counts=counts,proof_hints=export['hints'],local_checks=len(positive),bank_paths=131,bank_occurrences=len(controls['bank_occurrences']),newly_excluded_graph_edges=430797,strengthened_demands=148609,remaining_graph_edges=int((~g['excluded']).sum()),normalized_minimum_mean=result['normalized_charge_mean'],sources_sha256=sources,scope='The triple inequality, sharpness, and common-budget arithmetic are Lean checked. Critical-family solver exclusions remain exploratory. No improved global bound; graph-to-snake bridge pending.')
out.update(exploratory_models=exploratory,selected_next_certificates=160)
(HERE/'data/verification.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k not in ['audited_theorems','sources_sha256']},indent=2))
