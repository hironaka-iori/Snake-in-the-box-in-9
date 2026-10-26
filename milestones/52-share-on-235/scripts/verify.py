"""Audit the native/Lean certificate, positive controls and complete finite potentials."""
from pathlib import Path
from fractions import Fraction
import collections,gzip,hashlib,json,re,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'milestones/28-direct-share-certificates/scripts'))
from tagged_share import TaggedShare
from geometry_helpers import forest,shares,np
def read(p):return json.loads((HERE/p).read_text())
def sha(b):return hashlib.sha256(b).hexdigest()
def canon(ds):
 names={};return tuple(names.setdefault(d,len(names)) for d in ds)
def code(cs):
 v=0
 for c in cs:v=6*v+c-1
 return v
def raw(name):
 p=HERE/'certificates'/name
 return p.read_bytes() if p.exists() else gzip.decompress(p.with_name(p.name+'.gz').read_bytes())
def cnf(name):return [list(map(int,l.split()))[:-1] for l in raw(name).decode().splitlines() if l and not l.startswith(('p','c'))]
meta=read('data/supported0_95.json');enc=TaggedShare(meta['directions'],meta['bounds'],95)
assert enc.clauses==cnf('supported0_95.full.cnf') and enc.nv==meta['variables']
ids=[i-1 for i in meta['source_original_clause_ids']];core=[enc.clauses[i] for i in ids];rename={int(k):v for k,v in meta['original_to_new'].items()}
compact=[[(-1 if v<0 else 1)*rename[abs(v)] for v in row] for row in core]
assert compact==cnf('supported0_95.cnf')
used={abs(v) for row in core for v in row};needed=used|{abs(v) for ls,k,kind in enc.ctrs for v in ls}|{abs(v) for ls,kind in enc.tots for v in ls}
assert set(rename)==needed and len(used)==5191
source=(HERE/'lean/LocalWindowCnf/SharePressure520.lean').read_text();body=source.split('def raw : List (List Nat) := [',1)[1].split('def cnf',1)[0]
leanraw=[[int(v) for v in row.split(',') if v.strip()] for row in re.findall(r'\[([0-9, ]*)\]',body)]
assert leanraw==[[2*v if v>0 else -2*v+1 for v in row] for row in compact]
assert dict(collections.Counter(enc.tags[i][0] for i in ids))==meta['families']
assert meta['families']['shareCap']==1 and meta['families']['shareCl']>0
assert 's VERIFIED' in (HERE/'logs/supported0_95-drat-check.txt').read_text()
export=read('logs/supported0_95-export.txt');assert export['simulated'] and export['hints']==382890
for r in read('data/archives.json'):
 assert sha(raw(r['file']))==r['sha256'] and sha((HERE/'certificates'/(r['file']+'.gz')).read_bytes())==r['archive_sha256']
controls=[]
for row in read('data/supported-critical-windows.json'):
 c=row['controls'][0];path=ROOT/c['file'];assert sha(path.read_bytes())==c['sha256'];r=json.loads(path.read_text())
 ds=r.get('directions',r.get('dirs'));W=[0]
 for d in ds:W.append(W[-1]^(1<<d))
 S=set(r['selected']);counts=forest(S,W);ss=shares(S,W[1:-1])
 assert counts==r['census']['alpha'] and ss==r['census']['share'] and sum(ss)==c['total_share']
 k=min((canon(ds),tuple(min(a,6) for a in counts)),(canon(ds[::-1]),tuple(min(a,6) for a in counts[::-1])))
 assert k==(tuple(row['directions']),tuple(row['counts']))
 controls.append(c)
assignment=read('data/assignment-controls.json');assert assignment['status']=='PASSED' and len(assignment['rows'])==4
assert assignment['rows'][0]['only_expected_premise_failures']==1
models=[]
for name in ['checked-share','exploratory-share','cycle-share','combined-share']:
 folder=HERE/name;md=json.loads((folder/'data/model.json').read_text());r=json.loads((folder/'data/analysis.json').read_text())
 with np.load(folder/'build/graph.npz') as z:a={k:z[k] for k in z.files}
 for k,digest in md['arrays_sha256'].items():assert sha(a[k].tobytes())==digest
 keep=~a['excluded'];U=a['U'][keep];V=a['V'][keep]
 weights=336*a['count'][keep].astype(np.int64)+48*a['demand'][keep]+42*a['share'][keep]+a['share_lower'][keep]
 mean=Fraction(r['integer_weight_mean']);p,q=mean.numerator,mean.denominator
 encoded=gzip.decompress((folder/'data/potential.i64.gz').read_bytes());potential=np.frombuffer(encoded,dtype='<i8')
 assert sha(encoded)==r['potential_sha256'] and np.all(p+potential[V]<=q*weights+potential[U])
 shapes={tuple(s):i for i,s in enumerate(md['direction_shapes'])};cycle=r['cycle']
 for j,row in enumerate(cycle):
  ds,cs=row['directions'],row['counts'];u=shapes[canon(ds[:7])]*6**6+code(cs[:6]);v=shapes[canon(ds[1:])]*6**6+code(cs[1:])
  assert u==row['state'] and v==row['next_state']==cycle[(j+1)%len(cycle)]['state']
  matches=np.flatnonzero(keep&(a['U']==u)&(a['V']==v)&(a['count_code']==code(cs)))
  assert any(md['extensions'][int(a['direction'][i])]==ds and int(a['demand'][i])==row['demand'] and int(a['share'][i])==row['share_event'] and int(a['share_lower'][i])==row['share_lower'] for i in matches)
  assert row['weight']==336*cs[-1]+48*row['demand']+42*row['share_event']+row['share_lower']
 assert Fraction(sum(row['weight'] for row in cycle),len(cycle))==mean and mean/336==4
 models.append(dict(name=name,edges=len(U),mean='4',potential_loss=str(Fraction(r['potential_range'],q)),cycle_length=len(cycle)))
finite=dict(status='PASS',positive_controls=len(controls),control_files=controls,assignment_cases=4,assignment_clauses=445111,models=models,scope='Native certificate, independent positive controls and finite potentials checked. This receipt does not claim the pending Lean geometric theorem.')
(HERE/'data/finite-verification.json').write_text(json.dumps(finite,indent=2)+'\n')
if '--finite-only' in sys.argv:
 print({k:v for k,v in finite.items() if k!='control_files'});sys.exit(0)
record=read('logs/build-record.json');build=Path((HERE/'build/latest.txt').read_text().strip());assert str(build)==record['build']
sources={p.relative_to(HERE/'lean').with_suffix('').as_posix():p for p in (HERE/'lean').rglob('*.lean')}
assert len(record['records'])==len(sources)
for r in record['records']:
 assert r['exit_code']==0 and r['source_sha256']==sha(sources[r['module']].read_bytes())
 assert (build/(r['module']+'.olean')).exists()
audits=[]
for module,count in [('RetainedEmpty235',7),('LocalWindowSat-SharePressure520',1),('SharePressure',2),('ShareInSnake',2)]:
 log=(HERE/f'logs/{module}.log').read_text(encoding='utf-8')
 assert not any(x in log for x in ['error:','sorryAx','Lean.ofReduceBool'])
 rows=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",log,re.S)
 rows += [(n,'') for n in re.findall(r"'([^']+)' does not depend on any axioms",log)]
 assert len(rows)==count,(module,rows)
 for name,axs in rows:
  assert {a.strip() for a in axs.split(',') if a.strip()}<={'propext','Classical.choice','Quot.sound'}
  audits.append(name)
out=dict(status='PASS',lean_modules=len(sources),lean_audits=len(audits),audited_theorems=audits,core_clauses=len(core),active_variables=len(used),semantic_variables=len(needed),hints=export['hints'],positive_controls=len(controls),control_files=controls,assignment_cases=4,assignment_clauses=445111,models=models,checked_share=96,source_hashes={n:sha(p.read_bytes()) for n,p in sources.items()},scope='Local share96 and conditional empty-square arithmetic checked in Lean. Four finite-model means checked independently. No new global bound; contributor235 remains the baseline.')
(HERE/'data/verification.json').write_text(json.dumps(out,indent=2)+'\n');print({k:v for k,v in out.items() if k not in ['source_hashes','control_files','audited_theorems']})
