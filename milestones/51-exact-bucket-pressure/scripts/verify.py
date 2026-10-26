"""Audit the genuine share proof separately from unreplayed exploratory screens."""
from pathlib import Path
import gzip,hashlib,json,re,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'milestones/28-direct-share-certificates/scripts'))
from tagged_share import TaggedShare
def sha(b):return hashlib.sha256(b).hexdigest()
def read(p):return json.loads((HERE/p).read_text())
def raw(name):
 p=HERE/'certificates'/name
 return p.read_bytes() if p.exists() else gzip.decompress(p.with_name(p.name+'.gz').read_bytes())
def cnf(name):return [list(map(int,l.split()))[:-1] for l in raw(name).decode().splitlines() if l and not l.startswith(('p','c'))]
meta=read('data/share3_47.json');enc=TaggedShare(meta['directions'],meta['bounds'],47)
assert enc.clauses==cnf('share3_47.full.cnf') and enc.nv==meta['variables']
ids=[i-1 for i in meta['source_original_clause_ids']];core=[enc.clauses[i] for i in ids]
rename={int(k):v for k,v in meta['original_to_new'].items()}
compact=[[(-1 if v<0 else 1)*rename[abs(v)] for v in row] for row in core]
assert compact==cnf('share3_47.cnf')
used={abs(v) for row in core for v in row};needed=used|{abs(v) for ls,k,kind in enc.ctrs for v in ls}|{abs(v) for ls,kind in enc.tots for v in ls}
assert set(rename)==needed and len(used)==4196 and len(needed)==6525
source=(HERE/'lean/LocalWindowCnf/SharePressure513.lean').read_text();body=source.split('def raw : List (List Nat) := [',1)[1].split('def cnf',1)[0]
leanraw=[[int(v) for v in row.split(',') if v.strip()] for row in re.findall(r'\[([0-9, ]*)\]',body)]
assert leanraw==[[2*v if v>0 else -2*v+1 for v in row] for row in compact]
families={}
for i in ids:k=enc.tags[i][0];families[k]=families.get(k,0)+1
assert families==meta['families'] and families['shareCap']==1 and families['shareCl']>0
assert 's VERIFIED' in (HERE/'logs/share3_47-drat-check.txt').read_text()
export=read('logs/share3_47-export.txt');assert export['simulated'] and export['hints']==353479
for r in read('data/archives.json'):
 assert sha(raw(r['file']))==r['sha256'] and sha((HERE/'certificates'/(r['file']+'.gz')).read_bytes())==r['archive_sha256']
record=read('logs/build-record.json');build=Path((HERE/'build/latest.txt').read_text().strip());assert str(build)==record['build']
sources={p.relative_to(HERE/'lean').with_suffix('').as_posix():p for p in (HERE/'lean').rglob('*.lean')}
assert len(record['records'])==len(sources)
for r in record['records']:
 assert r['exit_code']==0 and r['source_sha256']==sha(sources[r['module']].read_bytes())
 assert (build/(r['module']+'.olean')).exists()
audits=[]
for module,count in [('JointChargeBudget',5),('WindowShareBudget',3),('ShareFrame',1),('LocalWindowSat-SharePressure513',1),('SharePressure',2),('ShareInSnake',2)]:
 log=(HERE/f'logs/{module}.log').read_text(encoding='utf-8')
 assert not any(x in log for x in ['error:','sorryAx','Lean.ofReduceBool'])
 rows=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",log,re.S)
 rows += [(n,'') for n in re.findall(r"'([^']+)' does not depend on any axioms",log)]
 assert len(rows)==count,(module,rows)
 for name,axs in rows:
  assert {a.strip() for a in axs.split(',') if a.strip()}<={'propext','Classical.choice','Quot.sound'}
  audits.append(name)
geometry=read('data/geometry-verification.json');assert geometry['status']=='PASS'
for row in geometry['controls']:assert sha((HERE/row['file']).read_bytes())==row['sha256']
assignment=read('data/assignment-controls.json');assert assignment['status']=='PASSED' and len(assignment['rows'])==4
assert assignment['rows'][0]['bank_index']=='local' and assignment['rows'][0]['only_expected_premise_failures']==1
out=dict(status='PASS',lean_modules=len(sources),lean_audits=len(audits),audited_theorems=audits,core_clauses=len(core),active_variables=len(used),semantic_variables=len(needed),hints=export['hints'],families=families,positive_controls=geometry['positive_controls'],assignment_clauses=182516,assignment_cases=4,checked_share_lower_bound=48,exploratory_share_lower_bound=96,exploratory_mean='35/9',source_hashes={n:sha(p.read_bytes()) for n,p in sources.items()},scope='Share at least48 is Lean checked for the specified genuine window, including arbitrary coordinate labels. Other exclusions and the share96 screen remain numerical premises. This round does not lower the global bound. The paper still records236; the separately reviewed contributor theorem proves235, without a full local rebuild.')
(HERE/'data/verification.json').write_text(json.dumps(out,indent=2)+'\n');print({k:v for k,v in out.items() if k not in ['source_hashes','audited_theorems']})
