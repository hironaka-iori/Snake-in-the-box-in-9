"""Audit the four completed cases and the universal conditional bridges."""
import gzip,hashlib,json
from fractions import Fraction
from pathlib import Path
from certify import HERE,ROOT,TaggedEncoding,window
CASES=(0,1,14,22)
def read(p):return json.loads((HERE/p).read_text(encoding='utf-8'))
def raw(name):
 p=HERE/'certificates'/name
 return p.read_bytes() if p.exists() else gzip.decompress(p.with_name(p.name+'.gz').read_bytes())
def clauses(name):return [list(map(int,l.split()))[:-1] for l in raw(name).decode().splitlines() if l.strip() and not l.startswith(('p','c'))]
def audit(name,n):
 s=(HERE/f'logs/{name}.log').read_text(encoding='utf-8')
 assert s.count('depends on axioms:')==n,(name,n,s)
 assert all(x not in s for x in ('sorryAx','Lean.ofReduceBool','error:','failed to'))
 for line in s.splitlines():
  if 'depends on axioms:' in line:
   assert set(line.split('depends on axioms:')[1].strip().strip('[]').split(', ')) <= {'propext','Classical.choice','Quot.sound'}
 return n

def main():
 build=Path((HERE/'build/proofs-latest.txt').read_text().strip());records=[];audits=0;sources={}
 for name,n in [('FamilyCoverage',3),('ParityCoverage',2),('SnakeCoverage',3),('RunDensity',1),('SnakeRunDensity',1)]:
  audits+=audit('bridge-'+name,n);assert (build/f'{name}.olean').exists()
 for i in CASES:
  meta=read(f'data/four{i}.json');e=TaggedEncoding(window(meta['dirs']),meta['bounds'],radius=4)
  full=clauses(f'four{i}.full.cnf');assert full==e.clauses
  rename={int(k):v for k,v in meta['original_to_new'].items()}
  core=clauses(f'four{i}.cnf');assert core==[[(-1 if v<0 else 1)*rename[abs(v)] for v in full[j-1]] for j in meta['source_original_clause_ids']]
  assert 's VERIFIED' in (HERE/f'logs/four{i}-drat-check.txt').read_text()
  stats=read(f'logs/four{i}-export.txt');assert stats['simulated']
  audits+=audit(f'LocalWindowSat-FourRun{i}',0)+audit(f'RunWindow{i}',2)
  paths=[HERE/f'lean/LocalWindowCnf/FourRun{i}.lean',HERE/f'lean/LocalWindowSat/FourRun{i}.lean',HERE/f'lean/LocalWindowUnsat/FourRun{i}.lean',HERE/f'lean/RunWindow{i}.lean']+list((HERE/f'lean/LocalWindowUnsat/FourRun{i}').glob('*.lean'))
  for p in paths:
   rel=p.relative_to(HERE/'lean');o=build/rel.with_suffix('.olean');assert o.exists() and p.stat().st_mtime<=o.stat().st_mtime,(p,o)
   log=HERE/'logs'/(str(rel.with_suffix('')).replace('\\','-').replace('/','-')+'.log')
   assert log.exists() and not any(x in log.read_text(encoding='utf-8') for x in ('error:','sorryAx','failed to'))
   sources[str(p.relative_to(HERE)).replace('\\','/')]=hashlib.sha256(p.read_bytes().replace(b'\r\n',b'\n')).hexdigest()
  records.append(dict(case=i,clauses=len(core),hints=stats['hints']))
 for r in read('data/archives.json'):
  assert hashlib.sha256(raw(r['file'])).hexdigest()==r['sha256']
  assert hashlib.sha256((HERE/'certificates'/(r['file']+'.gz')).read_bytes()).hexdigest()==r['archive_sha256']
 for r in read('data/normalization-support.json'):
  p=HERE/'upstream'/Path(r['path']).name
  assert hashlib.sha256(p.read_bytes().replace(b'\r\n',b'\n')).hexdigest()==r['sha256_lf']
 graph=read('data/six-four-graph.json')
 for r in graph['runs']:
  cc=r['cycle'];assert all(e['next_state']==cc[(j+1)%len(cc)]['state'] for j,e in enumerate(cc))
  assert Fraction(sum(e['weight'] for e in cc),360*len(cc))==Fraction(r['mean'])
  if r['stage']=='after':assert all(not(e['state'][2]>=5 and e['alpha']==4) for e in cc)
 out=dict(status='PASSED',audited_theorems=audits,replayed_cases=records,remaining_cases=[i for i in range(34) if i not in CASES],sources_sha256_lf=sources,scope='Four geometric exclusions and universal conditional bridges are checked. Six-count-four theorem remains conditional on 30 further cases; no new global bound.')
 (HERE/'data/proof-verification.json').write_text(json.dumps(out,indent=2)+'\n');print(out['status'],audits,'audits;',len(records),'of 34 exclusions replayed')
 inventory=[]
 for i in range(34):
  stats=read(f'logs/four{i}-export.txt');inventory.append(dict(case=i,hints=stats['hints'],slots=stats['slots'],kernel_replayed=i in CASES))
 (HERE/'data/native-inventory.json').write_text(json.dumps(inventory,indent=2)+'\n')
if __name__=='__main__':main()
