"""Proof provenance, geometric controls, audit receipts, and conditional charge accounting."""
from pathlib import Path
import gzip,hashlib,importlib.util,json,re,sys
from certify import ROOT,HERE,DIRS,BOUNDS,TaggedEncoding,window,joint_literals
sys.path.insert(0,str(ROOT/'milestones/40-intervening-counts/scripts'))
spec=importlib.util.spec_from_file_location('local_controls',ROOT/'milestones/40-intervening-counts/scripts/verify.py')
controls=importlib.util.module_from_spec(spec);spec.loader.exec_module(controls)
def read(p):return json.loads((HERE/p).read_text())
def raw(name):
 p=HERE/'certificates'/name
 return p.read_bytes() if p.exists() else gzip.decompress(p.with_name(p.name+'.gz').read_bytes())
def cnf(name):return [list(map(int,l.split()))[:-1] for l in raw(name).decode().splitlines() if l and not l.startswith(('c','p'))]
def main():
 d=read('data/sum411.json');assert d['dirs']==DIRS and d['bounds']==[list(x) for x in BOUNDS] and d['positions']==[3,6] and d['joint_cap']==11
 e=TaggedEncoding(window(DIRS),d['bounds'],radius=4);lits=joint_literals(e,window(DIRS),d['positions'])
 assert len(lits)==42
 e.atmost(lits,11,('ends',));base=len(e.clauses)
 for c in d['cycle_cuts']:
  controls.cycle(c);assert set(c)<=e.B;e.add([-e.var[v] for v in c],('cut',))
 assert e.clauses==cnf('sum411.full.cnf')
 ren={int(k):v for k,v in d['original_to_new'].items()}
 core=[[(-1 if x<0 else 1)*ren[abs(x)] for x in e.clauses[j-1]] for j in d['source_original_clause_ids']]
 assert core==cnf('sum411.cnf')
 inv={i:v for v,i in e.var.items()};retained_cycles=0
 for j in d['source_original_clause_ids']:
  if e.tags[j-1][0]=='cut':controls.cycle([inv[-x] for x in e.clauses[j-1]]);retained_cycles+=1
 assert 's VERIFIED' in (HERE/'logs/sum411-drat-check.txt').read_text()
 stats=read('logs/sum411-export.txt');assert stats['simulated'] and stats['hints']==5222602
 audits=0
 for name,count in [('MultiCentreCount',1),('LocalWindowSat-JointIntervening411',1),('SumWindow411',3),('JointExcess',4),('SumExcess',1)]:
  log=(HERE/f'logs/{name}.log').read_text(encoding='utf-8')
  assert log.count('depends on axioms:')==count
  assert not any(x in log for x in ['sorryAx','error:','Lean.ofReduceBool'])
  dependencies=re.findall(r'depends on axioms:\s*\[([^]]*)\]',log,re.S)
  assert len(dependencies)==count
  for entry in dependencies:assert {x.strip() for x in entry.split(',')}<={'propext','Classical.choice','Quot.sound'}
  audits+=count
 records=read('logs/build-record.json')['records'];assert len(records)==208 and len({r['module'] for r in records})==208 and all(r['exit_code']==0 for r in records)
 positive_path=ROOT/'milestones/40-intervening-counts/data/two-middle-sum-12.json'
 positive=controls.witness(json.loads(positive_path.read_text()))
 assert positive['alpha'][0]<=3 and positive['alpha'][-1]<=3 and positive['alpha'][2]+positive['alpha'][5]==12
 bank=read('data/bank-controls.json');assert bank['verified_paths']==131 and bank['qualifying_occurrences']==0 and len(bank['occurrences'])==1442
 assert bank['bank_sha256']==hashlib.sha256((ROOT/'work/bank9.json').read_bytes()).hexdigest()
 build=Path((HERE/'build/latest.txt').read_text().strip());source_hashes={}
 for p in (HERE/'lean').rglob('*.lean'):
  o=build/p.relative_to(HERE/'lean').with_suffix('.olean');assert o.exists() and o.stat().st_mtime>=p.stat().st_mtime,p
  source_hashes[p.relative_to(HERE).as_posix()]=hashlib.sha256(p.read_bytes().replace(b'\r\n',b'\n')).hexdigest()
 for r in read('data/archives.json'):
  assert hashlib.sha256(raw(r['file'])).hexdigest()==r['sha256']
  assert hashlib.sha256((HERE/'certificates'/(r['file']+'.gz')).read_bytes()).hexdigest()==r['archive_sha256']
 out=dict(status='PASSED',audited_theorems=audits,clauses=len(core),variables=d['active_variables'],lrat_hints=stats['hints'],replay_check_modules=stats['check_modules'],successful_build_modules=len(records),supplied_additional_cycle_cuts=len(d['cycle_cuts']),retained_additional_cycle_cuts=sum(j>base for j in d['source_original_clause_ids']),retained_cycle_clauses=retained_cycles,positive_local_forest=positive,positive_source_sha256=hashlib.sha256(positive_path.read_bytes()).hexdigest(),bank_pattern_occurrences=1442,bank_qualifying_occurrences=0,sources_sha256_lf=source_hashes,scope='Universal conditional joint-sum theorem and its conditional overlap accounting. Local attainment does not establish full-snake sharpness or a frequency theorem. Global interval unchanged.')
 (HERE/'data/verification.json').write_text(json.dumps(out,indent=2)+'\n')
 print('PASSED',audits,'audits;',len(core),'clauses;',stats['hints'],'hints; local sum12 attained; zero qualifying bank occurrences.')
if __name__=='__main__':main()
