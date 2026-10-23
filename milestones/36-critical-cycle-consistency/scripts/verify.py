"""Verify core provenance, Lean receipts, coarse-symbol handling and saved cycles."""
import gzip,hashlib,itertools,json
from fractions import Fraction
from pathlib import Path
from screen import TaggedEncoding,window,canonical
from cycle_graph import WORDS,PATTERNS,progress,step
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
def read(n):return json.loads((HERE/n).read_text(encoding='utf-8'))
def sha(p):return hashlib.sha256(p.read_bytes().replace(b'\r\n',b'\n')).hexdigest()
def raw(n):
 p=HERE/'certificates'/n
 return p.read_bytes() if p.exists() else gzip.decompress(p.with_name(p.name+'.gz').read_bytes())
def cnf(n):return [list(map(int,l.split()))[:-1] for l in raw(n).decode().splitlines() if l and not l.startswith(('c','p'))]
def main():
 source=ROOT/'milestones/33-distance-three-singletons/data/pair-graph.json'
 screens={}
 for prefix,n in [('',6),('lower-',29)]:
  rows=read(f'data/{prefix}candidates.json');assert rows['source_sha256_lf']==sha(source)
  saved=next(r for r in json.loads(source.read_text())['runs'] if r['stage']=='pair' and r['table']==('lower' if prefix else 'witness'))
  cc=saved['cycle'];assert len(cc)==n
  statuses=[]
  for j,c in enumerate(rows['cases']):
   assert c['dirs']==list(canonical(cc[j]['directions']))
   assert c['counts']==[cc[(j-k)%n]['alpha'] for k in range(6,-1,-1)]
   r=read(f'data/{prefix}screen-{j}.json');assert r['dirs']==c['dirs'] and r['counts']==c['counts']
   assert r['selected'] is None and r['status'] in ('UNSAT','UNKNOWN')
   statuses.append(r['status'])
  screens[prefix or 'witness']={s:statuses.count(s) for s in set(statuses)}
 assert screens['witness']=={'UNSAT':6} and screens['lower-']=={'UNSAT':28,'UNKNOWN':1}
 audits=0;proofs=[]
 for idx,wrapper in [(3,'CriticalPattern'),(100,'CriticalLower')]:
  m=read(f'data/cycle{idx}.json');e=TaggedEncoding(window(m['dirs']),m['bounds'],radius=4)
  assert e.clauses==cnf(f'cycle{idx}.full.cnf')
  rename={int(k):v for k,v in m['original_to_new'].items()}
  core=[[(-1 if x<0 else 1)*rename[abs(x)] for x in e.clauses[i-1]] for i in m['source_original_clause_ids']]
  assert core==cnf(f'cycle{idx}.cnf')
  assert 's VERIFIED' in (HERE/f'logs/cycle{idx}-drat-check.txt').read_text()
  stats=read(f'logs/cycle{idx}-export.txt');assert stats['simulated']
  for log,count in [(f'CycleExclusion{idx}',2),(f'check-{wrapper}',1)]:
   s=(HERE/f'logs/{log}.log').read_text();assert s.count('depends on axioms:')==count
   assert all(x not in s for x in ('sorryAx','error:','Lean.ofReduceBool','failed to'))
   for line in s.splitlines():
    if 'depends on axioms:' in line:assert set(line.split('depends on axioms:')[1].strip().strip('[]').split(', '))<={'propext','Classical.choice','Quot.sound'}
   audits+=count
  proofs.append(dict(case=idx,clauses=len(core),variables=m['active_variables'],hints=stats['hints']))
 graph=read('data/cycle-graph.json');assert graph['script_sha256_lf']==sha(HERE/'scripts/cycle_graph.py')
 transitions=0
 for hist in itertools.product(range(1,7),repeat=7):
  k,hits=step(progress(hist[:-1]),hist[-1])
  assert k==progress(hist) and hits==[hist==w for w in WORDS];transitions+=1
 cycle_summary=[]
 for r in graph['runs']:
  cc=r['cycle'];n=len(cc);aa=[e['alpha'] for e in cc]
  assert Fraction(sum(e['weight'] for e in cc),360*n)==Fraction(r['mean'])
  for j,e in enumerate(cc):
   c,a,run,pr,h,k=e['state'];assert e['next_state']==cc[(j+1)%n]['state']
   assert a==[aa[(j-t)%n] for t in (4,3,2,1)]
   hist=[aa[(j-t)%n] for t in range(6,0,-1)];assert tuple(k)==progress(hist)
   nk,hits=step(tuple(k),e['alpha']);assert list(nk)==e['next_state'][-1]
   if r['stage']=='after':assert not any(hit and canonical(e['directions'])==p for hit,p in zip(hits,PATTERNS))
  cycle_summary.append(dict(stage=r['stage'],table=r['table'],mean=r['mean'],period=n))
 build=Path((HERE/'build/latest.txt').read_text().strip());sources={}
 for p in (HERE/'lean').rglob('*.lean'):
  o=build/p.relative_to(HERE/'lean').with_suffix('.olean');assert o.exists() and p.stat().st_mtime<=o.stat().st_mtime,(p,o)
  sources[p.relative_to(HERE).as_posix()]=sha(p)
 for r in read('data/archives.json'):
  assert hashlib.sha256(raw(r['file'])).hexdigest()==r['sha256']
  assert hashlib.sha256((HERE/'certificates'/(r['file']+'.gz')).read_bytes()).hexdigest()==r['archive_sha256']
 out=dict(status='PASSED',audited_theorems=audits,proofs=proofs,screens=screens,history_transitions=transitions,cycles=cycle_summary,sources_sha256_lf=sources,scope='Two local exclusions for arbitrary distinct coordinate labels. Other screens are numerical; saved means do not prove a global minimum or a new snake bound.')
 (HERE/'data/verification.json').write_text(json.dumps(out,indent=2)+'\n');print('PASSED',audits,'audits;',transitions,'history updates;',proofs)
if __name__=='__main__':main()
