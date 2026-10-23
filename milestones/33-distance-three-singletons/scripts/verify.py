"""Check certificate provenance, transitive axiom audits and graph receipts."""
import gzip,hashlib,json
from fractions import Fraction
from pathlib import Path
from certify import HERE,ROOT,TaggedEncoding,window,joint_literals,BOUNDS

def read(s):return json.loads((HERE/s).read_text(encoding='utf-8'))
def raw(n):
 p=HERE/'certificates'/n
 return p.read_bytes() if p.exists() else gzip.decompress(p.with_name(p.name+'.gz').read_bytes())
def clauses(n):return [list(map(int,l.split()))[:-1] for l in raw(n).decode().splitlines() if l.strip() and not l.startswith(('p','c'))]
def audit(name,n):
 log=(HERE/f'logs/{name}.log').read_text(encoding='utf-8')
 assert log.count('depends on axioms:')==n,(name,log)
 assert all(s not in log for s in ('error:','sorryAx','Lean.ofReduceBool','failed to'))
 for l in log.splitlines():
  if 'depends on axioms:' in l:assert set(l.split('depends on axioms:')[1].strip().strip('[]').split(', '))<={'propext','Classical.choice','Quot.sound'}
 return n

def main():
 build=Path((HERE/'build/latest.txt').read_text().strip());proofs=[];sources={};audits=audit('support-TwoCentreCount',1)
 for i,cap,wrapper in [(0,9,'DistanceThreeWindow'),(1,8,'DistanceThreeFresh')]:
  meta=read(f'data/sum{i}.json');W=window(meta['dirs']);e=TaggedEncoding(W,BOUNDS,radius=4);e.atmost(joint_literals(e,W),cap,('ends',))
  full=clauses(f'sum{i}.full.cnf');assert full==e.clauses and meta['cycle_cuts']==[]
  rename={int(k):v for k,v in meta['original_to_new'].items()}
  core=clauses(f'sum{i}.cnf');assert core==[[(-1 if v<0 else 1)*rename[abs(v)] for v in full[j-1]] for j in meta['source_original_clause_ids']]
  assert 's VERIFIED' in (HERE/f'logs/sum{i}-drat-check.txt').read_text()
  stats=read(f'logs/sum{i}-export.txt');assert stats['simulated']
  audits+=audit(f'LocalWindowSat-DistanceThree{i}',1)+audit(wrapper,3)
  proofs.append(dict(case=i,lower_bound=cap+1,clauses=len(core),variables=meta['active_variables'],hints=stats['hints']))
 for p in (HERE/'lean').rglob('*.lean'):
  rel=p.relative_to(HERE/'lean');o=build/rel.with_suffix('.olean')
  assert o.exists() and p.stat().st_mtime<=o.stat().st_mtime,(p,o)
  sources[str(rel).replace('\\','/')]=hashlib.sha256(p.read_bytes().replace(b'\r\n',b'\n')).hexdigest()
 for r in read('data/archives.json'):
  assert hashlib.sha256(raw(r['file'])).hexdigest()==r['sha256']
  assert hashlib.sha256((HERE/'certificates'/(r['file']+'.gz')).read_bytes()).hexdigest()==r['archive_sha256']
 graph=read('data/pair-graph.json')
 assert hashlib.sha256((HERE/'scripts/pair_graph.py').read_bytes().replace(b'\r\n',b'\n')).hexdigest()==graph['script_sha256_lf']
 def canon(ds):
  d={};return [d.setdefault(a,len(d)) for a in ds]
 graphstats=[]
 for r in graph['runs']:
  cc=r['cycle'];a=[e['alpha'] for e in cc];n=len(cc)
  assert Fraction(sum(e['weight'] for e in cc),360*n)==Fraction(r['mean'])
  for j,e in enumerate(cc):
   c,history,run,phase,h=e['state']
   assert e['next_state']==cc[(j+1)%n]['state']
   assert history==[a[(j-k)%n] for k in (4,3,2,1)]
   assert h==(a[(j-5)%n] if canon(c[-6:])==[0,1,2,3,4,1] else 0)
   if r['stage']!='before':
    pat=canon(e['directions'][-7:]);bound=10 if pat==[0,1,2,3,4,1,0] else 9 if pat==[0,1,2,3,4,1,5] else 0
    assert not bound or h==6 or e['alpha']==6 or h+e['alpha']>=bound
   if r['stage']=='pair-and-six':assert not(run>=5 and e['alpha']==4)
  graphstats.append(dict(stage=r['stage'],table=r['table'],mean=r['mean'],period=n))
 controls=read('data/geometry-controls.json');assert controls['verified_bank_paths']==131 and len(controls['occurrences'])==956
 assert all(sum(r['counts'])>=r['bound'] for r in controls['occurrences'])
 out=dict(status='PASSED',audited_theorems=audits,proofs=proofs,total_lrat_hints=sum(p['hints'] for p in proofs),sources_sha256_lf=sources,graph_cycles=graphstats,scope='Both Q9 pattern inequalities are Lean-checked for arbitrary distinct coordinates. Graph means are recorded-cycle diagnostics, not global minimum means or a new snake bound.')
 (HERE/'data/verification.json').write_text(json.dumps(out,indent=2)+'\n');print('PASSED',audits,'audits;',out['total_lrat_hints'],'hints; six recorded graph cycles checked.')
if __name__=='__main__':main()
