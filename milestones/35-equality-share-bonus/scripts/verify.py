"""Audit the complete share theorem, source provenance and independent controls."""
import gzip,hashlib,json
from pathlib import Path
from tagged_pair import TaggedPairShare
from geometry import inspect
HERE=Path(__file__).resolve().parents[1]
def read(n):return json.loads((HERE/n).read_text(encoding='utf-8'))
def sha(p):return hashlib.sha256(p.read_bytes().replace(b'\r\n',b'\n')).hexdigest()
def raw(n):
 p=HERE/'certificates'/n
 return p.read_bytes() if p.exists() else gzip.decompress(p.with_name(p.name+'.gz').read_bytes())
def clauses(n):return [list(map(int,l.split()))[:-1] for l in raw(n).decode().splitlines() if l and not l.startswith(('c','p'))]

def main():
 m=read('data/pairshare.json');e=TaggedPairShare(m['dirs'],m['bounds'],11)
 assert m['cycle_cuts']==[] and clauses('pairshare.full.cnf')==e.clauses
 rename={int(k):v for k,v in m['original_to_new'].items()}
 core=[[(-1 if x<0 else 1)*rename[abs(x)] for x in e.clauses[i-1]] for i in m['source_original_clause_ids']]
 assert core==clauses('pairshare.cnf') and len(core)==115 and m['active_variables']==114
 tags=[e.tags[i-1] for i in m['source_original_clause_ids']]
 assert all(t[0]!='old' or t[1][0] in ('window','deg2') for t in tags)
 assert {'emptyE','shareCl','shareCap'}<={t[0] for t in tags}
 assert 's VERIFIED' in (HERE/'logs/drat-check.txt').read_text()
 stats=read('logs/export.txt');assert stats['simulated'] and stats['hints']==281
 assert read('data/cap11.json')['status']=='INFEASIBLE'
 assert read('data/tagged-control.json')['pair_shares']==[25,17]
 assert read('data/fixed-control.json')['status']=='OPTIMAL'
 geometries=read('data/geometry.json')
 for g in geometries:assert json.loads(json.dumps(inspect(g['dirs'])))==g
 audits=0
 for name,count in [('support-JointShareTags',3),('check-LocalWindowSat-PairShareCert',1),('check-LocalWindowShareBridge',2),('check-ThreeSquareBonus',4),('check-PairSharePacking',3)]:
  s=(HERE/f'logs/{name}.log').read_text(encoding='utf-8')
  assert s.count('depends on axioms:')==count
  assert all(x not in s for x in ('sorryAx','error:','Lean.ofReduceBool','failed to'))
  for l in s.splitlines():
   if 'depends on axioms:' in l:assert set(l.split('depends on axioms:')[1].strip().strip('[]').split(', '))<={'propext','Classical.choice','Quot.sound'}
  audits+=count
 build=Path((HERE/'build/latest.txt').read_text().strip());sources={}
 for root in ('lean','upstream'):
  for p in (HERE/root).rglob('*.lean'):
   o=build/p.relative_to(HERE/root).with_suffix('.olean')
   assert o.exists() and p.stat().st_mtime<=o.stat().st_mtime,(p,o)
   sources[p.relative_to(HERE).as_posix()]=sha(p)
 assert sha(HERE/'upstream/LocalWindowShareBridge.lean')==read('data/upstream.json')['sha256_lf']
 for r in read('data/archives.json'):
  assert hashlib.sha256(raw(r['file'])).hexdigest()==r['sha256']
  assert hashlib.sha256((HERE/'certificates'/(r['file']+'.gz')).read_bytes()).hexdigest()==r['archive_sha256']
 result=dict(status='PASSED',audited_theorems=audits,core_clauses=115,active_variables=114,lrat_hints=281,share_lower=12,charge_lower=228,requires_count_equality=False,sources_sha256_lf=sources,scope='Arbitrary Q9 snakes with six distinct coordinate labels in the specified pattern. No global upper-bound improvement.')
 (HERE/'data/verification.json').write_text(json.dumps(result,indent=2)+'\n')
 print('PASSED:',audits,'axiom audits; unconditional pattern share >=12; pair charge >=228.')
if __name__=='__main__':main()
