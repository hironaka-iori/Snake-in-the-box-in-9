"""Independent local-witness census, certificate provenance, and proof receipts."""
import gzip,hashlib,itertools,json,re
from collections import Counter
from pathlib import Path
from probe import ROOT,HERE,TaggedEncoding,window,DIRS

def read(name):return json.loads((HERE/name).read_text(encoding='utf-8'))
def sha(p):return hashlib.sha256(p.read_bytes().replace(b'\r\n',b'\n')).hexdigest()
def raw(name):
 p=HERE/'certificates'/name
 return p.read_bytes() if p.exists() else gzip.decompress(p.with_name(p.name+'.gz').read_bytes())
def cnf(name):return [list(map(int,l.split()))[:-1] for l in raw(name).decode().splitlines() if l and not l.startswith(('c','p'))]

def witness(row):
 W=window(row['directions']);S=set(row['selected']);assert len(S)==len(row['selected'])
 nbr=lambda v:{v^(1<<i) for i in range(9)}
 ball={v for v in range(512) if min((v^w).bit_count() for w in W[1:-1])<=4}
 assert set(W)<=S<=ball
 deg={v:len(nbr(v)&S) for v in S}
 assert max(deg.values())<=2
 interior={v for v in S if nbr(v)<=ball}
 assert all(deg[v]>=1 for v in interior)
 assert sum(deg[v]==1 for v in interior)<=2
 remaining=set(S);components=0
 while remaining:
  todo=[remaining.pop()];cc=set(todo)
  while todo:
   v=todo.pop()
   for w in nbr(v)&remaining:remaining.remove(w);cc.add(w);todo.append(w)
  assert sum(deg[v] for v in cc)==2*(len(cc)-1)
  components+=1
 alpha=[sum(not({v^(1<<a),v^(1<<b),v^(1<<a)^(1<<b)}&S) for a,b in itertools.combinations(range(9),2)) for v in W[1:-1]]
 assert alpha==row['census']['alpha'] and all(a<=b for a,b in zip(alpha,row['caps']))
 assert row['joint_cap'] is None or sum(alpha[4:6])<=row['joint_cap']
 return dict(name=row['name'],vertices=len(S),components=components,alpha=alpha,pair=[alpha[0],alpha[6]])

def main():
 proofs=[];audits=0
 for i,A,B in [(381,1,21),(382,2,3),(383,8,1)]:
  meta=read(f'data/cycle{i}.json');assert meta['dirs']==DIRS
  assert meta['bounds']==[[0,A]]+[[0,21]]*5+[[0,B]]
  enc=TaggedEncoding(window(DIRS),meta['bounds'],radius=4)
  assert enc.clauses==cnf(f'cycle{i}.full.cnf')
  rename={int(k):v for k,v in meta['original_to_new'].items()}
  core=[[(-1 if x<0 else 1)*rename[abs(x)] for x in enc.clauses[j-1]] for j in meta['source_original_clause_ids']]
  assert core==cnf(f'cycle{i}.cnf')
  assert 's VERIFIED' in (HERE/f'logs/cycle{i}-drat-check.txt').read_text()
  stats=read(f'logs/cycle{i}-export.txt');assert stats['simulated']
  proofs.append(dict(case=i,caps=[A,B],clauses=len(core),variables=meta['active_variables'],hints=stats['hints']))
 for name,count in [('CycleExclusion381',2),('CycleExclusion382',2),('CycleExclusion383',2),('FourPosition',4),('CorePositivity',1),('PairFrontier',6)]:
  s=(HERE/f'logs/{name}.log').read_text(encoding='utf-8')
  assert s.count('depends on axioms:')==count
  assert not any(x in s for x in ('error:','sorryAx','Lean.ofReduceBool','failed to'))
  for line in s.splitlines():
   if 'depends on axioms:' in line:assert set(line.split('depends on axioms:')[1].strip().strip('[]').split(', '))<={'propext','Classical.choice','Quot.sound'}
  audits+=count
 reports=[];statuses=Counter()
 for p in sorted((HERE/'data').glob('*.json')):
  row=json.loads(p.read_text())
  if 'status' not in row or 'caps' not in row:continue
  statuses[row['status']]+=1
  if row['status']=='SAT':reports.append(witness(row))
 assert {tuple(r['pair']) for r in reports if r['name'] in ('pair-2-4','pair-3-2','pair-9-1')}=={(2,4),(3,2),(9,1)}
 graph=ROOT/'milestones/36-critical-cycle-consistency/data/cycle-graph.json'
 def canon(ds):
  names={};return tuple(names.setdefault(d,len(names)) for d in ds)
 matches=[]
 for row in json.loads(graph.read_text())['runs']:
  if row['stage']!='after':continue
  cc=row['cycle'];n=len(cc);hits=[]
  for j,edge in enumerate(cc):
   ds=edge['directions'];aa=[cc[(j-k)%n]['alpha'] for k in range(6,-1,-1)]
   for rev in (False,True):
    d=canon(ds[::-1] if rev else ds);a=aa[::-1] if rev else aa
    if d!=tuple(DIRS):continue
    A,B=a[0],a[-1]
    # Symbol6 can exceed8; it cannot be used to infer the cap8 exclusion.
    excluded=A==1 or (A<=2 and B<=3) or (A<6 and B==1)
    assert not excluded
    hits.append(dict(phase=j,reversed=rev,pair=[A,B]))
  matches.append(dict(table=row['table'],mean=row['mean'],matches=hits))
 build=Path((HERE/'build/latest.txt').read_text().strip());sources={}
 for p in (HERE/'lean').rglob('*.lean'):
  o=build/p.relative_to(HERE/'lean').with_suffix('.olean')
  assert o.exists() and p.stat().st_mtime<=o.stat().st_mtime,p
  sources[p.relative_to(HERE).as_posix()]=sha(p)
 for r in read('data/archives.json'):
  assert hashlib.sha256(raw(r['file'])).hexdigest()==r['sha256']
  assert hashlib.sha256((HERE/'certificates'/(r['file']+'.gz')).read_bytes()).hexdigest()==r['archive_sha256']
 out=dict(status='PASSED',audited_theorems=audits,proofs=proofs,solver_statuses=dict(statuses),independent_local_witnesses=reports,prior_graph_sha256_lf=sha(graph),remaining_cycles=matches,sources_sha256_lf=sources,scope='Universal local pair inequalities with complete Lean interpretation; local forest attainments do not establish full-snake sharpness; no new global bound.')
 (HERE/'data/verification.json').write_text(json.dumps(out,indent=2)+'\n')
 print('PASSED',audits,'audits;',dict(statuses),';',len(reports),'independent forest checks;',proofs)
if __name__=='__main__':main()
