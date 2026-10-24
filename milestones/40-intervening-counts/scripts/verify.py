"""Independent geometric checks, then certificate provenance and Lean audit receipts."""
from pathlib import Path
from collections import Counter
import gzip,hashlib,itertools,json
from probe import ROOT,HERE,TaggedEncoding,window,DIRS

def read(p):return json.loads((HERE/p).read_text())
def nbr(v):return {v^(1<<d) for d in range(9)}
def components(S):
 remaining=set(S);out=[]
 while remaining:
  todo=[remaining.pop()];cc=set(todo)
  while todo:
   v=todo.pop()
   for w in nbr(v)&remaining:remaining.remove(w);cc.add(w);todo.append(w)
  out.append(cc)
 return out
def cycle(C):
 S=set(C);assert len(S)==len(C) and S
 assert all(len(nbr(v)&S)==2 for v in S)
 assert len(components(S))==1
def witness(row,forest=True):
 W=window(row['directions']);S=set(row['selected']);assert len(S)==len(row['selected'])
 B={v for v in range(512) if min((v^w).bit_count() for w in W[1:-1])<=4}
 assert set(W)<=S<=B
 deg={v:len(nbr(v)&S) for v in S};assert max(deg.values())<=2
 interior={v for v in S if nbr(v)<=B}
 assert all(deg[v]>=1 for v in interior)
 assert sum(deg[v]==1 for v in interior)<=2
 cc=components(S)
 if forest:assert all(sum(deg[v] for v in c)==2*(len(c)-1) for c in cc)
 else:assert any(all(deg[v]==2 for v in c) for c in cc)
 alpha=[sum(not({v^(1<<a),v^(1<<b),v^(1<<a)^(1<<b)}&S) for a,b in itertools.combinations(range(9),2)) for v in W[1:-1]]
 assert alpha==row['census']['alpha'] and all(a<=b for a,b in zip(alpha,row['caps']))
 if row.get('joint'):
  positions,cap=row['joint'];assert sum(alpha[j-1] for j in positions)<=cap
 return dict(name=row.get('name','cyclic-relaxation'),vertices=len(S),components=len(cc),alpha=alpha)
def raw(name):
 p=HERE/'certificates'/name
 return p.read_bytes() if p.exists() else gzip.decompress(p.with_name(p.name+'.gz').read_bytes())
def cnf(name):return [list(map(int,l.split()))[:-1] for l in raw(name).decode().splitlines() if l and not l.startswith(('c','p'))]
def main():
 positive=[];statuses=Counter()
 for p in (HERE/'data').glob('*.json'):
  row=json.loads(p.read_text())
  if 'caps' not in row or 'status' not in row:continue
  statuses[row['status']]+=1
  for c in row['cycle_cuts']:cycle(c)
  if row['status']=='SAT':positive.append(witness(row))
 relaxed=witness(read('data/cyclic-relaxation.json'),False)
 template=read('data/ten-cycle-template.json');cycle(template['base_vertices'])
 order=template['cyclic_order'];assert set(order)==set(template['base_vertices'])
 assert all((order[j]^order[(j+1)%len(order)]).bit_count()==1 for j in range(len(order)))
 assert template['copies']==[sorted(v^(1<<d) for v in template['base_vertices']) for d in range(5,9)]
 assert template['copies']==read('data/cycle402.json')['cycle_cuts']
 proofs=[]
 for i,idx in [(401,2),(402,5)]:
  meta=read(f'data/cycle{i}.json');caps=[3,21,21,21,21,21,3];caps[idx]=4
  assert meta['dirs']==DIRS and meta['bounds']==[[0,k] for k in caps]
  enc=TaggedEncoding(window(DIRS),meta['bounds'],radius=4)
  base_clauses=len(enc.clauses)
  for c in meta['cycle_cuts']:
   cycle(c);assert set(c)<=set(enc.ball);enc.add([-enc.var[v] for v in c],('cut',))
  assert enc.clauses==cnf(f'cycle{i}.full.cnf')
  rename={int(k):v for k,v in meta['original_to_new'].items()}
  core=[[(-1 if x<0 else 1)*rename[abs(x)] for x in enc.clauses[j-1]] for j in meta['source_original_clause_ids']]
  assert core==cnf(f'cycle{i}.cnf')
  assert 's VERIFIED' in (HERE/f'logs/cycle{i}-drat-check.txt').read_text()
  stats=read(f'logs/cycle{i}-export.txt');assert stats['simulated']
  inverse={i:v for v,i in enc.var.items()};cut_lengths=Counter()
  for j in meta['source_original_clause_ids']:
   if enc.tags[j-1][0]=='cut':
    clause=enc.clauses[j-1];assert all(x<0 for x in clause)
    cycle([inverse[-x] for x in clause]);cut_lengths[len(clause)]+=1
  proofs.append(dict(case=i,clauses=len(core),variables=meta['active_variables'],hints=stats['hints'],supplied_additional_cycle_cuts=len(meta['cycle_cuts']),retained_additional_cycle_cuts=sum(j>base_clauses for j in meta['source_original_clause_ids']),retained_cycle_lengths=dict(cut_lengths)))
 audits=0
 for name,count in [('CycleExclusion401',2),('CycleExclusion402',2),('InterveningCounts',4)]:
  text=(HERE/f'logs/{name}.log').read_text(encoding='utf-8')
  assert text.count('depends on axioms:')==count
  assert not any(x in text for x in ['sorryAx','error:','Lean.ofReduceBool'])
  for line in text.splitlines():
   if 'depends on axioms:' in line:assert set(line.split('depends on axioms:')[1].strip().strip('[]').split(', '))<={'propext','Classical.choice','Quot.sound'}
  audits+=count
 target=read('data/target.json');assert target['counts']==[3,4,4,5,5,3,3]
 assert target['counts'][0]<=3 and target['counts'][-1]<=3 and target['counts'][2]<5 and target['counts'][5]<5
 assert hashlib.sha256((ROOT/target['source']).read_bytes()).hexdigest()==target['source_sha256']
 build=Path((HERE/'build/latest.txt').read_text().strip())
 for p in (HERE/'lean').rglob('*.lean'):
  o=build/p.relative_to(HERE/'lean').with_suffix('.olean');assert o.exists() and o.stat().st_mtime>=p.stat().st_mtime,p
 for r in read('data/archives.json'):
  assert hashlib.sha256(raw(r['file'])).hexdigest()==r['sha256']
  assert hashlib.sha256((HERE/'certificates'/(r['file']+'.gz')).read_bytes()).hexdigest()==r['archive_sha256']
 out=dict(status='PASSED',audited_theorems=audits,proofs=proofs,solver_statuses=dict(statuses),independent_forests=positive,cyclic_relaxation=relaxed,ten_cycle_template_checked=True,excluded_saved_cycle=dict(mean=target['cycle_mean'],phase=target['phase'],reversed=True,counts=target['counts']),scope='Universal local three-position exclusions; thresholds attained only in local forests. Joint-sum thresholds remain numerical. No new global upper bound or minimum cycle mean.')
 (HERE/'data/verification.json').write_text(json.dumps(out,indent=2)+'\n')
 print('PASSED:',audits,'audits,',len(positive),'independent forests;',proofs)
if __name__=='__main__':main()
