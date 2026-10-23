"""Recheck full paths, singleton counts, local controls and Lean receipts."""
import hashlib,json,sys
from pathlib import Path
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'milestones/33-distance-three-singletons/scripts'))
from certify import prior

def read(n):return json.loads((HERE/n).read_text(encoding='utf-8'))
def main():
 summary=[];cuts=0
 for i,cap in ((0,10),(1,9)):
  row=read(f'data/pair-{i}-cap-{cap}.json');cc=prior.census(row)
  assert cc['alpha'][0]+cc['alpha'][5]==cap
  full=read(f'data/full-{i}-cap-{cap}.json');w=read(f'data/witness-{i}.json');vs=w['vertex_sequence'];S=set(vs);n=w['edges']
  assert hashlib.sha256((HERE/f'data/full-{i}-cap-{cap}.json').read_bytes()).hexdigest()==w['source_sha256']
  assert len(vs)==len(S)==n+1 and set(full['selected'])==S and all(0<=v<512 for v in S)
  assert all(((vs[a]^vs[b]).bit_count()==1)==(b==a+1) for a in range(len(vs)) for b in range(a+1,len(vs)))
  ds=[(a^b).bit_length()-1 for a,b in zip(vs,vs[1:])];start=w['start'];assert ds[start:start+7]==w['dirs']
  import itertools
  def alpha(v):return sum(all(q not in S for q in (v^(1<<a),v^(1<<b),v^(1<<a)^(1<<b))) for a,b in itertools.combinations(range(9),2))
  counts=[alpha(vs[start+1]),alpha(vs[start+6])];assert counts==w['pair_counts'] and sum(counts)==cap
  for data in (row,full,read(f'data/length-192-case-{i}.json')):
   for cut in data['cycle_cuts']:prior.check_cut(cut);cuts+=1
  length=read(f'data/length-192-case-{i}.json');assert length['status']=='UNKNOWN' and length['selected'] is None
  shares=[]
  for z in (vs[start+1],vs[start+6]):
   total=0
   for q in prior.neighbors(z):
    degree=sum(w in S for w in prior.neighbors(q));assert degree>0
    empty=sum(all(w not in S for w in (q,q^(1<<a),q^(1<<b),q^(1<<a)^(1<<b))) for a,b in itertools.combinations(range(9),2))
    total+=12*empty//degree
   shares.append(total)
  assert shares==[full['census']['share'][j] for j in (0,5)]
  summary.append(dict(case=i,edges=n,start_vertex=vs[0],window_start=start,pair_counts=counts,pair_sum=cap,pair_shares=shares,pair_charge=24*cap+sum(shares),local_components=len(prior.components(set(row['selected']))),length_192_status=length['status']))
 build=Path((HERE/'build/latest.txt').read_text().strip());sources={};audits=0
 for name,count in [('Witness0',5),('Witness1',5),('OptimalConstants',2)]:
  s=(HERE/f'logs/support-{name}.log').read_text(encoding='utf-8');assert s.count('depends on axioms:')==count,(name,s)
  assert all(x not in s for x in ('sorryAx','error:','Lean.ofReduceBool','failed to'))
  for l in s.splitlines():
   if 'depends on axioms:' in l:assert set(l.split('depends on axioms:')[1].strip().strip('[]').split(', '))<={'propext','Quot.sound','Classical.choice'}
  p=HERE/f'lean/{name}.lean';o=build/f'{name}.olean';assert o.exists() and p.stat().st_mtime<=o.stat().st_mtime
  sources[name]=hashlib.sha256(p.read_bytes().replace(b'\r\n',b'\n')).hexdigest();audits+=count
 out=dict(status='PASSED',audited_theorems=audits,witnesses=summary,cycle_cuts_checked=cuts,sources_sha256_lf=sources,scope='Sharp universal constants for the two fixed direction-pattern inequalities; no improvement to the maximum snake length.')
 (HERE/'data/verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
if __name__=='__main__':main()
