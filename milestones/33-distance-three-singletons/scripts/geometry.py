"""Independent geometric and actual-bank controls for the pair inequality."""
import hashlib,itertools,json,sys
from pathlib import Path
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'milestones/28-direct-share-certificates/scripts'))
from verify import check_cut
x,y=1,29;D=(2,3,4);F=(5,6,7,8)
A={x^(1<<a)^(1<<b) for a,b in itertools.combinations(range(2,9),2)}
B={y^(1<<a)^(1<<b) for a,b in itertools.combinations(range(2,9),2)}
forcedA={x^(1<<a)^(1<<b) for a,b in itertools.combinations(D,2)}
forcedB={y^(1<<a)^(1<<b) for a,b in itertools.combinations(D,2)}
assert all((v^y).bit_count()==1 and v not in (y^1,y^2) for v in forcedA)
assert all((v^x).bit_count()==1 and v not in (x^1,x^2) for v in forcedB)
cycles=[[x^(1<<2)^(1<<f),y^(1<<3)^(1<<f),x^(1<<4)^(1<<f),y^(1<<2)^(1<<f),x^(1<<3)^(1<<f),y^(1<<4)^(1<<f)] for f in F]
for cc in cycles:check_cut(cc)
# For a fresh exit direction 5, retain only the cycles for coordinates 6,7,8.
Bfresh={y^(1<<a)^(1<<b) for a,b in itertools.combinations([0,2,3,4,6,7,8],2)}
assert forcedB <= Bfresh
assert all(set(cc)<=A|Bfresh for cc in cycles[1:])
assert all((v^x).bit_count()==1 and v not in (x^1,x^2) for v in forcedB)
sets=[forcedA,forcedB]+list(map(set,cycles))
assert all(not(s&t) for i,s in enumerate(sets) for t in sets[i+1:])
assert all(s<=A|B for s in sets) and not A&B and len(A)==len(B)==21
bankfile=ROOT/'work/bank9.json';bank=json.loads(bankfile.read_text());hits=[]
def canon(ds):
 d={};return [d.setdefault(a,len(d)) for a in ds]
for k,row in enumerate(bank):
 vs=row['vertex_sequence'];S=set(vs)
 assert len(vs)==len(S) and all(0<=v<512 for v in S)
 assert all(((vs[i]^vs[j]).bit_count()==1)==(j==i+1) for i in range(len(vs)) for j in range(i+1,len(vs)))
 ds=[(u^v).bit_length()-1 for u,v in zip(vs,vs[1:])]
 for r in range(len(ds)-6):
  pat=canon(ds[r:r+7])
  if pat not in ([0,1,2,3,4,1,0],[0,1,2,3,4,1,5]):continue
  bound=10 if pat[-1]==0 else 9
  counts=[sum(all(v not in S for v in (z^(1<<a),z^(1<<b),z^(1<<a)^(1<<b))) for a,b in itertools.combinations(range(9),2)) for z in (vs[r+1],vs[r+6])]
  assert sum(counts)>=bound
  hits.append(dict(bank_index=k,start=r,counts=counts,bound=bound))
out=dict(forced_corner_sets=[sorted(forcedA),sorted(forcedB)],disjoint_induced_six_cycles=cycles,forced_totals=[10,9],
 verified_bank_paths=len(bank),bank_sha256=hashlib.sha256(bankfile.read_bytes()).hexdigest(),occurrences=hits,
 minimum_observed_sum={str(b):min((sum(h['counts']) for h in hits if h['bound']==b),default=None) for b in (9,10)},scope='Finite geometric checks and bank control; the separate Lean theorem proves the Q9 pattern inequality.')
(HERE/'data/geometry-controls.json').write_text(json.dumps(out,indent=2)+'\n')
print('Four disjoint cycles checked;',len(hits),'bank occurrences; minimum observed sum',out['minimum_observed_sum'])
