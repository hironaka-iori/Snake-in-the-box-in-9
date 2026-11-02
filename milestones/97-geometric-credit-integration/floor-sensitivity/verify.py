"""Independent reconstruction and certificate verification for five floor tests.
No discovery routine or saved relaxation distances are imported.
"""
from pathlib import Path
from fractions import Fraction
import gzip,hashlib,json,sys,time
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[2]
sys.path.insert(0,str(ROOT/'work/solver_packages'))
import numpy as np
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'));digest=lambda b:hashlib.sha256(b).hexdigest()
start=time.monotonic();pins=read(HERE/'input-pins.json');report=read(HERE/'results.json')
for path,expected in pins['files'].items():assert digest((ROOT/path).read_bytes())==expected,path
OLD=ROOT/'milestones/72-four-count-proof-closure/critical-current';meta=read(OLD/'data/source-proved-model.json')
with np.load(OLD/'build/source-graph.npz') as z:A={k:z[k] for k in z.files}
for k,expected in meta['arrays_sha256'].items():assert digest(A[k].tobytes())==expected,k
assert len(A['U'])==4947008
extensions=read(ROOT/'milestones/59-extended-share-window/extended/data/model.json')['extensions']
def canonical(word):
 order=[];out=[]
 for value in word:
  if value not in order:order.append(value)
  out.append(order.index(value))
 return tuple(out)
key=[min(canonical(row[3:]),canonical(row[3:][::-1])) for row in extensions]
expected_floors={'012031':16,'012032':16,'012034':20,'012301':16,'012304':16,
                 '012310':12,'012314':16,'012340':16,'012345':16}
assert report['full_floors']==expected_floors, 'Results do not use the intended nine baseline floors'
assert pins['full_floors']==expected_floors, 'Input pins do not use the intended nine baseline floors'
floors={tuple(map(int,k)):v for k,v in expected_floors.items()}
expected_cases={7301:'012032',7302:'012034',7303:'012301',7307:'012340',7308:'012345'}
assert {r['case']:r['shape'] for r in report['results']}==expected_cases
summary=[]
for result in report['results']:
 current=floors.copy();selected=tuple(map(int,result['shape']));assert result['tested_floor']==current[selected]-1
 current[selected]-=1
 by_direction=np.asarray([current[k] for k in key],dtype=np.int64)
 W=np.maximum(A['weight'].astype(np.int64),120*(A['count_code'].astype(np.int64)%6+1)+by_direction[A['direction']])
 assert digest(W.tobytes())==result['weight_sha256']
 def check_walk(rows,closed=False):
  assert rows
  total=0
  for i,row in enumerate(rows):
   e=row['edge'];assert 0<=e<len(W)
   for name in ['direction','history','count_code']:assert row[name]==int(A[name][e]),(name,e)
   assert row['u']==int(A['U'][e]) and row['v']==int(A['V'][e])
   assert row['weight']==int(W[e]) and row['base_weight']==int(A['weight'][e])
   assert row['shape']==''.join(map(str,key[row['direction']]))
   if i:assert rows[i-1]['v']==row['u']
   total+=row['weight']
  if closed:assert rows[-1]['v']==rows[0]['u']
  return len(rows),total
 cn,ct=check_walk(result['cycle'],True);mu=Fraction(ct,cn);assert str(mu)==result['cycle_mean']
 row=dict(case=result['case'],shape=result['shape'],tested_floor=result['tested_floor'],status=result['status'],cycle_mean=str(mu),cycle_edges=cn,cycle_weight=ct)
 if result['status']=='CONDITIONAL_234_POTENTIAL':
  raw=gzip.decompress((HERE/result['potential_file']).read_bytes());assert digest(raw)==result['potential_sha256']
  pi=np.frombuffer(raw,dtype='<i8');assert len(pi)==meta['states'] and int(pi.min())==0
  p,d=mu.numerator,mu.denominator;R=int(pi.max());assert R==result['potential_range_scaled']
  minimum=None
  for lo in range(0,len(W),65536):
   hi=min(lo+65536,len(W));slack=d*W[lo:hi]+pi[A['U'][lo:hi]]-pi[A['V'][lo:hi]]-p
   q=int(slack.min());minimum=q if minimum is None else min(minimum,q);assert q>=0,(lo,q)
  bound=Fraction(1098960*d+8*p+R,4200*d+p);margin=227*p-111960*d-R
  assert bound==Fraction(result['comparison_bound'])<235 and margin==result['strict_margin_scaled']>0
  row.update(all_edges_checked=len(W),minimum_scaled_slack=minimum,potential_range=str(Fraction(R,d)),comparison_bound=str(bound),strict_margin_scaled=margin)
 elif result['status']=='ALL_SLOPE_RANGE_OBSTRUCTION':
  n,total=check_walk(result['walk']);assert n==result['length']<=227 and total==result['total_weight']
  deficit=n*mu-total;ceiling=(227-n)*mu+total
  assert ceiling==Fraction(result['criterion_ceiling'])<=111960
  assert deficit*mu.denominator==result['deficit_scaled']
  row.update(walk_length=n,walk_weight=total,deficit=str(deficit),criterion_ceiling=str(ceiling))
 elif result['status']=='IMMEDIATE_ALL_SLOPE_RANGE_OBSTRUCTION':
  n,total=check_walk(result['witness']['walk']);assert n<=227 and (227-n)*mu+total<=111960
 elif result['status'].startswith('UNRESOLVED') or result['status']=='CONVERGED_COMPARISON_NOT_234':
  row['decisive']=False
 else:raise AssertionError(result['status'])
 summary.append(row);print(row,flush=True)
elapsed=time.monotonic()-start
total=read(HERE/'saved-witness-tests.json')['seconds']+report['numerical_seconds']+elapsed
assert total<600,total
out=dict(status='PASS_INDEPENDENT_FINITE_GRAPH_CERTIFICATES',verified_baseline_floors=expected_floors,results=summary,verification_seconds=elapsed,total_recorded_numerical_seconds=total,source_result_sha256=digest((HERE/'results.json').read_bytes()),input_pins_sha256=digest((HERE/'input-pins.json').read_bytes()),verifier_sha256=digest(Path(__file__).read_bytes()),scope='Independent integer reconstruction and full-edge potential/path checks on the pinned graph. All other conditional floors remain fixed. No Lean replay or new global snake theorem.')
(HERE/'verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(out['status'],'total numerical seconds',total,flush=True)
