"""Independent checks for the adjacent floor17/floor18 certificates.
No discovery module is imported. Writes only in this subfolder.
"""
from pathlib import Path
from fractions import Fraction
import gzip,hashlib,json,sys,time
HERE=Path(__file__).resolve().parent;PARENT=HERE.parent;ROOT=HERE.parents[3]
sys.path.insert(0,str(ROOT/'work/solver_packages'))
import numpy as np
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'));sha=lambda b:hashlib.sha256(b).hexdigest()
start=time.monotonic();pins=read(HERE/'input-pins.json');report=read(HERE/'results.json')
expected={'012031':16,'012032':16,'012034':20,'012301':16,'012304':16,'012310':12,'012314':16,'012340':16,'012345':16}
assert pins['full_floors']==expected
assert report['status']=='SHARP_FIXED_GRAPH_SINGLE_FLOOR_THRESHOLD'
assert report['known_infeasible_floor']==17 and report['known_feasible_floor']==18 and report['least_feasible_floor']==18
assert [r['floor'] for r in report['candidates']]==[9,14,16,17,18]
for file,h in pins['parent_files_sha256'].items():assert sha((PARENT/file).read_bytes())==h,file
for file,h in pins['graph_files_sha256'].items():assert sha((ROOT/file).read_bytes())==h,file
assert sha((HERE/'search.py').read_bytes())==report['script_sha256']
OLD=ROOT/'milestones/72-four-count-proof-closure/critical-current'
meta=read(OLD/'data/source-proved-model.json')
with np.load(OLD/'build/source-graph.npz') as z:A={k:z[k] for k in z.files}
for k,h in meta['arrays_sha256'].items():assert sha(A[k].tobytes())==h,k
assert len(A['U'])==4947008 and meta['states']==1601856
ext=read(ROOT/'milestones/59-extended-share-window/extended/data/model.json')['extensions']
def canonical(word):
 order=[];result=[]
 for d in word:
  if d not in order:order.append(d)
  result.append(order.index(d))
 return tuple(result)
shapes=[min(canonical(ds[3:]),canonical(ds[3:][::-1])) for ds in ext]
base={tuple(map(int,w)):n for w,n in expected.items()}
def weights(floor):
 floors=base.copy();floors[(0,1,2,0,3,4)]=floor
 credit=np.asarray([floors[s] for s in shapes],dtype=np.int64)
 return np.maximum(A['weight'].astype(np.int64),120*(A['count_code'].astype(np.int64)%6+1)+credit[A['direction']])
def walk(rows,W,closed=False):
 assert rows;total=0
 for i,r in enumerate(rows):
  e=r['edge'];assert 0<=e<len(W)
  for name in ['direction','history','count_code']:assert int(A[name][e])==r[name]
  assert int(A['U'][e])==r['u'] and int(A['V'][e])==r['v']
  assert int(W[e])==r['weight'] and int(A['weight'][e])==r['base_weight']
  assert r['shape']==''.join(map(str,shapes[r['direction']]))
  if i:assert rows[i-1]['v']==r['u']
  total+=r['weight']
 if closed:assert rows[-1]['v']==rows[0]['u']
 return len(rows),total
checks=[]
for result in report['candidates']:
 floor=result['floor'];W=weights(floor);assert sha(W.tobytes())==result['weight_sha256']
 n,C=walk(result['cycle'],W,True);assert n==3 and C==1488
 row=dict(floor=floor,cycle_length=n,cycle_weight=C,status=result['status'])
 if result['status']=='ALL_SLOPE_RANGE_OBSTRUCTION':
  k,C=walk(result['walk'],W);D=496*k-C
  assert k==result['length']<=227 and C==result['total_weight'] and D==result['deficit']>=632
  row.update(walk_length=k,walk_weight=C,deficit=D,criterion_ceiling=112592-D)
 elif result['status']=='CONDITIONAL_234_POTENTIAL':
  assert floor==18
  raw=gzip.decompress((HERE/result['potential_file']).read_bytes());assert sha(raw)==result['potential_sha256']
  pi=np.frombuffer(raw,dtype='<i8');assert len(pi)==meta['states'] and int(pi.min())==0 and int(pi.max())==602
  for lo in range(0,len(W),65536):
   hi=min(lo+65536,len(W));slack=W[lo:hi]+pi[A['U'][lo:hi]]-pi[A['V'][lo:hi]]-496
   assert int(slack.min())>=0,lo
  bound=Fraction(1098960+8*496+602,4200+496);assert bound==Fraction(result['comparison_bound'])==Fraction(551765,2348)<235
  assert 227*496-111960-602==result['strict_margin']==30
  row.update(all_edges_checked=len(W),potential_range=602,strict_margin=30,comparison_bound=str(bound))
 else:raise AssertionError(result['status'])
 checks.append(row);print(row,flush=True)
W17=weights(17);W18=weights(18);assert np.all(W17<=W18)
assert all(r['shape']!='012034' for r in report['feasible_certificate']['cycle'])
oldpath=ROOT/'milestones/93-defined-graph-potential/data/full-conditional-range-certificate.json'
saved=read(oldpath);path=[]
for old in saved['path']:
 e=old['edge']
 for key,col in [('u','U'),('v','V'),('direction','direction'),('history','history'),('count_code','count_code')]:assert old[key]==int(A[col][e])
 path.append(dict(edge=e,u=int(A['U'][e]),v=int(A['V'][e]),direction=int(A['direction'][e]),history=int(A['history'][e]),count_code=int(A['count_code'][e]),shape=''.join(map(str,shapes[int(A['direction'][e])])),weight=int(W18[e]),base_weight=int(A['weight'][e]),source_potential=int(pi[A['U'][e]]),target_potential=int(pi[A['V'][e]])))
k,C=walk(path,W18);assert k==7
pathcheck=dict(status='REEVALUATED_SAVED_SEVEN_EDGE_PATH',floor=18,path_length=k,path_weight=C,path_deficit=496*k-C,certifies_range602=(C==2870),source_path=str(oldpath.relative_to(ROOT)),source_path_sha256=sha(oldpath.read_bytes()),scope='The saved path is checked separately from the adjacent-floor threshold. No other path is sought; range optimality is not claimed unless its deficit is602.')
if C==2870:
 assert path[0]['source_potential']-path[-1]['target_potential']==602
 assert all(r['weight']+r['source_potential']-r['target_potential']==496 for r in path)
 pathcheck['path']=path
(HERE/'saved-seven-edge-path-check.json').write_text(json.dumps(pathcheck,indent=2)+'\n',encoding='utf-8')
print('Saved seven-edge path',pathcheck,flush=True)
assert pins['parent_files_sha256']=={p.name:sha(p.read_bytes()) for p in PARENT.iterdir() if p.is_file()}
secs=time.monotonic()-start;total=report['numerical_seconds']+secs;assert total<600
out=dict(status='PASS_SHARP_FIXED_GRAPH_INTEGER_FLOOR_THRESHOLD',least_feasible_integer_floor=18,adjacent_obstructed_floor=17,verified_baseline_floors=expected,results=checks,all_parent_files_unchanged=True,monotonic_weights_checked_at_adjacent_pair=True,monotonicity_argument='For fixed base weights and all other floors, max(base,entering+floor) is nondecreasing in floor. The18 potential remains feasible above18; the17 cycle/path obstruction remains valid below17.',saved_path_check_sha256=sha((HERE/'saved-seven-edge-path-check.json').read_bytes()),saved_path_certifies_range602=pathcheck['certifies_range602'],verification_seconds=secs,total_additional_numerical_seconds=total,source_result_sha256=sha((HERE/'results.json').read_bytes()),input_pins_sha256=sha((HERE/'input-pins.json').read_bytes()),verifier_sha256=sha(Path(__file__).read_bytes()),scope='Sharp nonnegative integer threshold for012034 alone in the fixed saved graph, constant slope/global potential range and current boundary budget. Saved seven-edge path re-evaluated separately; no universal share bound, complete Lean graph certificate or global snake optimum.')
(HERE/'verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8');print(out['status'],'seconds',total,'saved path',k,C,flush=True)
