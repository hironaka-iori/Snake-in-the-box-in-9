"""Bounded monotone search for the012034 floor in one fixed weighted graph.
Reads the parent experiment; never writes to its files.
"""
from pathlib import Path
from fractions import Fraction
import datetime,gzip,hashlib,importlib.util,json,sys,time
HERE=Path(__file__).resolve().parent;PARENT=HERE.parent;ROOT=HERE.parents[3]
sys.path.insert(0,str(ROOT/'work/solver_packages'))
import numpy as np
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'));sha=lambda b:hashlib.sha256(b).hexdigest()
def save(name,obj):(HERE/name).write_text(json.dumps(obj,indent=2)+'\n',encoding='utf-8')
spec=importlib.util.spec_from_file_location('parent_floor_test97',PARENT/'test.py');parent=importlib.util.module_from_spec(spec);spec.loader.exec_module(parent)
START=time.monotonic();DEADLINE=START+500
frozen={p.name:sha(p.read_bytes()) for p in PARENT.iterdir() if p.is_file()}
meta,a,shape,entering,full,cycle,paths,pins=parent.setup()
assert pins==read(PARENT/'input-pins.json')['files']
expected={'012031':16,'012032':16,'012034':20,'012301':16,'012304':16,'012310':12,'012314':16,'012340':16,'012345':16}
assert dict(zip(parent.SHAPES,parent.FLOORS))==expected
U,V,N=a['U'],a['V'],meta['states'];selected=shape==2

def weight(floor):
 w=full.copy();w[selected]=np.maximum(a['weight'][selected],entering[selected]+floor);return w

def existing_bounds():
 prior=read(ROOT/'milestones/74-graph-interpretation-audit/optimization/data/weaken-012034.json')
 w=weight(0);es=[row['edge'] for row in prior['walk']];parent.valid_walk(es,a)
 rows=parent.rows(es,a,shape,w);assert rows==prior['walk']
 total=sum(row['weight'] for row in rows);assert len(es)<=227 and 496*len(es)-total>=632
 assert sum(int(w[e]) for e in cycle)==1488
 zero=dict(floor=0,status='ALL_SLOPE_RANGE_OBSTRUCTION',origin='milestone74 saved zero-floor walk',cycle=parent.rows(cycle,a,shape,w),walk=rows,length=len(es),total_weight=total,deficit=496*len(es)-total,weight_sha256=sha(w.tobytes()))
 nineteen=read(PARENT/'case7302.json');assert nineteen['tested_floor']==19
 w=weight(19);assert sha(w.tobytes())==nineteen['weight_sha256']
 raw=gzip.decompress((PARENT/nineteen['potential_file']).read_bytes());assert sha(raw)==nineteen['potential_sha256']
 pi=np.frombuffer(raw,dtype='<i8');assert len(pi)==N and pi.min()==0 and pi.max()==601
 assert np.all(496+pi[V]<=w+pi[U])
 save('known-zero-obstruction.json',zero)
 save('known-nineteen-feasible.json',dict(nineteen,origin='parent case7302',potential_path='../'+nineteen['potential_file']))
 return zero,nineteen

lowdata,highdata=existing_bounds();low,high=0,19;candidates=[]
save('input-pins.json',dict(parent_files_sha256=frozen,graph_files_sha256=pins,source_arrays_sha256=meta['arrays_sha256'],full_floors=expected,known_infeasible=0,known_feasible=19,script_sha256=sha(Path(__file__).read_bytes())))

for attempt in range(1,6):
 if high-low<=1:break
 floor=(low+high)//2;before=time.monotonic();w=weight(floor)
 assert sum(int(w[e]) for e in cycle)==1488
 result=dict(floor=floor,attempt=attempt,initial_bracket=[low,high],cycle=parent.rows(cycle,a,shape,w),weight_sha256=sha(w.tobytes()),changed_edges=int(np.count_nonzero(w!=full)),status='UNRESOLVED_ITERATION_LIMIT')
 dist=np.zeros(N,dtype=np.int64);parents=[]
 for iteration in range(1,228):
  if time.monotonic()>=DEADLINE:
   result['status']='UNRESOLVED_RUNTIME_BUDGET';break
  candidate=dist[U]+w-496;nxt=dist.copy();np.minimum.at(nxt,V,candidate)
  if np.array_equal(nxt,dist):
   potential=dist-dist.min();R=int(potential.max());assert np.all(496+potential[V]<=w+potential[U])
   margin=632-R;bound=Fraction(1102928+R,4696)
   raw=potential.astype('<i8').tobytes();filename=f'floor{floor}-potential.i64.gz';(HERE/filename).write_bytes(gzip.compress(raw,mtime=0))
   result.update(status='CONDITIONAL_234_POTENTIAL' if margin>0 else 'CONVERGED_COMPARISON_NOT_234',mean='496',potential_range=R,strict_margin=margin,comparison_bound=str(bound),potential_file=filename,potential_sha256=sha(raw),all_edge_inequalities_checked=True)
   break
  eligible=np.flatnonzero((candidate==nxt[V])&(nxt[V]<dist[V]));pred=np.full(N,-1,dtype=np.int32)
  np.maximum.at(pred,V[eligible],eligible);assert np.all(pred[nxt<dist]>=0);parents.append(pred);dist=nxt
  deficit=-int(dist.min())
  if deficit>=632:
   end=int(np.argmin(dist));es=[]
   for layer in reversed(parents):
    e=int(layer[end])
    if e>=0:es.append(e);end=int(U[e])
   es.reverse();parent.valid_walk(es,a);total=sum(int(w[e]) for e in es)
   assert len(es)<=iteration<=227 and 496*len(es)-total==deficit
   result.update(status='ALL_SLOPE_RANGE_OBSTRUCTION',length=len(es),total_weight=total,deficit=deficit,criterion_ceiling=112592-deficit,walk=parent.rows(es,a,shape,w));break
 result.update(iterations=iteration,seconds=time.monotonic()-before);save(f'floor{floor}.json',result);candidates.append(result)
 print({k:result[k] for k in ['floor','status','iterations','seconds']},'range',result.get('potential_range'),'deficit',result.get('deficit'),flush=True)
 del dist,parents
 if result['status']=='CONDITIONAL_234_POTENTIAL':high=floor;highdata=result
 elif result['status']=='ALL_SLOPE_RANGE_OBSTRUCTION':low=floor;lowdata=result
 else:break
assert frozen=={p.name:sha(p.read_bytes()) for p in PARENT.iterdir() if p.is_file()},'Parent experiment changed'
status='SHARP_FIXED_GRAPH_SINGLE_FLOOR_THRESHOLD' if high-low==1 else 'BRACKET_WITH_UNRESOLVED_GAP'
result=dict(status=status,shape='012034',least_feasible_floor=high if high-low==1 else None,known_infeasible_floor=low,known_feasible_floor=high,candidates=candidates,feasible_certificate=highdata,obstruction_certificate=lowdata,numerical_seconds=time.monotonic()-START,search_budget_seconds=500,candidate_limit=5,parent_files_unchanged=True,input_pins_sha256=sha((HERE/'input-pins.json').read_bytes()),script_sha256=sha(Path(__file__).read_bytes()),recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),scope='One varying nonnegative integer floor, eight other full-profile floors fixed, pinned saved graph and boundary budget. Local and global proof obligations remain. No universal share floor or snake optimum claim.')
save('results.json',result);print(status,'bracket',low,high,'seconds',result['numerical_seconds'],flush=True)
