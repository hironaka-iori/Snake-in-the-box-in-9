"""Lower one pending floor by one on the pinned full conditional graph.
Read-only inputs. Writes only beside this script. No SAT, Lean or background jobs.
"""
from pathlib import Path
from fractions import Fraction
import datetime, gzip, hashlib, json, sys, time
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
OLD=ROOT/'milestones/72-four-count-proof-closure/critical-current'
sys.path.insert(0,str(ROOT/'work/solver_packages'))
import numpy as np
TAG='countfree16-all-except012034x20-except012310x12'
SHAPES=['012031','012032','012034','012301','012304','012310','012314','012340','012345']
FLOORS=[16,16,20,16,16,12,16,16,16]
TESTS=[(7301,1),(7302,2),(7303,3),(7307,7),(7308,8)]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda b:hashlib.sha256(b).hexdigest()
def save(name,obj):
 (HERE/name).write_text(json.dumps(obj,indent=2)+'\n',encoding='utf-8')
def canon(word):
 names={};return ''.join(str(names.setdefault(int(x),len(names))) for x in word)
def setup():
 inputs=[OLD/'data/source-proved-model.json',OLD/'build/source-graph.npz',OLD/f'data/{TAG}-model.json',OLD/f'build/{TAG}-graph.npz',OLD/f'data/{TAG}-analysis.json',ROOT/'milestones/59-extended-share-window/extended/data/model.json',ROOT/'milestones/74-graph-interpretation-audit/optimization/data/catalogue-tests.json']
 inputs+=sorted((ROOT/'milestones/93-defined-graph-potential/data').glob('*-range-certificate.json'))
 meta=read(inputs[0]);fullmeta=read(inputs[2])
 with np.load(inputs[1]) as z:a={k:z[k] for k in z.files}
 assert len(a['U'])==4947008 and meta['states']==1601856
 for k,h in meta['arrays_sha256'].items():assert sha(a[k].tobytes())==h,k
 ext=read(inputs[5])['extensions']
 shapes=np.array([SHAPES.index(min(canon(ds[-6:]),canon(ds[-6:][::-1]))) for ds in ext],dtype=np.int8)[a['direction']]
 entering=120*(a['count_code'].astype(np.int64)%6+1)
 full=np.maximum(a['weight'],entering+np.asarray(FLOORS,dtype=np.int64)[shapes])
 with np.load(inputs[3]) as z:
  for k in ['U','V','direction','history','count_code']:assert np.array_equal(a[k],z[k]),k
  assert np.array_equal(full,z['weight'])
  for k,h in fullmeta['arrays_sha256'].items():assert sha(z[k].tobytes())==h,k
 cycle=[int(r['edge']) for r in read(inputs[4])['cycle']]
 paths=[]
 for row in read(inputs[6])['tests']:
  if 'walk' in row:paths.append(('74/'+row['shape'],[int(e['edge']) for e in row['walk']]))
 for p in inputs[7:]:
  d=read(p);paths.append(('93/'+d['model'],[int(e['edge']) for e in d['path']]))
 pins={str(p.relative_to(ROOT)):sha(p.read_bytes()) for p in inputs}
 return meta,a,shapes,entering,full,cycle,paths,pins

def rows(edges,a,shape,w):
 return [dict(edge=int(e),u=int(a['U'][e]),v=int(a['V'][e]),direction=int(a['direction'][e]),history=int(a['history'][e]),count_code=int(a['count_code'][e]),shape=SHAPES[int(shape[e])],weight=int(w[e]),base_weight=int(a['weight'][e])) for e in edges]
def valid_walk(es,a,closed=False):
 assert es and all(int(a['V'][x])==int(a['U'][y]) for x,y in zip(es,es[1:]))
 if closed:assert int(a['V'][es[-1]])==int(a['U'][es[0]])
def weaken(index,a,shape,entering,full):
 w=full.copy();selected=shape==index
 w[selected]=np.maximum(a['weight'][selected],entering[selected]+FLOORS[index]-1)
 assert np.all((full-w==0)|(full-w==1))
 return w

def inspect():
 start=time.monotonic();meta,a,shape,entering,full,cycle,paths,pins=setup();out=[]
 valid_walk(cycle,a,True)
 for case,index in TESTS:
  w=weaken(index,a,shape,entering,full);mu=Fraction(sum(int(w[e]) for e in cycle),len(cycle))
  witnesses=[]
  for origin,es in paths:
   valid_walk(es,a);total=sum(int(w[e]) for e in es);deficit=mu*len(es)-total
   ceiling=(227-len(es))*mu+total
   witnesses.append(dict(origin=origin,length=len(es),total_weight=total,deficit_at_cycle_mean=str(deficit),criterion_ceiling=str(ceiling),decisive=len(es)<=227 and ceiling<=111960,walk=rows(es,a,shape,w)))
  decisive=next((x for x in witnesses if x['decisive']),None)
  result=dict(case=case,shape=SHAPES[index],original_floor=FLOORS[index],tested_floor=FLOORS[index]-1,changed_edges=int(np.count_nonzero(w!=full)),cycle_mean=str(mu),cycle=rows(cycle,a,shape,w),saved_walk_tests=witnesses,status='IMMEDIATE_ALL_SLOPE_RANGE_OBSTRUCTION' if decisive else 'INCONCLUSIVE_SAVED_WITNESSES',weight_sha256=sha(w.tobytes()))
  out.append(result);print({k:result[k] for k in ['case','shape','tested_floor','changed_edges','cycle_mean','status']},flush=True)
 save('input-pins.json',dict(files=pins,source_arrays_sha256=meta['arrays_sha256'],full_floors=dict(zip(SHAPES,FLOORS)),script_sha256=sha(Path(__file__).read_bytes())))
 save('saved-witness-tests.json',dict(status='EXACT_SAVED_WITNESS_RECHECK',results=out,seconds=time.monotonic()-start,scope='Finite graph evidence under the full conditional profile, one specified floor lowered by one.'))

def run():
 start=time.monotonic();deadline=start+500
 meta,a,shape,entering,full,cycle,paths,pins=setup();initial=read(HERE/'saved-witness-tests.json')
 assert pins==read(HERE/'input-pins.json')['files']
 U,V,N=a['U'],a['V'],meta['states'];results=[]
 for case,index in TESTS:
  before=time.monotonic();old=next(x for x in initial['results'] if x['case']==case)
  w=weaken(index,a,shape,entering,full)
  result={k:old[k] for k in ['case','shape','original_floor','tested_floor','changed_edges','cycle','cycle_mean','weight_sha256']}
  assert result['weight_sha256']==sha(w.tobytes())
  if old['status']=='IMMEDIATE_ALL_SLOPE_RANGE_OBSTRUCTION':
   witness=next(x for x in old['saved_walk_tests'] if x['decisive']);result.update(status=old['status'],witness=witness)
  elif time.monotonic()>=deadline:
   result.update(status='UNRESOLVED_RUNTIME_BUDGET')
  else:
   mu=Fraction(result['cycle_mean']);p,d=mu.numerator,mu.denominator
   dist=np.zeros(N,dtype=np.int64);parents=[];result['status']='UNRESOLVED_ITERATION_LIMIT'
   for iteration in range(1,228):
    if time.monotonic()>=deadline:
     result['status']='UNRESOLVED_RUNTIME_BUDGET';break
    candidate=dist[U]+d*w-p;nxt=dist.copy();np.minimum.at(nxt,V,candidate)
    if np.array_equal(nxt,dist):
     potential=dist-dist.min();R=int(potential.max());assert np.all(p+potential[V]<=d*w+potential[U])
     bound=Fraction(1098960*d+8*p+R,4200*d+p);margin=227*p-111960*d-R
     raw=potential.astype('<i8').tobytes();filename=f'case{case}-potential.i64.gz'
     (HERE/filename).write_bytes(gzip.compress(raw,mtime=0))
     result.update(status='CONDITIONAL_234_POTENTIAL' if margin>0 else 'CONVERGED_COMPARISON_NOT_234',mean=str(mu),potential_range_scaled=R,potential_range=str(Fraction(R,d)),denominator=d,comparison_bound=str(bound),comparison_integer_bound=bound.numerator//bound.denominator,strict_margin_scaled=margin,potential_sha256=sha(raw),potential_file=filename,all_edge_inequalities_checked=True)
     break
    eligible=np.flatnonzero((candidate==nxt[V])&(nxt[V]<dist[V]));parent=np.full(N,-1,dtype=np.int32)
    np.maximum.at(parent,V[eligible],eligible);assert np.all(parent[nxt<dist]>=0);parents.append(parent);dist=nxt
    deficit=-int(dist.min())
    if deficit>=227*p-111960*d:
     endpoint=int(np.argmin(dist));es=[]
     for layer in reversed(parents):
      e=int(layer[endpoint])
      if e>=0:es.append(e);endpoint=int(U[e])
     es.reverse();valid_walk(es,a);total=sum(int(w[e]) for e in es)
     assert len(es)<=iteration<=227 and p*len(es)-d*total==deficit
     ceiling=Fraction((227-len(es))*p,d)+total;assert ceiling<=111960
     result.update(status='ALL_SLOPE_RANGE_OBSTRUCTION',length=len(es),total_weight=total,deficit_scaled=deficit,criterion_ceiling=str(ceiling),walk=rows(es,a,shape,w));break
   result['iterations']=iteration
   del dist,parents
  result['seconds']=time.monotonic()-before;results.append(result);save(f'case{case}.json',result)
  print({k:v for k,v in result.items() if k in ['case','shape','status','iterations','mean','potential_range','comparison_bound','strict_margin_scaled','seconds']},flush=True)
 elapsed=time.monotonic()-start
 save('results.json',dict(status='BOUNDED_EXACT_INTEGER_FLOOR_SENSITIVITY',results=results,numerical_seconds=elapsed,discovery_budget_seconds=500,full_floors=dict(zip(SHAPES,FLOORS)),input_pins_sha256=sha((HERE/'input-pins.json').read_bytes()),script_sha256=sha(Path(__file__).read_bytes()),recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),scope='Computational finite graph evidence only. Every other full-profile floor is retained. Local share proofs, reference premises, complete graph coverage, weight interpretation and potential replay remain separate. No new global snake bound.'))
 print('Total numerical discovery seconds',elapsed,flush=True)

if __name__=='__main__':
 inspect() if '--inspect' in sys.argv else run()
