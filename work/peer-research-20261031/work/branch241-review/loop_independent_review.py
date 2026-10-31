"""Rebuild exact CNF; review saved full models and geometric cut provenance."""
from pathlib import Path
import gzip,json,sys,hashlib
from collections import Counter
R=Path(__file__).resolve().parent;B=R.parent/'branch241-next';sys.path[:0]=[str(B),str(B/'encoding')]
from github_query import build
from independent_encoding_review import direct,Geometry
from rup_check import check

def components(S):
 S=set(S);adj={x:[y for y in S if (x^y).bit_count()==1] for x in S};seen=set();out=[]
 for x in S:
  if x in seen:continue
  stack=[x];seen.add(x);vs=[]
  while stack:
   v=stack.pop();vs.append(v)
   for w in adj[v]:
    if w not in seen:seen.add(w);stack.append(w)
  out.append((vs,all(len(adj[v])==2 for v in vs)))
 return out

def run():
 rows=[];G=Geometry(9)
 for folder in sorted(R.glob('loop_k*_cap*_r*')):
  state=json.loads(gzip.decompress((folder/'checkpoint.json.gz').read_bytes()));meta=state['meta'];E,geo,m,got=build(meta['path'],meta['cap_scaled21'],radius=meta['geometry_radius']);base=E.cnf.clauses
  static_count=0
  if (folder/'static8.json.gz').exists():
   from all8_cycles import enumerate_all8
   static=json.loads(gzip.decompress((folder/'static8.json.gz').read_bytes()));expected_static,static_meta=enumerate_all8(E.var)
   assert {tuple(c) for c in static['cycles']}==set(expected_static)
   assert static['allowed']==sorted(E.var)
   fullcycles=static['cycles'];activecycles=fullcycles
   if meta.get('static8_count',len(fullcycles))!=len(fullcycles):
    activecycles=[c for c in fullcycles if not set(c)&E.forbidden]
    assert len(activecycles)==meta['static8_count']
    assert all([-E.var[v]] in base for v in E.forbidden)
   base=base+[[-E.var[v] for v in c] for c in activecycles];static_count=len(activecycles)
  assert hashlib.sha256(json.dumps(base,separators=(',',':')).encode()).hexdigest()==state['CNF_sha256']
  for cut in state['cuts']:
   vs=cut['vertices'];cs=components(vs);assert len(set(vs))==len(vs) and len(cs)==1 and cs[0][1]
   if cut.get('kind')=='exhaustive_rooted8':
    assert len(vs)==8 and set(meta['path'][:3])<=set(vs)
   else:
    md=json.loads(gzip.decompress((folder/cut['model_file']).read_bytes()));assert set(vs)<=set(md['selected'])
  rootlens=Counter();cyclesizes=Counter();modelcount=0
  for h in state['history']:
   if h['status']!='SAT':continue
   md=json.loads(gzip.decompress((folder/h['model_file']).read_bytes()));a={abs(l):l>0 for l in md['model']};S={v for v,var in E.var.items() if a[var]};assert S==set(md['selected'])
   clauses=base+[[-E.var[v] for v in cut['vertices']] for cut in state['cuts'][:md['cuts_before']]]
   assert all(any(a[abs(l)]==(l>0) for l in c) for c in clauses)
   cost=sum(21*al+2*e2+e3+bonus for al,e2,e3,bonus,adaptive in [direct(G,S,x) for x in meta['path'][1:-1]])
   assert cost==md['score_scaled21']<=meta['cap_scaled21']
   for vs,cyc in components(S):
    if cyc:cyclesizes[len(vs)]+=1
    if meta['path'][1] in vs:rootlens[(len(vs),cyc)]+=1
   modelcount+=1
  finalbase=base+[[-E.var[v] for v in cut['vertices']] for cut in state['cuts']]
  ck=check(finalbase,state['prefix_proof'],require_empty=state['status']=='UNSAT')
  rows.append({'folder':folder.name,'snapshot_status':state['status'],'SAT_models_independently_rechecked':modelcount,'cuts_checked':len(state['cuts']),'static8_cuts_checked':static_count,'root_component_sizes_and_cycle_flag':{str(k):v for k,v in rootlens.items()},'cycle_lengths_over_all_models':dict(cyclesizes),'retained_learning_check':ck})
 (R/'loop_independent_results.json').write_text(json.dumps(rows,indent=2));print(json.dumps(rows,indent=2))
if __name__=='__main__':run()



