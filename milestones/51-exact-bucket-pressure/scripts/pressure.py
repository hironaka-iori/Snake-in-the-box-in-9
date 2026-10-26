"""Adaptive exact-bucket screens of the complete minimum-mean cycle family.

This is exploratory. No UNSAT result is promoted to a geometric theorem.
"""
from pathlib import Path
import concurrent.futures,collections,gzip,hashlib,itertools,json,sys,time,argparse
from fractions import Fraction
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'milestones/29-overlapping-share-windows/scripts'))
from joint import TaggedEncoding,window,Cadical153,census
sys.path.insert(0,str(ROOT/'milestones/42-six-count-state-model/scripts'))
import model,analyze
np=model.np
def read(p):return json.loads(p.read_text())
def write(p,r):p.parent.mkdir(exist_ok=True,parents=True);p.write_text(json.dumps(r,indent=2)+'\n')
def query(item):
 folder,index,row=item;folder=Path(folder);ds=row['directions'];cs=row['counts'];W=window(ds)
 bounds=[(6,21) if c==6 else (c,c) for c in cs];positions=[j+1 for j,c in enumerate(cs) if c==6];records=[]
 for delta in [None]+(list(range(12)) if positions else []):
  name=f'w{index:03d}-'+('plain' if delta is None else f'd{delta:02d}');file=folder/'data/queries'/(name+'.json')
  if file.exists():r=read(file)
  else:
   t=time.monotonic();e=TaggedEncoding(W,bounds,radius=4)
   cap=None if delta is None else 6*len(positions)+delta
   if cap is not None:
    lits=[-e.var[W[j]^(1<<a)^(1<<b)] for j in positions for a,b in itertools.combinations(range(9),2) if a not in (ds[j-1],ds[j]) and b not in (ds[j-1],ds[j])]
    e.atmost(lits,cap,('ends',))
   status='UNKNOWN';cuts=[];selected=None;report=None;seconds=4 if delta is None else 5
   with Cadical153(bootstrap_with=e.clauses) as solver:
    while time.monotonic()-t<seconds:
     solver.conf_budget(10000);ok=solver.solve_limited()
     if ok is None:continue
     if not ok:status='UNSAT';break
     assignment=solver.get_model();S={v for v in e.ball if assignment[e.var[v]-1]>0};report=census(S,9,W[1:-1]);report.pop('degree')
     if report['cycles']:
      for cycle in report['cycles']:cuts.append(cycle);solver.add_clause([-e.var[v] for v in cycle])
     else:status='SAT';selected=sorted(S);break
   r=dict(name=name,directions=ds,counts=cs,bounds=bounds,positions=positions,excess_cap=delta,joint_cap=cap,status=status,selected=selected,census=report if selected else None,cycle_cuts=cuts,seconds=time.monotonic()-t,scope='Necessary local model only; UNSAT requires certificate replay and geometric interpretation.')
   write(file,r)
  records.append({k:r[k] for k in ['name','directions','counts','positions','excess_cap','status','seconds']})
  print(folder.name,name,r['status'],round(r['seconds'],2),flush=True)
  if (delta is None and r['status']=='UNSAT') or (delta is not None and r['status']=='SAT'):break
 return records

def critical(folder,save=True):
 meta=read(folder/'data/model.json');res=read(folder/'data/analysis.json')
 with np.load(folder/'build/graph.npz') as z:a={k:z[k] for k in z.files}
 pi=np.frombuffer(gzip.decompress((folder/'data/potential.i64.gz').read_bytes()),dtype='<i8');mean=Fraction(res['integer_weight_mean'])
 ids=np.flatnonzero(~a['excluded']);U=a['U'][ids];V=a['V'][ids];W=168*a['count'][ids].astype(np.int64)+24*a['demand'][ids]+42*a['share'][ids]
 zero=mean.denominator*W+pi[U]-pi[V]==mean.numerator;ids=ids[zero]
 adj={};rev={}
 for u,v in zip(a['U'][ids],a['V'][ids]):
  u=int(u);v=int(v);adj.setdefault(u,[]).append(v);adj.setdefault(v,[]);rev.setdefault(v,[]).append(u);rev.setdefault(u,[])
 seen=set();order=[]
 for root in adj:
  if root in seen:continue
  seen.add(root);stack=[(root,iter(adj[root]))]
  while stack:
   node,children=stack[-1];nxt=next(children,None)
   if nxt is None:order.append(node);stack.pop();continue
   if nxt not in seen:seen.add(nxt);stack.append((nxt,iter(adj[nxt])))
 comp={};label=0
 for root in reversed(order):
  if root in comp:continue
  comp[root]=label;stack=[root]
  while stack:
   node=stack.pop()
   for nxt in rev[node]:
    if nxt not in comp:comp[nxt]=label;stack.append(nxt)
  label+=1
 ids=ids[np.array([comp[int(u)]==comp[int(v)] for u,v in zip(a['U'][ids],a['V'][ids])])]
 windows=collections.Counter()
 for i in ids:
  ds=meta['extensions'][int(a['direction'][i])];cs=analyze.decode(int(a['count_code'][i]),7)
  for start in range(3):
   word=ds[start:start+6];counts=tuple(cs[start:start+5]);key=min((model.canon(word),counts),(model.canon(word[::-1]),counts[::-1]));windows[key]+=1
 rows=[dict(directions=list(ds),counts=list(cs),occurrences=n) for (ds,cs),n in windows.most_common()]
 if save:write(folder/'data/critical-family.json',dict(edges=len(ids),states=len(set(a['U'][ids].tolist()+a['V'][ids].tolist())),windows=rows,scope='All zero-slack edges inside strongly connected components; exactly the critical cycle edges in this finite graph.'))
 return rows

def apply(prior,folder,rows):
 meta=read(prior/'data/model.json')
 with np.load(prior/'build/graph.npz') as z:a={k:z[k].copy() for k in z.files}
 oldex=a['excluded'].copy();oldd=a['demand'].copy();rules=[r for r in rows if r['status']=='UNSAT']
 for i,ds in enumerate(meta['extensions']):
  mask=a['direction']==i;codes=a['count_code'][mask];bad=a['excluded'][mask].copy();req=a['demand'][mask].copy()
  for start in range(3):
   for reverse in [False,True]:
    word=ds[start:start+6];shape=model.canon(word[::-1] if reverse else word)
    for row in rules:
     if shape!=tuple(row['directions']):continue
     hit=np.ones(len(codes),dtype=bool)
     for j,c in enumerate(row['counts'],1):
      p=start+6-j if reverse else start+j;hit&=(codes//6**(7-p)%6+1)==c
     if row['excess_cap'] is None:bad|=hit
     else:req=np.maximum(req,np.where(hit,row['excess_cap']+1,0))
  a['excluded'][mask]=bad;a['demand'][mask]=req
 meta.update(new_exclusions=int((a['excluded']&~oldex).sum()),new_demands=int(((a['demand']>oldd)&~a['excluded']).sum()),excluded_edges=int(a['excluded'].sum()),remaining_edges=int((~a['excluded']).sum()),new_rules=rules)
 meta['arrays_sha256']={k:hashlib.sha256(v.tobytes()).hexdigest() for k,v in a.items()};meta['scope']='Exploratory exact-bucket exclusions and common-window demand rules; new premises unreplayed, no new global bound.'
 write(folder/'data/model.json',meta);(folder/'build').mkdir(exist_ok=True);np.savez_compressed(folder/'build/graph.npz',**a)
 analyze.HERE=folder;analyze.main()

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--passes',type=int,default=3);ap.add_argument('--start',type=int,default=1);args=ap.parse_args();prior=ROOT/'milestones/50-three-count-return/excess-screen';summary=[]
 if args.start>1:prior=HERE/f'pass{args.start-1}';summary=read(HERE/'data/summary.json')[:args.start-1]
 for k in range(args.start,args.passes+1):
  folder=HERE/f'pass{k}';(folder/'data').mkdir(parents=True,exist_ok=True);rows=critical(prior,save=prior.is_relative_to(HERE))
  write(folder/'data/input-windows.json',rows);results=[]
  print('PASS',k,'windows',len(rows),flush=True)
  with concurrent.futures.ProcessPoolExecutor(max_workers=2) as pool:
   for records in pool.map(query,[(str(folder),i,r) for i,r in enumerate(rows)]):
    results.extend(records);write(folder/'data/survey.json',results)
  apply(prior,folder,results);res=read(folder/'data/analysis.json');critical(folder)
  summary.append(dict(pass_number=k,input_windows=len(rows),statuses=dict(collections.Counter(r['status'] for r in results)),mean=res['normalized_charge_mean'],potential_range=res['potential_range']))
  write(HERE/'data/summary.json',summary);prior=folder
if __name__=='__main__':main()
