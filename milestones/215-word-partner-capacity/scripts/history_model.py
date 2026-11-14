"""Exact fixed-base-history CSP; native search, not a Lean exclusion proof."""
from pathlib import Path
import argparse,collections,hashlib,itertools,json,os,time
from native_resources import snapshot
H=Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def pack(x,coords):return sum(((x>>a)&1)<<i for i,a in enumerate(coords))
def spread(x,coords):return sum(((x>>i)&1)<<a for i,a in enumerate(coords))
def valid(v):return len(v)==len(set(v)) and all(((x^v[j]).bit_count()==1)==(j==i+1) for i,x in enumerate(v) for j in range(i+1,len(v)))
def canon(v):
 out=[]
 for w in (v,v[::-1]):
  names={};seq=[]
  for x,y in zip(w,w[1:]):
   bit=(x^y).bit_length()-1
   if bit not in names:names[bit]=len(names)
   seq.append(names[bit])
  out.append(tuple(seq))
 return min(out)
def members(mask):
 while mask:
  bit=mask&-mask;yield bit.bit_length()-1;mask-=bit
def model(seed,block):
 assert seed[0]==0
 size=1<<len(block);base=[i for i in range(8) if i not in block];zs=[pack(x,base) for x in seed];us=[pack(x,block) for x in seed]
 group=[0]
 for i in range(1,len(seed)):group.append(group[-1]+(zs[i]==zs[i-1]))
 n=group[-1]+1;original=[None]*n
 for g,u in zip(group,us):
  assert original[g] is None or original[g]==u
  original[g]=u
 domains=[sum(1<<u for u in range(size) if u.bit_count()%2==i%2) for i in range(n)]
 assert all(x.bit_count()%2==i%2 for i,x in enumerate(original))
 rows={};cache={}
 for i in range(len(seed)):
  for j in range(i+1,len(seed)):
   bd=(zs[i]^zs[j]).bit_count();consecutive=j==i+1
   if bd>=2:
    assert not consecutive
    continue
   x,y=group[i],group[j]
   key=(bd,consecutive,domains[y])
   if key not in cache:cache[key]=[sum(1<<v for v in members(domains[y]) if (bd>0 or u!=v) and ((bd+(u^v).bit_count()==1)==consecutive)) for u in range(size)]
   relation=cache[key]
   if x==y:domains[x]&=sum(1<<u for u in members(domains[x]) if relation[u]>>u&1)
   elif (x,y) in rows:rows[x,y]=[a&b for a,b in zip(rows[x,y],relation)]
   else:rows[x,y]=relation
 nogoods=[];witnesses=[]
 for reverse,source in [(False,seed),(True,[v^seed[-1] for v in seed[::-1]])]:
  columns=[tuple((v>>i)&1 for v in source) for i in range(8)];fixed={};possible=True
  for output in base:
   wanted=tuple((v>>output)&1 for v in seed)
   if wanted not in columns:possible=False;break
   fixed[output]=columns.index(wanted)
  if not possible:continue
  assert len(set(fixed.values()))==len(fixed)
  for inputs in itertools.permutations(sorted(set(range(8))-set(fixed.values()))):
   mapping={**fixed,**dict(zip(block,inputs))}
   image=[sum(((v>>mapping[i])&1)<<i for i in range(8)) for v in source]
   values=[None]*n
   for g,v in zip(group,image):
    u=pack(v,block);assert values[g] is None or values[g]==u;values[g]=u
   if values[1]!=1:continue
   assert valid(image) and canon(image)==canon(seed)
   assert all(domains[i]>>v&1 for i,v in enumerate(values))
   assert all(table[values[x]]>>values[y]&1 for (x,y),table in rows.items())
   if values not in nogoods:
    nogoods.append(values);witnesses.append(dict(reverse=reverse,output_to_input=[mapping[i] for i in range(8)],vertices=image))
 domains[0]=1;domains[1]=2
 assert nogoods
 return dict(block=block,base=base,z=zs,group=group,variables=n,domains=domains,constraints=[dict(x=x,y=y,rows=t) for (x,y),t in sorted(rows.items())],nogoods=nogoods,excluded_witnesses=witnesses)
def search(data,seconds,nodelimit):
 n=data['variables'];size=1<<len(data['block']);arcs={};neighbours=[set() for _ in range(n)]
 for c in data['constraints']:
  x,y,t=c['x'],c['y'],c['rows'];arcs[x,y]=t
  arcs[y,x]=[sum(1<<u for u in range(size) if t[u]>>v&1) for v in range(size)]
  neighbours[x].add(y);neighbours[y].add(x)
 start=time.monotonic();nodes=0;removals=0
 def propagate(ds):
  nonlocal removals
  queue=collections.deque(arcs);queued=set(arcs)
  while True:
   while queue:
    x,y=queue.popleft();queued.discard((x,y));table=arcs[x,y];before=ds[x]
    after=sum(1<<u for u in members(before) if table[u]&ds[y])
    if after==before:continue
    removals+=(before^after).bit_count();ds[x]=after
    if not after:return False
    for z in neighbours[x]:
     if z!=y and (z,x) not in queued:queue.append((z,x));queued.add((z,x))
   changed=False
   for forbidden in data['nogoods']:
    if any(not (ds[i]>>v&1) for i,v in enumerate(forbidden)):continue
    free=[i for i in range(n) if ds[i].bit_count()>1]
    if not free:return False
    if len(free)==1:
     x=free[0];ds[x]&=~(1<<forbidden[x]);removals+=1;changed=True
     if not ds[x]:return False
     for y in neighbours[x]:
      if (y,x) not in queued:queue.append((y,x));queued.add((y,x))
   if not changed:return True
 def visit(ds):
  nonlocal nodes
  nodes+=1
  if nodes>nodelimit or time.monotonic()-start>seconds:raise TimeoutError
  if not propagate(ds):return None
  choices=[i for i in range(n) if ds[i].bit_count()>1]
  if not choices:return [next(members(s)) for s in ds]
  x=min(choices,key=lambda i:(ds[i].bit_count(),-len(neighbours[i]),i))
  for v in members(ds[x]):
   nxt=ds[:];nxt[x]=1<<v;result=visit(nxt)
   if result is not None:return result
  return None
 status='EXHAUSTED';solution=None
 try:
  solution=visit(data['domains'][:])
  if solution is not None:status='FOUND'
 except TimeoutError:status='LIMIT'
 return dict(status=status,solution=solution,nodes=nodes,removals=removals,seconds=time.monotonic()-start)
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--seconds',type=float,default=3);ap.add_argument('--nodes',type=int,default=100000);ap.add_argument('--index',type=int);ap.add_argument('--block-size',type=int,choices=[4,5,6],default=5);ap.add_argument('--stop-after-new',action='store_true');a=ap.parse_args()
 gate=snapshot();assert not gate['errors'] and not gate['processes'] and gate['free_bytes']>=1024**3,gate
 lock=H/'data/history-search.lock';assert not lock.exists();lock.write_text(str(os.getpid())+'\n')
 source=H/'data/lower-dimensional-input.json';seed=json.loads(source.read_bytes())['8']['vertices'];assert valid(seed)
 blocks=list(itertools.combinations(range(8),a.block_size));indices=list(range(len(blocks)) if a.index is None else [a.index]);records=[];start=time.monotonic();outstatus='COMPLETE'
 try:
  for index in indices:
   gate_now=snapshot()
   if gate_now['errors'] or gate_now['processes'] or gate_now['free_bytes']<768*1024**2:raise RuntimeError(gate_now)
   data=model(seed,list(blocks[index]));modelpath=H/'data'/f'model-{a.block_size}-{index}.json';modelpath.write_text(json.dumps(data,separators=(',',':'))+'\n')
   result=search(data,a.seconds,a.nodes);result.update(index=index,block=list(blocks[index]),variables=data['variables'],constraints=len(data['constraints']),excluded=len(data['nogoods']),model_sha256=sha(modelpath))
   if result['solution'] is not None:
    v=[spread(z,data['base'])|spread(result['solution'][g],data['block']) for z,g in zip(data['z'],data['group'])]
    assert valid(v) and all(pack(x,data['base'])==pack(y,data['base']) for x,y in zip(seed,v))
    assert all(c['rows'][result['solution'][c['x']]]>>result['solution'][c['y']]&1 for c in data['constraints'])
    result.update(vertices=v,new_class=canon(v)!=canon(seed),endpoint_distance=(v[0]^v[-1]).bit_count(),canonical=list(canon(v)))
   records.append(result)
   (H/'data/search-progress.json').write_text(json.dumps(dict(status='RUNNING',pid=os.getpid(),completed=len(records),total=len(indices),records=records),indent=2)+'\n')
   print(index,result['status'],'nodes',result['nodes'],'seconds',round(result['seconds'],3),'new_class',result.get('new_class'),flush=True)
   if a.stop_after_new and result.get('new_class'):outstatus='STOPPED_AFTER_WITNESS';break
  out=dict(status=outstatus,block_size=a.block_size,completed=len(records),total=len(indices),records=records,source_sha256=sha(source),script_sha256=sha(__file__),seconds=time.monotonic()-start,resource_gate=gate,scope='Native exact fixed-base-history models with normalized first block edge and exclusion of explicitly witnessed isometric assignments. EXHAUSTED is a native finite exclusion, not a Lean proof; LIMIT proves no exclusion.')
  (H/'data'/('history-search-'+str(a.block_size)+('' if a.index is None else '-'+str(a.index))+'.json')).write_text(json.dumps(out,indent=2)+'\n');(H/'data/search-progress.json').write_text(json.dumps(out,indent=2)+'\n')
 finally:lock.unlink()
if __name__=='__main__':main()
