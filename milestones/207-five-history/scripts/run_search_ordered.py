"""One-worker exact coordinate-history search with saved inputs and receipts."""
from pathlib import Path
import argparse,ctypes,hashlib,itertools,json,os,subprocess,time
from native_resources import snapshot,kernel,psapi,PROCESS_MEMORY_COUNTERS_EX
from history_model import model,pack,spread,valid,canon
H=Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def private_bytes(pid):
 h=kernel.OpenProcess(0x1000,False,pid)
 if not h:return None
 try:
  c=PROCESS_MEMORY_COUNTERS_EX();c.cb=ctypes.sizeof(c)
  return int(c.PrivateUsage) if psapi.GetProcessMemoryInfo(h,ctypes.byref(c),c.cb) else None
 finally:kernel.CloseHandle(h)
def save(p,d):p.write_text(json.dumps(d,indent=2)+'\n',encoding='utf-8')
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--block-size',type=int,choices=[5,6],default=5);ap.add_argument('--seconds',type=float,default=10);ap.add_argument('--nodes',type=int,default=100000000);ap.add_argument('--index',type=int);ap.add_argument('--no-lex',action='store_true');ap.add_argument('--start',type=int,default=13);a=ap.parse_args()
 waiting=[];gate=snapshot();deadline=time.monotonic()+55
 while gate['errors'] or gate['processes'] or gate['free_bytes']<1024**3:
  waiting.append(gate)
  if time.monotonic()>=deadline:
   save(H/'logs'/('resource-wait-'+str(time.time_ns())+'.json'),waiting)
   raise RuntimeError('Startup resource threshold not reached; no search started.')
  time.sleep(1);gate=snapshot()
 if waiting:save(H/'logs'/('resource-wait-'+str(time.time_ns())+'.json'),waiting+[gate])
 lock=H/'data/history-search.lock';assert not lock.exists();lock.write_text(str(os.getpid()))
 seed=json.loads((H/'data/lower-dimensional-input.json').read_bytes())['8']['vertices'];assert valid(seed)
 blocks=list(itertools.combinations(range(8),a.block_size));frequencies={i:sum((x^y)==1<<i for x,y in zip(seed,seed[1:])) for i in range(8)};indices=sorted(range(a.start,len(blocks)),key=lambda j:(sum(frequencies[i] for i in blocks[j]),j)) if a.index is None else [a.index]
 tag=str(a.block_size)+'-ordered-from-'+str(a.start)+('-no-lex' if a.no_lex else '')+('' if a.index is None else '-'+str(a.index));records=[];start=time.monotonic();status='COMPLETE'
 binary=H/'build/history_solver.exe';pins={str(p.relative_to(H)):sha(p) for p in [Path(__file__),H/'scripts/history_model.py',H/'scripts/history_solver.c',H/'scripts/native_resources.py',binary,H/'data/lower-dimensional-input.json']}
 try:
  for index in indices:
   state=snapshot();assert not state['errors'] and not state['processes'] and state['free_bytes']>=768*1024**2,state
   m=model(seed,list(blocks[index]));size=1<<a.block_size;n=m['variables'];perms=[]
   if not a.no_lex:
    for rest in itertools.permutations(range(1,a.block_size)):
     order=(0,)+rest;perms.append([sum(((u>>order[i])&1)<<i for i in range(a.block_size)) for u in range(size)])
   folder=H/'data'/('case-'+tag+'-'+str(index));folder.mkdir();save(folder/'model.json',m);save(folder/'permutations.json',perms)
   lines=[f'{n} {size} {len(m["constraints"])} {len(m["nogoods"])} {len(perms)}',f'{a.seconds} {a.nodes}',' '.join(map(str,m['domains']))]
   lines += [f'{c["x"]} {c["y"]} '+' '.join(map(str,c['rows'])) for c in m['constraints']]
   lines += [' '.join(map(str,v)) for v in m['nogoods']]+[' '.join(map(str,v)) for v in perms]
   (folder/'input.txt').write_text('\n'.join(lines)+'\n');before=time.monotonic();samples=[];stop=None
   with (folder/'input.txt').open('rb') as inp,(folder/'stdout.json').open('wb') as out,(folder/'stderr.txt').open('wb') as err:
    child=subprocess.Popen([str(binary)],stdin=inp,stdout=out,stderr=err,cwd=H)
    while child.poll() is None:
     s=snapshot();private=private_bytes(child.pid);samples.append(dict(free_bytes=s['free_bytes'],private_bytes=private))
     if s['errors'] or s['processes']:stop='RESOURCE_QUERY_OR_OTHER_LEAN'
     elif s['free_bytes']<768*1024**2:stop='LOW_FREE_MEMORY'
     elif private is not None and private>256*1024**2:stop='MEMORY_LIMIT'
     elif time.monotonic()-before>a.seconds+5:stop='WALL_TIMEOUT'
     if stop:child.terminate();break
     time.sleep(.2)
    code=child.wait(timeout=30)
   if stop or code:
    record=dict(index=index,block=list(blocks[index]),status='INTERRUPTED',stop=stop,exit_code=code,resource_samples=samples);save(folder/'record.json',record);records.append(record);status='INTERRUPTED';break
   result=json.loads((folder/'stdout.json').read_bytes());assert result['status'] in ['EXHAUSTED','LIMIT','FOUND']
   result.update(index=index,block=list(blocks[index]),folder=str(folder.relative_to(H)),model_sha256=sha(folder/'model.json'),input_sha256=sha(folder/'input.txt'),resource_samples=samples,exit_code=code)
   if result['solution'] is not None:
    sol=result['solution'];assert len(sol)==n
    assert all(m['domains'][i]>>u&1 for i,u in enumerate(sol))
    assert all(c['rows'][sol[c['x']]]>>sol[c['y']]&1 for c in m['constraints'])
    assert sol not in m['nogoods'] and all(tuple(sol)<=tuple(p[u] for u in sol) for p in perms)
    vertices=[spread(z,m['base'])|spread(sol[g],m['block']) for z,g in zip(m['z'],m['group'])]
    assert valid(vertices) and all(pack(x,m['base'])==pack(y,m['base']) for x,y in zip(seed,vertices))
    result.update(vertices=vertices,new_class=canon(vertices)!=canon(seed),endpoint_distance=(vertices[0]^vertices[-1]).bit_count(),canonical=list(canon(vertices)))
   save(folder/'record.json',result);records.append(result)
   save(H/'data/search-progress.json',dict(status='RUNNING',pid=os.getpid(),completed=len(records),total=len(indices),records=records))
   print(index,result['status'],'nodes',result['nodes'],'seconds',result['seconds'],'new_class',result.get('new_class'),flush=True)
   if result.get('new_class'):status='STOPPED_AFTER_WITNESS';break
  assert all(sha(H/p)==h for p,h in pins.items())
  report=dict(status=status,block_size=a.block_size,lex=not a.no_lex,completed=len(records),total=len(indices),records=records,seconds=time.monotonic()-start,input_pins=pins,resource_gate=gate,scope='Native enumeration only. LIMIT and INTERRUPTED prove no exclusion. Lex normalization preserves whole cube-isometry classes; full Lean search certificate pending.')
  save(H/'data'/('search-'+tag+'.json'),report);save(H/'data/search-progress.json',report)
 finally:lock.unlink()
if __name__=='__main__':main()
