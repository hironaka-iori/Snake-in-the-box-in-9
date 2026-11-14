"""Spare-capacity support continuation; explicit source model and native evidence."""
from pathlib import Path
import argparse,ctypes,hashlib,json,os,subprocess,time
from native_resources import snapshot,kernel,psapi,PROCESS_MEMORY_COUNTERS_EX
from history_model import pack,spread,valid,canon
H=Path(__file__).resolve().parents[1]
PREVIOUS=H.parent/'207-five-history'

def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def encoded(d):return (json.dumps(d,indent=2)+'\n').encode('utf-8')
def save(p,d):
 temporary=p.with_name(p.name+'.'+str(os.getpid())+'.tmp')
 with temporary.open('wb') as stream:
  stream.write(encoded(d));stream.flush();os.fsync(stream.fileno())
 os.replace(temporary,p)
def private_bytes(pid):
 handle=kernel.OpenProcess(0x1000,False,pid)
 if not handle:return None
 try:
  counter=PROCESS_MEMORY_COUNTERS_EX();counter.cb=ctypes.sizeof(counter)
  if not psapi.GetProcessMemoryInfo(handle,ctypes.byref(counter),counter.cb):return None
  return int(counter.PrivateUsage)
 finally:kernel.CloseHandle(handle)
def engine_pins():
 return {str(p.relative_to(H)):sha(p) for p in [Path(__file__),H/'scripts/spare_solver.c',H/'scripts/history_model.py',H/'scripts/native_resources.py',H/'build/spare_solver.exe',H/'data/lower-dimensional-input.json',H/'data/square-capacity.json']}
def resource_start():
 observations=[];deadline=time.monotonic()+55
 while True:
  gate=snapshot();observations.append(gate)
  if not gate['errors'] and not gate['processes'] and gate['free_bytes']>=1024**3:return gate,observations
  if time.monotonic()>=deadline:return None,observations
  time.sleep(1)

def prepare(index,pins):
 folder=H/'data'/f'case-{index}';statepath=folder/'state.json'
 if statepath.exists():
  state=json.loads(statepath.read_bytes());assert state['engine_pins']==pins
  for name,digest in state['model_pins'].items():assert sha(folder/name)==digest
  return folder,state
 raise RuntimeError('Create the explicit transfer record before continuation.')

def one_job(folder,state,seconds,node_limit,seed):
 assert state['status']=='OPEN' and state['frontier']
 gate,observations=resource_start()
 if gate is None:
  save(H/'logs'/('startup-wait-'+str(time.time_ns())+'.json'),observations);return state,'STARTUP_WAIT'
 assert not gate['processes']
 m=json.loads((folder/'model.json').read_bytes());perms=json.loads((folder/'permutations.json').read_bytes());tail=(folder/'input-tail.txt').read_bytes()
 statepath=folder/'state.json';before=statepath.read_bytes();assert json.loads(before)==state
 job=state['frontier'][-1];domains=job['domains'];n=m['variables'];size=64
 assert len(domains)==n and all(x and x&root==x for x,root in zip(domains,m['domains']))
 run=folder/('run-'+str(state['committed_jobs'])+'-'+str(time.time_ns()));run.mkdir()
 (run/'state-before.json').write_bytes(before)
 head=(f'{n} {size} {len(m["constraints"])} {len(m["nogoods"])} {len(perms)}\n{seconds} {node_limit}\n'+' '.join(map(str,domains))+'\n').encode('ascii')
 (run/'input-head.txt').write_bytes(head)
 receipt={'status':'RUNNING','job_id':job['id'],'state_before_sha256':hashlib.sha256(before).hexdigest(),'input_sha256':hashlib.sha256(head+tail).hexdigest(),'engine_pins':state['engine_pins'],'model_pins':state['model_pins'],'resource_gate':gate,'startup_observations':observations,'resource_samples':[]}
 started=time.monotonic();stop=None;stop_at=None;hard_stop=False
 with (run/'stdout.json').open('wb') as out,(run/'stderr.txt').open('wb') as err:
  child=subprocess.Popen([str(H/'build/spare_solver.exe')],stdin=subprocess.PIPE,stdout=out,stderr=err,cwd=run)
  receipt['pid']=child.pid;save(run/'receipt.json',receipt)
  try:
   child.stdin.write(head);child.stdin.write(tail);child.stdin.close()
   while child.poll() is None:
    sample=snapshot();private=private_bytes(child.pid)
    receipt['resource_samples'].append({'free_bytes':sample['free_bytes'],'private_bytes':private})
    reason=None
    if sample['errors'] or sample['processes']:reason='RESOURCE_QUERY_OR_OTHER_LEAN'
    elif sample['free_bytes']<768*1024**2:reason='LOW_FREE_MEMORY'
    elif private is None and child.poll() is None:reason='PROCESS_MEMORY_UNAVAILABLE'
    elif private is not None and private>256*1024**2:reason='MEMORY_LIMIT'
    elif time.monotonic()-started>seconds+5:reason='WALL_TIMEOUT'
    if reason and stop is None:
     stop=reason;stop_at=time.monotonic();(run/'STOP').write_text(reason+'\n')
    if stop_at is not None and time.monotonic()-stop_at>2:
     child.terminate();hard_stop=True;break
    time.sleep(.1)
   code=child.wait(timeout=30)
  finally:
   if child.poll() is None:child.terminate();child.wait(timeout=30)
   if not child.stdin.closed:child.stdin.close()
 receipt.update(exit_code=code,stop_reason=stop,hard_stop=hard_stop,wall_seconds=time.monotonic()-started)
 if code or hard_stop:
  receipt['status']='NOT_COMMITTED';save(run/'receipt.json',receipt)
  assert statepath.read_bytes()==before
  return state,'INTERRUPTED'
 result=json.loads((run/'stdout.json').read_bytes());status=result['status'];pending=result['pending'];solution=result['solution']
 assert status in ['EXHAUSTED','LIMIT','FOUND']
 if status=='LIMIT':assert pending and solution is None
 else:assert not pending
 if status=='EXHAUSTED':assert solution is None
 for part in pending:
  assert len(part)==n and all(x and x&old==x for x,old in zip(part,domains))
 assert all(any(not(x&y) for x,y in zip(a,b)) for i,a in enumerate(pending) for b in pending[i+1:])
 if status=='FOUND':
  assert len(solution)==n and all(domains[i]>>u&1 for i,u in enumerate(solution))
  assert all(c['rows'][solution[c['x']]]>>solution[c['y']]&1 for c in m['constraints'])
  assert solution not in m['nogoods'] and all(tuple(solution)<=tuple(p[u] for u in solution) for p in perms)
  vertices=[spread(z,m['base'])|spread(solution[g],m['block']) for z,g in zip(m['z'],m['group'])]
  assert valid(vertices) and all(pack(x,m['base'])==pack(y,m['base']) for x,y in zip(seed,vertices))
  result.update(vertices=vertices,new_class=canon(vertices)!=canon(seed),endpoint_distance=(vertices[0]^vertices[-1]).bit_count(),canonical=list(canon(vertices)))
  save(run/'witness.json',result)
 assert all(sha(H/name)==digest for name,digest in state['engine_pins'].items())
 assert all(sha(folder/name)==digest for name,digest in state['model_pins'].items())
 assert statepath.read_bytes()==before
 after=json.loads(before);after['committed_jobs']+=1;after['nodes']+=result['nodes'];after['seconds']+=result['seconds']
 if status=='FOUND':
  after['status']='FOUND';after['witness']=str((run/'witness.json').relative_to(H))
 else:
  rest=after['frontier'][:-1];children=[]
  for part in pending:
   children.append({'id':after['next_id'],'domains':part});after['next_id']+=1
  after['frontier']=rest+list(reversed(children));after['status']='OPEN' if after['frontier'] else 'EXHAUSTED'
 receipt.update(status='ACCEPTED_TRANSITION',solver_status=status,returned_frontier=len(pending),nodes=result['nodes'],solver_seconds=result['seconds'],stdout_sha256=sha(run/'stdout.json'),state_after_sha256=None)
 # The receipt is durable before replacing the current state. If replacement
 # is interrupted, the old job remains represented and can safely be repeated.
 after['receipts'].append(str((run/'receipt.json').relative_to(H)))
 afterbytes=encoded(after);receipt['state_after_sha256']=hashlib.sha256(afterbytes).hexdigest();save(run/'receipt.json',receipt)
 (run/'state-after.json').write_bytes(afterbytes);save(statepath,after)
 print('case',state['index'],'job',job['id'],status,'nodes',result['nodes'],'pending',len(after['frontier']),'stop',stop,flush=True)
 return after,('WITNESS' if status=='FOUND' else 'RESOURCE_STOP' if stop else 'CONTINUE')

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--indices',type=int,nargs='+',default=[22]);ap.add_argument('--jobs',type=int,default=20);ap.add_argument('--seconds',type=float,default=5);ap.add_argument('--nodes',type=int,default=100000000);a=ap.parse_args()
 assert a.jobs>0 and a.seconds>0 and a.nodes>0 and len(a.indices)==len(set(a.indices)) and all(i==22 for i in a.indices)
 lock=H/'data/history-search.lock';assert not lock.exists();lock.write_text(str(os.getpid())+'\n')
 try:
  pins=engine_pins();seed=json.loads((H/'data/lower-dimensional-input.json').read_bytes())['8']['vertices'];assert valid(seed)
  cases={i:prepare(i,pins) for i in a.indices};count=0;reason='BUDGET'
  for _ in range(a.jobs):
   for i in a.indices:
    folder,state=cases[i]
    if state['status']!='OPEN':continue
    state,outcome=one_job(folder,state,a.seconds,a.nodes,seed);cases[i]=(folder,state)
    if outcome in ['STARTUP_WAIT','INTERRUPTED','RESOURCE_STOP','WITNESS']:reason=outcome;break
    count+=1
   else:
    if not any(s['status']=='OPEN' for _,s in cases.values()):reason='COMPLETE';break
    continue
   break
  summary={'status':reason,'indices':a.indices,'case_states':{str(i):{'status':s['status'],'committed_jobs':s['committed_jobs'],'pending':len(s['frontier']),'nodes':s['nodes'],'seconds':s['seconds'],'state_sha256':sha(folder/'state.json')} for i,(folder,s) in cases.items()},'new_committed_jobs_without_resource_stop':count,'engine_pins':pins,'scope':'Native saved-domain continuation. An open frontier proves no exclusion; the generic coverage argument is separate from native replay certification.'}
  save(H/'data'/('spare-batch-'+str(time.time_ns())+'.json'),summary);save(H/'data/spare-search-progress.json',summary)
 finally:lock.unlink()
if __name__=='__main__':main()
