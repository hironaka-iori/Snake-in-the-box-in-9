"""One bounded native falsification attempt, preserving every model and valid cut."""
from pathlib import Path
from itertools import combinations
import argparse,datetime,hashlib,json,os,subprocess,sys,time
H=Path(__file__).resolve().parents[1];R=H.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def save(p,j):
 t=p.with_name(p.name+'.pending');t.write_text(json.dumps(j,indent=2)+'\n',encoding='utf-8');t.replace(p)
def verify(folder,meta):
 assert sha(folder/'base.cnf')==meta['cnf_sha256']
 for n,h in meta['source_files_sha256'].items():assert sha(R/n)==h,n
def resources():
 raw=subprocess.check_output(['powershell','-NoProfile','-Command',"$o=Get-CimInstance Win32_OperatingSystem;@{free_bytes=[long]$o.FreePhysicalMemory*1024;processes=@(Get-CimInstance Win32_Process | Where-Object {$_.Name -eq 'python.exe' -and $_.CommandLine -match '140-five-cycle-window.*probe(?:_short)?\.py'} | Select-Object ProcessId,CommandLine)}|ConvertTo-Json -Depth 4 -Compress"],text=True)
 j=json.loads(raw);assert j['free_bytes']>=1536*1024**2
 return j
def raw_cnf(nv,clauses):return (f'p cnf {nv} {len(clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in clauses)).encode('ascii')
def worker(folder,meta,parent):
 verify(folder,meta);save(folder/'worker-resources.json',resources())
 sys.dont_write_bytecode=True;sys.path[:0]=[str(R/'work/share_packages'),str(R/'work/solver_packages')]
 from pysat.solvers import Cadical153
 lines=(folder/'base.cnf').read_text().splitlines();nv,nc=map(int,lines[0].split()[2:])
 clauses=[list(map(int,line.split()[:-1])) for line in lines[1:]]
 assert len(clauses)==nc and raw_cnf(nv,clauses)==(folder/'base.cnf').read_bytes()
 state=dict(status='RUNNING',pid=os.getpid(),parent_pid=parent,calls=0,models=0,cycle_cuts=[],nominal_seconds=45)
 start=time.monotonic();save(folder/'worker-status.json',state)
 with Cadical153(bootstrap_with=clauses) as solver:
  while time.monotonic()-start<45:
   solver.conf_budget(1000);answer=solver.solve_limited();state['calls']+=1
   state['seconds']=time.monotonic()-start;save(folder/'worker-status.json',state)
   if answer is None:continue
   if answer is False:state['status']='UNSAT_UNCERTIFIED';break
   model=solver.get_model();state['models']+=1;n=state['models'];save(folder/f'model-{n:04d}.json',model)
   assignment={abs(x):x>0 for x in model}
   assert all(any(assignment[abs(l)]==(l>0) for l in c) for c in clauses)
   selected={v for v in range(512) if assignment[1+v]}
   flags={v for v in range(512) if assignment[513+v]}
   adj={v:[v^(1<<d) for d in range(9) if v^(1<<d) in selected] for v in selected}
   assert set(meta['window'])<=selected and all(len(x) in [1,2] for x in adj.values())
   assert flags=={v for v in selected if len(adj[v])==1} and len(flags)<=2
   assert not(flags&set(meta['forbidden_endpoints']))
   unseen=set(selected);components=[]
   while unseen:
    todo=[min(unseen)];comp=set()
    while todo:
     v=todo.pop()
     if v in comp:continue
     comp.add(v);todo.extend(adj[v])
    unseen-=comp;components.append(sorted(comp))
   cycles=[c for c in components if all(len(adj[v])==2 for v in c)]
   save(folder/f'selected-{n:04d}.json',dict(selected=sorted(selected),endpoints=sorted(flags),components=components,cycles=cycles))
   if cycles:
    for c in cycles:
     assert c and len(c)==len(set(c)) and all(sum((v^w).bit_count()==1 for w in c)>=2 for v in c)
     assert c not in state['cycle_cuts'];state['cycle_cuts'].append(c)
     clause=[-(1+v) for v in c];clauses.append(clause)
     save(folder/'cycle-cuts.json',state['cycle_cuts']);(folder/'current.cnf').write_bytes(raw_cnf(nv,clauses))
     save(folder/'worker-status.json',state);solver.add_clause(clause)
    if len(state['cycle_cuts'])>=64:state['status']='UNKNOWN_CUT_LIMIT';break
    continue
   assert len(components)==1 and len(flags)==2
   path=[];previous=None;current=min(flags)
   while True:
    assert current not in path;path.append(current)
    nxt=[v for v in adj[current] if v!=previous]
    if not nxt:break
    assert len(nxt)==1;previous,current=current,nxt[0]
   assert set(path)==selected and len(path)==len(selected)
   window=meta['window'];k=len(window)
   find=lambda p:next((i for i in range(len(p)-k+1) if p[i:i+k]==window),None)
   offset=find(path)
   if offset is None:path.reverse();offset=find(path)
   assert offset is not None
   assert all(((path[i]^path[j]).bit_count()==1)==(j==i+1) for i in range(len(path)) for j in range(i+1,len(path)))
   dirs=[(a^b).bit_length()-1 for a,b in zip(path,path[1:])]
   counts=[]
   for index in range(offset+1,offset+k-1):
    x=path[index]
    direct=sum(all(y not in selected for y in [x^(1<<a),x^(1<<b),x^(1<<a)^(1<<b)]) for a,b in combinations(range(9),2))
    inc={dirs[index-1],dirs[index]}
    corner=sum(x^(1<<a)^(1<<b) not in selected for a,b in combinations(range(9),2) if a not in inc and b not in inc)
    assert direct==corner;counts.append(direct)
   assert all(lo<=c<=hi for c,(lo,hi) in zip(counts,meta['bounds']))
   witness=dict(vertices=path,edges=len(path)-1,window_start=offset,directions=dirs,window=window,counts=counts,
    endpoints=[path[0],path[-1]],endpoint_distances=[[(e^c).bit_count() for c in meta['centres']] for e in [path[0],path[-1]]],
    pairs_checked=len(path)*(len(path)-1)//2,independently_validated=True)
   save(folder/'witness.json',witness);state['status']='ACTUAL_PATH_CHECKED';break
  else:state['status']='UNKNOWN'
 (folder/'final.cnf').write_bytes(raw_cnf(nv,clauses));verify(folder,meta)
 state.update(seconds=time.monotonic()-start,clauses=len(clauses),final_cnf_sha256=sha(folder/'final.cnf'),
  scope='Native bounded search. A checked actual path is a finite witness; native UNSAT is uncertified. UNKNOWN excludes nothing.')
 save(folder/'worker-status.json',state)
def main():
 ap=argparse.ArgumentParser();ap.add_argument('label',choices=['short']);ap.add_argument('--worker',action='store_true');args=ap.parse_args()
 folder=H/'work'/args.label;meta=json.loads((folder/'encoding.json').read_text())
 if args.worker:worker(folder,meta,int(os.environ['SNAKE140_PARENT']));return
 assert {p.name for p in folder.iterdir()}=={'base.cnf','encoding.json'},'Do not overwrite an attempt'
 verify(folder,meta);res=resources();assert all(x['ProcessId']==os.getpid() for x in res['processes'])
 (folder/'probe.exact.py').write_bytes(Path(__file__).read_bytes())
 state=dict(status='RUNNING',parent_pid=os.getpid(),resources=res,started_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),encoding_sha256=sha(folder/'encoding.json'),script_sha256=sha(Path(__file__)))
 env=os.environ.copy();env['SNAKE140_PARENT']=str(os.getpid())
 command=[sys.executable,'-B','-X','utf8',str(Path(__file__).resolve()),args.label,'--worker']
 with (folder/'stdout.log').open('w') as out,(folder/'stderr.log').open('w') as err:
  child=subprocess.Popen(command,stdout=out,stderr=err,env=env);state.update(worker_pid=child.pid,command=command);save(folder/'run-status.json',state)
  try:
   code=child.wait(timeout=90);state['exit_code']=code
   state['status']=json.loads((folder/'worker-status.json').read_text())['status'] if code==0 else 'FAILED'
  except subprocess.TimeoutExpired:
   subprocess.run(['taskkill','/PID',str(child.pid),'/T','/F'],capture_output=True);child.wait();state['status']='TIMEOUT'
 state.update(finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),preserved_files_sha256={p.name:sha(p) for p in folder.iterdir() if p.is_file() and p.name!='run-status.json'})
 save(folder/'run-status.json',state);print(json.dumps(state))
 if state['status']=='FAILED':raise SystemExit(1)
if __name__=='__main__':main()
