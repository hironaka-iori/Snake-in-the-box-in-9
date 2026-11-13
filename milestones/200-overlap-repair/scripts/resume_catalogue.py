from pathlib import Path
import hashlib,json,subprocess,sys,time
from native_resources import snapshot
H=Path(__file__).resolve().parents[1];R=H.parents[1]
catalogue=H/'data/low-overlap-maps.json';d=json.loads(catalogue.read_bytes());start=time.monotonic();waits=[];rows=[];state='RUNNING'
dest=H/'data/catalogue-d4.json';stamp=str(time.time_ns())
if dest.exists():(H/'logs'/('catalogue-before-resume-'+stamp+'.json')).write_bytes(dest.read_bytes())
def key(c):return c['permutation'],c['translation']
prior=[(p,json.loads(p.read_bytes())) for p in (H/'data').glob('coupled100-case*-d4.json')]
for i in d['representatives']:
 matches=[(p,r) for p,r in prior if key(d['rows'][i])==key(r['case'])]
 target=H/f'data/catalogue-d4-case{i}.json'
 if target.exists():matches.append((target,json.loads(target.read_bytes())))
 if matches:
  p,r=matches[0];rows.append(dict(case=i,record=p.name,status=r['status'],seconds=r['seconds'],reused=True,sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
for i in d['representatives']:
 if any(r['case']==i for r in rows):continue
 tag=f'catalogue-d4-case{i}';p=H/'data'/(tag+'.json')
 while True:
  snap=snapshot()
  if snap['errors'] or snap['processes'] or snap['free_bytes']<1280*1024**2:
   waits.append(snap)
   if time.monotonic()-start>150:state='DEFERRED';break
   time.sleep(3);continue
  run=subprocess.run([sys.executable,'-B','-X','utf8',str(H/'scripts/coupled_catalogue.py'),'--case',str(i),'--omissions','4','--seconds','20','--tag',tag],cwd=R,capture_output=True,text=True)
  output=run.stdout+run.stderr;(H/'logs'/(tag+'-resume-'+str(time.time_ns())+'.log')).write_text(output,encoding='utf-8');print(output,flush=True)
  if run.returncode:
   if 'AssertionError:' in output and 'free_bytes' in output and time.monotonic()-start<150:time.sleep(3);continue
   state='STOPPED';break
  r=json.loads(p.read_bytes());rows.append(dict(case=i,record=p.name,status=r['status'],seconds=r['seconds'],reused=False,sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
  if r['witness'] is not None:state='WITNESS'
  break
 dest.write_text(json.dumps(dict(status=state,rows=rows,waits=waits),indent=2)+'\n')
 if state!='RUNNING':break
 if time.monotonic()-start>180:state='DEFERRED';break
if len(rows)==len(d['representatives']) and state=='RUNNING':state='COMPLETE'
out=dict(status=state,rows=sorted(rows,key=lambda r:r['case']),waits=waits,seconds=time.monotonic()-start,catalogue_sha256=hashlib.sha256(catalogue.read_bytes()).hexdigest(),all_infeasible=state=='COMPLETE' and all(r['status']=='INFEASIBLE' for r in rows),scope='One representative of each inverse-map pair; previous matching-map results reused. Complete native exclusion only if every representative is INFEASIBLE. Unknown or resource-deferred cases remain open.')
dest.write_text(json.dumps(out,indent=2)+'\n');print('CATALOGUE_RESUME',state,'ALL_INFEASIBLE',out['all_infeasible'],flush=True)
