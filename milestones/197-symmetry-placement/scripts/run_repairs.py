from pathlib import Path
import datetime,json,subprocess,sys,time
H=Path(__file__).resolve().parents[1];R=H.parents[1];d=json.loads((H/'data/placements.json').read_bytes())
cases=[i for i,row in enumerate(d['rows']) if len(row['full_path_conflicts'])==2];assert len(cases)==5
receipt=H/'data/repair-batch.json';assert not receipt.exists();rows=[];start=time.monotonic()
for i in cases:
 tag=f'repair-{i}-omit4';cmd=[sys.executable,'-B','-X','utf8',str(H/'scripts/repair.py'),'--case',str(i),'--free-ends','--omissions','4','--seconds','35','--tag',tag]
 result=subprocess.run(cmd,cwd=R,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 (H/'logs'/(tag+'.log')).write_text(result.stdout);print(result.stdout,flush=True)
 path=H/'data'/(tag+'.json');record=json.loads(path.read_bytes()) if path.exists() else None
 rows.append(dict(matching=i,tag=tag,exit_code=result.returncode,status=record['status'] if record else 'STARTUP_FAILED'))
 receipt.write_text(json.dumps(dict(status='RUNNING',rows=rows,seconds=time.monotonic()-start),indent=2)+'\n')
 if result.returncode or record['status'] in ['RESOURCE_LIMIT','WITNESS']:break
receipt.write_text(json.dumps(dict(status='COMPLETE' if len(rows)==len(cases) else 'STOPPED',rows=rows,seconds=time.monotonic()-start,utc=datetime.datetime.now(datetime.timezone.utc).isoformat()),indent=2)+'\n')
