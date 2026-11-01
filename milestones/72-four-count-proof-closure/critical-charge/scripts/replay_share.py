"""Sequential, resumable Lean share-semantic checks with exact dependency hashes."""
from pathlib import Path
import hashlib,json,os,subprocess,sys,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[2];OUT=HERE/'share-proof';BUILD=OUT/'build/semantic';BUILD.mkdir(parents=True,exist_ok=True)
BIN=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin')
paths=[BUILD,Path((ROOT/'milestones/28-direct-share-certificates/build/latest.txt').read_text().strip())]
paths.extend(ROOT/p for p in ['milestones/20-middle-path-release/build','milestones/14-component-construction/build','milestones/07-window-223/lean/generated/geometry/support-ci2y7deg','work/spectral/.verification/strengthened-n8g3mwjy/core/.lake/build/lib/lean','work/spectral/.verification/strengthened-n8g3mwjy'])
env=os.environ.copy();env['PATH']=str(BIN)+';'+env['PATH'];env['LEAN_PATH']=';'.join(map(str,paths))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
record=OUT/'logs/semantic-record.json';rows=json.loads(record.read_text())['records'] if record.exists() else []
base=['LocalWindowCnf/ShareWindow120','Share120/Data']
modules=base+(['Share120/Structure','Share120/Shard00','Share120/Shard58'] if '--pilot' in sys.argv else ['Share120/Structure']+[f'Share120/Shard{i:02d}' for i in range(59)])
for name in modules:
 source=OUT/'lean'/(name+'.lean');dest=BUILD/(name+'.olean');dest.parent.mkdir(parents=True,exist_ok=True)
 deps={n:sha(OUT/'lean'/(n+'.lean')) for n in base if n!=name and (name not in base or base.index(n)<base.index(name))}
 previous=next((r for r in reversed(rows) if r['module']==name),None)
 if previous and previous.get('exit_code')==0 and previous['source_sha256']==sha(source) and previous['dependencies']==deps and dest.exists():continue
 log=OUT/'logs'/(name.replace('/','-')+'.log');start=time.monotonic()
 try:
  with log.open('w',encoding='utf-8') as f:r=subprocess.run([str(BIN/'lake.exe'),'env','lean','-s','65536','-R',str(OUT/'lean'),'-o',str(dest),str(source)],cwd=BIN.parent.parent/'mathlib',env=env,stdout=f,stderr=subprocess.STDOUT,timeout=300)
  code=r.returncode
 except subprocess.TimeoutExpired:code='TIMEOUT'
 row=dict(module=name,exit_code=code,source_sha256=sha(source),dependencies=deps,seconds=time.monotonic()-start)
 rows.append(row);record.write_text(json.dumps(dict(build=str(BUILD),records=rows),indent=2)+'\n')
 print(name,code,round(row['seconds'],2),flush=True)
 if code!=0:
  print(log.read_text(encoding='utf-8')[-3000:],flush=True);sys.exit(1)
print('Requested share semantic modules completed.',flush=True)
