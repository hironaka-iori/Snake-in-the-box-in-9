"""Sequential, resumable Lean share-semantic checks with exact dependency hashes."""
from pathlib import Path
import hashlib,json,os,subprocess,sys,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[2];OUT=HERE/'share-proof';BUILD=OUT/'build/semantic';BUILD.mkdir(parents=True,exist_ok=True)
BIN=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin')
paths=[BUILD,Path((ROOT/'milestones/28-direct-share-certificates/build/latest.txt').read_text().strip())]
paths.insert(1,Path((ROOT/'milestones/49-six-direction-pair-catalogue/build/latest.txt').read_text().strip()))
paths.insert(1,Path((ROOT/'milestones/32-seven-count-four-screen/build/proofs-latest.txt').read_text().strip()))
paths.extend(ROOT/p for p in ['milestones/20-middle-path-release/build','milestones/14-component-construction/build','milestones/07-window-223/lean/generated/geometry/support-ci2y7deg','work/spectral/.verification/strengthened-n8g3mwjy/core/.lake/build/lib/lean','work/spectral/.verification/strengthened-n8g3mwjy'])
env=os.environ.copy();env['PATH']=str(BIN)+';'+env['PATH'];env['LEAN_PATH']=';'.join(map(str,paths))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()

record=OUT/('logs/composition-record.json' if '--composition' in sys.argv else 'logs/completion-record.json');rows=json.loads(record.read_text())['records'] if record.exists() else []
sources={f.relative_to(OUT/'lean').with_suffix('').as_posix():f for f in (OUT/'lean').rglob('*.lean')}
semantic=json.loads((OUT/'logs/semantic-record.json').read_text())['records']
complete={r['module'] for r in semantic if r['exit_code']==0 and sha(sources[r['module']])==r['source_sha256'] and (BUILD/(r['module']+'.olean')).exists()}
deps={n:{line.split()[1].replace('.','/') for line in f.read_text().splitlines() if line.startswith('import ')}&sources.keys() for n,f in sources.items()}
for saved in [OUT/'logs/composition-record.json']:
 if saved.exists() and saved!=record:rows+=json.loads(saved.read_text())['records']
for row in rows:
 if row['exit_code']==0 and sha(sources[row['module']])==row['source_sha256'] and row['dependencies']=={n:sha(sources[n]) for n in deps[row['module']]} and (BUILD/(row['module']+'.olean')).exists():complete.add(row['module'])
if '--force-compose' in sys.argv:complete.discard('Share120/Compose')
pending=set(sources)-complete
if '--composition' in sys.argv:pending={n for n in pending if n in ['Share120/Compose','Share120/Sat','LocalWindowShareBridge']}
while pending:
 ready=sorted(n for n in pending if deps[n]<=complete)
 if not ready:raise RuntimeError(str(pending))
 name=ready[0];source=sources[name];dest=BUILD/(name+'.olean');dest.parent.mkdir(parents=True,exist_ok=True)
 log=OUT/'logs'/(name.replace('/','-')+'.log');start=time.monotonic()
 try:
  with log.open('w',encoding='utf-8') as f:r=subprocess.run([str(BIN/'lake.exe'),'env','lean','-s','65536','-R',str(OUT/'lean'),'-o',str(dest.with_suffix('.fresh.olean')),str(source)],cwd=BIN.parent.parent/'mathlib',env=env,stdout=f,stderr=subprocess.STDOUT,timeout=300)
  code=r.returncode
  if code==0:os.replace(dest.with_suffix('.fresh.olean'),dest)
 except subprocess.TimeoutExpired:code='TIMEOUT'
 row=dict(module=name,exit_code=code,source_sha256=sha(source),dependencies={n:sha(sources[n]) for n in deps[name]},seconds=time.monotonic()-start)
 rows.append(row);record.write_text(json.dumps(dict(build=str(BUILD),records=rows),indent=2)+'\n')
 print(name,code,round(row['seconds'],2),flush=True)
 if code!=0:
  print(log.read_text(encoding='utf-8')[-3500:],flush=True);sys.exit(1)
 pending.remove(name);complete.add(name)
print('All generated share modules completed.',flush=True)
