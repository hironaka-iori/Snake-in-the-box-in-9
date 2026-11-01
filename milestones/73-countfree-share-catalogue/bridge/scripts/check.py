"""One-process Lean replay of pinned ShareCharge and the small core budget bridge."""
from pathlib import Path
import hashlib,json,os,re,subprocess,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[2];BUILD=HERE/'build'
BIN=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin')
paths=[BUILD,ROOT/'milestones/72-four-count-proof-closure/critical-current/share-proof/build/semantic',Path((ROOT/'milestones/28-direct-share-certificates/build/latest.txt').read_text().strip()),Path((ROOT/'milestones/32-seven-count-four-screen/build/proofs-latest.txt').read_text().strip()),Path((ROOT/'milestones/49-six-direction-pair-catalogue/build/latest.txt').read_text().strip())]
paths.extend(ROOT/p for p in ['milestones/20-middle-path-release/build','milestones/14-component-construction/build','milestones/07-window-223/lean/generated/geometry/support-ci2y7deg','work/spectral/.verification/strengthened-n8g3mwjy/core/.lake/build/lib/lean','work/spectral/.verification/strengthened-n8g3mwjy'])
env=os.environ.copy();env['PATH']=str(BIN)+';'+env['PATH'];env['LEAN_PATH']=';'.join(map(str,paths))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
record=HERE/'logs/build-record.json';rows=json.loads(record.read_text())['records'] if record.exists() else []
for name,folder in [('ShareCharge','upstream'),('CoreShareBudget','lean'),('FiveCentreOverlap','lean')]:
    source=HERE/f'{folder}/{name}.lean';dest=BUILD/(name+'.olean');log=HERE/'logs'/(name+'.log')
    dependency={str(p):sha(p) for p in [HERE/'upstream/ShareCharge.lean',ROOT/'milestones/72-four-count-proof-closure/critical-current/share-proof/lean/LocalWindowShareBridge.lean']}
    if name=='FiveCentreOverlap':dependency[str(HERE/'lean/CoreShareBudget.lean')]=sha(HERE/'lean/CoreShareBudget.lean')
    previous=next((r for r in reversed(rows) if r['module']==name),None)
    if previous and previous['exit_code']==0 and previous['source_sha256']==sha(source) and previous['dependencies']==dependency and dest.exists():continue
    start=time.monotonic()
    with log.open('w',encoding='utf-8') as f:
        try:r=subprocess.run([str(BIN/'lake.exe'),'env','lean','-s','65536','-R',str(HERE/folder),'-o',str(dest.with_suffix('.fresh.olean')),str(source)],cwd=BIN.parent.parent/'mathlib',env=env,stdout=f,stderr=subprocess.STDOUT,timeout=180);code=r.returncode
        except subprocess.TimeoutExpired:code='TIMEOUT'
    if code==0:os.replace(dest.with_suffix('.fresh.olean'),dest)
    rows.append(dict(module=name,exit_code=code,source_sha256=sha(source),dependencies=dependency,seconds=time.monotonic()-start))
    record.write_text(json.dumps(dict(build=str(BUILD),paths=list(map(str,paths)),records=rows),indent=2)+'\n')
    print(name,code,round(rows[-1]['seconds'],2),flush=True)
    if code!=0:print(log.read_text()[-5000:],flush=True);raise SystemExit(1)
print('Requested bridge modules passed.',flush=True)
