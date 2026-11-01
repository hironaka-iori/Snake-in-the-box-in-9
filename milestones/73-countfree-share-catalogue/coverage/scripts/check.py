"""Compile the small coverage theorem with one Lean process."""
from pathlib import Path
import hashlib,json,os,subprocess,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[2];BUILD=HERE/'build'
BIN=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin')
support=json.loads((HERE/'data/support.json').read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for r in support['modules']:
    assert sha(HERE/'upstream'/(r['module']+'.lean'))==r['source_sha256']
    assert sha(Path(r['olean_path']))==r['olean_sha256']
paths=[BUILD,Path(support['build']),Path((ROOT/'milestones/28-direct-share-certificates/build/latest.txt').read_text().strip())]
paths.extend(ROOT/p for p in ['milestones/20-middle-path-release/build','milestones/14-component-construction/build','milestones/07-window-223/lean/generated/geometry/support-ci2y7deg','work/spectral/.verification/strengthened-n8g3mwjy/core/.lake/build/lib/lean','work/spectral/.verification/strengthened-n8g3mwjy'])
env=os.environ.copy();env['PATH']=str(BIN)+';'+env['PATH'];env['LEAN_PATH']=';'.join(map(str,paths))
source=HERE/'lean/SixShapeCoverage.lean';dest=BUILD/'SixShapeCoverage.olean';log=HERE/'logs/SixShapeCoverage.log';start=time.monotonic()
with log.open('w',encoding='utf-8') as f:
    try:r=subprocess.run([str(BIN/'lake.exe'),'env','lean','-s','65536','-R',str(HERE/'lean'),'-o',str(dest.with_suffix('.fresh.olean')),str(source)],cwd=BIN.parent.parent/'mathlib',env=env,stdout=f,stderr=subprocess.STDOUT,timeout=180);code=r.returncode
    except subprocess.TimeoutExpired:code='TIMEOUT'
if code==0:os.replace(dest.with_suffix('.fresh.olean'),dest)
record=dict(module='SixShapeCoverage',exit_code=code,seconds=time.monotonic()-start,source_sha256=sha(source),support_record_sha256=sha(HERE/'data/support.json'),paths=list(map(str,paths)),olean_sha256=sha(dest) if code==0 else None)
(HERE/'logs/build-record.json').write_text(json.dumps(record,indent=2)+'\n')
print(record,flush=True)
if code!=0:print(log.read_text()[-5000:],flush=True);raise SystemExit(1)
