"""Read-only snapshot of running proof manifests; never upgrades evidence."""
from datetime import datetime, timezone
import hashlib,json,pathlib
ROOT=pathlib.Path(__file__).resolve().parents[2]
OUT=ROOT/'outputs/window244'
report=dict(captured_utc=datetime.now(timezone.utc).isoformat(),
    evidence='Progress snapshot only; not final theorem verification',jobs={})
paths=[OUT/(name+'.json') for name in ['certificate-repeated-build',
    'certificate-distinct-build','repeated-geometry-build','distinct-geometry-build']]
paths+=sorted((ROOT/'work/spectral/.verification').glob('window244-*/manifest.json'))
for path in paths:
    if not path.exists():continue
    raw=path.read_bytes();state=json.loads(raw)
    passed={n:r for n,r in state.get('modules',{}).items() if r.get('exit_code')==0}
    item=dict(status=state.get('status'),active=state.get('active'),pid=state.get('pid'),
        manifest_sha256=hashlib.sha256(raw).hexdigest(),passed_modules=len(passed),
        total_modules=len(state['module_order']) if 'module_order' in state else None,
        peak_observed_bytes=max((r.get('peak_private_bytes',r.get('peak_bytes',0)) for r in passed.values()),default=0))
    if state.get('status')=='FAILED':item['error']=state.get('error')
    report['jobs'][path.relative_to(ROOT).as_posix()]=item
target=OUT/'progress-checkpoint.json'
target.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print(json.dumps(report,indent=2))
