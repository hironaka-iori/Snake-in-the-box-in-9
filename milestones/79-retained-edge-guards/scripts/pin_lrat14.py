"""Pin the inherited fourteen-bit checker required by two interval cases."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
old=ROOT/'milestones/50-three-count-return'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
record=json.loads((old/'logs/build-record.json').read_text())
source=old/'lean/LratFast14.lean';obj=Path(record['build'])/'LratFast14.olean'
row=next(r for r in record['records'] if r['module']=='LratFast14' and r['exit_code']==0)
assert row['source_sha256']==sha(source)
path=HERE/'data/interval-support.json';out=json.loads(path.read_text())
out['modules']['external/LratFast14']=dict(source=str(source),source_sha256=sha(source),object=str(obj),object_sha256=sha(obj))
out['additional_paths']=[str(obj.parent)]
path.write_text(json.dumps(out,indent=2)+'\n')
print('Pinned inherited LratFast14; total',len(out['modules']),'objects')
