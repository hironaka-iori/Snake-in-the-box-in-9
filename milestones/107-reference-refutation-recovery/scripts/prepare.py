"""Recover one selected reference entry from exact pinned contributor bytes."""
from pathlib import Path
import gzip,hashlib,json,subprocess
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
PIN='7cb52aad9fbb83aea8a6ced73c9a18a1ad531c9b'
for name in ['data','upstream','lean','build','logs','audit','work']:(HERE/name).mkdir(parents=True,exist_ok=True)
sha=lambda b:hashlib.sha256(b).hexdigest()
selection=json.loads((ROOT/'milestones/105-reference-proof-closure/data/source-selection.json').read_text())
entry=next(r for r in selection['rows'] if r['root']=='Q012A11')
assert entry['pin']==PIN and entry['union_index']==0
paths=['work/final_lean/LocalWindowCnf/Q012A11.lean','work/final_lean/LocalWindowSat/Q012A11.lean',
 'milestones/10-window-aggregate/data/lean_core_direction_r4/d012_a1_1.json',
 'milestones/10-window-aggregate/certificates/direction_r4/d012_a1_1.cnf.gz',
 'milestones/10-window-aggregate/scripts/gen_lean_core.py','milestones/10-window-aggregate/scripts/gen_lean_lrat.py']
records=[]
for path in paths:
    raw=subprocess.check_output(['git','-c','core.commitGraph=false','show',PIN+':'+path],cwd=ROOT)
    target=HERE/'upstream'/path
    target.parent.mkdir(parents=True,exist_ok=True)
    if target.exists():assert target.read_bytes()==raw
    else:target.write_bytes(raw)
    records.append(dict(pin=PIN,path=path,saved=target.relative_to(ROOT).as_posix(),sha256=sha(raw),bytes=len(raw)))
    if path.startswith('work/final_lean/'):
        target=HERE/'lean'/Path(path).relative_to('work/final_lean');target.parent.mkdir(parents=True,exist_ok=True)
        if target.exists():assert target.read_bytes()==raw
        else:target.write_bytes(raw)
cnf=gzip.decompress((HERE/'upstream/milestones/10-window-aggregate/certificates/direction_r4/d012_a1_1.cnf.gz').read_bytes())
(HERE/'work/d012_a1_1.cnf').write_bytes(cnf)
meta=json.loads((HERE/'upstream/milestones/10-window-aggregate/data/lean_core_direction_r4/d012_a1_1.json').read_text())
clauses=[[int(x) for x in line.split()[:-1]] for line in cnf.decode().splitlines() if line and not line.startswith(('p','c'))]
ids=meta['core_ids'];core=[clauses[i-1] for i in ids]
variables=max(abs(x) for c in core for x in c)
assert len(clauses)==meta['cnf_clauses'] and len(set(ids))==len(ids)
coretext=f'p cnf {variables} {len(core)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in core)
(HERE/'work/Q012A11-core.cnf').write_bytes(coretext.encode('ascii'))
out=dict(status='PINNED_REFERENCE_INPUTS_NOT_REFUTATION',entry=entry,files=records,
    full_clauses=len(clauses),core_clauses=len(core),variables=variables,
    full_cnf_sha256=sha(cnf),core_cnf_sha256=sha(coretext.encode('ascii')),
    core_ids=ids,scope='Exact selected input and semantic sources. No new solver result or Lean proof.')
(HERE/'data/input-pins.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
(HERE/'.gitattributes').write_text('* -text\n')
print(json.dumps({k:v for k,v in out.items() if k not in ['files','core_ids','entry']},indent=2))
