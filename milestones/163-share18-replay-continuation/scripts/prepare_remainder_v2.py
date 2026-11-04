"""Preserve the resource stop and retry the identical proof body with narrow imports."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1]

def sha(p):
    h=hashlib.sha256()
    with Path(p).open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''):h.update(b)
    return h.hexdigest()
def write(p,b):
    b=b.encode() if isinstance(b,str) else b
    if p.exists():assert p.read_bytes()==b,str(p)
    else:p.write_bytes(b)

def main():
    old=H/'data/remainder-execution.json';plan=json.loads(old.read_text())
    failures=sorted((H/'logs').glob('RemainderComparison163-*/record.json'))
    assert len(failures)==1
    failure=failures[0];q=json.loads(failure.read_text())
    assert q['status']=='FAILED' and q['stop_reason']=='LOW_FREE_MEMORY'
    assert not (H/'data/RemainderComparison163-audit.json').exists()
    oldsrc=H/'lean/RemainderComparison163.lean';raw=oldsrc.read_bytes()
    assert sha(oldsrc)==plan['source_sha256']['RemainderComparison163']
    assert raw.startswith(b'import Mathlib.Tactic\n')
    body=raw.split(b'\n',1)[1]
    imports=b'import Mathlib.Data.Real.Basic\nimport Mathlib.Tactic.Linarith\nimport Lean.Elab.Tactic.Omega\n'
    src=H/'lean/RemainderComparison163V2.lean';write(src,imports+body)
    assert src.read_bytes().split(imports,1)[1]==body
    checker_path=H/'scripts/check_remainder_v2.py'
    write(checker_path,(H/'scripts/check_remainder.py').read_text().replace(
        'data/remainder-execution.json','data/remainder-execution-v2.json'))
    auditor=(H/'scripts/audit_remainder.py').read_text().replace(
        'data/remainder-execution.json','data/remainder-execution-v2.json').replace(
        'data/RemainderComparison163-audit.json','data/RemainderComparison163V2-audit.json').replace(
        "['RemainderComparison163']","['RemainderComparison163V2']")
    write(H/'scripts/audit_remainder_v2.py',auditor)
    plan['module_order']=plan['new_module_order']=['RemainderComparison163V2']
    plan['source_sha256']={'RemainderComparison163V2':sha(src)}
    plan['checker_sha256']=sha(checker_path)
    for p in [old,oldsrc,failure,failure.parent/'source.lean.txt',Path(__file__),checker_path]:
        plan['input_pins'][str(p)]=sha(p)
    plan['resource_retry']=dict(original_record=str(failure),reason='LOW_FREE_MEMORY',
        only_mathematical_source_change='Replace the umbrella import by three narrow imports.',
        unchanged_proof_body_sha256=hashlib.sha256(body).hexdigest(),resource_limits_unchanged=True)
    write(H/'data/remainder-execution-v2.json',json.dumps(plan,indent=2)+'\n')
    print('PREPARED_NARROW_IMPORT_RETRY_WITH_IDENTICAL_PROOF_BODY')

if __name__=='__main__':main()
