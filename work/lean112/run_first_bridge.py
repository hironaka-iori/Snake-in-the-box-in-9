"""Resume kernel checking of the actual first-entry geometric bridge."""
import hashlib,json,subprocess,sys
from pathlib import Path
from service import save,read,OUT,event
HERE=Path(__file__).resolve().parent
modules=['RegrowthBridge','First112Data','First112Semantics']+[f'First112Clauses{i:02d}' for i in range(49)]+['First112Complete']
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for name in modules:
    records=read(OUT/'bridge-checks.json',{})
    r=records.get(name,{})
    src=HERE/(name+'.lean');obj=HERE/(name+'.olean')
    cached=r.get('exit_code')==0 and r.get('sha256')==sha(src) and obj.exists() and r.get('olean_sha256')==sha(obj)
    state=read(OUT/'reasoning.json',{})
    count=sum(records.get(f'First112Clauses{i:02d}',{}).get('exit_code')==0 for i in range(49))
    state.update(status='IN_PROGRESS',detail=f'正在完成首例实际数学证明：49组约束连接已通过{count}组；当前核验 {name}。完整入口需最终定理及公理审计通过后才计入。')
    save('reasoning.json',state)
    if cached and name!='First112Complete':
        print('Verified cache '+name,flush=True);continue
    p=subprocess.run([sys.executable,str(HERE/'check.py'),name],cwd=HERE.parents[1])
    if p.returncode:
        event('bridge','首例数学证明编译遇到错误，继续修复。',module=name)
        sys.exit(p.returncode)
    event('bridge','数学连接模块已通过 Lean 并保存。',module=name)
print('All first-entry modules checked. Inspect final axioms and scope before recording completion.',flush=True)
