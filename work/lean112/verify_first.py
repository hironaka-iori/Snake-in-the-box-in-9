"""Publish a first-entry completion receipt only after complete kernel checks."""
import hashlib,json,re,subprocess
from pathlib import Path
from service import OUT,ROOT,read,save,event
HERE=Path(__file__).resolve().parent
modules=['RegrowthBridge','First112Data','First112Semantics']+[f'First112Clauses{i:02d}' for i in range(49)]+['First112Complete']
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
records=read(OUT/'bridge-checks.json',{})
for name in modules:
    r=records[name];src=HERE/(name+'.lean');obj=HERE/(name+'.olean')
    assert r['exit_code']==0,name
    assert r['sha256']==sha(src),name+' source changed'
    assert r['olean_sha256']==sha(obj),name+' compiled artifact changed'
    assert not re.search(r'\b(sorry|native_decide)\b|^\s*axiom\s',src.read_text(encoding='utf-8'),re.M),name
boolean=read(OUT/'first-certificate.json')
assert boolean['status']=='PASSED_BOOLEAN_ONLY'
assert len(boolean['checked'])==150
folder=ROOT/'work/lean/sat-first-checked'
for r in boolean['checked']:
    src=folder/(r['module']+'.lean');obj=folder/(r['module']+'.olean')
    assert r['exit_code']==0
    assert r['sha256']==hashlib.sha256(src.read_text(encoding='utf-8').encode()).hexdigest()
    assert r['olean_sha256']==sha(obj)
log=(OUT/'bridge-logs/First112Complete.log').read_text(encoding='utf-8')
theorems=['no192','no_long_prefix','no_long_suffix']
for name in theorems:
    line=next(x for x in log.splitlines() if f"'Snake9.Regrowth.First112.{name}' depends on axioms:" in x)
    axioms=set(re.search(r'\[(.*)\]',line)[1].split(', '))
    assert axioms=={'propext','Classical.choice','Quot.sound'},line
data=(HERE/'First112Data.lean').read_text(encoding='utf-8')
pre=json.loads(re.search(r'def pre : Array Nat := #([^\n]+)',data)[1])
bank=json.loads((ROOT/'work/bank9.json').read_text())
assert pre==bank[0]['vertex_sequence'][:112]
receipt=dict(status='PASSED_FIRST_GEOMETRIC_ENTRY',entry_zero_based=0,bank_index=0,orientation='forward',keep_vertices=112,
    excluded_edges=192,all_longer_lengths=True,geometric_entries_completed=1,total_entries=262,
    bridge_modules=len(modules),boolean_modules=150,core_clauses=1547,
    theorems=['Snake9.Regrowth.First112.'+x for x in theorems],
    axioms=sorted(axioms),modules={name:records[name] for name in modules},
    scope='Only the first oriented bank entry. No global optimum or other-entry exclusion is claimed.')
save('first-geometric-proof.json',receipt)
state=read(OUT/'reasoning.json',{})
state.update(status='IN_PROGRESS',formally_certified_entries=1,
    title='首例完整数学连接已通过 Lean',
    detail='第一个入口已完成完整112档形式化证明：路径到约束的1547条连接、无解证书及最终公理审计全部通过。完整入口1/262；其余261个尚未认证。',
    completed_entry_indices=[0])
save('reasoning.json',state)
event('bridge','首个112档入口的完整几何排除定理通过 Lean 与公理审计。',entry=0,formally_certified_entries=1)
print('PASSED: first complete geometric KEEP=112 entry (1/262).')
