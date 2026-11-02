"""Check one assignment module at a time; run only after the compiler slot is released."""
from pathlib import Path
import hashlib,json,os,re,subprocess,sys,time
HERE=Path(__file__).resolve().parents[1]
REPO=HERE.parents[1]
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
    return h.hexdigest()
module=sys.argv[1]
expected_audits={'ContextAssignmentData':0,'ContextAssignment':3,'ContextAssignmentChecks':6}
assert module in expected_audits
build=json.loads((HERE/'data/ContextAssignment-build.json').read_text())
assert sha(HERE/'data/context-assignment-plan.json')==build['plan_sha256']
assert sha(HERE/'lean/BatchContextData.lean')==build['batch_context_source_sha256']
assert sha(HERE/'lean/ContextAssignmentData.lean')==build['source_sha256']
for rel,pin in build['input_sha256'].items():assert sha(REPO/rel)==pin,rel
deps={}
def verify(root,name,pin=None):
    path=root/'data'/f'{name}-audit.json'
    if pin:assert sha(path)==pin
    r=json.loads(path.read_text());assert r['status'].startswith('PASS_')
    for folder,suffix,key in [('lean','.lean','source_sha256'),('build','.olean','olean_sha256'),('logs','.log','log_sha256')]:
        assert sha(root/folder/(name+suffix))==r[key]
    deps[str(path.relative_to(REPO))]=sha(path)
    return r
support=verify(HERE,'BatchAssembly','8f333dafa31814234e9341e98fa5bb512a826430e45ed45da2e281b94d2793f7')
verify(HERE,'BatchContextData')
verify(HERE.parent/'77-direction-state-coverage','LookupTableCheck','cf301d632638f44d8ce772024ad9d419c9b000fa5693a2aa094f9e37c66dc3eb')
verify(HERE.parent/'87-retained-array-membership','NumericRetention','364985551bcfdec435cd08bb258c7bfb705074b996d5384a597da7e6d468e4df')
if module!='ContextAssignmentData':verify(HERE,'ContextAssignmentData')
if module=='ContextAssignmentChecks':verify(HERE,'ContextAssignment')
assert sha(HERE.parent/'87-retained-array-membership/data/RetainedPredicates-support.json')==support['combined_support_sha256']
paths=support['paths']
BIN=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin')
env=os.environ.copy();env['PATH']=str(BIN)+';'+env['PATH'];env['LEAN_PATH']=';'.join(paths)
src=HERE/'lean'/f'{module}.lean';obj=HERE/'build'/f'{module}.olean';log=HERE/'logs'/f'{module}.log'
if log.exists():log.rename(HERE/'logs'/f'{module}-{time.time_ns()}.log')
start=time.monotonic()
with log.open('w',encoding='utf-8') as out:
    p=subprocess.run([str(BIN/'lake.exe'),'env','lean','-s','65536','-R',str(HERE/'lean'),'-o',str(obj.with_suffix('.fresh.olean')),str(src)],cwd=BIN.parent.parent/'mathlib',env=env,stdout=out,stderr=subprocess.STDOUT,timeout=900 if module=='ContextAssignmentChecks' else 300)
r=dict(module=module,exit_code=p.returncode,seconds=time.monotonic()-start,source_sha256=sha(src),log_sha256=sha(log),paths=paths,dependency_receipts=deps,combined_support_sha256=support['combined_support_sha256'],build_receipt_sha256=sha(HERE/'data/ContextAssignment-build.json'),checker_sha256=sha(Path(__file__)))
(HERE/'logs'/f'{module}-record.json').write_text(json.dumps(r,indent=2)+'\n')
if p.returncode:print(log.read_text()[-20000:]);raise SystemExit(p.returncode)
os.replace(obj.with_suffix('.fresh.olean'),obj)
text=log.read_text();assert 'error:' not in text and 'sorryAx' not in text
assert not re.search(r'\b(sorry|admit|native_decide)\b',src.read_text())
audits=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",text,re.S)
audits += [(name,'') for name in re.findall(r"'([^']+)' does not depend on any axioms",text)]
assert len(audits)==expected_audits[module]==src.read_text().count('#print axioms')
checked=[]
for name,axs in audits:
    values=re.findall(r'[A-Za-z][\w.]*',axs);assert set(values)<={'propext','Classical.choice','Quot.sound'}
    checked.append(dict(theorem=name,axioms=values))
r.update(status='PASS_CONTEXT_ASSIGNMENT_MODULE',olean_sha256=sha(obj),theorem_audits=checked,scope='Only the named assignment module. Source projection preserves di<505. The finite checker identifies chosen classes and roots with the pinned saved block/class/root literals for all bounded source-compatible pairs. All-class diagram acceptance retains an explicit ClassMembershipFamily premise; saved row-array coverage remains separate.')
(HERE/'data'/f'{module}-audit.json').write_text(json.dumps(r,indent=2)+'\n')
print(module,'PASS',round(r['seconds'],3),'seconds;',len(checked),'audits',flush=True)
