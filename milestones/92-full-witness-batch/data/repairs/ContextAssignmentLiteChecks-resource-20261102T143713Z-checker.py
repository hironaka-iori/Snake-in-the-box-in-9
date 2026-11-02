"""Check one assignment module at a time; run only after the compiler slot is released."""
from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,sys,time
HERE=Path(__file__).resolve().parents[1]
REPO=HERE.parents[1]
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
    return h.hexdigest()
module=sys.argv[1]
expected_audits={'ContextAssignmentData':0,'ContextAssignment':3,'ContextAssignmentChecks':6,
    'ContextAssignmentLiteData':0,'ContextAssignmentLiteChecks':4,'ContextAssignmentLiteBridge':1}
assert module in expected_audits
is_lite=module in ['ContextAssignmentLiteData','ContextAssignmentLiteChecks']
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
combined_support=None
if is_lite:
    paths=[str(HERE/'build')]
else:
    support=verify(HERE,'BatchAssembly','8f333dafa31814234e9341e98fa5bb512a826430e45ed45da2e281b94d2793f7')
    verify(HERE,'BatchContextData')
    verify(HERE.parent/'77-direction-state-coverage','LookupTableCheck','cf301d632638f44d8ce772024ad9d419c9b000fa5693a2aa094f9e37c66dc3eb')
    verify(HERE.parent/'87-retained-array-membership','NumericRetention','364985551bcfdec435cd08bb258c7bfb705074b996d5384a597da7e6d468e4df')
    if module!='ContextAssignmentData':verify(HERE,'ContextAssignmentData')
    if module in ['ContextAssignmentChecks','ContextAssignmentLiteBridge']:verify(HERE,'ContextAssignment')
    combined_support=support['combined_support_sha256']
    assert sha(HERE.parent/'87-retained-array-membership/data/RetainedPredicates-support.json')==combined_support
    paths=support['paths']
if module.startswith('ContextAssignmentLite') or module=='ContextAssignmentChecks':
    lite_build=json.loads((HERE/'data/ContextAssignmentLite-build.json').read_text())
    assert sha(HERE/'lean/ContextAssignmentLiteData.lean')==lite_build['source_sha256']
    assert sha(HERE/'data/ContextAssignment-build.json')==lite_build['original_build_sha256']
if module in ['ContextAssignmentLiteChecks','ContextAssignmentLiteBridge','ContextAssignmentChecks']:
    verify(HERE,'ContextAssignmentLiteData')
if module in ['ContextAssignmentLiteBridge','ContextAssignmentChecks']:verify(HERE,'ContextAssignmentLiteChecks')
if module=='ContextAssignmentChecks':verify(HERE,'ContextAssignmentLiteBridge')
BIN=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin')
env=os.environ.copy();env['PATH']=str(BIN)+';'+env['PATH'];env['LEAN_PATH']=';'.join(paths)
src=HERE/'lean'/f'{module}.lean';obj=HERE/'build'/f'{module}.olean';log=HERE/'logs'/f'{module}.log'
if log.exists():log.rename(HERE/'logs'/f'{module}-{time.time_ns()}.log')
start=time.monotonic()
timeout_seconds=900 if module=='ContextAssignmentLiteChecks' else 300
timeout_info=None
with log.open('w',encoding='utf-8') as out:
    p=subprocess.Popen([str(BIN/'lake.exe'),'env','lean','-s','65536','-R',str(HERE/'lean'),'-o',str(obj.with_suffix('.fresh.olean')),str(src)],cwd=BIN.parent.parent/'mathlib',env=env,stdout=out,stderr=subprocess.STDOUT)
    try:
        exit_code=p.wait(timeout=timeout_seconds)
    except subprocess.TimeoutExpired:
        # The launcher is still alive here. Terminate only its owned compiler tree,
        # before killing the launcher could orphan its Lean child.
        cleanup=subprocess.run(['taskkill','/PID',str(p.pid),'/T','/F'],capture_output=True,text=True)
        p.wait(timeout=30)
        exit_code=124
        timeout_info=dict(timeout_seconds=timeout_seconds,launcher_pid=p.pid,cleanup_exit_code=cleanup.returncode,cleanup_stdout=cleanup.stdout,cleanup_stderr=cleanup.stderr)
r=dict(module=module,exit_code=exit_code,seconds=time.monotonic()-start,source_sha256=sha(src),log_sha256=sha(log),paths=paths,dependency_receipts=deps,combined_support_sha256=combined_support,build_receipt_sha256=sha(HERE/'data/ContextAssignment-build.json'),checker_sha256=sha(Path(__file__)),resource_scope='literal-only local+Mathlib imports' if is_lite else 'existing heavy proof environment, generic bridge only',timeout_seconds=timeout_seconds)
if timeout_info:r['timeout']=timeout_info
(HERE/'logs'/f'{module}-record.json').write_text(json.dumps(r,indent=2)+'\n')
if exit_code:
    repairs=HERE/'data/repairs';repairs.mkdir(exist_ok=True)
    stem=f'{module}-{time.time_ns()}'
    for path,suffix in [(src,'.lean'),(log,'.log'),(Path(__file__),'-checker.py')]:shutil.copyfile(path,repairs/(stem+suffix))
    (repairs/(stem+'-record.json')).write_text(json.dumps(r,indent=2)+'\n')
    print(log.read_text()[-20000:]);print(json.dumps(r,indent=2));raise SystemExit(exit_code)
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
