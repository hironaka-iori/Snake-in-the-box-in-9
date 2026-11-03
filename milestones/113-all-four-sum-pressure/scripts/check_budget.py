"""Check only PairBudget113, with one extra compiler and immutable attempt records."""
from pathlib import Path
import datetime, hashlib, json, os, re, subprocess, time

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
BIN = Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin')
MATHLIB = BIN.parent.parent / 'mathlib'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
for directory in ['data', 'logs', 'build']:
    (HERE / directory).mkdir(exist_ok=True)
run = str(time.time_ns())
source = HERE / 'lean/PairBudget113.lean'
log = HERE / 'logs' / ('PairBudget113-' + run + '.log')
record = HERE / 'logs' / ('PairBudget113-' + run + '-record.json')
snapshot = HERE / 'logs' / ('PairBudget113-' + run + '-source.lean.txt')
checker_snapshot = HERE / 'logs' / ('PairBudget113-' + run + '-checker.py.txt')
snapshot.write_bytes(source.read_bytes())
checker_snapshot.write_bytes(Path(__file__).read_bytes())
assert not re.search(r'\b(sorry|admit|native_decide)\b', source.read_text(encoding='utf-8'))
dependencies = {}
for p in [MATHLIB/'Mathlib/Tactic.lean', MATHLIB/'.lake/build/lib/lean/Mathlib/Tactic.olean',
          MATHLIB/'lake-manifest.json', BIN/'lean.exe', BIN/'lake.exe',
          ROOT/'milestones/41-joint-intervening-sum/lean/JointExcess.lean',
          ROOT/'milestones/98-concrete-weight-integration/lean/GlobalCharge98.lean']:
    dependencies[str(p)] = sha(p)
old = ROOT/'milestones/112-critical-sum-refinement'
receipt = old/'data/SumBudget112-audit.json'
inherited = json.loads(receipt.read_text(encoding='utf-8-sig'))
assert inherited['status'] == 'PASS_SUM_BUDGET_ARITHMETIC' and inherited['exit_code'] == 0
for p, digest in [(old/'lean/SumBudget112.lean', inherited['source_sha256']),
                  (old/'build/SumBudget112.olean', inherited['olean_sha256']),
                  (old/inherited['log'], inherited['log_sha256'])]:
    assert sha(p) == digest
    dependencies[str(p)] = digest
dependencies[str(receipt)] = sha(receipt)
command = '@(Get-CimInstance Win32_Process -Filter "Name=\'lean.exe\'" | Select-Object ProcessId,PrivatePageCount,CommandLine) | ConvertTo-Json -Compress'
raw = subprocess.check_output(['powershell','-NoProfile','-Command',command], text=True).strip()
others = json.loads(raw) if raw else []
if isinstance(others, dict): others = [others]
state = dict(module='PairBudget113', status='PREPARED', run=run,
    started_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    source_sha256=sha(source), source_snapshot=snapshot.relative_to(HERE).as_posix(),
    checker_sha256=sha(Path(__file__)), checker_snapshot=checker_snapshot.relative_to(HERE).as_posix(),
    dependencies=dependencies, other_lean_processes=others,
    gate='At most one other Lean process, with aggregate private memory below 8 GiB.',
    scope='Generic arithmetic and boundary accounting only; all local sum bounds remain explicit premises.')
def save(): record.write_text(json.dumps(state,indent=2)+'\n', encoding='utf-8')
save()
assert len(others) <= 1 and sum(int(p['PrivatePageCount']) for p in others) < 8*1024**3, 'Compiler memory gate not satisfied; no compiler started.'
env = os.environ.copy()
env['PATH'] = str(BIN) + ';' + env['PATH']
env['LEAN_PATH'] = str(HERE/'build') + ';' + str(ROOT/'milestones/112-critical-sum-refinement/build')
fresh = HERE/'build'/('PairBudget113.'+run+'.olean')
args = [str(BIN/'lake.exe'),'env','lean','-s','65536','-R',str(HERE/'lean'),'-o',str(fresh),str(source)]
state.update(status='RUNNING', command=args, cwd=str(MATHLIB))
start = time.monotonic(); timedout = False
with log.open('w',encoding='utf-8') as output:
    proc = subprocess.Popen(args,cwd=MATHLIB,env=env,stdout=output,stderr=subprocess.STDOUT)
    state['launcher_pid'] = proc.pid; save()
    try: code = proc.wait(timeout=120)
    except subprocess.TimeoutExpired:
        timedout = True
        subprocess.run(['taskkill','/PID',str(proc.pid),'/T','/F'],stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL,check=False)
        code = proc.wait(timeout=30)
state.update(exit_code=code,timeout=timedout,seconds=time.monotonic()-start,
    log=log.relative_to(HERE).as_posix(),log_sha256=sha(log),status='FAILED' if code or timedout else 'CHECKED')
save()
assert not timedout and code == 0, log.read_text(encoding='utf-8')
assert sha(source)==state['source_sha256'] and sha(Path(__file__))==state['checker_sha256']
assert all(sha(Path(p))==v for p,v in dependencies.items())
output = log.read_text(encoding='utf-8')
assert 'error:' not in output and 'sorryAx' not in output
rows = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",output,re.S)
rows += [(n,'') for n in re.findall(r"'([^']+)' does not depend on any axioms",output)]
assert len(rows)==source.read_text(encoding='utf-8').count('#print axioms')==3
audits=[]
for theorem,ax in rows:
    axioms=re.findall(r'[A-Za-z][\w.]*',ax)
    assert set(axioms)<={'propext','Classical.choice','Quot.sound'}
    audits.append(dict(theorem=theorem,axioms=axioms))
obj=HERE/'build/PairBudget113.olean';os.replace(fresh,obj)
state.update(status='PASS_PAIR_BUDGET_ARITHMETIC',olean_sha256=sha(obj),theorem_audits=audits)
save()
receipt=HERE/'data/PairBudget113-audit.json'
receipt.write_text(json.dumps(state,indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(status=state['status'],seconds=state['seconds'],audits=len(audits),
    source_sha256=state['source_sha256'],olean_sha256=state['olean_sha256'],log_sha256=state['log_sha256'],receipt_sha256=sha(receipt)),indent=2))
