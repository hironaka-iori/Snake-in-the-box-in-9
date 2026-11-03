"""Order the immutable replay sources by dependencies; retain the checked pilot."""
from pathlib import Path
import hashlib,json,re
P=Path(__file__).resolve().parents[1];H=P/'replay'
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
fullpath=H/'data/full-source-plan.json';pilotpath=H/'data/pilot-source-plan.json'
full=read(fullpath);pilot=read(pilotpath)
items={a['module']:a for a in full['artifacts']};order=[];active=set();done=set()
def visit(m):
    if m in done:return
    assert m not in active,m
    active.add(m);a=items[m];p=H/a['path'];assert sha(p)==a['sha256'],m
    for d in re.findall(r'^import ([\w.]+)$',p.read_text(encoding='utf-8'),re.M):
        if d in items:visit(d)
    active.remove(m);done.add(m);order.append(m)
for m in pilot['module_order']:visit(m)
assert order==pilot['module_order']
visit('ReplayUnsat147')
assert len(order)==len(items)==1789 and set(order)==set(items)
assert order[36:47]==['ReplayCheckpoint147_00032','ReplayData147_0000']+[
    f'ReplayCheck147_{i:05d}' for i in range(0,32,4)]+['ReplaySteps147_0000']
plan=dict(full)
plan.update(module_order=order,derivation='Dependency order after the unchanged checked pilot; mathematical sources unchanged.',
    source_plan_sha256=sha(fullpath),pilot_plan_sha256=sha(pilotpath),deriver_sha256=sha(Path(__file__)))
out=H/'data/full-execution-plan.json';assert not out.exists()
out.write_text(json.dumps(plan,indent=2)+'\n',encoding='utf-8',newline='\n')
def write(name,s):
    p=P/'scripts'/name;assert not p.exists();p.write_text(s,encoding='utf-8',newline='\n');return p
checker=(P/'scripts/check_replay.py').read_text(encoding='utf-8')
checker=checker.replace("data/pilot-source-plan.json","data/full-execution-plan.json")
checker=checker.replace("r'[A-Za-z][A-Za-z0-9.]*'","r'[A-Za-z][A-Za-z0-9_.]*'")
checker=write('check_full_replay.py',checker)
driver=(P/'scripts/run_replay.py').read_text(encoding='utf-8')
driver=driver.replace('pilot-source-plan.json','full-execution-plan.json').replace('check_replay.py','check_full_replay.py')
driver=driver.replace('replay-batch','full-replay-batch').replace('replay-progress','full-replay-progress').replace('replay-launch','full-replay-launch')
driver=driver.replace('PASS_BOUNDED_REPLAY_PILOT_PREFIX','PASS_BOUNDED_FULL_REPLAY_PREFIX').replace('PASS_COMPLETE_REPLAY_PILOT','PASS_COMPLETE_FULL_REPLAY_MODULES')
driver=driver.replace('15-bit checker, full initial-tree bridge and bounded prefix/checkpoint. The full contradiction and actual-snake theorem remain separate.',
    'Complete core contradiction replay. Actual-snake geometry, symmetry and composition remain separate.')
driver=write('run_full_replay.py',driver)
receipt=dict(status='PREPARED_DEPENDENCY_ORDERED_FULL_REPLAY_RUNNER',
    files_sha256={p.relative_to(P).as_posix():sha(p) for p in [Path(__file__),fullpath,pilotpath,out,checker,driver]},
    pilot_modules=36,first_group_new_modules=11,total_modules=len(order),first_group=order[36:47])
(P/'data/full-replay-runner-plan.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps(receipt,indent=2))
