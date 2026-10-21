"""Frozen FastRup replay of the exact 34 share cores, preserving legacy results.

The shared core format remains compatible with the live applicability batch.
Handoff stops only the verified legacy worker and retains every checkpoint.
No SAT search is performed. All new Boolean proofs use the audited FastRup bridge.
"""
import argparse
import http.server
import json
import os
from pathlib import Path
import subprocess
import sys
import time
import traceback
import runner as common
from develop_lean import SEARCH

HERE=common.HERE;ROOT=common.ROOT
JOB=HERE/'runtime/fast-kernel';SRC=JOB/'src'
OLD=HERE/'runtime/kernel';INPUTS=HERE/'build/frozen/cases'
EXPORT_COMMIT='4887deb02a3a51e2775ef5e81a2fb5ddc980a669'
EXPORT_PATH='milestones/07-window-223/bridge/fast/gen_fast.py'

def file_lock(path):
    import msvcrt
    path.parent.mkdir(parents=True,exist_ok=True)
    f=path.open('a+b');f.seek(0);f.write(b'0');f.flush();f.seek(0)
    msvcrt.locking(f.fileno(),msvcrt.LK_NBLCK,1);return f

def verify_legacy(state,manifest):
    checked={}
    def visit(name):
        if name in checked:return checked[name]
        row=state['completed']['lean:'+name]
        p=OLD/'src'/(name.replace('.','/')+'.lean')
        assert common.digest(p)==row['source_sha256'],name
        deps={d:visit(d) for d in row['dependency_hashes']}
        assert deps==row['dependency_hashes'],name
        h=common.hashbytes(json.dumps([row['source_sha256'],deps,manifest['config']],sort_keys=True).encode())
        assert h==row['closure_hash'] and common.digest(p.with_suffix('.olean'))==row['artifact_sha256'],name
        checked[name]=h;return h
    for case,row in state['case_results'].items():
        assert visit(row['target'])==row['closure_hash'],case
        assert row['axioms'] and all(set(a['axioms'])<=common.ALLOWED for a in row['axioms'])
    return checked

def prepare(refresh=False):
    exists=(JOB/'manifest.json').exists()
    if exists and not refresh:raise RuntimeError('Existing batch: use run, or prepare --refresh for a stopped operational repair')
    if refresh and not exists:raise RuntimeError('No existing batch to refresh')
    held=[];previous=None;history=None
    if refresh:
        held=[file_lock(JOB/'runner.lock'),file_lock(OLD/'runner.lock')]
        old=common.read(JOB/'manifest.json');previous=common.read(JOB/'state.json')
        # This refresh changes only the worker invocation policy. The checker,
        # exporter, generated proofs and all other controllers stay immutable.
        for p,h in old['controllers'].items():
            if Path(p).resolve()!=Path(__file__).resolve():assert common.digest(p)==h,p
        assert common.digest(JOB/'gen_fast.py')==old['exporter_sha256']
        assert common.digest(JOB/'legacy-inherited-state.json')==old['inherited_state_sha256']
        head=common.git('rev-parse','HEAD').decode().strip()
        for name,d in old['frozen_modules'].items():
            assert common.digest(SRC/(name.replace('.','/')+'.lean'))==d['sha256']
            assert common.hashbytes(common.blob(head,d['path']))==d['sha256'],('changed framework',name)
        for file in (JOB/'cases').glob('*.json'):
            row=common.read(file)
            assert common.digest(OLD/'cases'/f"{row['index']:02d}"/'ready.json')==row['core_ready_sha256']
            for p,h in row['files'].items():assert common.digest(SRC/p)==h,p
        verify_legacy(common.read(JOB/'legacy-inherited-state.json'),common.read(OLD/'manifest.json'))
        history=JOB/'history'/str(time.time_ns())
        common.atomic(history/'manifest.json',old);common.atomic(history/'state.json',previous)
        last_log=Path(previous.get('latest_log',''))
        if previous.get('failure') and last_log.is_file():
            (history/'failure.log').write_bytes(last_log.read_bytes())
    original=common.read(HERE/'runtime/manifest.json');common.validate(original)
    legacy=common.read(OLD/'manifest.json');state=common.read(OLD/'state.json')
    legacy_modules=verify_legacy(state,legacy)
    commit=common.git('rev-parse','HEAD').decode().strip()
    files=set(common.git('ls-tree','-r','--name-only',commit).decode().splitlines());frozen={}
    def freeze(name):
        if name.startswith(('Init','Std','Lean','Mathlib')) or name in frozen:return
        rel=name.replace('.','/')+'.lean'
        path=next((r+'/'+rel for r in SEARCH if r+'/'+rel in files),None)
        assert path,('missing source',name)
        data=common.blob(commit,path)
        for line in data.decode().splitlines():
            if line.startswith('import '):
                for dep in line.split('--')[0].split()[1:]:freeze(dep)
        p=SRC/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
        frozen[name]=dict(path=path,sha256=common.digest(p))
    for name in ['FastRupCmd','FastRupLocalWindow','LocalWindowRename']:freeze(name)
    exporter=JOB/'gen_fast.py';exporter.write_bytes(common.blob(EXPORT_COMMIT,EXPORT_PATH))
    controls={str(HERE/'scripts'/n):common.digest(HERE/'scripts'/n)
        for n in ['fast_share_batch.py','runner.py','replay.py','develop_lean.py','kernel_batch.py']}
    for p in controls:
        relative=Path(p).relative_to(ROOT).as_posix()
        assert common.blob(commit,relative)==Path(p).read_bytes().replace(b'\r\n',b'\n'),('uncommitted controller',p)
    common.atomic(JOB/'legacy-inherited-state.json',state)
    config=original['config'].copy();config.update(source_commit=commit,timeout_seconds=1800,
        enforce_memory_budget=False,memory_policy='observe_only',thread_stack_kb=65536)
    manifest=dict(created=common.now(),config=config,controllers=controls,frozen_modules=frozen,
        exporter_commit=EXPORT_COMMIT,exporter_sha256=common.digest(exporter),
        original_manifest_sha256=common.digest(HERE/'runtime/manifest.json'),
        legacy_manifest_sha256=common.digest(OLD/'manifest.json'),
        inherited_state_sha256=common.digest(JOB/'legacy-inherited-state.json'),legacy_modules=legacy_modules,
        refresh_history=str(history) if history else None,
        scope='Exact Boolean refutations only; geometric applicability and global bounds remain separate')
    common.atomic(JOB/'manifest.json',manifest)
    cases={i:dict(**r,backend='legacy',verified_at=common.now()) for i,r in state['case_results'].items()}
    new=previous or dict(completed={},cases=cases,kernel_cases=len(cases),total_cases=34,
        failures=[],global_231='UNRESOLVED',global_230='UNRESOLVED')
    new.update(status='prepared',source_commit=commit,pid=None,child_pid=None)
    new.pop('failure',None)
    common.atomic(JOB/'state.json',new)
    for lock in held:lock.close()
    print(json.dumps(dict(source_commit=commit,modules=len(frozen),inherited_cases=list(cases))))

def validate(m):
    for p,h in m['controllers'].items():assert common.digest(p)==h,('changed controller',p)
    assert common.digest(JOB/'gen_fast.py')==m['exporter_sha256']
    assert common.digest(HERE/'runtime/manifest.json')==m['original_manifest_sha256']
    assert common.digest(OLD/'manifest.json')==m['legacy_manifest_sha256']
    assert common.digest(JOB/'legacy-inherited-state.json')==m['inherited_state_sha256']
    for name,d in m['frozen_modules'].items():assert common.digest(SRC/(name.replace('.','/')+'.lean'))==d['sha256']
    common.validate(common.read(HERE/'runtime/manifest.json'))
    verify_legacy(common.read(JOB/'legacy-inherited-state.json'),common.read(OLD/'manifest.json'))

def handoff():
    m=common.read(JOB/'manifest.json');validate(m)
    old=common.read(OLD/'state.json');pid=old.get('pid')
    inherited=common.read(JOB/'legacy-inherited-state.json')
    assert old['case_results']==inherited['case_results'], 'Completed cases changed since preparation; preserve them before handoff'
    if pid and common.psutil.pid_exists(pid):
        p=common.psutil.Process(pid);args=p.cmdline()
        assert len(args)>=3 and Path(args[1]).resolve()==(HERE/'scripts/kernel_batch.py').resolve() and args[2]=='run',args
        common.atomic(JOB/'legacy-before-handoff.json',old)
        p.suspend();common.kill_tree(p);p.wait(timeout=15)
    held=file_lock(OLD/'runner.lock')
    try:
        old=common.read(OLD/'state.json')
        common.atomic(JOB/'legacy-at-handoff.json',old)
        old.update(status='superseded',superseded_by=str(JOB/'state.json'),superseded_at=common.now(),
            handoff_reason='Validated faster replay of the same compact cores',child_pid=None)
        common.atomic(OLD/'state.json',old)
    finally:held.close()
    print('Legacy worker stopped; all completed and partial checkpoints retained.')

def core(index,legacy):
    case=OLD/'cases'/f'{index:02d}';ready=case/'ready.json';mod=f'ParallelShare{index:02d}'
    if ready.exists():
        r=common.read(ready)
        for p,h in r['artifacts'].items():assert common.digest(case/p)==h
        rel=f'LocalWindowCnf/{mod}.lean'
        assert common.digest(OLD/'src'/rel)==r['generated_files'][rel]
        return r
    source=INPUTS/f'{index:02d}'
    for f,h in legacy['inputs'][str(index)].items():assert common.digest(source/f)==h,f
    # Keep only line offsets until the empty-clause dependency graph is known.
    offsets={};last=None
    with (source/'proof.lrat').open('rb') as stream:
        while True:
            offset=stream.tell();line=stream.readline()
            if not line:break
            t=line.split(maxsplit=2)
            if len(t)<2 or t[1]==b'd':continue
            last=int(t[0]);offsets[last]=offset
    assert last is not None
    lemmas={};needed={last};todo=[last]
    with (source/'proof.lrat').open('rb') as stream:
        while todo:
            key=todo.pop()
            if key not in offsets:continue
            stream.seek(offsets[key]);xs=list(map(int,stream.readline().split()));z=xs.index(0,1)
            assert xs[0]==key and xs[-1]==0
            hs=xs[z+1:-1];assert all(0<h<key for h in hs)
            lemmas[key]=(xs[1:z],hs)
            for h in hs:
                if h not in needed:needed.add(h);todo.append(h)
    assert not lemmas[last][0]
    input_ids=sorted(needed-lemmas.keys());inputs={};variables=set();nc=0
    with (source/'model.cnf').open() as stream:
        for line in stream:
            if not line.strip() or line[0] in 'pc':continue
            nc+=1
            if nc in needed and nc not in lemmas:
                inputs[nc]=list(map(int,line.split()[:-1]));variables.update(map(abs,inputs[nc]))
    assert set(inputs)==set(input_ids)
    used=sorted(lemmas)
    for key in used:variables.update(map(abs,lemmas[key][0]))
    variables=sorted(variables);ren={v:i+1 for i,v in enumerate(variables)}
    ids={v:i+1 for i,v in enumerate(input_ids+used)}
    def rename(cl):return [ren[abs(x)] if x>0 else -ren[-x] for x in cl]
    clauses=[rename(inputs[k]) for k in input_ids];case.mkdir(parents=True,exist_ok=True)
    stem=f'parallel_share_{index:02d}';cnf=case/(stem+'.cnf');proof=case/(stem+'.lrat')
    with cnf.open('w',encoding='ascii',newline='\n') as f:
        f.write(f'p cnf {len(variables)} {len(clauses)}\n')
        for cl in clauses:f.write(' '.join(map(str,cl))+' 0\n')
    with proof.open('w',encoding='ascii',newline='\n') as f:
        for key in used:
            cl,hs=lemmas[key];f.write(' '.join(map(str,[ids[key],*rename(cl),0,*[ids[h] for h in hs],0]))+'\n')
    common.atomic(case/'compact-replay.json',common.check(cnf,proof))
    meta=dict(module=mod,core_ids=list(range(1,len(clauses)+1)),original_clause_ids=input_ids,
        original_variable_ids=variables,source_hashes=legacy['inputs'][str(index)])
    common.atomic(case/(stem+'.json'),meta)
    raw=[[2*abs(x)+(x<0) for x in cl] for cl in clauses]
    text='import LocalWindowRename\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n'
    text+=f'namespace Snake9.LocalWindow.{mod}\n'
    text+='noncomputable def raw : List (List Nat) := '+repr(raw)+'\n'
    text+='noncomputable def cnf : List (List Int) := raw.map (List.map decodeLit)\n'
    text+='def originalIdsMinusOne : List Nat := '+repr([x-1 for x in variables])+'\n'
    text+='def originalVar (n : Nat) : Nat := originalIdsMinusOne.getD (n - 1) 0 + 1\n'
    text+='noncomputable def originalCnf : List (List Int) := renameCnf originalVar cnf\n'
    text+='theorem originalVar_pos (n : Nat) : 0 < originalVar n := by unfold originalVar; omega\n'
    text+=f'end Snake9.LocalWindow.{mod}\n'
    rel=f'LocalWindowCnf/{mod}.lean';dest=OLD/'src'/rel;dest.parent.mkdir(parents=True,exist_ok=True)
    dest.write_text(text,encoding='utf-8',newline='\n')
    r=dict(index=index,backend='FastRup',format='compact-core-only-v1',variables=len(variables),input_clauses=len(clauses),
        generated_files={rel:common.digest(dest)},artifacts={p.name:common.digest(p) for p in case.iterdir() if p.is_file() and p.name!='ready.json'})
    common.atomic(ready,r);return r

def generate(index,legacy,state):
    row=JOB/'cases'/f'{index:02d}.json';case=OLD/'cases'/f'{index:02d}'
    ready=core(index,legacy);mod=f'ParallelShare{index:02d}';name=f'FastShare{index:02d}'
    if row.exists():
        r=common.read(row);assert common.digest(case/'ready.json')==r['core_ready_sha256']
        for p,h in r['files'].items():assert common.digest(SRC/p)==h
        return r
    rel=f'LocalWindowCnf/{mod}.lean';dest=SRC/rel;dest.parent.mkdir(parents=True,exist_ok=True)
    dest.write_bytes((OLD/'src'/rel).read_bytes())
    command=[sys.executable,str(JOB/'gen_fast.py'),str(case/f'parallel_share_{index:02d}.cnf'),
        str(case/f'parallel_share_{index:02d}.lrat'),name,name,'--block-hints','25000','--module-hints','250000']
    env=os.environ.copy();env['PYTHONUTF8']='1'
    result=subprocess.run(command,cwd=SRC,env=env,text=True,encoding='utf-8',capture_output=True,timeout=1800)
    log=JOB/'logs'/(name+'-generation.log');log.parent.mkdir(parents=True,exist_ok=True)
    log.write_text(result.stdout+result.stderr,encoding='utf-8');assert result.returncode==0,result.stderr
    code=f'''import {name}.Main
import LocalWindowCnf.{mod}
import FastRupLocalWindow
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace Snake9.LocalWindow.Fast{mod}
theorem exact_cnf : {name}.F = {mod}.cnf := by rfl
theorem unsat : Unsat {mod}.cnf := by
  rw [\u2190 exact_cnf]
  exact unsat_of_fastRup {name}_unsat
theorem original_unsat : Unsat {mod}.originalCnf :=
  Unsat.rename unsat {mod}.originalVar {mod}.originalVar_pos
#print axioms unsat
#print axioms original_unsat
end Snake9.LocalWindow.Fast{mod}
'''
    (SRC/name/'LocalWindow.lean').write_text(code,encoding='utf-8',newline='\n')
    paths=[dest,*sorted((SRC/name).glob('*.lean'))]
    r=dict(index=index,target=name+'.LocalWindow',core_ready_sha256=common.digest(case/'ready.json'),
        files={p.relative_to(SRC).as_posix():common.digest(p) for p in paths},command=command,
        generation_log_sha256=common.digest(log),statistics=result.stderr.strip())
    common.atomic(row,r);return r

def build(name,m,state,checked):
    if name.startswith(('Init','Std','Lean','Mathlib')):return None
    if name in checked:return checked[name]
    source=SRC/(name.replace('.','/')+'.lean');data=source.read_bytes();deps={}
    for line in data.decode().splitlines():
        if line.startswith('import '):
            for dep in line.split('--')[0].split()[1:]:
                h=build(dep,m,state,checked)
                if h:deps[dep]=h
    c=m['config'];own=common.hashbytes(data)
    closure=common.hashbytes(json.dumps([own,deps,c['lean_version'],c['tools'],c['mathlib_commit']],sort_keys=True).encode())
    out=source.with_suffix('.olean');old=state['completed'].get(name)
    if old and old['closure_hash']==closure and out.exists() and common.digest(out)==old['artifact_sha256']:
        checked[name]=closure;return closure
    log=JOB/'logs'/(name.replace('.','_')+'.log');log.parent.mkdir(parents=True,exist_ok=True)
    state.update(status='running',phase='FastRup kernel replay',current_item=name,latest_log=str(log),last_progress=common.now())
    common.atomic(JOB/'state.json',state)
    # Lean 4.19's kernel recursion guard depends on the native thread stack.
    # This changes capacity only; all proof terms still go through the same kernel.
    result=common.supervise([str(Path(c['lean_bin'])/'lean.exe'),'--tstack='+str(c['thread_stack_kb']),
        '--root='+str(SRC),'-o',str(out),str(source)],log,c,state)
    result.update(source_sha256=own,dependency_hashes=deps,closure_hash=closure,artifact_sha256=common.digest(out),
        log_sha256=common.digest(log),axiom_audits=common.audit_axioms(log.read_text(encoding='utf-8')),completed=common.now())
    state['completed'][name]=result;state['last_progress']=common.now();common.atomic(JOB/'state.json',state)
    checked[name]=closure;print(name,'PASS',round(result['elapsed_seconds'],2),flush=True);return closure

def run():
    m=common.read(JOB/'manifest.json');validate(m)
    own=file_lock(JOB/'runner.lock');shared=file_lock(OLD/'runner.lock')
    assert common.read(OLD/'state.json')['status']=='superseded', 'Use the validated handoff first'
    legacy=common.read(OLD/'manifest.json');state=common.read(JOB/'state.json')
    context=common.process_context
    def isolated(c):
        env=context(c);base=str(HERE/'build/frozen/src')
        external=[p for p in env['LEAN_PATH'].split(os.pathsep) if os.path.normcase(p)!=os.path.normcase(base)]
        env['LEAN_PATH']=os.pathsep.join([str(SRC),*external]);return env
    common.RUNTIME=JOB;common.process_context=isolated
    state.update(status='running',pid=os.getpid(),started=common.now());state.pop('failure',None)
    common.atomic(JOB/'state.json',state)
    try:
        for index in range(34):
            if str(index) in state['cases'] and state['cases'][str(index)]['backend']=='legacy':continue
            state.update(current_item=f'core {index:02d}',phase='Exact compact core and replay generation',heartbeat=common.now())
            common.atomic(JOB/'state.json',state)
            r=generate(index,legacy,state);target=r['target'];h=build(target,m,state,{})
            audits=state['completed'][target]['axiom_audits'];assert len(audits)==2,('missing audit',target)
            state['cases'][str(index)]=dict(backend='FastRup',target=target,closure_hash=h,axiom_audits=audits,
                generation_receipt_sha256=common.digest(JOB/'cases'/f'{index:02d}.json'),completed=common.now())
            state.update(kernel_cases=len(state['cases']),last_progress=common.now());common.atomic(JOB/'state.json',state)
        validate(m);state.update(status='boolean_complete',current_item=None,finished=common.now())
    except BaseException as ex:
        state.update(status='action_required',failure=str(ex));state['failures'].append(dict(time=common.now(),item=state.get('current_item'),error=str(ex)))
        traceback.print_exc()
    finally:
        common.atomic(JOB/'state.json',state);shared.close();own.close()
    print(json.dumps(dict(status=state['status'],kernel_cases=state['kernel_cases'],failure=state.get('failure'))))

PAGE='''<!doctype html><meta charset="utf-8"><title>Q9 verification</title>
<style>body{font:16px system-ui;max-width:1100px;margin:40px auto;padding:0 24px;background:#f5f5f2;color:#212522}table{width:100%;background:white;border-collapse:collapse}th,td{padding:12px;text-align:left;border-bottom:1px solid #ddd}pre{white-space:pre-wrap;overflow-wrap:anywhere}</style>
<h1>Q9 · 231 验证</h1><p>全局 231 / 230 尚未完成。各项检查分开显示，完成数不代表最终证明的进度。</p><div id="app"></div>
<script>const esc=x=>String(x??'—').replaceAll('&','&amp;').replaceAll('<','&lt;');async function refresh(){let s=await(await fetch('/state')).json();let a=s.applicability,k=s.kernel,l=s.live,f=s.aggregate;let rows=[['Boolean 内核反证（含已完成旧结果）',(k.kernel_cases??0)+' / 34'],['Boolean 状态 / 当前项',k.status+' / '+k.current_item],['Boolean 阶段',k.phase],['Boolean 最新完成',k.last_progress],['Boolean 资源',JSON.stringify(k.resources)],['几何适用性',(a.applicability_cases??0)+' / 34'],['几何状态 / 当前项',a.status+' / '+a.current_item],['几何最新完成',a.last_progress],['几何资源',JSON.stringify(l.resources)],['条件式聚合独立重建',Object.keys(f.completed??{}).length+' / 220'],['聚合状态 / 当前项',f.status+' / '+f.current],['检查点',s.checkpoint],['全局上界','未解决；尚需局部计数反证、汇总定理及完整独立审计']];document.getElementById('app').innerHTML='<table>'+rows.map(([x,y])=>'<tr><th>'+esc(x)+'</th><td>'+esc(y)+'</td></tr>').join('')+'</table><h2>失败记录（含历史记录）</h2><pre>'+esc(JSON.stringify({boolean:k.failures,applicability:a.failures,aggregate:f.failure},null,2))+'</pre><h2>最新 Boolean 日志</h2><pre>'+esc(await(await fetch('/log')).text())+'</pre>';}refresh();setInterval(refresh,5000);</script>'''

def serve(port):
    class Handler(http.server.BaseHTTPRequestHandler):
        def do_GET(self):
            if self.path=='/state':
                ap=HERE/'runtime/applicability'
                data=json.dumps(dict(kernel=common.read(JOB/'state.json'),applicability=common.read(ap/'state.json'),
                    live=common.read(ap/'live.json'),
                    aggregate=common.read(HERE/'runtime/fresh/97db4f7433a54258ca26ec7329a81011781290c3/ParallelShareAggregate231/state.json'),
                    checkpoint=str(JOB/'state.json'))).encode();kind='application/json'
            elif self.path=='/log':
                p=common.read(JOB/'state.json').get('latest_log')
                data=('\n'.join(Path(p).read_text(encoding='utf-8',errors='replace').splitlines()[-20:]) if p else '').encode();kind='text/plain'
            else:data=PAGE.encode();kind='text/html'
            self.send_response(200);self.send_header('Content-Type',kind+'; charset=utf-8');self.end_headers();self.wfile.write(data)
        def log_message(self,*args):pass
    http.server.ThreadingHTTPServer(('127.0.0.1',port),Handler).serve_forever()

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('mode',choices=['prepare','handoff','run','serve']);p.add_argument('--port',type=int,default=8798)
    p.add_argument('--refresh',action='store_true',help='Refreeze a stopped operational repair while retaining matching proof checkpoints')
    a=p.parse_args()
    if a.refresh and a.mode!='prepare':p.error('--refresh requires prepare')
    if a.mode=='prepare':prepare(a.refresh)
    elif a.mode=='handoff':handoff()
    elif a.mode=='run':run()
    else:serve(a.port)
