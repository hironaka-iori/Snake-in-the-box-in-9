"""Rebuild a complete custom closure from one Git commit in an isolated directory.

Pinned external Lean/mathlib dependencies are validated. No custom .olean path
from the development or Boolean-batch builds is on LEAN_PATH. A matching saved
checkpoint may resume this particular frozen build; a new commit gets a new path.
"""
import argparse
import json
import os
from pathlib import Path
import subprocess
import time
import runner
from develop_lean import SEARCH

HERE=runner.HERE
ROOT=runner.ROOT

def main(target,commit):
    original=runner.read(HERE/'runtime/manifest.json');runner.validate(original);config=original['config']
    commit=subprocess.check_output(['git','rev-parse',commit],cwd=ROOT,text=True).strip()
    files=set(subprocess.check_output(['git','ls-tree','-r','--name-only',commit],cwd=ROOT,text=True).splitlines())
    job=HERE/'runtime/fresh'/commit/target.replace('.','_');src=job/'src';logs=job/'logs'
    src.mkdir(parents=True,exist_ok=True);logs.mkdir(exist_ok=True)
    modules={};order=[]
    def visit(name):
        if name.startswith(('Std','Init','Lean','Mathlib')):return None
        if name in modules:return modules[name]['closure_hash']
        rel=name.replace('.','/')+'.lean'
        path=next((p+'/'+rel for p in SEARCH if p+'/'+rel in files),None)
        assert path,('missing source',name)
        data=subprocess.check_output(['git','show',commit+':'+path],cwd=ROOT)
        deps={}
        for line in data.decode('utf-8').splitlines():
            if line.startswith('import '):
                for d in line.split('--')[0].split()[1:]:
                    h=visit(d)
                    if h:deps[d]=h
        own=runner.hashbytes(data)
        closure=runner.hashbytes(json.dumps([own,deps,config['lean_version'],config['tools'],config['mathlib_commit']],sort_keys=True).encode())
        dest=src/rel;dest.parent.mkdir(parents=True,exist_ok=True)
        if dest.exists():assert dest.read_bytes()==data,('changed frozen source',name)
        else:dest.write_bytes(data)
        modules[name]=dict(source_path=path,source_sha256=own,dependency_hashes=deps,closure_hash=closure)
        order.append(name);return closure
    visit(target)
    env=runner.process_context(config)
    old_custom=str(HERE/'build/frozen/src')
    external=[p for p in env['LEAN_PATH'].split(os.pathsep) if p and os.path.normcase(p)!=os.path.normcase(old_custom)]
    assert all('runtime' not in p.split(os.sep) for p in external),external
    env['LEAN_PATH']=os.pathsep.join([str(src),*external])
    manifest=dict(source_commit=commit,target=target,modules=modules,order=order,
        lean_version=config['lean_version'],mathlib_commit=config['mathlib_commit'],tools=config['tools'],
        lean_path=env['LEAN_PATH'],fresh_custom_sources=True,builder_sha256=runner.digest(__file__))
    manifest_path=job/'manifest.json'
    if manifest_path.exists():assert runner.read(manifest_path)==manifest,'Frozen build manifest changed'
    else:runner.atomic(manifest_path,manifest)
    state_path=job/'state.json';state=runner.read(state_path) if state_path.exists() else dict(completed={})
    state.update(status='running',pid=os.getpid(),source_commit=commit,target=target)
    runner.atomic(state_path,state)
    started=time.monotonic()
    try:
        for name in order:
            item=modules[name];file=src/(name.replace('.','/')+'.lean');out=file.with_suffix('.olean')
            prior=state['completed'].get(name)
            if prior and prior['closure_hash']==item['closure_hash'] and out.exists() and runner.digest(out)==prior['artifact_sha256']:continue
            log=logs/(name.replace('.','_')+'.log')
            state.update(current=name,log=str(log),heartbeat=runner.now());runner.atomic(state_path,state)
            command=[str(Path(config['lean_bin'])/'lean.exe'),'--root='+str(src),'-o',str(out),str(file)]
            before=time.monotonic()
            with log.open('w',encoding='utf-8') as handle:
                handle.write(json.dumps(command)+'\n');handle.flush()
                result=subprocess.run(command,cwd=src,env=env,stdout=handle,stderr=subprocess.STDOUT,timeout=1800)
            content=log.read_text(encoding='utf-8')
            assert result.returncode==0,(name,content)
            audits=runner.audit_axioms(content)
            state['completed'][name]=dict(**item,artifact_sha256=runner.digest(out),
                log_sha256=runner.digest(log),axiom_audits=audits,elapsed_seconds=time.monotonic()-before,
                completed=runner.now(),command=command)
            runner.atomic(state_path,state);print(name,'PASS',round(time.monotonic()-before,2),flush=True)
        runner.validate(original)
        for name,item in modules.items():
            file=src/(name.replace('.','/')+'.lean')
            assert runner.digest(file)==item['source_sha256']
            assert runner.digest(file.with_suffix('.olean'))==state['completed'][name]['artifact_sha256']
        assert state['completed'][target]['axiom_audits'],'Target has no printed axiom audit'
        state.update(status='complete',current=None,elapsed_seconds=time.monotonic()-started,finished=runner.now())
    except BaseException as ex:
        state.update(status='failed',failure=str(ex),failed=runner.now())
        runner.atomic(state_path,state);raise
    runner.atomic(state_path,state)
    print(json.dumps({'status':state['status'],'modules':len(order),'state':str(state_path),
        'target_audits':state['completed'][target]['axiom_audits']}))

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('target');ap.add_argument('--commit',default='HEAD')
    a=ap.parse_args();main(a.target,a.commit)
