"""Hash-checked incremental development build; not a final fresh source rebuild."""
import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import time
import runner

ROOT=runner.ROOT
HERE=runner.HERE
BUILD=HERE/'runtime/bridge-development'
SOURCE=BUILD/'src'
BASE=HERE/'build/frozen/src'
SEARCH=['work/final_lean','work/spectral/stronger','work/spectral','milestones/27-empty-square-packing/lean',
    'milestones/28-unconditional-231-230/lean']

def main(targets):
    BUILD.mkdir(parents=True,exist_ok=True);SOURCE.mkdir(exist_ok=True)
    original=runner.read(HERE/'runtime/manifest.json');c=original['config']
    runner.validate(original)
    original_state=runner.read(HERE/'runtime/state.json')
    receipt=BUILD/'state.json'
    state=runner.read(receipt) if receipt.exists() else {'completed':{}}
    env=runner.process_context(c)
    env['LEAN_PATH']=str(SOURCE)+os.pathsep+env['LEAN_PATH']
    checked={};base_compatible={}
    state['base_dependencies']={}
    def build(name):
        if name.startswith(('Std','Init','Lean','Mathlib')):return None
        if name in checked:return checked[name]
        rel=name.replace('.','/')+'.lean'
        src=next((ROOT/p/rel for p in SEARCH if (ROOT/p/rel).exists()),None)
        assert src is not None,('missing source',name)
        data=src.read_text(encoding='utf-8').replace('\r\n','\n').encode('utf-8')
        sha=runner.hashbytes(data)
        deps={}
        for line in data.decode().splitlines():
            if line.startswith('import '):
                for dep in line.split('--')[0].split()[1:]:
                    h=build(dep)
                    if h:deps[dep]=h
        fingerprint=runner.hashbytes(json.dumps([sha,deps,c['lean_version'],c['tools'],c['mathlib_commit']],sort_keys=True).encode())
        prior=original_state['completed'].get('lean:'+name)
        frozen=original['modules'].get(name)
        base=BASE/rel
        dest=SOURCE/rel;dest.parent.mkdir(parents=True,exist_ok=True)
        if not dest.exists() or dest.read_bytes()!=data:dest.write_bytes(data)
        out=dest.with_suffix('.olean')
        compatible=(prior and frozen and prior['closure_hash']==frozen['closure_hash']
            and prior['source_sha256']==sha and all(base_compatible.get(dep,False) for dep in deps)
            and base.exists() and base.with_suffix('.olean').exists() and runner.digest(base)==sha
            and runner.digest(base.with_suffix('.olean'))==prior['artifact_sha256'])
        base_compatible[name]=bool(compatible)
        if compatible:
            # Put the checked artifact first on LEAN_PATH, replacing any stale development copy.
            if not out.exists() or runner.digest(out)!=prior['artifact_sha256']:
                shutil.copyfile(base.with_suffix('.olean'),out)
            state['base_dependencies'][name]=dict(source_sha256=sha,
                frozen_closure_hash=prior['closure_hash'],closure_hash=fingerprint,
                dependency_hashes=deps,artifact_sha256=prior['artifact_sha256'])
            checked[name]=fingerprint
            return fingerprint
        cached=state['completed'].get(name)
        if cached and cached['closure_hash']==fingerprint and out.exists() and runner.digest(out)==cached['artifact_sha256']:
            checked[name]=fingerprint;return fingerprint
        command=[str(Path(c['lean_bin'])/'lean.exe'),'--root='+str(SOURCE),'-o',str(out),str(dest)]
        log=BUILD/(name.replace('.','_')+'.log');start=time.monotonic()
        with log.open('w',encoding='utf-8') as f:
            f.write(json.dumps(command)+'\n');f.flush()
            r=subprocess.run(command,stdout=f,stderr=subprocess.STDOUT,env=env)
        text=log.read_text(encoding='utf-8')
        if r.returncode:
            print(text);raise RuntimeError(name+' failed')
        state['completed'][name]=dict(source_sha256=sha,dependency_hashes=deps,closure_hash=fingerprint,
            artifact_sha256=runner.digest(out),command=command,log_sha256=runner.digest(log),
            elapsed_seconds=time.monotonic()-start,axioms=runner.audit_axioms(text),completed=runner.now())
        runner.atomic(receipt,state);checked[name]=fingerprint
        print(name,'PASS',round(time.monotonic()-start,2),flush=True)
        if '#print axioms' in data.decode():print(text,flush=True)
        return fingerprint
    for target in targets:build(target)
    state.update(validated=runner.now(),targets=targets,active_modules=checked,builder_sha256=runner.digest(__file__),
        scope='Hash-checked incremental development build; not a final fresh source rebuild')
    runner.atomic(receipt,state)

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('targets',nargs='+');a=ap.parse_args();main(a.targets)
