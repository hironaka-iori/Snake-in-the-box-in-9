"""Isolated development build reusing only hash-validated fresh dependencies.

This does not claim a new full fresh build. It also avoids writing the shared
development directory while the count-certificate worker is using it.
"""
import argparse
import json
from pathlib import Path
import shutil
import develop_lean as dev
import runner as r

def main(targets):
    base=r.HERE/'runtime/fresh/97db4f7433a54258ca26ec7329a81011781290c3/ParallelShareAggregate231'
    manifest=r.read(base/'manifest.json');old=r.read(base/'state.json')
    original=r.read(r.HERE/'runtime/manifest.json');r.validate(original);cfg=original['config']
    dev.BUILD=r.HERE/'runtime/count-pair-bridge';dev.SOURCE=dev.BUILD/'src'
    dev.SOURCE.mkdir(parents=True,exist_ok=True)
    receipt=dev.BUILD/'state.json';state=r.read(receipt) if receipt.exists() else dict(completed={})
    visited=set();imported={}
    def visit(name):
        if name.startswith(('Init','Lean','Std','Mathlib')) or name in visited:return
        visited.add(name);rel=name.replace('.','/')+'.lean'
        src=next((r.ROOT/folder/rel for folder in dev.SEARCH if (r.ROOT/folder/rel).exists()),None)
        assert src,('missing source',name)
        data=src.read_text(encoding='utf-8').replace('\r\n','\n').encode()
        for line in data.decode().splitlines():
            if line.startswith('import '):
                for dep in line.split('--')[0].split()[1:]:visit(dep)
        if name in state['completed'] or name not in old['completed']:return
        row=old['completed'][name];frozen=base/'src'/rel
        if r.hashbytes(data)!=row['source_sha256']:return
        assert r.digest(frozen)==row['source_sha256']
        assert r.digest(frozen.with_suffix('.olean'))==row['artifact_sha256']
        assert r.digest(base/'logs'/(name.replace('.','_')+'.log'))==row['log_sha256']
        deps={dep:old['completed'][dep]['closure_hash'] for dep in row['dependency_hashes']}
        assert deps==row['dependency_hashes']
        fp=r.hashbytes(json.dumps([row['source_sha256'],deps,cfg['lean_version'],cfg['tools'],cfg['mathlib_commit']],sort_keys=True).encode())
        assert fp==row['closure_hash']==manifest['modules'][name]['closure_hash']
        dest=dev.SOURCE/rel;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(data)
        shutil.copyfile(frozen.with_suffix('.olean'),dest.with_suffix('.olean'))
        state['completed'][name]={**row,'axioms':row['axiom_audits'],'donor_manifest_sha256':r.digest(base/'manifest.json')}
        imported[name]=fp
    for target in targets:visit(target)
    state['reuse_scope']='Source, dependency, tool, log and artifact hashes validated; not a new full fresh build'
    state.setdefault('fresh_donors',{}).update(imported)
    state['driver_sha256']=r.digest(__file__);r.atomic(receipt,state)
    print('Validated reusable fresh modules:',len(imported),flush=True)
    dev.main(targets)

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('targets',nargs='+')
    main(parser.parse_args().targets)
