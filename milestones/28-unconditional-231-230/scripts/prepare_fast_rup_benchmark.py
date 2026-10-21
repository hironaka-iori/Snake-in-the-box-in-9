"""Prepare an isolated comparison on an already replayed compact LRAT core.

No solver runs and neither live batch is modified. Compilation and axiom audits
use develop_lean.py with this benchmark's src directory as an extra source root.
"""
import argparse
import importlib.util
import os
from pathlib import Path
import subprocess
import sys
import runner

PIN='4887deb02a3a51e2775ef5e81a2fb5ddc980a669'
HERE=runner.HERE
ROOT=runner.ROOT

def add_bridge(index,job,manifest,ready):
    mod=f'ParallelShare{index:02d}';fast=f'FastShare{index:02d}'
    rel=f'LocalWindowCnf/{mod}.lean'
    core=HERE/'runtime/kernel/src'/rel
    assert runner.digest(core)==ready['generated_files'][rel]
    code=f'''import {fast}.Main
import LocalWindowCnf.{mod}
import FastRupLocalWindow
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace Snake9.LocalWindow.Fast{mod}
theorem exact_cnf : {fast}.F = {mod}.cnf := by rfl
theorem unsat : Unsat {mod}.cnf := by
  rw [\u2190 exact_cnf]
  exact unsat_of_fastRup {fast}_unsat
#print axioms unsat
end Snake9.LocalWindow.Fast{mod}
'''
    for path,data in {f'src/{rel}':core.read_bytes(),f'src/{fast}/LocalWindowV2.lean':code.encode()}.items():
        p=job/path;p.parent.mkdir(parents=True,exist_ok=True)
        if p.exists():assert p.read_bytes()==data,('changed bridge source',p)
        else:p.write_bytes(data)
        manifest['files'][path]=runner.hashbytes(data)
    manifest['bridge_target']=fast+'.LocalWindowV2'
    manifest['preparer_sha256']=runner.digest(__file__)
    runner.atomic(job/'manifest.json',manifest)

def prepare(index):
    original=runner.read(HERE/'runtime/manifest.json');runner.validate(original)
    case=HERE/'runtime/kernel/cases'/f'{index:02d}'
    ready=runner.read(case/'ready.json')
    for p,h in ready['artifacts'].items():assert runner.digest(case/p)==h,('changed input',p)
    job=HERE/'runtime/fast-rup'/f'{index:02d}';src=job/'src'
    if (job/'manifest.json').exists():
        old=runner.read(job/'manifest.json')
        assert old['ready_sha256']==runner.digest(case/'ready.json')
        for p,h in old['files'].items():assert runner.digest(job/p)==h,('changed benchmark',p)
        add_bridge(index,job,old,ready)
        print('Existing immutable benchmark:',job)
        return
    src.mkdir(parents=True,exist_ok=True)
    imported={}
    for name in ['WinCNF','FastRup','FastRupCmd']:
        path=f'work/spectral/stronger/{name}.lean'
        data=runner.blob(PIN,path);dest=src/(name+'.lean');dest.write_bytes(data)
        imported[path]=runner.hashbytes(data)
    gp='milestones/07-window-223/bridge/fast/gen_fast.py'
    data=runner.blob(PIN,gp);generator=job/'gen_fast.py';generator.write_bytes(data)
    imported[gp]=runner.hashbytes(data)
    cnf=case/f'parallel_share_{index:02d}.cnf'
    lrat=case/f'parallel_share_{index:02d}.lrat'
    spec=importlib.util.spec_from_file_location('frozen_fast_exporter',generator)
    gen=importlib.util.module_from_spec(spec);spec.loader.exec_module(gen)
    nv,clauses=gen.read_cnf(cnf);steps=gen.read_lrat(lrat,len(clauses))
    used=sorted({h for _,_,hs in steps for h in hs if h<=len(clauses)})
    assert used==list(range(1,len(clauses)+1)),'Benchmark must use the same complete compact core'
    env=os.environ.copy();env['PYTHONUTF8']='1'
    targets=[]
    def generate(name,cnf_path,lrat_path):
        command=[sys.executable,str(generator),str(cnf_path),str(lrat_path),name,name,
            '--block-hints','25000','--module-hints','250000']
        result=subprocess.run(command,cwd=src,env=env,text=True,capture_output=True,encoding='utf-8')
        (job/(name+'-generation.log')).write_text(result.stdout+result.stderr,encoding='utf-8')
        assert result.returncode==0,result.stderr
        target=name+'.Audit'
        (src/name/'Audit.lean').write_text(f'import {name}.Main\n#print axioms {name}_unsat\n',encoding='utf-8')
        targets.append(dict(target=target,command=command,statistics=result.stderr.strip()))
    generate(f'FastShare{index:02d}',cnf,lrat)
    control=job/'controls';control.mkdir(exist_ok=True)
    (control/'model.cnf').write_text('p cnf 1 2\n1 0\n-1 0\n',encoding='ascii')
    (control/'valid.lrat').write_text('3 0 1 2 0\n',encoding='ascii')
    (control/'corrupt.lrat').write_text('3 0 1 0\n',encoding='ascii')
    generate('FastRupPositive',control/'model.cnf',control/'valid.lrat')
    generate('FastRupNegative',control/'model.cnf',control/'corrupt.lrat')
    manifest=dict(created=runner.now(),upstream_commit=PIN,imported=imported,index=index,
        scope='Checker comparison and corruption control only; no new global result',
        ready_sha256=runner.digest(case/'ready.json'),cnf_sha256=runner.digest(cnf),lrat_sha256=runner.digest(lrat),
        same_compact_core=True,variables=nv,clauses=len(clauses),steps=len(steps),hints=sum(len(s[2]) for s in steps),
        targets=targets,expected_rejection='FastRupNegative.Audit',
        files={p.relative_to(job).as_posix():runner.digest(p) for p in job.rglob('*') if p.is_file()})
    add_bridge(index,job,manifest,ready)
    print({k:manifest[k] for k in ['index','variables','clauses','steps','hints','same_compact_core']})
    print('Source root:',src)

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--index',type=int,default=0)
    prepare(ap.parse_args().index)
