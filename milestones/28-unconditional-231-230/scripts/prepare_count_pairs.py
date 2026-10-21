"""Reproduce four existing two-centre cores, without changing their geometry.

Existing Lean CNF and applicability sources are reused. A single fixed solver
configuration produces LRAT for each missing replay; an independent RUP checker
validates it before FastRup export. Lean verifies the exact selected-clause map.
"""
import ast
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time
import runner as r

PIN='4887deb02a3a51e2775ef5e81a2fb5ddc980a669'
JOB=r.HERE/'runtime/count-pairs'
SRC=JOB/'src'
MODULES=['D012A11','D012A12','D012A13','Q012A14']

def prepare():
    manifest=r.read(r.HERE/'runtime/manifest.json');r.validate(manifest)
    c=manifest['config'];commit=r.git('rev-parse','HEAD').decode().strip()
    SRC.mkdir(parents=True,exist_ok=True)
    exporter=JOB/'gen_fast.py';data=r.blob(PIN,'milestones/07-window-223/bridge/fast/gen_fast.py')
    if exporter.exists():assert exporter.read_bytes()==data
    else:exporter.write_bytes(data)
    spec=importlib.util.spec_from_file_location('count_pair_fast_exporter',exporter)
    gen=importlib.util.module_from_spec(spec);spec.loader.exec_module(gen)
    receipts=[]
    for i,mod in enumerate(MODULES):
        case=JOB/'cases'/mod;case.mkdir(parents=True,exist_ok=True)
        source=r.blob(commit,f'work/final_lean/LocalWindowCnf/{mod}.lean')
        text=source.decode();body=text.split('def raw : List (List Nat) :=',1)[1]
        raw=ast.literal_eval(re.split(r'\n(?:noncomputable )?def cnf',body,maxsplit=1)[0].strip())
        clauses=[[x//2 if x%2==0 else -(x//2) for x in cl] for cl in raw]
        nv=max(abs(x) for cl in clauses for x in cl)
        cnf=case/'model.cnf';proof=case/'proof.lrat';log=case/'solver.log'
        data=(f'p cnf {nv} {len(clauses)}\n'+''.join(' '.join(map(str,cl))+' 0\n' for cl in clauses)).encode('ascii')
        if cnf.exists():assert cnf.read_bytes()==data
        else:cnf.write_bytes(data)
        solver=Path(c['lean_bin'])/'cadical.exe'
        command=[str(solver),'--elim=false','--lrat','--no-binary','--seed=1','-q',str(cnf),str(proof)]
        receipt=case/'replay.json'
        if receipt.exists():
            row=r.read(receipt)
            assert row['command']==command and row['cnf_sha256']==r.digest(cnf) and row['proof_sha256']==r.digest(proof)
            assert row['solver_sha256']==r.digest(solver)
        else:
            start=time.monotonic()
            with log.open('w',encoding='utf-8') as f:
                result=subprocess.run(command,stdout=f,stderr=subprocess.STDOUT,timeout=1800)
            assert result.returncode==20,('unresolved solver',mod,result.returncode)
            solved=time.monotonic();row=r.check(cnf,proof)
            row.update(command=command,solver_sha256=r.digest(solver),solver_version=c['solver_version'],
                solver_seconds=solved-start,replay_seconds=time.monotonic()-solved,seed=1,threads=1,
                timeout_seconds=1800,memory_policy='observe_only',existing_cnf_source_sha256=r.hashbytes(source),
                source_commit=commit,module=mod,created=r.now())
            r.atomic(receipt,row)
        steps=gen.read_lrat(proof,len(clauses))
        ids=sorted({h-1 for _,_,hs in steps for h in hs if h<=len(clauses)})
        name='FastCount'+mod;env=os.environ.copy();env['PYTHONUTF8']='1'
        command=[sys.executable,str(exporter),str(cnf),str(proof),name,name,
            '--block-hints','25000','--module-hints','250000']
        result=subprocess.run(command,cwd=SRC,env=env,text=True,encoding='utf-8',capture_output=True,timeout=1800)
        (case/'generation.log').write_text(result.stdout+result.stderr,encoding='utf-8')
        assert result.returncode==0,result.stderr
        code=f'''import {name}.Main
import LocalWindowSat.{mod}
import FastRupLocalWindow
import LocalWindowSelectedClauses
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace Snake9.LocalWindow.{name}
def ids : List Nat := {ids}
theorem valid : ids.all (fun i => decide (i < {mod}.cnf.length)) = true := by decide +kernel
theorem exact_cnf : {name}.F = selectedClauses {mod}.cnf ids := by rfl
theorem unsat : Unsat {mod}.cnf := by
  apply unsat_of_selected valid
  rw [\u2190 exact_cnf]
  exact unsat_of_fastRup {name}_unsat
theorem refuted : Refuted (winOf [0,1,2]) [(1,1),({i+1},{i+1})] :=
  Tags.refuted_of_sat {mod}.sat unsat
#print axioms unsat
#print axioms refuted
end Snake9.LocalWindow.{name}
'''
        (SRC/name/'LocalWindow.lean').write_text(code,encoding='utf-8',newline='\n')
        row=dict(module=mod,target=name+'.LocalWindow',solver_receipt_sha256=r.digest(receipt),
            cnf_source_sha256=r.hashbytes(source),generation_command=command,
            generated_files={p.relative_to(SRC).as_posix():r.digest(p) for p in (SRC/name).glob('*.lean')},
            statistics=result.stderr.strip())
        receipts.append(row);r.atomic(JOB/'manifest.json',dict(source_commit=commit,exporter_commit=PIN,
            exporter_sha256=r.digest(exporter),preparer_sha256=r.digest(__file__),cases=receipts,
            scope='Four two-centre replay preparations; Lean targets are not yet compiled by this script'))
        print(mod,'independent RUP passed;',result.stderr.strip(),flush=True)
    print('Build targets:', ' '.join(x['target'] for x in receipts))

if __name__=='__main__':prepare()
