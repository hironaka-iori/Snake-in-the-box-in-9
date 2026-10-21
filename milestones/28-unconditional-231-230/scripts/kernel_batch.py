"""Resumable source-only Lean replay of the 34 parallel-share Boolean cores.

This is Boolean refutation only. The geometric applicability theorem is separate.
Inputs are the exact CNF/LRAT pairs independently checked by runner.py. Every
generated source, dependency closure, tool and compiled output is hash-bound.
"""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time
import traceback
import runner as common

HERE=common.HERE
ROOT=common.ROOT
JOB=HERE/'runtime/kernel'
SRC=JOB/'src'
INPUTS=HERE/'build/frozen/cases'
SCRIPT_DIR='milestones/10-window-aggregate/scripts/'

def freeze(commit,relative,dest):
    dest.parent.mkdir(parents=True,exist_ok=True)
    dest.write_bytes(common.blob(commit,relative))

def prepare():
    if (JOB/'manifest.json').exists():raise RuntimeError('Use run for an existing batch')
    JOB.mkdir(parents=True,exist_ok=True)
    commit=common.git('rev-parse','HEAD').decode().strip()
    original=common.read(HERE/'runtime/manifest.json')
    common.validate(original)
    config=original['config'].copy()
    config.update(source_commit=commit,worker_sha256=common.digest(__file__),
        runner_sha256=common.digest(HERE/'scripts/runner.py'),timeout_seconds=1800,
        input_manifest_sha256=common.digest(HERE/'runtime/manifest.json'))
    for name in ['gen_lean_lrat.py','gen_checker_variants.py']:
        freeze(commit,SCRIPT_DIR+name,JOB/'exporter'/name)
    for name in ['LocalWindowModel','LocalWindowRename','ParallelShareTerm','ParallelShareCounter',
                 'LratCheck','LratFast','LratFast2','LratFast2F']:
        freeze(commit,'work/final_lean/'+name+'.lean',SRC/(name+'.lean'))
    inputs={}
    for i in range(34):
        p=INPUTS/f'{i:02d}'
        receipt=common.read(p/'result.json')
        assert receipt['status']=='independent_RUP_replay_passed'
        assert common.digest(p/'model.cnf')==receipt['cnf_sha256']
        assert common.digest(p/'proof.lrat')==receipt['proof_sha256']
        inputs[str(i)]={f:common.digest(p/f) for f in ['model.cnf','proof.lrat','result.json']}
    files={p.relative_to(JOB).as_posix():common.digest(p)
           for folder in [SRC,JOB/'exporter'] for p in folder.rglob('*') if p.is_file()}
    m=dict(created=common.now(),config=config,inputs=inputs,frozen_files=files,
        scope='Lean Boolean refutations of exact share cores; arbitrary-snake applicability and global 231/230 unresolved')
    common.atomic(JOB/'manifest.json',m)
    common.atomic(JOB/'state.json',dict(status='prepared',completed={},case_results={},failures=[],
        global_231='UNRESOLVED',global_230='UNRESOLVED',last_progress=common.now()))
    print(json.dumps(dict(commit=commit,cases=34,manifest=str(JOB/'manifest.json'))))

def validate(m):
    c=m['config']
    assert common.digest(__file__)==c['worker_sha256']
    assert common.digest(HERE/'scripts/runner.py')==c['runner_sha256']
    assert common.digest(HERE/'scripts/replay.py')==c['replay_sha256']
    for p,h in c['tools'].items():assert common.digest(p)==h,p
    for p,h in m['frozen_files'].items():assert common.digest(JOB/p)==h,p

def load_exporter():
    sys.path.insert(0,str(JOB/'exporter'))
    import gen_lean_lrat as gen
    import gen_checker_variants as variants
    return gen,variants

def checker(gen,variants,off):
    """Generate and compile ordinary proved checkers at the required constants."""
    suffix=f'P{off}W17'
    bns='LratP'+str(off);bmod='LratCheckP'+str(off)
    fmod='LratFast'+suffix;f2='LratFast2'+suffix;f2f='LratFast2F'+suffix
    base=(SRC/'LratCheck.lean').read_text(encoding='utf-8')
    fast=(SRC/'LratFast.lean').read_text(encoding='utf-8')
    two=(SRC/'LratFast2.lean').read_text(encoding='utf-8')
    force=(SRC/'LratFast2F.lean').read_text(encoding='utf-8')
    texts={bmod:variants.variant(base,13,off,bns,'LratFast','LocalWindowModel'),
        fmod:variants.variant(fast,17,off,bns,fmod,bmod)}
    text=two.replace('import LratFast\n','import '+fmod+'\n')
    text=text.replace('4096',str(1<<16)).replace('4800',str(2*off)).replace('2400',str(off))
    text=re.sub(r'\b13\b','17',text.replace('8191',str((1<<17)-1)))
    text=text.replace('Snake9.LratFast2','@@F2@@').replace('Snake9.LratFast','Snake9.'+fmod)
    text=text.replace('Snake9.Lrat ','Snake9.'+bns+' ').replace('Snake9.Lrat.','Snake9.'+bns+'.')
    texts[f2]=text.replace('@@F2@@','Snake9.'+f2)
    text=force.replace('import LratFast2\n','import '+f2+'\n')
    text=text.replace('Snake9.LratFast2F','@@F2F@@').replace('Snake9.LratFast2','@@F2@@')
    text=text.replace('Snake9.LratFast','Snake9.'+fmod)
    text=text.replace('Snake9.Lrat ','Snake9.'+bns+' ').replace('Snake9.Lrat.','Snake9.'+bns+'.')
    texts[f2f]=text.replace('@@F2F@@','Snake9.'+f2f).replace('@@F2@@','Snake9.'+f2)
    for mod,text in texts.items():
        p=SRC/(mod+'.lean')
        if p.exists():assert p.read_text(encoding='utf-8')==text,mod
        else:p.write_text(text,encoding='utf-8',newline='\n')
    gen.set_width(17,True,2400,True)
    gen.OFF=off;gen.BASE_NS='Snake9.'+bns;gen.F2F=f2f
    gen.CHECKER_IMPORT='import '+f2
    gen.CHECKER_OPEN=f'open Snake9.{fmod}\nopen Snake9.{f2}\nopen Snake9.{bns} (Tree TreeTrue andB)'
    gen.DATA_DEF='noncomputable def';gen.GROUPED=True

def prepare_case(index,m):
    case=JOB/'cases'/f'{index:02d}';case.mkdir(parents=True,exist_ok=True)
    ready=case/'ready.json'
    if ready.exists():
        d=common.read(ready)
        for p,h in d['generated_files'].items():assert common.digest(SRC/p)==h,p
        for p,h in d['artifacts'].items():assert common.digest(case/p)==h,p
        return d
    source=INPUTS/f'{index:02d}'
    for f,h in m['inputs'][str(index)].items():assert common.digest(source/f)==h,f
    lemmas={};last=None
    for line in (source/'proof.lrat').read_text().splitlines():
        t=line.split()
        if len(t)<2 or t[1]=='d':continue
        t=list(map(int,t));z=t.index(0,1)
        assert t[-1]==0 and all(x>0 for x in t[z+1:-1])
        assert all(x<t[0] for x in t[z+1:-1])
        lemmas[t[0]]=(t[1:z],t[z+1:-1]);last=t[0]
    assert not lemmas[last][0]
    needed={last};stack=[last]
    while stack:
        k=stack.pop()
        if k in lemmas:
            for h in lemmas[k][1]:
                if h not in needed:needed.add(h);stack.append(h)
    input_ids=sorted(needed-lemmas.keys());inputs={};nv=set();nc=0
    for line in (source/'model.cnf').read_text().splitlines():
        if not line or line[0] in 'pc':continue
        nc+=1
        if nc in needed and nc not in lemmas:
            inputs[nc]=list(map(int,line.split()[:-1]));nv.update(map(abs,inputs[nc]))
    assert set(inputs)==set(input_ids)
    used_lemmas=sorted(needed&lemmas.keys())
    for k in used_lemmas:nv.update(map(abs,lemmas[k][0]))
    variables=sorted(nv);ren={v:i+1 for i,v in enumerate(variables)}
    ids={v:i+1 for i,v in enumerate(input_ids+used_lemmas)}
    def rename(cl):return [ren[abs(x)] if x>0 else -ren[abs(x)] for x in cl]
    core=[rename(inputs[k]) for k in input_ids]
    name=f'parallel_share_{index:02d}';mod=f'ParallelShare{index:02d}'
    cnf=case/(name+'.cnf');proof=case/(name+'.lrat')
    with open(cnf,'w',encoding='ascii',newline='\n') as f:
        f.write(f'p cnf {len(variables)} {len(core)}\n')
        for cl in core:f.write(' '.join(map(str,cl))+' 0\n')
    with open(proof,'w',encoding='ascii',newline='\n') as f:
        for k in used_lemmas:
            cl,hs=lemmas[k]
            f.write(' '.join(map(str,[ids[k],*rename(cl),0,*[ids[h] for h in hs],0]))+'\n')
    replay=common.check(cnf,proof)
    common.atomic(case/'compact-replay.json',replay)
    meta=dict(module=mod,core_ids=list(range(1,len(core)+1)),original_clause_ids=input_ids,
        original_variable_ids=variables,source_hashes=m['inputs'][str(index)])
    common.atomic(case/(name+'.json'),meta)
    cnfdir=SRC/'LocalWindowCnf';cnfdir.mkdir(exist_ok=True)
    raw=[[2*abs(x)+(x<0) for x in cl] for cl in core]
    text='import LocalWindowRename\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n'
    text+=f'namespace Snake9.LocalWindow.{mod}\n'
    text+='noncomputable def raw : List (List Nat) := '+repr(raw)+'\n'
    text+='noncomputable def cnf : List (List Int) := raw.map (List.map decodeLit)\n'
    text+='def originalIdsMinusOne : List Nat := '+repr([x-1 for x in variables])+'\n'
    text+='def originalVar (n : Nat) : Nat := originalIdsMinusOne.getD (n - 1) 0 + 1\n'
    text+='noncomputable def originalCnf : List (List Int) := renameCnf originalVar cnf\n'
    text+='theorem originalVar_pos (n : Nat) : 0 < originalVar n := by unfold originalVar; omega\n'
    text+=f'end Snake9.LocalWindow.{mod}\n'
    (cnfdir/(mod+'.lean')).write_text(text,encoding='utf-8',newline='\n')
    gen,variants=load_exporter()
    off=next(x for x in [2400,4000,8000,16000,32000] if len(variables)<x)
    checker(gen,variants,off)
    stats=gen.export(name,str(case),12000,1,1,True,str(SRC),str(case))
    entry=SRC/'LocalWindowUnsat'/(mod+'.lean')
    with open(entry,'a',encoding='utf-8',newline='\n') as f:
        f.write(f'\nnamespace Snake9.LocalWindow.{mod}\n')
        f.write('theorem original_unsat : Unsat originalCnf := Unsat.rename unsat originalVar originalVar_pos\n')
        f.write('#print axioms original_unsat\n')
        f.write(f'end Snake9.LocalWindow.{mod}\n')
    generated={p.relative_to(SRC).as_posix():common.digest(p)
        for p in SRC.rglob('*.lean') if mod in p.parts or p.stem==mod or 'P'+str(off) in p.stem}
    d=dict(index=index,target='LocalWindowUnsat.'+mod,stats=stats,variables=len(variables),
        input_clauses=len(core),offset=off,generated_files=generated,
        artifacts={p.name:common.digest(p) for p in case.iterdir() if p.is_file() and p.name!='ready.json'})
    common.atomic(ready,d)
    return d

def build_module(name,m,state,visiting=None):
    if name.startswith(('Std','Init','Lean')):return None
    visiting=set() if visiting is None else visiting
    if name in visiting:raise RuntimeError('Cyclic import '+name)
    visiting.add(name)
    source=SRC/(name.replace('.','/')+'.lean')
    text=source.read_text(encoding='utf-8');deps={}
    for line in text.splitlines():
        if line.startswith('import '):
            for dep in line.split('--')[0].split()[1:]:
                h=build_module(dep,m,state,visiting)
                if h:deps[dep]=h
    visiting.remove(name)
    source_hash=common.digest(source)
    closure=common.hashbytes(json.dumps([source_hash,deps,m['config']],sort_keys=True).encode())
    out=source.with_suffix('.olean');key='lean:'+name;cached=state['completed'].get(key)
    if cached and cached['closure_hash']==closure and out.exists() and common.digest(out)==cached['artifact_sha256']:
        return closure
    log=JOB/'logs'/(name.replace('.','_')+'.log');log.parent.mkdir(exist_ok=True)
    state.update(current_item=name,latest_log=str(log),phase='Lean Boolean-certificate source rebuild')
    common.current('Lean kernel replay; geometric applicability still unresolved')
    command=[str(Path(m['config']['lean_bin'])/'lean.exe'),'--root='+str(SRC),'-o',str(out),str(source)]
    result=common.supervise(command,log,m['config'],state)
    result.update(source_sha256=source_hash,dependency_hashes=deps,closure_hash=closure,
        artifact_sha256=common.digest(out),axiom_audits=common.audit_axioms(log.read_text(encoding='utf-8')),
        completed=common.now())
    state['completed'][key]=result;state['last_progress']=common.now()
    common.atomic(JOB/'state.json',state)
    return closure

def run(indices):
    m=common.read(JOB/'manifest.json');validate(m)
    # Reuse the tested process supervisor, with an isolated lock, output directory,
    # and LEAN_PATH containing only this batch's custom modules.
    common.RUNTIME=JOB
    def context(config):
        env=os.environ.copy()
        env['PATH']=config['lean_bin']+os.pathsep+env.get('PATH','')
        env['LEAN_PATH']=str(SRC)
        return env
    common.process_context=context
    held=common.lock();state=common.read(JOB/'state.json')
    state.pop('failure',None)
    state.update(status='running',pid=os.getpid(),started=common.now(),checkpoint=str(JOB/'state.json'),
        manifest=str(JOB/'manifest.json'),target='231: Lean refutations of 34 parallel-share Boolean cores',
        totals=dict(lean_modules='generated as cases are prepared',solver_cases=34,independent_replays=34,kernel_cases=34),
        solver_receipts=34,independent_replay_count=34,kernel_cases=len(state['case_results']),
        semantic_obligations=['Connect full parallel-share CNF to arbitrary snakes',
            '15,959 count-window Lean refutations and complete normalization',
            'Unconditional 231 theorem, interval, full fresh transitive rebuild',
            'Then unconditional 230 and its full fresh transitive rebuild'])
    common.atomic(JOB/'state.json',state)
    try:
        build_module('ParallelShareCounter',m,state)
        for index in indices:
            state.update(phase='Prepare exact dependency-trimmed proof',current_item=f'Share case {index:02d}')
            common.atomic(JOB/'state.json',state)
            d=prepare_case(index,m)
            closure=build_module(d['target'],m,state)
            receipt=state['completed']['lean:'+d['target']]
            assert receipt['axiom_audits'], 'No final theorem audit'
            state['case_results'][str(index)]=dict(target=d['target'],closure_hash=closure,
                theorem='Snake9.LocalWindow.ParallelShare'+f'{index:02d}'+'.original_unsat',
                axioms=receipt['axiom_audits'],completed=common.now(),stats=d['stats'])
            state['kernel_cases']=len(state['case_results']);state['last_progress']=common.now()
            common.atomic(JOB/'state.json',state)
        validate(m)
        state.update(status='partial_batch_complete',phase='Boolean batch complete; geometric proof still required',
            current_item=None,child_pid=None,last_progress=common.now(),completion_scope=m['scope'])
    except BaseException as ex:
        state.update(status='action_required',failure=str(ex),child_pid=None)
        state['failures'].append(dict(time=common.now(),item=state.get('current_item'),error=str(ex)))
        traceback.print_exc()
    finally:
        common.atomic(JOB/'state.json',state);held.close()
    print(json.dumps(dict(status=state['status'],kernel_cases=state['kernel_cases'],failure=state.get('failure'))))

def serve(a):
    common.RUNTIME=JOB
    common.PAGE=common.PAGE.replace("k+' / 34'","(s.independent_replay_count??0)+' / 34'")
    common.PAGE=common.PAGE.replace("['Lean 局部 share 反证','0 / 34']",
        "['Lean Boolean share 反证',(s.kernel_cases??0)+' / 34']")
    common.serve(a)

if __name__=='__main__':
    ap=argparse.ArgumentParser();sub=ap.add_subparsers(dest='action',required=True)
    sub.add_parser('prepare')
    p=sub.add_parser('run');p.add_argument('--indices',type=int,nargs='*',default=[1,*[i for i in range(34) if i!=1]])
    p=sub.add_parser('serve');p.add_argument('--port',type=int,default=8796)
    a=ap.parse_args()
    if a.action=='prepare':prepare()
    elif a.action=='run':run(a.indices)
    else:serve(a)
