"""Prepare a bounded-memory equivalent of the frozen157 experiment."""
from pathlib import Path
import ast
import hashlib
import json

H = Path(__file__).resolve().parents[1]
R = H.parents[1]
OLD = R/'milestones/157-weaker-share-floor'

def sha(p):
    h=hashlib.sha256()
    with Path(p).open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''): h.update(b)
    return h.hexdigest()

def read(p):
    return json.loads(Path(p).read_text(encoding='utf-8-sig'))

def write(p,b):
    if isinstance(b,str): b=b.encode('utf-8')
    if p.exists(): assert p.read_bytes()==b, str(p)
    else: p.write_bytes(b)

def main():
    (H/'data').mkdir(exist_ok=True)
    old=read(OLD/'data/preparation.json')
    assert sha(OLD/'data/preparation.json')=='acb48dd573b7707ace113e87d5fe1c5dcd026336c12c1fea32bbad85a05077e9'
    for p,d in {**old['script_pins'],**old['input_pins']}.items(): assert sha(R/p)==d,p
    worker=(OLD/'scripts/potential_range.py').read_text(encoding='utf-8')
    assert worker.count('from reconstruct144 import reconstruct')==1
    worker=worker.replace('from reconstruct144 import reconstruct','from reconstruct_small import reconstruct').replace('SNAKE157_WORKER_PARENT','SNAKE158_WORKER_PARENT')
    write(H/'scripts/potential_range.py',worker)
    runner=(OLD/'scripts/run_potential.py').read_text(encoding='utf-8')
    assert runner.count('(3*GIB if before_start else 768*1024**2)')==1
    assert runner.count("> 3*GIB:")==1
    runner=runner.replace('(3*GIB if before_start else 768*1024**2)','(2*GIB if before_start else 768*1024**2)').replace('> 3*GIB:', '> GIB:').replace('SNAKE157_WORKER_PARENT','SNAKE158_WORKER_PARENT')
    write(H/'scripts/run_potential.py',runner)
    for name in ['native_resources.py','native_guard.py']:
        write(H/'scripts'/name,(OLD/'scripts'/name).read_bytes())
    plan=read(R/old['plan_path'])
    plan['memory_strategy']='Accepted144 mask reused; source column hashes checked; shared weights rebuilt in batches; original144 and156 weight hashes must match before weakening floor.'
    write(H/'data/experiment-plan.json',json.dumps(plan,indent=2)+'\n')
    inputs=dict(old['input_pins'])
    for p in [OLD/'data/preparation.json', R/old['plan_path'], OLD/'scripts/potential_range.py',OLD/'scripts/run_potential.py']:
        inputs[p.relative_to(R).as_posix()]=sha(p)
    names=['prepare_sources.py','reconstruct_small.py','potential_range.py','run_potential.py','native_resources.py','native_guard.py']
    for name in names: ast.parse((H/'scripts'/name).read_text(encoding='utf-8'))
    prep=dict(status='SOURCE_PREPARED_NOT_EXECUTED',plan_path=(H/'data/experiment-plan.json').relative_to(R).as_posix(),
        plan_sha256=sha(H/'data/experiment-plan.json'),input_pins=inputs,accepted156_pins=old['accepted156_pins'],
        script_pins={(H/'scripts'/name).relative_to(R).as_posix():sha(H/'scripts'/name) for name in names},
        source157_preparation_sha256=sha(OLD/'data/preparation.json'),
        memory_limits=dict(startup_free_bytes=2*1024**3,runtime_free_bytes=768*1024**2,owned_private_bytes=1024**3),
        mask_rederived=False,mask_reused_with_hash=True,original_weight_hash_equality_required=True,
        arithmetic_and_stopping_algorithm_unchanged=True,new_global_bound=False)
    write(H/'data/preparation.json',json.dumps(prep,indent=2)+'\n')
    write(H/'.gitattributes',b'* -text\n')
    print('SOURCE_PREPARED_NOT_EXECUTED',sha(H/'data/preparation.json'))

if __name__=='__main__': main()
