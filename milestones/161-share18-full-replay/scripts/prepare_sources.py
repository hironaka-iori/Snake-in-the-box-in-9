"""Prepare161 sources and exact input pins only; no proof scan or export."""
import ast
import json
from pathlib import Path
from common import H,R,M144,M160,read,sha,completed160


def main():
    assert __debug__
    (H/'data').mkdir(parents=True,exist_ok=True)
    completion=completed160()
    for name in ['native_resources.py','native_guard.py']:
        source=M160/'scripts'/name;target=H/'scripts'/name
        if target.exists():assert target.read_bytes()==source.read_bytes()
        else:target.write_bytes(source.read_bytes())
    pins={}
    def add(path,expected=None):
        path=Path(path)
        if not path.is_absolute():path=R/path
        try:name=path.relative_to(R).as_posix()
        except ValueError:name=str(path)
        digest=sha(path)
        assert expected is None or digest==expected,name
        assert name not in pins or pins[name]==digest
        pins[name]=digest
    for relative in ['data/completion.json','data/source-plan.json','data/checkpoint-execution.json',
                     'data/checkpoint-progress.json','data/prefix1055/prefix-transport.json',
                     'data/prefix1055/run-status.json','scripts/prefix_transport.py',
                     'scripts/native_resources.py','scripts/native_guard.py','scripts/audit_checkpoint.py']:
        add(M160/relative)
    native=read(M160/'data/prefix1055/prefix-transport.json')
    assert sha(M160/'data/prefix1055/prefix-transport.json')==completion['native_receipt_sha256']
    add(M160/'data/prefix1055'/native['checkpoint_file'],native['checkpoint_sha256'])
    previous=read(M160/'data/source-plan.json')
    for mapping in [previous['input_pins'],previous['source_pins'],read(M160/'data/checkpoint-execution.json')['input_pins']]:
        for path,digest in mapping.items():add(path,digest)
    external={}
    for home,module in [(M160,'CheckpointData160'),(M160,'CheckpointCheck160'),(M160,'CheckpointConsequence160'),
                        (M144,'LratCheck144'),(M144,'LratFast144'),(M144,'LocalWindowCnf.ShareWindow144')]:
        receipt_path=home/'data'/(module+'-audit.json');receipt=read(receipt_path);add(receipt_path)
        assert receipt['status'] in ['PASS','PASS_WINDOW_REPLAY_MODULE'] and receipt['exit_code']==0
        source=Path(receipt['source']) if 'source' in receipt else home/'lean'/(module.replace('.','/')+'.lean')
        obj=Path(receipt['object']) if 'object' in receipt else home/'build-base'/(module.replace('.','/')+'.olean')
        log=Path(receipt['log']);log=log if log.is_absolute() else home/log
        add(source,receipt['source_sha256']);add(obj,receipt['olean_sha256']);add(log,receipt['log_sha256'])
        for path,digest in receipt['dependencies'].items():add(path,digest)
        external[module]=dict(receipt=receipt_path.relative_to(R).as_posix(),receipt_sha256=sha(receipt_path),
            status=receipt['status'],source=str(source),source_sha256=receipt['source_sha256'],
            object=str(obj),object_sha256=receipt['olean_sha256'],log=str(log),log_sha256=receipt['log_sha256'])
    for path in ['milestones/153-pair-conditioned-share17/replay/prepare_replay.py',
                 'milestones/153-pair-conditioned-share17/replay/transport_replay.py',
                 'milestones/155-share17-replay/scripts/emit_full_v2.py',
                 'milestones/159-share18-proof-continuation/data/semantics-completion.json']:
        add(path)
    assert sha(M144/'certificates/share144.lrat')=='74ab1a039d1476e03cfed0500f95f5f27d5935589942c227ff39315d5bd139d9'
    names=['common.py','transport_remaining.py','emit_lean.py','run_prepare.py','prepare_sources.py',
           'native_resources.py','native_guard.py']
    for name in names:ast.parse((H/'scripts'/name).read_text(encoding='utf-8'),filename=name)
    plan=dict(status='SOURCE_PREPARED_NOT_EXECUTED',
        source_pins={(H/'scripts'/name).relative_to(R).as_posix():sha(H/'scripts'/name) for name in names},
        input_pins=pins,external_receipts=external,
        accepted160_completion_sha256=sha(M160/'data/completion.json'),
        accepted_prefix_packed_sha256=native['packed_prefix_hex_lines_sha256'],
        accepted_allocator_sha256=native['allocation_cid_slot_lines_sha256'],
        accepted_checkpoint_sha256=native['checkpoint_sha256'],
        expected=dict(prefix_deductions=1055,prefix_references=6006,remaining_deductions=144160,
            remaining_references=14704875,segments=2415,groups=76,checkpoints=75,modules=833,pilot_modules=12),
        limits=dict(owned_private_bytes=1024**3,startup_free_bytes=1536*1024**2,
            runtime_free_bytes=768*1024**2,seconds=600,source_bytes=128*1024**2),
        full_remaining_unit_propagation_replayed=False,
        transport_validation='Exact compact literals and IDs; prefix and allocator digests; live owner/hint identities; every packed row decoded identically; exact160 checkpoint; final empty clause.',
        source_measurement='Two deterministic emission passes. Exact UTF-8 count and hashes checked before any Lean source is written.',
        kernel_gate='The twelve-module first-group pilot must be accepted before full replay. Reuse160 objects without recompilation.',
        Python_syntax_checked=True,native_snapshot_run=False,transport_executed=False,
        Lean_invoked=False,solver_invoked=False,new_global_bound=False)
    target=H/'data/preparation.json';payload=(json.dumps(plan,indent=2)+'\n').encode('utf-8')
    if target.exists():assert target.read_bytes()==payload,'Preserve the existing source preparation'
    else:target.write_bytes(payload)
    print(json.dumps(dict(status=plan['status'],scripts=len(names),input_pins=len(pins),
        preparation_sha256=sha(target),transport_executed=False,Lean_invoked=False)))


if __name__=='__main__':main()
