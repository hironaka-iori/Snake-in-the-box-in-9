"""Measure then emit bounded161 replay modules; never invokes Lean."""
import gzip
import hashlib
import json
import struct
from common import H,R,M160,sha,read,save

BASE='Snake9.Lrat144'
FAST='Snake9.LratFast144'
NS='Snake9.ReplayFull161'
CNF='Snake9.LocalWindow.ShareWindow144'
OPTIONS='set_option maxRecDepth 100000\nset_option maxHeartbeats 0\nset_option Elab.async false\n'


def packed_rows(path):
    with path.open('rb') as stream:
        while True:
            length=stream.read(4)
            if not length:break
            assert len(length)==4
            size=struct.unpack('<I',length)[0];assert 0<size<=1024*1024
            value=stream.read(size);assert len(value)==size
            yield format(int.from_bytes(value,'little'),'x')


def literals(values):return '['+',\n'.join('nat_lit 0x'+value for value in values)+']'


def modules(run,receipt):
    segments=receipt['segments'];count=len(segments)
    checkpoints={row['before_segment']:row for row in receipt['checkpoints']}
    assert count==2415 and sorted(checkpoints)==list(range(32,count,32))
    for at in range(32,count,32):
        checkpoint=checkpoints[at];path=run/checkpoint['path'];assert sha(path)==checkpoint['sha256']
        values=json.loads(gzip.decompress(path.read_bytes()))
        assert len(values)==16383 and all(isinstance(x,str) and int(x,16)>=0 for x in values)
        name=f'ReplayCheckpoint161_{at:05d}'
        yield name,'\n'.join(['import LratFast144',OPTIONS,'namespace '+NS,
            f'open {BASE} (Tree)',f'open {FAST}',
            f'noncomputable def start{at} : Tree := build 14 '+literals(values),'end '+NS])+'\n'
    stream=packed_rows(run/'remaining-steps.bin');groups=[]
    for begin in range(0,count,32):
        end=min(begin+32,count);group=begin//32;data_module=f'ReplayData161_{group:04d}'
        imports=['CheckpointData160'] if begin==0 else [f'ReplayCheckpoint161_{begin:05d}']
        if end<count:imports.append(f'ReplayCheckpoint161_{end:05d}')
        data=['import '+name for name in imports]+[OPTIONS,'namespace '+NS,f'open {BASE} (Tree)',f'open {FAST}']
        if begin==0:data+=['noncomputable def start0 : Tree := Snake9.Checkpoint160.afterPrefix']
        for k in range(begin,end):
            n=segments[k]['after_step']-segments[k]['first_step']
            values=[next(stream) for _ in range(n)]
            data += [f'noncomputable def proof{k} : List Nat := '+literals(values)]
            if k+1<end:data += [f'noncomputable def start{k+1} : Tree := replay start{k} proof{k}']
        data+=['end '+NS]
        yield data_module,'\n'.join(data)+'\n'
        checks=[]
        for first in range(begin,end,4):
            name=f'ReplayCheck161_{first:05d}';checks.append(name)
            check=['import '+data_module,OPTIONS,'namespace '+NS,f'open {BASE} (andB)',f'open {FAST}']
            for k in range(first,min(first+4,end)):
                prop=f'check start{k} proof{k}'
                if k+1==count:prop=f'andB ({prop}) (hasEmpty (replay start{k} proof{k}) {receipt["final_tree_key"]})'
                elif k+1==end:prop=f'andB ({prop}) (cpOk (replay start{k} proof{k}) start{end})'
                check += [f'theorem ok{k} : {prop} = true := by','  decide +kernel',f'#print axioms ok{k}']
            check+=['end '+NS]
            yield name,'\n'.join(check)+'\n'
        name=f'ReplaySteps161_{group:04d}';groups.append(name)
        steps=['import '+m for m in checks]+[OPTIONS,'namespace '+NS,f'open {BASE} (TreeTrue)',f'open {FAST}',
            f'theorem steps{group} (τ : Nat → Bool) (h{begin} : TreeTrue τ start{begin}) : '+
            ('False' if end==count else f'TreeTrue τ start{end}')+' := by']
        for k in range(begin,end):
            if k+1==count:steps += [f'  exact final_false τ ok{k} h{k}']
            else:
                method='cp_true' if k+1==end else 'replay_true'
                steps += [f'  have h{k+1} : TreeTrue τ start{k+1} := {method} τ ok{k} h{k}']
        if end<count:steps += [f'  exact h{end}']
        steps += [f'#print axioms steps{group}','end '+NS]
        yield name,'\n'.join(steps)+'\n'
        if group==0:
            yield 'ReplayPilot161','\n'.join(['import CheckpointConsequence160','import ReplaySteps161_0000',
                OPTIONS,'namespace '+NS,f'open {BASE} (TreeTrue)',
                'theorem pilot_true (τ : Nat → Bool)',
                f'    (h : Snake9.LocalWindow.cnfTrue τ {CNF}.cnf = true) : TreeTrue τ start32 := by',
                '  have h0 : TreeTrue τ start0 := Snake9.Checkpoint160.afterPrefix_true τ h',
                '  exact steps0 τ h0','#print axioms pilot_true','end '+NS])+'\n'
    assert next(stream,None) is None
    final=['import CheckpointConsequence160']+['import '+m for m in groups]+[OPTIONS,'namespace '+NS,
        f'open {BASE} (TreeTrue unsat_of_raw)',f'theorem unsat : Snake9.LocalWindow.Unsat {CNF}.cnf := by',
        '  apply unsat_of_raw','  intro τ h',
        '  have h0 : TreeTrue τ start0 := Snake9.Checkpoint160.afterPrefix_true τ h']
    for group,begin in enumerate(range(0,count,32)):
        end=min(begin+32,count)
        final += [f'  exact steps{group} τ h{begin}'] if end==count else [f'  have h{end} : TreeTrue τ start{end} := steps{group} τ h{begin}']
    final += ['#print axioms unsat','end '+NS]
    yield 'ReplayUnsat161','\n'.join(final)+'\n'


def emit_sources(run,receipt,preparation,progress):
    assert receipt['status']=='PASS_COMPLETE_REMAINING_TRANSPORT_ONLY'
    for row in receipt['artifacts']+receipt['checkpoints']:assert sha(run/row['path'])==row['sha256']
    target=H/'data/full-source-plan.json';assert not target.exists()
    inventory=[];total=0
    # First pass measures exact UTF-8 bytes and hashes. No Lean source is written.
    for name,body in modules(run,receipt):
        encoded=body.encode('utf-8');total+=len(encoded)
        inventory.append(dict(module=name,path='lean/'+name+'.lean',bytes=len(encoded),sha256=hashlib.sha256(encoded).hexdigest()))
    cap=preparation['limits']['source_bytes'];assert cap==128*1024**2
    measurement=dict(status='PASS_EXACT_SOURCE_SIZE' if total<=cap else 'STOP_SOURCE_SIZE_LIMIT',
        source_bytes=total,source_limit_bytes=cap,modules=len(inventory),source_files_written=0,
        transport_sha256=sha(run/'transport.json'),emitter_sha256=sha(__file__),artifacts=inventory)
    save(run/'source-size-measurement.json',measurement)
    assert total<=cap, f'Exact source estimate exceeds128MiB: {total}'
    assert len(inventory)==833 and len({row['module'] for row in inventory})==833
    progress('EMITTING_MEASURED_SOURCES',source_bytes=total,modules=len(inventory))
    (H/'lean').mkdir(exist_ok=True)
    # Second pass must reproduce the measured source byte-for-byte.
    written=[]
    for expected,(name,body) in zip(inventory,modules(run,receipt),strict=True):
        encoded=body.encode('utf-8')
        assert expected['module']==name and expected['bytes']==len(encoded)
        assert hashlib.sha256(encoded).hexdigest()==expected['sha256']
        path=H/expected['path'];assert not path.exists(),path
        path.write_bytes(encoded);assert sha(path)==expected['sha256'];written.append(name)
    pilot=['ReplayCheckpoint161_00032','ReplayData161_0000']+[f'ReplayCheck161_{n:05d}' for n in range(0,32,4)]+['ReplaySteps161_0000','ReplayPilot161']
    assert len(pilot)==12 and set(pilot)<=set(written)
    groups=[]
    for begin in range(0,receipt['segment_count'],32):
        end=min(begin+32,receipt['segment_count'])
        groups.append(dict(group=begin//32,first_segment=begin,after_segment=end,
            first_step=receipt['segments'][begin]['first_step'],after_step=receipt['segments'][end-1]['after_step'],
            references=sum(row['references'] for row in receipt['segments'][begin:end])))
    plan=dict(status='SOURCE_PREPARED_UNCHECKED',module_order=written,module_count=len(written),artifacts=inventory,
        source_bytes=total,source_limit_bytes=cap,source_size_measurement=(run/'source-size-measurement.json').relative_to(H).as_posix(),
        source_size_measurement_sha256=sha(run/'source-size-measurement.json'),
        pilot_module_order=pilot,pilot_modules=12,pilot_segments=32,
        pilot_remaining_deductions=receipt['segments'][31]['after_step'],
        pilot_references=sum(row['references'] for row in receipt['segments'][:32]),
        pilot_final_theorem=NS+'.pilot_true',
        full_segments=2415,full_checkpoint_groups=76,groups=groups,
        remaining_deductions=144160,remaining_references=14704875,
        reused_prefix_deductions=1055,reused_prefix_references=6006,
        final_theorem=NS+'.unsat',final_CNF=CNF+'.cnf',final_module='ReplayUnsat161',
        final_original_clause_id=receipt['final_original_clause_id'],final_tree_key=receipt['final_tree_key'],
        transport_receipt=(run/'transport.json').relative_to(H).as_posix(),transport_receipt_sha256=sha(run/'transport.json'),
        generator_sha256=sha(__file__),preparation_sha256=sha(H/'data/preparation.json'),
        external_receipts=preparation['external_receipts'],input_pins=preparation['input_pins'],
        full_kernel_replay_requires_accepted_pilot=True,recompile160=False,
        full_remaining_unit_propagation_replayed=False,Lean_invoked=False,new_global_bound=False,
        axiom_expectation='Only propext, Classical.choice and Quot.sound; no sorry, added axioms or native_decide.',
        scope='Remaining proof source only. The twelve-module first-group pilot must pass before full kernel replay; final actual-snake composition is separate.')
    save(target,plan)
    return plan
