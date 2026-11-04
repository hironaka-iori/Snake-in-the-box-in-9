"""Stream the remaining144 proof into packed rows and bounded checkpoints.

Owner/lifetime checks and exact encoding checks cover every row. No full native
unit-propagation replay is performed; the future Lean replay checks validity.
"""
import argparse
import collections
import gzip
import hashlib
import heapq
import importlib.util
import json
import os
import re
import struct
import time
from pathlib import Path
from common import H,R,M144,M160,read,sha,save,check_pins,completed160,no_batch_locks


def main():
    assert __debug__
    ap=argparse.ArgumentParser();ap.add_argument('--run',type=Path,required=True);ap.add_argument('--parent',type=int,required=True)
    args=ap.parse_args();run=args.run.resolve();run.relative_to(H/'data')
    request=read(run/'request.json');lock=read(H/'data/preparation-worker.lock')
    assert lock['parent_pid']==args.parent==request['parent_pid'] and lock['run']==str(run)
    assert os.environ.get('SNAKE161_PARENT')==str(args.parent)
    plan=read(H/'data/preparation.json')
    assert sha(H/'data/preparation.json')==request['preparation_sha256']
    check_pins(plan);completed160();assert no_batch_locks()
    spec=importlib.util.spec_from_file_location('accepted_prefix160',M160/'scripts/prefix_transport.py')
    p=importlib.util.module_from_spec(spec);spec.loader.exec_module(p)
    before=read(M160/'data/prefix1055/prefix-transport.json')
    assert before['packed_rows_equal']==1055 and before['prefix_references']==6006
    assert before['allocator_slots']==14114 and not before['second_renaming_applied']
    expected_checkpoint=M160/'data/prefix1055'/before['checkpoint_file']
    assert sha(expected_checkpoint)==before['checkpoint_sha256']
    initial_checkpoint=[int(x,16) for x in json.loads(gzip.decompress(expected_checkpoint.read_bytes()))]
    assert len(initial_checkpoint)==16383
    started=time.monotonic()
    def progress(phase,**values):save(run/'progress.json',dict(phase=phase,worker_pid=os.getpid(),**values))
    proof=M144/'certificates/share144.lrat';meta=read(M144/'data/share144.json')
    ids=meta['core_ids'];assert ids==list(range(1,13225))
    rename={int(k):v for k,v in meta['original_to_new'].items()}
    assert len(rename)==6371 and set(rename.values())==set(range(1,6372)) and meta['active_variables']==5779
    original_ids=read(M144/'work/certificate-alternative/core-ids.json')
    assert original_ids==meta['source_original_clause_ids'] and len(set(original_ids))==13224
    compact=list(p.clauses(M144/'certificates/share144.cnf'));assert len(compact)==13224
    ordinal={cid:i for i,cid in enumerate(original_ids)};comparisons=0
    for number,clause in enumerate(p.clauses(M144/'work/certificate-alternative/input.cnf'),1):
        if number in ordinal:
            assert [rename[abs(x)]*(1 if x>0 else -1) for x in clause]==compact[ordinal[number]]
            comparisons+=1
    assert comparisons==13224 and number==96091
    assert all(0<abs(x)<=5779 for clause in compact for x in clause)
    progress('COUNTING_PROOF')
    uses=collections.Counter();last={};seen=set(ids);prev=96091;refs=0;lits_total=0;maxrefs=0
    for i,(cid,literals,hints) in enumerate(p.proof_rows(proof)):
        assert cid>prev and cid not in seen and all(h in seen for h in hints)
        assert all(0<abs(x)<=5779 for x in literals)
        prev=cid;seen.add(cid);uses.update(hints)
        for h in hints:last[h]=i
        refs+=len(hints);lits_total+=len(literals);maxrefs=max(maxrefs,len(hints))
        if i%10000==0:progress('COUNTING_PROOF',deductions=i+1,references=refs)
    assert (i+1,refs,lits_total,maxrefs)==(145215,14710881,2561006,710) and literals==[]
    final_id=cid;last[cid]=i+1
    for cid in ids:last.setdefault(cid,-1)
    del seen
    order=sorted(ids,key=lambda cid:(-uses[cid],cid));slots={cid:i+1 for i,cid in enumerate(order)}
    initial_slots=[slots[cid] for cid in ids]
    expire=collections.defaultdict(list)
    for cid,at in last.items():expire[at].append(cid)
    free=[];next_slot=len(ids)+1;allocation=[];allocation_digest=hashlib.sha256()
    for i,(cid,literals,hints) in enumerate(p.proof_rows(proof)):
        for old in expire.get(i,[]):heapq.heappush(free,slots[old])
        target=heapq.heappop(free) if free else next_slot
        if target==next_slot:next_slot+=1
        slots[cid]=target;allocation.append(target)
        if cid not in last:heapq.heappush(free,target)
        allocation_digest.update(f'{cid}:{target}\n'.encode('ascii'))
        if i%10000==0:progress('REPRODUCING_ALLOCATOR',deductions=i+1,slots=next_slot-1)
    assert len(allocation)==145215 and next_slot-1==14114 and cid==final_id
    assert allocation_digest.hexdigest()==before['allocation_cid_slot_lines_sha256']
    keys=p.preorder(14);key={slot:keys[i] for i,slot in enumerate(initial_slots)}
    unused=iter(keys[len(ids):])
    for slot in range(1,next_slot):
        if slot not in key:key[slot]=next(unused)
    assert len(key)==len(set(key.values()))==14114
    assert [key[s] for s in initial_slots]==keys[:13224]
    accepted=[int(x,16) for x in re.findall(r'nat_lit 0x([0-9a-fA-F]+)',(M144/'experiments/lean/LiteralProbe144.lean').read_text())]
    assert len(accepted)==1055
    owner=dict(zip(initial_slots,ids))
    entries={k:0 for k in keys}
    for slot,clause in zip(initial_slots,compact):entries[key[slot]]=p.pack([p.bit(x)+1 for x in clause])
    packed=run/'remaining-steps.bin';indexfile=run/'remaining-index.jsonl.gz'
    checkpoint_dir=run/'checkpoints';checkpoint_dir.mkdir()
    checkpoints=[];segments=[];segment_begin=0;segment_refs=0;remaining_refs=0;remaining_rows=0
    prefix_refs=0;prefix_digest=hashlib.sha256();packed_hex_bytes=0;checkpoint_literal_bytes=0
    roundtrip_count=0;hint_owner_count=0;max_live=len(owner)

    def checkpoint(at_step,before_segment):
        nonlocal checkpoint_literal_bytes
        live={key[s] for s,c in owner.items() if last.get(c,-1)>=at_step}
        values=[entries[k] if k in live else 0 for k in keys]
        assert all(values[j]!=0 for j,k in enumerate(keys) if k in live)
        # These are the exact entries maintained by insertion; dead nodes are
        # replaced only by tautologies, as permitted by cpOk.
        for k,value in zip(keys,values):
            if value:assert value==entries[k]
        path=checkpoint_dir/f'cp{before_segment:05d}.json.gz'
        encoded=[format(x,'x') for x in values]
        path.write_bytes(gzip.compress(json.dumps(encoded,separators=(',',':')).encode('ascii'),mtime=0))
        literal_bytes=sum(len(x)+12 for x in encoded)
        checkpoint_literal_bytes+=literal_bytes
        checkpoints.append(dict(before_segment=before_segment,absolute_after_step=at_step,
            remaining_after_step=at_step-1055,live_clauses=len(live),entries=len(values),
            path=path.relative_to(run).as_posix(),sha256=sha(path),lean_literal_bytes=literal_bytes,
            live_entries_match_database=True,dead_entries_replaced_by_tautologies=True))
        for k,value in zip(keys,values):entries[k]=value

    with packed.open('wb') as output,gzip.open(indexfile,'wt',encoding='ascii') as index:
        for i,(cid,literals,hints) in enumerate(p.proof_rows(proof)):
            hint_slots=[slots[h] for h in hints]
            assert all(owner.get(s)==h for s,h in zip(hint_slots,hints))
            hint_owner_count+=len(hints)
            assert all(entries[key[s]]!=0 for s in hint_slots), 'A live hint was replaced by a tautology'
            dest=allocation[i];hint_keys=[key[s] for s in hint_slots]
            words=[key[dest]]+[p.bit(x)+1 for x in literals]+[0]+hint_keys
            value=p.pack(words)
            decoded=[];rest=value
            while rest:decoded.append(rest&((1<<14)-1));rest>>=14
            assert decoded==words, f'Packed identity failed at row{i}'
            roundtrip_count+=1
            if i<1055:
                assert value==accepted[i]
                prefix_digest.update((format(value,'x')+'\n').encode('ascii'))
                prefix_refs+=len(hints)
            else:
                payload=value.to_bytes((value.bit_length()+7)//8,'little');offset=output.tell()
                output.write(struct.pack('<I',len(payload)));output.write(payload)
                index.write(json.dumps([remaining_rows,i,cid,dest,key[dest],offset,len(payload),len(literals),len(hints)],separators=(',',':'))+'\n')
                remaining_rows+=1;remaining_refs+=len(hints);segment_refs+=len(hints)
                packed_hex_bytes+=len(format(value,'x'))+12
            for old in expire.get(i,[]):
                assert owner[slots[old]]==old
                owner.pop(slots[old])
            assert dest not in owner
            owner[dest]=cid;entries[key[dest]]=p.pack([p.bit(x)+1 for x in literals])
            if cid not in last:owner.pop(dest)
            max_live=max(max_live,len(owner))
            if i+1==1055:
                live={key[s] for s,c in owner.items() if last.get(c,-1)>=1055}
                got=[entries[k] if k in live else 0 for k in keys]
                assert got==initial_checkpoint
                assert prefix_refs==6006 and prefix_digest.hexdigest()==before['packed_prefix_hex_lines_sha256']
                entries=dict(zip(keys,initial_checkpoint))
            if i>=1055 and (segment_refs>=6000 or i+1==145215):
                segment=len(segments)
                segments.append(dict(segment=segment,first_step=segment_begin,after_step=remaining_rows,
                    absolute_first_step=1055+segment_begin,absolute_after_step=i+1,
                    references=segment_refs,packed_after_byte=output.tell()))
                segment_begin=remaining_rows;segment_refs=0
                if len(segments)%32==0 and i+1<145215:checkpoint(i+1,len(segments))
            if i%10000==0:progress('PACKING_REMAINING_PROOF',absolute_deductions=i+1,remaining_rows=remaining_rows,remaining_references=remaining_refs)
    assert (remaining_rows,remaining_refs,roundtrip_count,hint_owner_count)==(144160,14704875,145215,14710881)
    assert len(segments)==2415 and len(checkpoints)==75
    assert literals==[] and cid==final_id and entries[key[dest]]==0 and owner[dest]==final_id
    assert sum(row['references'] for row in segments)==14704875
    assert segments[0]['first_step']==0 and segments[-1]['after_step']==144160
    assert all(a['after_step']==b['first_step'] for a,b in zip(segments,segments[1:]))
    check_pins(plan);completed160();assert no_batch_locks()
    receipt=dict(status='PASS_COMPLETE_REMAINING_TRANSPORT_ONLY',
        original_deductions=145215,original_references=14710881,prefix_deductions=1055,prefix_references=6006,
        remaining_deductions=144160,remaining_references=14704875,segment_count=len(segments),segments=segments,
        checkpoint_interval_segments=32,checkpoints=checkpoints,tree_height=14,word_width=14,literal_offset=8192,
        allocator_slots=14114,initial_core_clauses=13224,active_variables=5779,semantic_variables=6371,
        original_input_clause_comparisons=13224,packed_prefix_hex_lines_sha256=prefix_digest.hexdigest(),
        allocation_cid_slot_lines_sha256=allocation_digest.hexdigest(),
        accepted_checkpoint_sha256=before['checkpoint_sha256'],accepted_checkpoint_reproduced=True,
        decoded_rows_equal=roundtrip_count,hint_ownership_checks=hint_owner_count,max_live_clauses=max_live,
        packed_literal_bytes=packed_hex_bytes,checkpoint_literal_bytes=checkpoint_literal_bytes,
        final_original_clause_id=final_id,final_tree_key=key[dest],final_clause_empty=True,
        full_remaining_unit_propagation_replayed=False,second_variable_renaming_applied=False,
        artifacts=[dict(path=x.relative_to(run).as_posix(),sha256=sha(x),bytes=x.stat().st_size) for x in [packed,indexfile]],
        preparation_sha256=sha(H/'data/preparation.json'),request_sha256=sha(run/'request.json'),
        transport_source_sha256=sha(Path(__file__)),seconds=time.monotonic()-started,
        Lean_invoked=False,full_Lean_replay_complete=False,actual_share18_complete=False,new_global_bound=False,
        scope='Every row is transported with exact decoding, clause ownership and allocation checks; native unit propagation of the remaining proof is omitted. Lean validity checks are pending.')
    save(run/'transport.json',receipt)
    progress('MEASURING_SOURCE')
    from emit_lean import emit_sources
    source_plan=emit_sources(run,receipt,plan,progress)
    progress('FINISHED',status='PASS_REMAINING_TRANSPORT_AND_UNCHECKED_SOURCES')
    print(json.dumps(dict(status='PASS_REMAINING_TRANSPORT_AND_UNCHECKED_SOURCES',
        remaining_deductions=remaining_rows,remaining_references=remaining_refs,
        modules=source_plan['module_count'],source_bytes=source_plan['source_bytes'],Lean_invoked=False)))


if __name__=='__main__':main()
