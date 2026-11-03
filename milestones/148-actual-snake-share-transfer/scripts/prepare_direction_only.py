"""Extract unchanged direction/reversal lemmas without the old239 table checks."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
prior=H/'data/transfer-plan-v3.json';plan=read(prior)
original=H/'lean/DirectionWindowBridge.lean';raw=original.read_bytes()
def span(a,b):
    a=a.encode();b=b.encode();assert raw.count(a)==raw.count(b)==1
    i=raw.index(a);j=raw.index(b);assert i<j;return raw[i:j]
blocks=[
    span('import WindowAutomatonLemmas','/-! ## The 145 keys'),
    span('theorem getD_idx','/-! ## Windows of a snake'),
    span('section Window','/-- A window whose canonical shape'),
    span('theorem dsOf_rev','/-- No window of two'),
    span('theorem pathDir_eq_dir','/-- The premises of')]
out=blocks[0]+blocks[1]+blocks[2]+blocks[3]+b'end Window\n\n'+blocks[4]
out+=b'\n#print axioms getD_idx\n#print axioms seenAfter_nodup\n#print axioms mem_seenAfter_cases\n#print axioms dsOf_rev\n#print axioms pathDir_eq_dir\nend Snake9.DirectionWindow\n'
dest=H/'lean-core/DirectionWindowBridge.lean';assert not dest.exists();dest.write_bytes(out)
row=next(x for x in plan['artifacts'] if x['module']=='DirectionWindowBridge')
row.update(path=dest.relative_to(H).as_posix(),sha256=sha(dest),prior_full_source=str(original),prior_full_source_sha256=sha(original),
    source_change='Exact selected generic direction, relabelling and reversal blocks retained. Old239 coverage and catalogue consequences omitted; none is assumed by the148 adapter.')
plan.update(status='PREPARED_TRANSFER_WITH_GENERIC_DIRECTION_CORE',prior_v3_plan_sha256=sha(prior),direction_preparer_sha256=sha(Path(__file__)),
    generic_direction_proof_blocks_preserved_byte_for_byte=True,unrelated239_coverage_rebuild_omitted=True)
target=H/'data/transfer-plan-v4.json';assert not target.exists();target.write_text(json.dumps(plan,indent=2)+'\n',encoding='utf-8',newline='\n')
for old,new in [('check_module_v3.py','check_module_v4.py'),('run_transfer_v3.py','run_transfer_v4.py'),('serialize_transfer_v3.py','serialize_transfer_v4.py')]:
    s=(H/'scripts'/old).read_text(encoding='utf-8').replace('transfer-plan-v3.json','transfer-plan-v4.json')
    s=s.replace('PREPARED_TRANSFER_WITH_GENERIC_SNAKE_CORE','PREPARED_TRANSFER_WITH_GENERIC_DIRECTION_CORE')
    s=s.replace('check_module_v3.py','check_module_v4.py').replace('run_transfer_v3.py','run_transfer_v4.py')
    s=s.replace('transfer-v3-','transfer-v4-').replace('serialization-v3-','serialization-v4-')
    p=H/'scripts'/new;assert not p.exists();p.write_text(s,encoding='utf-8',newline='\n')
q=dict(status='PASS_UNCHANGED_DIRECTION_PROOF_BLOCK_EXTRACTION',original_sha256=sha(original),extracted_sha256=sha(dest),
    block_sha256=[hashlib.sha256(b).hexdigest() for b in blocks],all_selected_blocks_preserved_exactly=True,
    old_table_refutations_not_assumed=True,compile_pending=True)
(H/'data/direction-source-review.json').write_text(json.dumps(q,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps(q))
