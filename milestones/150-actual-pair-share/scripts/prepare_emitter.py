"""Prepare the bounded replay pilot; no Lean or full-replay launch."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1];D=H/'replay'
old=R/'milestones/147-countfree-clause-semantics/replay/emit_lean.py'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sizes=read(D/'data/sizing.json')
assert (sizes['tree_height'],sizes['word_width'],sizes['literal_offset'])==(14,14,8192)
s=old.read_text(encoding='utf-8').replace('147','150').replace('ShareWindow146','ShareWindow150')
needle="    fast=re.sub(r'\\b14\\b','15',fast).replace('16383','32767')\n"
assert needle in s;s=s.replace(needle,"    assert s['tree_height']==14 and s['word_width']==14\n")
begin=s.index("    emit('ReplayRawChunks150',copied(")
end=s.index('    core=p.cnf(p.CORE);',begin)
replacement='''    # Derive the chunk decomposition for this exact CNF length.
    chunk_count=(len(p.cnf(p.CORE))+127)//128
    chunk_body=['import ReplayTools150',OPTIONS,'namespace Snake9.ReplayRawChunks150',
        'theorem chunks_true (τ : Nat → Bool)',
        f'    (h : Snake9.LocalWindow.cnfTrue τ {CNF}.cnf = true) :',
        '    '+(' ∧\\n    '.join(CNF+'.raw'+str(i)+'.all '+PRED+' = true' for i in range(chunk_count)))+' := by',
        '  simpa only ['+CNF+'.cnf, Snake9.LocalWindow.cnfTrue, List.all_map, '+CNF+'.raw,',
        '    List.all_append, Bool.and_eq_true, List.all_nil, and_true, and_assoc] using h',
        '#print axioms chunks_true','end Snake9.ReplayRawChunks150']
    emit('ReplayRawChunks150','\\n'.join(chunk_body))
'''
s=s[:begin]+replacement+s[end:]
dest=D/'emit_lean.py';assert not dest.exists();dest.write_text(s,encoding='utf-8',newline='\n')
record=dict(status='PREPARED_BOUNDED_PILOT_GENERATOR',old_generator_sha256=sha(old),
    generator_sha256=sha(dest),script_sha256=sha(Path(__file__)),
    tree_height=14,word_width=14,chunk_count=107,
    change='Retain the existing14-bit checker; regenerate the CNF chunk decomposition for107chunks. Mathematical checks remain pending.')
(H/'data/emitter-preparation.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
print(json.dumps(record))
