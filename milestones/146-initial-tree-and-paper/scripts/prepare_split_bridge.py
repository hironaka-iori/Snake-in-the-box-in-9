"""Split raw-clause extraction from the already checked tree-part assembly."""
from pathlib import Path
import hashlib,json,re
H=Path(__file__).resolve().parents[1];R=H.parents[1]
prior=R/'milestones/145-countfree-012301/lean/ChunkTruthAssemblyFixed145.lean'
source=prior.read_text();sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(prior)=='08abee629d93337b5cc1c6214d4beacdc683ebbdbeda7fa04acfe8664e4ba38b'
headers='set_option maxRecDepth 100000\nset_option maxHeartbeats 0\nset_option Elab.async false\n'
predicate='(fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit))'
ns='Snake9.LocalWindow.ShareWindow144'
text='import ChunkTruthTools145\n'+headers+'namespace Snake9.RawChunks146\n'
text+=f'''theorem raw_true (τ : Nat → Bool)
    (h : Snake9.LocalWindow.cnfTrue τ {ns}.cnf = true) :
    {ns}.raw.all {predicate} = true := by
  simpa only [{ns}.cnf, Snake9.LocalWindow.cnfTrue, List.all_map] using h
#print axioms raw_true
'''
conjunction=' ∧\n    '.join(f'{ns}.raw{i}.all {predicate} = true' for i in range(104))
text+=f'''theorem chunks_true (τ : Nat → Bool)
    (h : Snake9.LocalWindow.cnfTrue τ {ns}.cnf = true) :
    {conjunction} := by
  simpa only [{ns}.raw, List.all_append, List.all_nil, Bool.and_eq_true, and_true]
    using raw_true τ h
#print axioms chunks_true
end Snake9.RawChunks146
'''
p=H/'lean/RawChunks146.lean';assert not p.exists();p.write_text(text,encoding='utf-8',newline='\n')
prefix=source[:source.index('  have hraw')]
prefix='import RawChunks146\n'+prefix
prefix=prefix.replace('namespace Snake9.ChunkData145','namespace Snake9.Assembly146\nopen Snake9.ChunkData145')
constructor=source[source.index('  exact (Snake9.Lrat144.TreeTrue.node'):]
constructor=constructor.replace('end Snake9.ChunkData145','end Snake9.Assembly146')
extract='  obtain ⟨'+', '.join(f'h{i}' for i in range(104))+'⟩ := Snake9.RawChunks146.chunks_true τ h\n'
q=H/'lean/Assembly146.lean';assert not q.exists();q.write_text(prefix+extract+constructor,encoding='utf-8',newline='\n')
proof='''import Assembly146
import LiteralProbe144
namespace Snake9.Prefix146
theorem checked_prefix_true (τ : Nat → Bool)
    (h : Snake9.LocalWindow.cnfTrue τ Snake9.LocalWindow.ShareWindow144.cnf = true) :
    Snake9.Lrat144.TreeTrue τ
      (Snake9.LratFast144.replay Snake9.LiteralData144.start Snake9.LiteralProbe144.proof) := by
  exact Snake9.LratFast144.replay_true τ
    Snake9.LiteralProbe144.first_segment (Snake9.Assembly146.start_true τ h)
#print axioms checked_prefix_true
end Snake9.Prefix146
'''
t=H/'lean/Prefix146.lean';assert not t.exists();t.write_text(proof,encoding='utf-8',newline='\n')
record=dict(status='PREPARED_SPLIT_BRIDGE_LEAN_PENDING',original_source_sha256=sha(prior),
    source_files_sha256={p.relative_to(R).as_posix():sha(p) for p in [prior,Path(__file__)]},
    modules=[dict(name=p.stem,sha256=sha(p)) for p in [p,q,t]],
    scope='Preserved144 initial database and its6006-reference prefix only; neither complete share proof nor actual-snake theorem.')
(H/'data/bridge-preparation.json').write_text(json.dumps(record,indent=2)+'\n');print(record['status'])
