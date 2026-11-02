"""Generate the final family assembly; check it only after all class receipts pass."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
generation=json.loads((HERE/'data/batch-generation.json').read_text())
inputs={}
for i in range(127):
    name=f'Witness{i:03d}Checks.lean';p=HERE/'lean'/name
    assert sha(p)==generation['source_sha256'][name]
    inputs[p.relative_to(ROOT).as_posix()]=sha(p)
p=HERE/'lean/ContextAssignmentChecks.lean';inputs[p.relative_to(ROOT).as_posix()]=sha(p)
for name in ['lean/DefinedProofGraph.lean','data/DefinedProofGraph-audit.json']:
    p=HERE/name;inputs[p.relative_to(ROOT).as_posix()]=sha(p)
source='import ContextAssignmentChecks\nimport DefinedProofGraph\n'+''.join(f'import Witness{i:03d}Checks\n' for i in range(127))
source+='\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n\nnamespace Snake9.Batch92\nopen Snake9.Boxes88 Snake9.Certificate88 Snake9.Retained87\n\n'
source+='open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.GraphWalk78\n\n'
source+='theorem retained_class_family : ClassMembershipFamily retainedDiagram := by\n  intro cls hcls di q code hm hq hc hk\n  interval_cases cls\n'
source+=''.join(f'  · exact class{i:03d}_context_membership di q code hm hc hk\n' for i in range(127))
source+='\ntheorem retained_numeric_diagram (q di code : Nat) (hd : di < 505)\n    (hk : numericKeep q di code = true) :\n    Assigned di q ∧ diagramEval retainedDiagram (recordedClassRoot (chosenClass di q)) (digits code) = true :=\n  numeric_context_membership retainedDiagram retained_class_family q di code hd hk\n\n'
source+='theorem retained_defined_walk (h235 : AllRefuted6K235) (h236 : AllRefuted236)\n    {m : Nat} (p : Snake m) :\n    ∃ edge : Fin (m-8) → Fin (Snake9.DefinedGraph92.rows retainedDiagram).size, ∀ i,\n      (Snake9.DefinedGraph92.sources retainedDiagram).toList[(edge i).val]? = some (actualState p i.val) ∧\n      (Snake9.DefinedGraph92.targets retainedDiagram).toList[(edge i).val]? = some (actualState p (i.val+1)) :=\n  Snake9.DefinedGraph92.defined_actual_walk retainedDiagram retained_class_family assignment_checked h235 h236 p\n\n'
source+='#print axioms retained_class_family\n#print axioms retained_numeric_diagram\n#print axioms retained_defined_walk\nend Snake9.Batch92\n'
p=HERE/'lean/CloseBatch.lean';raw=source.encode()
assert not p.exists() or p.read_bytes()==raw
p.write_bytes(raw)
report=dict(status='GENERATED_PENDING_ALL_CLASS_PROOFS',source_sha256=sha(p),input_sha256=inputs,
            script_sha256=sha(Path(__file__)),scope='Queued family, numeric-diagram and defined-walk assembly only. The walk retains two reference-catalogue premises. No completed theorem is claimed before the final receipt.')
(HERE/'data/closure-generation.json').write_text(json.dumps(report,indent=2)+'\n')
print(report['status'])
