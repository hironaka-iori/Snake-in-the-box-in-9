"""Pin the numeric nonempty-history compatible-shape table."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
path=ROOT/'milestones/70-proof-supported-share-model/data/enriched-model.json'
metadata=json.loads(path.read_text(encoding='utf-8-sig'))
values=metadata['compatible_shapes']
assert len(values)==75 and values[0] is None
assert all(isinstance(v,int) and 0<=v<132 for v in values[1:])
values=[0]+values[1:]
src='''import DirectionTables
import ExactHistory
namespace Snake9.Direction77
open Snake9.WindowAutomaton
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def recordedCompatible : List Nat := '''+str(values)+'''
def compatibleShape (q : Nat) : Nat :=
  targetId ((Snake9.History75.prefixes.getD q []).getLastD 0)
def compatibilityCheck (q : Nat) : Bool :=
  q == 0 || (recordedCompatible.getD q 0 == compatibleShape q)
theorem compatibility_checked : allBelow 75 compatibilityCheck = true := by
  decide +kernel
theorem recorded_compatible_exact (q : Nat) (h0 : q ≠ 0) (hq : q < 75) :
    recordedCompatible.getD q 0 = compatibleShape q := by
  have h := allBelow_spec 75 _ compatibility_checked q hq
  simpa [compatibilityCheck, h0] using h
#print axioms compatibility_checked
#print axioms recorded_compatible_exact
end Snake9.Direction77
'''
(HERE/'lean/HistoryCompatibilityData.lean').write_text(src,encoding='utf-8',newline='\n')
(HERE/'data/compatibility-provenance.json').write_text(json.dumps(dict(source=path.relative_to(ROOT).as_posix(),source_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),zero_entry='Unused placeholder; original metadata has null at history0.',source_values=metadata['compatible_shapes'],lean_source_sha256=hashlib.sha256(src.encode()).hexdigest()),indent=2)+'\n',encoding='utf-8')
print('Generated75-entry history compatibility check.')
