import Witness085Data
import Balanced085Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs085_valid : jobs085.all (baseJobValid baseBoxes085) = true := by
  decide +kernel

def contextValid085 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs085) &&
    entriesValidAt directionsAt referencesAt 1378 c.2.1 c.1 [(headBox085,.history c.2.2.1)]

theorem contexts085_valid : contexts085.all contextValid085 = true := by
  decide +kernel

theorem contextKeys085_exact : contextKeys085 = recordedClassKeys 85 := by
  decide +kernel

theorem root085_exact : root085 = recordedClassRoot 85 := by
  decide +kernel

theorem boxes085_head_tail : boxes085 = headBox085 :: baseBoxes085 := by
  decide +kernel

theorem class085_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 85) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 85) (digits code) = true := by
  rw [← contextKeys085_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts085_valid c hcxt
  change (decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs085) &&
    entriesValidAt directionsAt referencesAt 1378 c.2.1 c.1 [(headBox085,.history c.2.2.1)]) = true at ht
  have hparts := Bool.and_eq_true_iff.mp ht
  have hp := of_decide_eq_true hparts.1
  have hh : boxWitnessValid c.2.1 c.1 headBox085 (.history c.2.2.1) = true := by
    simpa only [balanced_entries_eq,entriesValid,List.all_cons,List.all_nil,Bool.and_true] using hparts.2
  have hcover : checkCover retainedDiagram (headBox085 :: baseBoxes085) 6 [] root085 tree085 = true := by
    rw [← boxes085_head_tail]
    exact originalCover085
  have hj := List.all_eq_true.mp jobs085_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root085_exact]
  exact head_restored_numeric_membership headBox085 baseBoxes085 c.1 c.2.2.2 c.2.2.1 hj
    retainedDiagram root085 tree085 hcover c.2.1 code hp.1 hh hc hk'

#print axioms jobs085_valid
#print axioms contexts085_valid
#print axioms contextKeys085_exact
#print axioms root085_exact
#print axioms boxes085_head_tail
#print axioms class085_context_membership
end Snake9.Batch92
