import Witness089Data
import Balanced089Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs089_valid : jobs089.all (baseJobValid baseBoxes089) = true := by
  decide +kernel

def contextValid089 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs089) &&
    entriesValidAt directionsAt referencesAt 1378 c.2.1 c.1 [(headBox089,.history c.2.2.1)]

theorem contexts089_valid : contexts089.all contextValid089 = true := by
  decide +kernel

theorem contextKeys089_exact : contextKeys089 = recordedClassKeys 89 := by
  decide +kernel

theorem root089_exact : root089 = recordedClassRoot 89 := by
  decide +kernel

theorem boxes089_head_tail : boxes089 = headBox089 :: baseBoxes089 := by
  decide +kernel

theorem class089_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 89) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 89) (digits code) = true := by
  rw [← contextKeys089_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts089_valid c hcxt
  change (decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs089) &&
    entriesValidAt directionsAt referencesAt 1378 c.2.1 c.1 [(headBox089,.history c.2.2.1)]) = true at ht
  have hparts := Bool.and_eq_true_iff.mp ht
  have hp := of_decide_eq_true hparts.1
  have hh : boxWitnessValid c.2.1 c.1 headBox089 (.history c.2.2.1) = true := by
    simpa only [balanced_entries_eq,entriesValid,List.all_cons,List.all_nil,Bool.and_true] using hparts.2
  have hcover : checkCover retainedDiagram (headBox089 :: baseBoxes089) 6 [] root089 tree089 = true := by
    rw [← boxes089_head_tail]
    exact originalCover089
  have hj := List.all_eq_true.mp jobs089_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root089_exact]
  exact head_restored_numeric_membership headBox089 baseBoxes089 c.1 c.2.2.2 c.2.2.1 hj
    retainedDiagram root089 tree089 hcover c.2.1 code hp.1 hh hc hk'

#print axioms jobs089_valid
#print axioms contexts089_valid
#print axioms contextKeys089_exact
#print axioms root089_exact
#print axioms boxes089_head_tail
#print axioms class089_context_membership
end Snake9.Batch92
