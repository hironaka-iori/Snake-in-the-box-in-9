import Witness083Data
import Balanced083Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs083_valid : jobs083.all (baseJobValid baseBoxes083) = true := by
  decide +kernel

def contextValid083 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs083)

theorem contexts083_valid : contexts083.all contextValid083 = true := by
  decide +kernel

theorem contextKeys083_exact : contextKeys083 = recordedClassKeys 83 := by
  decide +kernel

theorem root083_exact : root083 = recordedClassRoot 83 := by
  decide +kernel

theorem class083_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 83) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 83) (digits code) = true := by
  rw [← contextKeys083_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts083_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs083) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs083_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root083_exact]
  exact base_job_numeric_membership baseBoxes083 c.1 c.2.2.2 hj
    retainedDiagram root083 tree083 originalCover083 c.2.1 code hp.1 hc hk'

#print axioms jobs083_valid
#print axioms contexts083_valid
#print axioms contextKeys083_exact
#print axioms root083_exact
#print axioms class083_context_membership
end Snake9.Batch92
