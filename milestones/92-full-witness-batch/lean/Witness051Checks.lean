import Witness051Data
import Balanced051Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs051_valid : jobs051.all (baseJobValid baseBoxes051) = true := by
  decide +kernel

def contextValid051 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs051)

theorem contexts051_valid : contexts051.all contextValid051 = true := by
  decide +kernel

theorem contextKeys051_exact : contextKeys051 = recordedClassKeys 51 := by
  decide +kernel

theorem root051_exact : root051 = recordedClassRoot 51 := by
  decide +kernel

theorem class051_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 51) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 51) (digits code) = true := by
  rw [← contextKeys051_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts051_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs051) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs051_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root051_exact]
  exact base_job_numeric_membership baseBoxes051 c.1 c.2.2.2 hj
    retainedDiagram root051 tree051 originalCover051 c.2.1 code hp.1 hc hk'

#print axioms jobs051_valid
#print axioms contexts051_valid
#print axioms contextKeys051_exact
#print axioms root051_exact
#print axioms class051_context_membership
end Snake9.Batch92
