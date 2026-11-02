import Witness110Data
import Balanced110Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs110_valid : jobs110.all (baseJobValid baseBoxes110) = true := by
  decide +kernel

def contextValid110 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs110)

theorem contexts110_valid : contexts110.all contextValid110 = true := by
  decide +kernel

theorem contextKeys110_exact : contextKeys110 = recordedClassKeys 110 := by
  decide +kernel

theorem root110_exact : root110 = recordedClassRoot 110 := by
  decide +kernel

theorem class110_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 110) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 110) (digits code) = true := by
  rw [← contextKeys110_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts110_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs110) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs110_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root110_exact]
  exact base_job_numeric_membership baseBoxes110 c.1 c.2.2.2 hj
    retainedDiagram root110 tree110 originalCover110 c.2.1 code hp.1 hc hk'

#print axioms jobs110_valid
#print axioms contexts110_valid
#print axioms contextKeys110_exact
#print axioms root110_exact
#print axioms class110_context_membership
end Snake9.Batch92
