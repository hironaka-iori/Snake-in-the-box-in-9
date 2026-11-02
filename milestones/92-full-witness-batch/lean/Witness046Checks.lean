import Witness046Data
import Balanced046Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs046_valid : jobs046.all (baseJobValid baseBoxes046) = true := by
  decide +kernel

def contextValid046 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs046)

theorem contexts046_valid : contexts046.all contextValid046 = true := by
  decide +kernel

theorem contextKeys046_exact : contextKeys046 = recordedClassKeys 46 := by
  decide +kernel

theorem root046_exact : root046 = recordedClassRoot 46 := by
  decide +kernel

theorem class046_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 46) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 46) (digits code) = true := by
  rw [← contextKeys046_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts046_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs046) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs046_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root046_exact]
  exact base_job_numeric_membership baseBoxes046 c.1 c.2.2.2 hj
    retainedDiagram root046 tree046 originalCover046 c.2.1 code hp.1 hc hk'

#print axioms jobs046_valid
#print axioms contexts046_valid
#print axioms contextKeys046_exact
#print axioms root046_exact
#print axioms class046_context_membership
end Snake9.Batch92
