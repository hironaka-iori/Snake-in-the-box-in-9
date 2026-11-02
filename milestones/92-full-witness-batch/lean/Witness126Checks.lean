import Witness126Data
import Balanced126Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs126_valid : jobs126.all (baseJobValid baseBoxes126) = true := by
  decide +kernel

def contextValid126 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs126)

theorem contexts126_valid : contexts126.all contextValid126 = true := by
  decide +kernel

theorem contextKeys126_exact : contextKeys126 = recordedClassKeys 126 := by
  decide +kernel

theorem root126_exact : root126 = recordedClassRoot 126 := by
  decide +kernel

theorem class126_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 126) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 126) (digits code) = true := by
  rw [← contextKeys126_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts126_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs126) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs126_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root126_exact]
  exact base_job_numeric_membership baseBoxes126 c.1 c.2.2.2 hj
    retainedDiagram root126 tree126 originalCover126 c.2.1 code hp.1 hc hk'

#print axioms jobs126_valid
#print axioms contexts126_valid
#print axioms contextKeys126_exact
#print axioms root126_exact
#print axioms class126_context_membership
end Snake9.Batch92
