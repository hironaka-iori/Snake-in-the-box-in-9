import Witness029Data
import Balanced029Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs029_valid : jobs029.all (baseJobValid baseBoxes029) = true := by
  decide +kernel

def contextValid029 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs029)

theorem contexts029_valid : contexts029.all contextValid029 = true := by
  decide +kernel

theorem contextKeys029_exact : contextKeys029 = recordedClassKeys 29 := by
  decide +kernel

theorem root029_exact : root029 = recordedClassRoot 29 := by
  decide +kernel

theorem class029_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 29) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 29) (digits code) = true := by
  rw [← contextKeys029_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts029_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs029) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs029_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root029_exact]
  exact base_job_numeric_membership baseBoxes029 c.1 c.2.2.2 hj
    retainedDiagram root029 tree029 originalCover029 c.2.1 code hp.1 hc hk'

#print axioms jobs029_valid
#print axioms contexts029_valid
#print axioms contextKeys029_exact
#print axioms root029_exact
#print axioms class029_context_membership
end Snake9.Batch92
