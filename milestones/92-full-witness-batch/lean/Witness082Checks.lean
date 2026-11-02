import Witness082Data
import Balanced082Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs082_valid : jobs082.all (baseJobValid baseBoxes082) = true := by
  decide +kernel

def contextValid082 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs082)

theorem contexts082_valid : contexts082.all contextValid082 = true := by
  decide +kernel

theorem contextKeys082_exact : contextKeys082 = recordedClassKeys 82 := by
  decide +kernel

theorem root082_exact : root082 = recordedClassRoot 82 := by
  decide +kernel

theorem class082_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 82) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 82) (digits code) = true := by
  rw [← contextKeys082_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts082_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs082) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs082_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root082_exact]
  exact base_job_numeric_membership baseBoxes082 c.1 c.2.2.2 hj
    retainedDiagram root082 tree082 originalCover082 c.2.1 code hp.1 hc hk'

#print axioms jobs082_valid
#print axioms contexts082_valid
#print axioms contextKeys082_exact
#print axioms root082_exact
#print axioms class082_context_membership
end Snake9.Batch92
