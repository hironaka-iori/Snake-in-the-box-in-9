import Witness117Data
import Balanced117Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs117_valid : jobs117.all (baseJobValid baseBoxes117) = true := by
  decide +kernel

def contextValid117 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs117)

theorem contexts117_valid : contexts117.all contextValid117 = true := by
  decide +kernel

theorem contextKeys117_exact : contextKeys117 = recordedClassKeys 117 := by
  decide +kernel

theorem root117_exact : root117 = recordedClassRoot 117 := by
  decide +kernel

theorem class117_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 117) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 117) (digits code) = true := by
  rw [← contextKeys117_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts117_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs117) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs117_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root117_exact]
  exact base_job_numeric_membership baseBoxes117 c.1 c.2.2.2 hj
    retainedDiagram root117 tree117 originalCover117 c.2.1 code hp.1 hc hk'

#print axioms jobs117_valid
#print axioms contexts117_valid
#print axioms contextKeys117_exact
#print axioms root117_exact
#print axioms class117_context_membership
end Snake9.Batch92
