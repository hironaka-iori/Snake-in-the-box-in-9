import Witness012Data
import Balanced012Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs012_valid : jobs012.all (baseJobValid baseBoxes012) = true := by
  decide +kernel

def contextValid012 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs012)

theorem contexts012_valid : contexts012.all contextValid012 = true := by
  decide +kernel

theorem contextKeys012_exact : contextKeys012 = recordedClassKeys 12 := by
  decide +kernel

theorem root012_exact : root012 = recordedClassRoot 12 := by
  decide +kernel

theorem class012_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 12) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 12) (digits code) = true := by
  rw [← contextKeys012_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts012_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs012) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs012_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root012_exact]
  exact base_job_numeric_membership baseBoxes012 c.1 c.2.2.2 hj
    retainedDiagram root012 tree012 originalCover012 c.2.1 code hp.1 hc hk'

#print axioms jobs012_valid
#print axioms contexts012_valid
#print axioms contextKeys012_exact
#print axioms root012_exact
#print axioms class012_context_membership
end Snake9.Batch92
