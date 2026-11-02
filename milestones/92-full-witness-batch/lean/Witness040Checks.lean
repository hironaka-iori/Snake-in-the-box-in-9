import Witness040Data
import Balanced040Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs040_valid : jobs040.all (baseJobValid baseBoxes040) = true := by
  decide +kernel

def contextValid040 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs040)

theorem contexts040_valid : contexts040.all contextValid040 = true := by
  decide +kernel

theorem contextKeys040_exact : contextKeys040 = recordedClassKeys 40 := by
  decide +kernel

theorem root040_exact : root040 = recordedClassRoot 40 := by
  decide +kernel

theorem class040_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 40) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 40) (digits code) = true := by
  rw [← contextKeys040_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts040_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs040) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs040_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root040_exact]
  exact base_job_numeric_membership baseBoxes040 c.1 c.2.2.2 hj
    retainedDiagram root040 tree040 originalCover040 c.2.1 code hp.1 hc hk'

#print axioms jobs040_valid
#print axioms contexts040_valid
#print axioms contextKeys040_exact
#print axioms root040_exact
#print axioms class040_context_membership
end Snake9.Batch92
