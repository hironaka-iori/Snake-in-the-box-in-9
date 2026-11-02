import Witness102Data
import Balanced102Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs102_valid : jobs102.all (baseJobValid baseBoxes102) = true := by
  decide +kernel

def contextValid102 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs102)

theorem contexts102_valid : contexts102.all contextValid102 = true := by
  decide +kernel

theorem contextKeys102_exact : contextKeys102 = recordedClassKeys 102 := by
  decide +kernel

theorem root102_exact : root102 = recordedClassRoot 102 := by
  decide +kernel

theorem class102_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 102) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 102) (digits code) = true := by
  rw [← contextKeys102_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts102_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs102) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs102_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root102_exact]
  exact base_job_numeric_membership baseBoxes102 c.1 c.2.2.2 hj
    retainedDiagram root102 tree102 originalCover102 c.2.1 code hp.1 hc hk'

#print axioms jobs102_valid
#print axioms contexts102_valid
#print axioms contextKeys102_exact
#print axioms root102_exact
#print axioms class102_context_membership
end Snake9.Batch92
