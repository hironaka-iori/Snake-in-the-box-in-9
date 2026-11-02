import Witness031Data
import Balanced031Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs031_valid : jobs031.all (baseJobValid baseBoxes031) = true := by
  decide +kernel

def contextValid031 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs031)

theorem contexts031_valid : contexts031.all contextValid031 = true := by
  decide +kernel

theorem contextKeys031_exact : contextKeys031 = recordedClassKeys 31 := by
  decide +kernel

theorem root031_exact : root031 = recordedClassRoot 31 := by
  decide +kernel

theorem class031_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 31) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 31) (digits code) = true := by
  rw [← contextKeys031_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts031_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs031) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs031_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root031_exact]
  exact base_job_numeric_membership baseBoxes031 c.1 c.2.2.2 hj
    retainedDiagram root031 tree031 originalCover031 c.2.1 code hp.1 hc hk'

#print axioms jobs031_valid
#print axioms contexts031_valid
#print axioms contextKeys031_exact
#print axioms root031_exact
#print axioms class031_context_membership
end Snake9.Batch92
