import Witness109Data
import Balanced109Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs109_valid : jobs109.all (baseJobValid baseBoxes109) = true := by
  decide +kernel

def contextValid109 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs109)

theorem contexts109_valid : contexts109.all contextValid109 = true := by
  decide +kernel

theorem contextKeys109_exact : contextKeys109 = recordedClassKeys 109 := by
  decide +kernel

theorem root109_exact : root109 = recordedClassRoot 109 := by
  decide +kernel

theorem class109_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 109) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 109) (digits code) = true := by
  rw [← contextKeys109_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts109_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs109) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs109_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root109_exact]
  exact base_job_numeric_membership baseBoxes109 c.1 c.2.2.2 hj
    retainedDiagram root109 tree109 originalCover109 c.2.1 code hp.1 hc hk'

#print axioms jobs109_valid
#print axioms contexts109_valid
#print axioms contextKeys109_exact
#print axioms root109_exact
#print axioms class109_context_membership
end Snake9.Batch92
