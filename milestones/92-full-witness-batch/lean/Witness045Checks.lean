import Witness045Data
import Balanced045Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs045_valid : jobs045.all (baseJobValid baseBoxes045) = true := by
  decide +kernel

def contextValid045 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs045)

theorem contexts045_valid : contexts045.all contextValid045 = true := by
  decide +kernel

theorem contextKeys045_exact : contextKeys045 = recordedClassKeys 45 := by
  decide +kernel

theorem root045_exact : root045 = recordedClassRoot 45 := by
  decide +kernel

theorem class045_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 45) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 45) (digits code) = true := by
  rw [← contextKeys045_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts045_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs045) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs045_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root045_exact]
  exact base_job_numeric_membership baseBoxes045 c.1 c.2.2.2 hj
    retainedDiagram root045 tree045 originalCover045 c.2.1 code hp.1 hc hk'

#print axioms jobs045_valid
#print axioms contexts045_valid
#print axioms contextKeys045_exact
#print axioms root045_exact
#print axioms class045_context_membership
end Snake9.Batch92
