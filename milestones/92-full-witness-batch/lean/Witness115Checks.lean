import Witness115Data
import Balanced115Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs115_valid : jobs115.all (baseJobValid baseBoxes115) = true := by
  decide +kernel

def contextValid115 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs115)

theorem contexts115_valid : contexts115.all contextValid115 = true := by
  decide +kernel

theorem contextKeys115_exact : contextKeys115 = recordedClassKeys 115 := by
  decide +kernel

theorem root115_exact : root115 = recordedClassRoot 115 := by
  decide +kernel

theorem class115_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 115) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 115) (digits code) = true := by
  rw [← contextKeys115_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts115_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs115) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs115_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root115_exact]
  exact base_job_numeric_membership baseBoxes115 c.1 c.2.2.2 hj
    retainedDiagram root115 tree115 originalCover115 c.2.1 code hp.1 hc hk'

#print axioms jobs115_valid
#print axioms contexts115_valid
#print axioms contextKeys115_exact
#print axioms root115_exact
#print axioms class115_context_membership
end Snake9.Batch92
