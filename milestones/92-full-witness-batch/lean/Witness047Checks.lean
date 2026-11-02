import Witness047Data
import Balanced047Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs047_valid : jobs047.all (baseJobValid baseBoxes047) = true := by
  decide +kernel

def contextValid047 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs047)

theorem contexts047_valid : contexts047.all contextValid047 = true := by
  decide +kernel

theorem contextKeys047_exact : contextKeys047 = recordedClassKeys 47 := by
  decide +kernel

theorem root047_exact : root047 = recordedClassRoot 47 := by
  decide +kernel

theorem class047_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 47) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 47) (digits code) = true := by
  rw [← contextKeys047_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts047_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs047) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs047_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root047_exact]
  exact base_job_numeric_membership baseBoxes047 c.1 c.2.2.2 hj
    retainedDiagram root047 tree047 originalCover047 c.2.1 code hp.1 hc hk'

#print axioms jobs047_valid
#print axioms contexts047_valid
#print axioms contextKeys047_exact
#print axioms root047_exact
#print axioms class047_context_membership
end Snake9.Batch92
