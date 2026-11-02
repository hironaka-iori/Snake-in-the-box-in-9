import Witness100Data
import Balanced100Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs100_valid : jobs100.all (baseJobValid baseBoxes100) = true := by
  decide +kernel

def contextValid100 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs100)

theorem contexts100_valid : contexts100.all contextValid100 = true := by
  decide +kernel

theorem contextKeys100_exact : contextKeys100 = recordedClassKeys 100 := by
  decide +kernel

theorem root100_exact : root100 = recordedClassRoot 100 := by
  decide +kernel

theorem class100_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 100) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 100) (digits code) = true := by
  rw [← contextKeys100_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts100_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs100) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs100_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root100_exact]
  exact base_job_numeric_membership baseBoxes100 c.1 c.2.2.2 hj
    retainedDiagram root100 tree100 originalCover100 c.2.1 code hp.1 hc hk'

#print axioms jobs100_valid
#print axioms contexts100_valid
#print axioms contextKeys100_exact
#print axioms root100_exact
#print axioms class100_context_membership
end Snake9.Batch92
