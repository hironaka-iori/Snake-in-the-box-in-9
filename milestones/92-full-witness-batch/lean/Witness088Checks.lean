import Witness088Data
import Balanced088Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs088_valid : jobs088.all (baseJobValid baseBoxes088) = true := by
  decide +kernel

def contextValid088 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs088)

theorem contexts088_valid : contexts088.all contextValid088 = true := by
  decide +kernel

theorem contextKeys088_exact : contextKeys088 = recordedClassKeys 88 := by
  decide +kernel

theorem root088_exact : root088 = recordedClassRoot 88 := by
  decide +kernel

theorem class088_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 88) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 88) (digits code) = true := by
  rw [← contextKeys088_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts088_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs088) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs088_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root088_exact]
  exact base_job_numeric_membership baseBoxes088 c.1 c.2.2.2 hj
    retainedDiagram root088 tree088 originalCover088 c.2.1 code hp.1 hc hk'

#print axioms jobs088_valid
#print axioms contexts088_valid
#print axioms contextKeys088_exact
#print axioms root088_exact
#print axioms class088_context_membership
end Snake9.Batch92
