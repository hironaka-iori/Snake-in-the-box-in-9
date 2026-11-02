import Witness084Data
import Balanced084Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs084_valid : jobs084.all (baseJobValid baseBoxes084) = true := by
  decide +kernel

def contextValid084 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs084)

theorem contexts084_valid : contexts084.all contextValid084 = true := by
  decide +kernel

theorem contextKeys084_exact : contextKeys084 = recordedClassKeys 84 := by
  decide +kernel

theorem root084_exact : root084 = recordedClassRoot 84 := by
  decide +kernel

theorem class084_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 84) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 84) (digits code) = true := by
  rw [← contextKeys084_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts084_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs084) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs084_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root084_exact]
  exact base_job_numeric_membership baseBoxes084 c.1 c.2.2.2 hj
    retainedDiagram root084 tree084 originalCover084 c.2.1 code hp.1 hc hk'

#print axioms jobs084_valid
#print axioms contexts084_valid
#print axioms contextKeys084_exact
#print axioms root084_exact
#print axioms class084_context_membership
end Snake9.Batch92
