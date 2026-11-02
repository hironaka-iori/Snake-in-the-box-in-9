import Witness052Data
import Balanced052Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs052_valid : jobs052.all (baseJobValid baseBoxes052) = true := by
  decide +kernel

def contextValid052 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs052)

theorem contexts052_valid : contexts052.all contextValid052 = true := by
  decide +kernel

theorem contextKeys052_exact : contextKeys052 = recordedClassKeys 52 := by
  decide +kernel

theorem root052_exact : root052 = recordedClassRoot 52 := by
  decide +kernel

theorem class052_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 52) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 52) (digits code) = true := by
  rw [← contextKeys052_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts052_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs052) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs052_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root052_exact]
  exact base_job_numeric_membership baseBoxes052 c.1 c.2.2.2 hj
    retainedDiagram root052 tree052 originalCover052 c.2.1 code hp.1 hc hk'

#print axioms jobs052_valid
#print axioms contexts052_valid
#print axioms contextKeys052_exact
#print axioms root052_exact
#print axioms class052_context_membership
end Snake9.Batch92
