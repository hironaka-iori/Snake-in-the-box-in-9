import Witness032Data
import Balanced032Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs032_valid : jobs032.all (baseJobValid baseBoxes032) = true := by
  decide +kernel

def contextValid032 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs032)

theorem contexts032_valid : contexts032.all contextValid032 = true := by
  decide +kernel

theorem contextKeys032_exact : contextKeys032 = recordedClassKeys 32 := by
  decide +kernel

theorem root032_exact : root032 = recordedClassRoot 32 := by
  decide +kernel

theorem class032_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 32) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 32) (digits code) = true := by
  rw [← contextKeys032_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts032_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs032) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs032_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root032_exact]
  exact base_job_numeric_membership baseBoxes032 c.1 c.2.2.2 hj
    retainedDiagram root032 tree032 originalCover032 c.2.1 code hp.1 hc hk'

#print axioms jobs032_valid
#print axioms contexts032_valid
#print axioms contextKeys032_exact
#print axioms root032_exact
#print axioms class032_context_membership
end Snake9.Batch92
