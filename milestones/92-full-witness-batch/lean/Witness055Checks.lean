import Witness055Data
import Balanced055Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs055_valid : jobs055.all (baseJobValid baseBoxes055) = true := by
  decide +kernel

def contextValid055 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs055)

theorem contexts055_valid : contexts055.all contextValid055 = true := by
  decide +kernel

theorem contextKeys055_exact : contextKeys055 = recordedClassKeys 55 := by
  decide +kernel

theorem root055_exact : root055 = recordedClassRoot 55 := by
  decide +kernel

theorem class055_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 55) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 55) (digits code) = true := by
  rw [← contextKeys055_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts055_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs055) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs055_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root055_exact]
  exact base_job_numeric_membership baseBoxes055 c.1 c.2.2.2 hj
    retainedDiagram root055 tree055 originalCover055 c.2.1 code hp.1 hc hk'

#print axioms jobs055_valid
#print axioms contexts055_valid
#print axioms contextKeys055_exact
#print axioms root055_exact
#print axioms class055_context_membership
end Snake9.Batch92
