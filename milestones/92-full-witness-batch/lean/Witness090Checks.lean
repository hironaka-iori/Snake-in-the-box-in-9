import Witness090Data
import Balanced090Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs090_valid : jobs090.all (baseJobValid baseBoxes090) = true := by
  decide +kernel

def contextValid090 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs090)

theorem contexts090_valid : contexts090.all contextValid090 = true := by
  decide +kernel

theorem contextKeys090_exact : contextKeys090 = recordedClassKeys 90 := by
  decide +kernel

theorem root090_exact : root090 = recordedClassRoot 90 := by
  decide +kernel

theorem class090_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 90) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 90) (digits code) = true := by
  rw [← contextKeys090_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts090_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs090) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs090_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root090_exact]
  exact base_job_numeric_membership baseBoxes090 c.1 c.2.2.2 hj
    retainedDiagram root090 tree090 originalCover090 c.2.1 code hp.1 hc hk'

#print axioms jobs090_valid
#print axioms contexts090_valid
#print axioms contextKeys090_exact
#print axioms root090_exact
#print axioms class090_context_membership
end Snake9.Batch92
