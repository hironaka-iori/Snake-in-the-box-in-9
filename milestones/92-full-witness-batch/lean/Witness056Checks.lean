import Witness056Data
import Balanced056Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs056_valid : jobs056.all (baseJobValid baseBoxes056) = true := by
  decide +kernel

def contextValid056 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs056)

theorem contexts056_valid : contexts056.all contextValid056 = true := by
  decide +kernel

theorem contextKeys056_exact : contextKeys056 = recordedClassKeys 56 := by
  decide +kernel

theorem root056_exact : root056 = recordedClassRoot 56 := by
  decide +kernel

theorem class056_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 56) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 56) (digits code) = true := by
  rw [← contextKeys056_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts056_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs056) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs056_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root056_exact]
  exact base_job_numeric_membership baseBoxes056 c.1 c.2.2.2 hj
    retainedDiagram root056 tree056 originalCover056 c.2.1 code hp.1 hc hk'

#print axioms jobs056_valid
#print axioms contexts056_valid
#print axioms contextKeys056_exact
#print axioms root056_exact
#print axioms class056_context_membership
end Snake9.Batch92
