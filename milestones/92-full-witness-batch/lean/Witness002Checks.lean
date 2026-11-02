import Witness002Data
import Balanced002Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs002_valid : jobs002.all (baseJobValid baseBoxes002) = true := by
  decide +kernel

def contextValid002 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs002)

theorem contexts002_valid : contexts002.all contextValid002 = true := by
  decide +kernel

theorem contextKeys002_exact : contextKeys002 = recordedClassKeys 2 := by
  decide +kernel

theorem root002_exact : root002 = recordedClassRoot 2 := by
  decide +kernel

theorem class002_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 2) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 2) (digits code) = true := by
  rw [← contextKeys002_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts002_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs002) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs002_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root002_exact]
  exact base_job_numeric_membership baseBoxes002 c.1 c.2.2.2 hj
    retainedDiagram root002 tree002 originalCover002 c.2.1 code hp.1 hc hk'

#print axioms jobs002_valid
#print axioms contexts002_valid
#print axioms contextKeys002_exact
#print axioms root002_exact
#print axioms class002_context_membership
end Snake9.Batch92
