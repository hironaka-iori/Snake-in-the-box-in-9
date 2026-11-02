import Witness057Data
import Balanced057Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs057_valid : jobs057.all (baseJobValid baseBoxes057) = true := by
  decide +kernel

def contextValid057 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs057)

theorem contexts057_valid : contexts057.all contextValid057 = true := by
  decide +kernel

theorem contextKeys057_exact : contextKeys057 = recordedClassKeys 57 := by
  decide +kernel

theorem root057_exact : root057 = recordedClassRoot 57 := by
  decide +kernel

theorem class057_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 57) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 57) (digits code) = true := by
  rw [← contextKeys057_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts057_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs057) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs057_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root057_exact]
  exact base_job_numeric_membership baseBoxes057 c.1 c.2.2.2 hj
    retainedDiagram root057 tree057 originalCover057 c.2.1 code hp.1 hc hk'

#print axioms jobs057_valid
#print axioms contexts057_valid
#print axioms contextKeys057_exact
#print axioms root057_exact
#print axioms class057_context_membership
end Snake9.Batch92
