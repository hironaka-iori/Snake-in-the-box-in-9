import Witness042Data
import Balanced042Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs042_valid : jobs042.all (baseJobValid baseBoxes042) = true := by
  decide +kernel

def contextValid042 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs042)

theorem contexts042_valid : contexts042.all contextValid042 = true := by
  decide +kernel

theorem contextKeys042_exact : contextKeys042 = recordedClassKeys 42 := by
  decide +kernel

theorem root042_exact : root042 = recordedClassRoot 42 := by
  decide +kernel

theorem class042_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 42) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 42) (digits code) = true := by
  rw [← contextKeys042_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts042_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs042) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs042_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root042_exact]
  exact base_job_numeric_membership baseBoxes042 c.1 c.2.2.2 hj
    retainedDiagram root042 tree042 originalCover042 c.2.1 code hp.1 hc hk'

#print axioms jobs042_valid
#print axioms contexts042_valid
#print axioms contextKeys042_exact
#print axioms root042_exact
#print axioms class042_context_membership
end Snake9.Batch92
