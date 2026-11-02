import Witness086Data
import Balanced086Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs086_valid : jobs086.all (baseJobValid baseBoxes086) = true := by
  decide +kernel

def contextValid086 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs086)

theorem contexts086_valid : contexts086.all contextValid086 = true := by
  decide +kernel

theorem contextKeys086_exact : contextKeys086 = recordedClassKeys 86 := by
  decide +kernel

theorem root086_exact : root086 = recordedClassRoot 86 := by
  decide +kernel

theorem class086_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 86) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 86) (digits code) = true := by
  rw [← contextKeys086_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts086_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs086) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs086_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root086_exact]
  exact base_job_numeric_membership baseBoxes086 c.1 c.2.2.2 hj
    retainedDiagram root086 tree086 originalCover086 c.2.1 code hp.1 hc hk'

#print axioms jobs086_valid
#print axioms contexts086_valid
#print axioms contextKeys086_exact
#print axioms root086_exact
#print axioms class086_context_membership
end Snake9.Batch92
