import Witness025Data
import Balanced025Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs025_valid : jobs025.all (baseJobValid baseBoxes025) = true := by
  decide +kernel

def contextValid025 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs025)

theorem contexts025_valid : contexts025.all contextValid025 = true := by
  decide +kernel

theorem contextKeys025_exact : contextKeys025 = recordedClassKeys 25 := by
  decide +kernel

theorem root025_exact : root025 = recordedClassRoot 25 := by
  decide +kernel

theorem class025_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 25) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 25) (digits code) = true := by
  rw [← contextKeys025_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts025_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs025) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs025_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root025_exact]
  exact base_job_numeric_membership baseBoxes025 c.1 c.2.2.2 hj
    retainedDiagram root025 tree025 originalCover025 c.2.1 code hp.1 hc hk'

#print axioms jobs025_valid
#print axioms contexts025_valid
#print axioms contextKeys025_exact
#print axioms root025_exact
#print axioms class025_context_membership
end Snake9.Batch92
