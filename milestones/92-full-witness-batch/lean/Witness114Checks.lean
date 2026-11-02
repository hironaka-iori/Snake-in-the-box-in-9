import Witness114Data
import Balanced114Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs114_valid : jobs114.all (baseJobValid baseBoxes114) = true := by
  decide +kernel

def contextValid114 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs114)

theorem contexts114_valid : contexts114.all contextValid114 = true := by
  decide +kernel

theorem contextKeys114_exact : contextKeys114 = recordedClassKeys 114 := by
  decide +kernel

theorem root114_exact : root114 = recordedClassRoot 114 := by
  decide +kernel

theorem class114_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 114) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 114) (digits code) = true := by
  rw [← contextKeys114_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts114_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs114) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs114_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root114_exact]
  exact base_job_numeric_membership baseBoxes114 c.1 c.2.2.2 hj
    retainedDiagram root114 tree114 originalCover114 c.2.1 code hp.1 hc hk'

#print axioms jobs114_valid
#print axioms contexts114_valid
#print axioms contextKeys114_exact
#print axioms root114_exact
#print axioms class114_context_membership
end Snake9.Batch92
