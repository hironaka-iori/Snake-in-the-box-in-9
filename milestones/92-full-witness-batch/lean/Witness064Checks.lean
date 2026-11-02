import Witness064Data
import Balanced064Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs064_valid : jobs064.all (baseJobValid baseBoxes064) = true := by
  decide +kernel

def contextValid064 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs064)

theorem contexts064_valid : contexts064.all contextValid064 = true := by
  decide +kernel

theorem contextKeys064_exact : contextKeys064 = recordedClassKeys 64 := by
  decide +kernel

theorem root064_exact : root064 = recordedClassRoot 64 := by
  decide +kernel

theorem class064_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 64) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 64) (digits code) = true := by
  rw [← contextKeys064_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts064_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs064) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs064_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root064_exact]
  exact base_job_numeric_membership baseBoxes064 c.1 c.2.2.2 hj
    retainedDiagram root064 tree064 originalCover064 c.2.1 code hp.1 hc hk'

#print axioms jobs064_valid
#print axioms contexts064_valid
#print axioms contextKeys064_exact
#print axioms root064_exact
#print axioms class064_context_membership
end Snake9.Batch92
