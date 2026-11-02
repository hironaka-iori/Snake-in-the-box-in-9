import Witness098Data
import Balanced098Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs098_valid : jobs098.all (baseJobValid baseBoxes098) = true := by
  decide +kernel

def contextValid098 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs098)

theorem contexts098_valid : contexts098.all contextValid098 = true := by
  decide +kernel

theorem contextKeys098_exact : contextKeys098 = recordedClassKeys 98 := by
  decide +kernel

theorem root098_exact : root098 = recordedClassRoot 98 := by
  decide +kernel

theorem class098_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 98) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 98) (digits code) = true := by
  rw [← contextKeys098_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts098_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs098) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs098_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root098_exact]
  exact base_job_numeric_membership baseBoxes098 c.1 c.2.2.2 hj
    retainedDiagram root098 tree098 originalCover098 c.2.1 code hp.1 hc hk'

#print axioms jobs098_valid
#print axioms contexts098_valid
#print axioms contextKeys098_exact
#print axioms root098_exact
#print axioms class098_context_membership
end Snake9.Batch92
