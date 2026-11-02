import Witness066Data
import Balanced066Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs066_valid : jobs066.all (baseJobValid baseBoxes066) = true := by
  decide +kernel

def contextValid066 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs066)

theorem contexts066_valid : contexts066.all contextValid066 = true := by
  decide +kernel

theorem contextKeys066_exact : contextKeys066 = recordedClassKeys 66 := by
  decide +kernel

theorem root066_exact : root066 = recordedClassRoot 66 := by
  decide +kernel

theorem class066_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 66) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 66) (digits code) = true := by
  rw [← contextKeys066_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts066_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs066) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs066_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root066_exact]
  exact base_job_numeric_membership baseBoxes066 c.1 c.2.2.2 hj
    retainedDiagram root066 tree066 originalCover066 c.2.1 code hp.1 hc hk'

#print axioms jobs066_valid
#print axioms contexts066_valid
#print axioms contextKeys066_exact
#print axioms root066_exact
#print axioms class066_context_membership
end Snake9.Batch92
