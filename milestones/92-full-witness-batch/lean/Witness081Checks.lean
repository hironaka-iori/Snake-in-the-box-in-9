import Witness081Data
import Balanced081Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs081_valid : jobs081.all (baseJobValid baseBoxes081) = true := by
  decide +kernel

def contextValid081 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs081)

theorem contexts081_valid : contexts081.all contextValid081 = true := by
  decide +kernel

theorem contextKeys081_exact : contextKeys081 = recordedClassKeys 81 := by
  decide +kernel

theorem root081_exact : root081 = recordedClassRoot 81 := by
  decide +kernel

theorem class081_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 81) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 81) (digits code) = true := by
  rw [← contextKeys081_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts081_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs081) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs081_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root081_exact]
  exact base_job_numeric_membership baseBoxes081 c.1 c.2.2.2 hj
    retainedDiagram root081 tree081 originalCover081 c.2.1 code hp.1 hc hk'

#print axioms jobs081_valid
#print axioms contexts081_valid
#print axioms contextKeys081_exact
#print axioms root081_exact
#print axioms class081_context_membership
end Snake9.Batch92
