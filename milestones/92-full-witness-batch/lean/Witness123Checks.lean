import Witness123Data
import Balanced123Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs123_valid : jobs123.all (baseJobValid baseBoxes123) = true := by
  decide +kernel

def contextValid123 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs123)

theorem contexts123_valid : contexts123.all contextValid123 = true := by
  decide +kernel

theorem contextKeys123_exact : contextKeys123 = recordedClassKeys 123 := by
  decide +kernel

theorem root123_exact : root123 = recordedClassRoot 123 := by
  decide +kernel

theorem class123_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 123) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 123) (digits code) = true := by
  rw [← contextKeys123_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts123_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs123) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs123_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root123_exact]
  exact base_job_numeric_membership baseBoxes123 c.1 c.2.2.2 hj
    retainedDiagram root123 tree123 originalCover123 c.2.1 code hp.1 hc hk'

#print axioms jobs123_valid
#print axioms contexts123_valid
#print axioms contextKeys123_exact
#print axioms root123_exact
#print axioms class123_context_membership
end Snake9.Batch92
