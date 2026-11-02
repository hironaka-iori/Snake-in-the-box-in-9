import Witness072Data
import Balanced072Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs072_valid : jobs072.all (baseJobValid baseBoxes072) = true := by
  decide +kernel

def contextValid072 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs072)

theorem contexts072_valid : contexts072.all contextValid072 = true := by
  decide +kernel

theorem contextKeys072_exact : contextKeys072 = recordedClassKeys 72 := by
  decide +kernel

theorem root072_exact : root072 = recordedClassRoot 72 := by
  decide +kernel

theorem class072_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 72) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 72) (digits code) = true := by
  rw [← contextKeys072_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts072_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs072) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs072_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root072_exact]
  exact base_job_numeric_membership baseBoxes072 c.1 c.2.2.2 hj
    retainedDiagram root072 tree072 originalCover072 c.2.1 code hp.1 hc hk'

#print axioms jobs072_valid
#print axioms contexts072_valid
#print axioms contextKeys072_exact
#print axioms root072_exact
#print axioms class072_context_membership
end Snake9.Batch92
