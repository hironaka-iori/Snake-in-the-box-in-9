import Witness036Data
import Balanced036Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs036_valid : jobs036.all (baseJobValid baseBoxes036) = true := by
  decide +kernel

def contextValid036 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs036)

theorem contexts036_valid : contexts036.all contextValid036 = true := by
  decide +kernel

theorem contextKeys036_exact : contextKeys036 = recordedClassKeys 36 := by
  decide +kernel

theorem root036_exact : root036 = recordedClassRoot 36 := by
  decide +kernel

theorem class036_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 36) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 36) (digits code) = true := by
  rw [← contextKeys036_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts036_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs036) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs036_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root036_exact]
  exact base_job_numeric_membership baseBoxes036 c.1 c.2.2.2 hj
    retainedDiagram root036 tree036 originalCover036 c.2.1 code hp.1 hc hk'

#print axioms jobs036_valid
#print axioms contexts036_valid
#print axioms contextKeys036_exact
#print axioms root036_exact
#print axioms class036_context_membership
end Snake9.Batch92
