import Witness061Data
import Balanced061Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs061_valid : jobs061.all (baseJobValid baseBoxes061) = true := by
  decide +kernel

def contextValid061 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs061)

theorem contexts061_valid : contexts061.all contextValid061 = true := by
  decide +kernel

theorem contextKeys061_exact : contextKeys061 = recordedClassKeys 61 := by
  decide +kernel

theorem root061_exact : root061 = recordedClassRoot 61 := by
  decide +kernel

theorem class061_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 61) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 61) (digits code) = true := by
  rw [← contextKeys061_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts061_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs061) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs061_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root061_exact]
  exact base_job_numeric_membership baseBoxes061 c.1 c.2.2.2 hj
    retainedDiagram root061 tree061 originalCover061 c.2.1 code hp.1 hc hk'

#print axioms jobs061_valid
#print axioms contexts061_valid
#print axioms contextKeys061_exact
#print axioms root061_exact
#print axioms class061_context_membership
end Snake9.Batch92
