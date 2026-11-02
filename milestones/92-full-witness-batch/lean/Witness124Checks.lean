import Witness124Data
import Balanced124Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs124_valid : jobs124.all (baseJobValid baseBoxes124) = true := by
  decide +kernel

def contextValid124 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs124)

theorem contexts124_valid : contexts124.all contextValid124 = true := by
  decide +kernel

theorem contextKeys124_exact : contextKeys124 = recordedClassKeys 124 := by
  decide +kernel

theorem root124_exact : root124 = recordedClassRoot 124 := by
  decide +kernel

theorem class124_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 124) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 124) (digits code) = true := by
  rw [← contextKeys124_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts124_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs124) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs124_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root124_exact]
  exact base_job_numeric_membership baseBoxes124 c.1 c.2.2.2 hj
    retainedDiagram root124 tree124 originalCover124 c.2.1 code hp.1 hc hk'

#print axioms jobs124_valid
#print axioms contexts124_valid
#print axioms contextKeys124_exact
#print axioms root124_exact
#print axioms class124_context_membership
end Snake9.Batch92
