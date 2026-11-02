import Witness034Data
import Balanced034Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs034_valid : jobs034.all (baseJobValid baseBoxes034) = true := by
  decide +kernel

def contextValid034 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs034)

theorem contexts034_valid : contexts034.all contextValid034 = true := by
  decide +kernel

theorem contextKeys034_exact : contextKeys034 = recordedClassKeys 34 := by
  decide +kernel

theorem root034_exact : root034 = recordedClassRoot 34 := by
  decide +kernel

theorem class034_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 34) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 34) (digits code) = true := by
  rw [← contextKeys034_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts034_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs034) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs034_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root034_exact]
  exact base_job_numeric_membership baseBoxes034 c.1 c.2.2.2 hj
    retainedDiagram root034 tree034 originalCover034 c.2.1 code hp.1 hc hk'

#print axioms jobs034_valid
#print axioms contexts034_valid
#print axioms contextKeys034_exact
#print axioms root034_exact
#print axioms class034_context_membership
end Snake9.Batch92
