import Witness011Data
import Balanced011Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs011_valid : jobs011.all (baseJobValid baseBoxes011) = true := by
  decide +kernel

def contextValid011 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs011)

theorem contexts011_valid : contexts011.all contextValid011 = true := by
  decide +kernel

theorem contextKeys011_exact : contextKeys011 = recordedClassKeys 11 := by
  decide +kernel

theorem root011_exact : root011 = recordedClassRoot 11 := by
  decide +kernel

theorem class011_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 11) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 11) (digits code) = true := by
  rw [← contextKeys011_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts011_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs011) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs011_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root011_exact]
  exact base_job_numeric_membership baseBoxes011 c.1 c.2.2.2 hj
    retainedDiagram root011 tree011 originalCover011 c.2.1 code hp.1 hc hk'

#print axioms jobs011_valid
#print axioms contexts011_valid
#print axioms contextKeys011_exact
#print axioms root011_exact
#print axioms class011_context_membership
end Snake9.Batch92
