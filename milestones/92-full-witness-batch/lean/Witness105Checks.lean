import Witness105Data
import Balanced105Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs105_valid : jobs105.all (baseJobValid baseBoxes105) = true := by
  decide +kernel

def contextValid105 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs105)

theorem contexts105_valid : contexts105.all contextValid105 = true := by
  decide +kernel

theorem contextKeys105_exact : contextKeys105 = recordedClassKeys 105 := by
  decide +kernel

theorem root105_exact : root105 = recordedClassRoot 105 := by
  decide +kernel

theorem class105_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 105) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 105) (digits code) = true := by
  rw [← contextKeys105_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts105_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs105) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs105_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root105_exact]
  exact base_job_numeric_membership baseBoxes105 c.1 c.2.2.2 hj
    retainedDiagram root105 tree105 originalCover105 c.2.1 code hp.1 hc hk'

#print axioms jobs105_valid
#print axioms contexts105_valid
#print axioms contextKeys105_exact
#print axioms root105_exact
#print axioms class105_context_membership
end Snake9.Batch92
