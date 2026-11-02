import Witness039Data
import Balanced039Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs039_valid : jobs039.all (baseJobValid baseBoxes039) = true := by
  decide +kernel

def contextValid039 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs039)

theorem contexts039_valid : contexts039.all contextValid039 = true := by
  decide +kernel

theorem contextKeys039_exact : contextKeys039 = recordedClassKeys 39 := by
  decide +kernel

theorem root039_exact : root039 = recordedClassRoot 39 := by
  decide +kernel

theorem class039_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 39) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 39) (digits code) = true := by
  rw [← contextKeys039_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts039_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs039) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs039_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root039_exact]
  exact base_job_numeric_membership baseBoxes039 c.1 c.2.2.2 hj
    retainedDiagram root039 tree039 originalCover039 c.2.1 code hp.1 hc hk'

#print axioms jobs039_valid
#print axioms contexts039_valid
#print axioms contextKeys039_exact
#print axioms root039_exact
#print axioms class039_context_membership
end Snake9.Batch92
