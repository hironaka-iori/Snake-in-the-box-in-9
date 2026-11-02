import Witness015Data
import Balanced015Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs015_valid : jobs015.all (baseJobValid baseBoxes015) = true := by
  decide +kernel

def contextValid015 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs015)

theorem contexts015_valid : contexts015.all contextValid015 = true := by
  decide +kernel

theorem contextKeys015_exact : contextKeys015 = recordedClassKeys 15 := by
  decide +kernel

theorem root015_exact : root015 = recordedClassRoot 15 := by
  decide +kernel

theorem class015_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 15) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 15) (digits code) = true := by
  rw [← contextKeys015_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts015_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs015) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs015_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root015_exact]
  exact base_job_numeric_membership baseBoxes015 c.1 c.2.2.2 hj
    retainedDiagram root015 tree015 originalCover015 c.2.1 code hp.1 hc hk'

#print axioms jobs015_valid
#print axioms contexts015_valid
#print axioms contextKeys015_exact
#print axioms root015_exact
#print axioms class015_context_membership
end Snake9.Batch92
