import Witness004Data
import Balanced004Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs004_valid : jobs004.all (baseJobValid baseBoxes004) = true := by
  decide +kernel

def contextValid004 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs004)

theorem contexts004_valid : contexts004.all contextValid004 = true := by
  decide +kernel

theorem contextKeys004_exact : contextKeys004 = recordedClassKeys 4 := by
  decide +kernel

theorem root004_exact : root004 = recordedClassRoot 4 := by
  decide +kernel

theorem class004_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 4) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 4) (digits code) = true := by
  rw [← contextKeys004_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts004_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs004) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs004_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root004_exact]
  exact base_job_numeric_membership baseBoxes004 c.1 c.2.2.2 hj
    retainedDiagram root004 tree004 originalCover004 c.2.1 code hp.1 hc hk'

#print axioms jobs004_valid
#print axioms contexts004_valid
#print axioms contextKeys004_exact
#print axioms root004_exact
#print axioms class004_context_membership
end Snake9.Batch92
