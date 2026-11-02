import Witness094Data
import Balanced094Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs094_valid : jobs094.all (baseJobValid baseBoxes094) = true := by
  decide +kernel

def contextValid094 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs094)

theorem contexts094_valid : contexts094.all contextValid094 = true := by
  decide +kernel

theorem contextKeys094_exact : contextKeys094 = recordedClassKeys 94 := by
  decide +kernel

theorem root094_exact : root094 = recordedClassRoot 94 := by
  decide +kernel

theorem class094_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 94) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 94) (digits code) = true := by
  rw [← contextKeys094_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts094_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs094) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs094_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root094_exact]
  exact base_job_numeric_membership baseBoxes094 c.1 c.2.2.2 hj
    retainedDiagram root094 tree094 originalCover094 c.2.1 code hp.1 hc hk'

#print axioms jobs094_valid
#print axioms contexts094_valid
#print axioms contextKeys094_exact
#print axioms root094_exact
#print axioms class094_context_membership
end Snake9.Batch92
