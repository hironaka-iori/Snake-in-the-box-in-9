import Witness113Data
import Balanced113Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs113_valid : jobs113.all (baseJobValid baseBoxes113) = true := by
  decide +kernel

def contextValid113 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs113)

theorem contexts113_valid : contexts113.all contextValid113 = true := by
  decide +kernel

theorem contextKeys113_exact : contextKeys113 = recordedClassKeys 113 := by
  decide +kernel

theorem root113_exact : root113 = recordedClassRoot 113 := by
  decide +kernel

theorem class113_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 113) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 113) (digits code) = true := by
  rw [← contextKeys113_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts113_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs113) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs113_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root113_exact]
  exact base_job_numeric_membership baseBoxes113 c.1 c.2.2.2 hj
    retainedDiagram root113 tree113 originalCover113 c.2.1 code hp.1 hc hk'

#print axioms jobs113_valid
#print axioms contexts113_valid
#print axioms contextKeys113_exact
#print axioms root113_exact
#print axioms class113_context_membership
end Snake9.Batch92
