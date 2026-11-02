import Witness058Data
import Balanced058Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs058_valid : jobs058.all (baseJobValid baseBoxes058) = true := by
  decide +kernel

def contextValid058 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs058)

theorem contexts058_valid : contexts058.all contextValid058 = true := by
  decide +kernel

theorem contextKeys058_exact : contextKeys058 = recordedClassKeys 58 := by
  decide +kernel

theorem root058_exact : root058 = recordedClassRoot 58 := by
  decide +kernel

theorem class058_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 58) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 58) (digits code) = true := by
  rw [← contextKeys058_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts058_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs058) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs058_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root058_exact]
  exact base_job_numeric_membership baseBoxes058 c.1 c.2.2.2 hj
    retainedDiagram root058 tree058 originalCover058 c.2.1 code hp.1 hc hk'

#print axioms jobs058_valid
#print axioms contexts058_valid
#print axioms contextKeys058_exact
#print axioms root058_exact
#print axioms class058_context_membership
end Snake9.Batch92
