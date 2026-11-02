import Witness009Data
import Balanced009Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs009_valid : jobs009.all (baseJobValid baseBoxes009) = true := by
  decide +kernel

def contextValid009 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs009)

theorem contexts009_valid : contexts009.all contextValid009 = true := by
  decide +kernel

theorem contextKeys009_exact : contextKeys009 = recordedClassKeys 9 := by
  decide +kernel

theorem root009_exact : root009 = recordedClassRoot 9 := by
  decide +kernel

theorem class009_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 9) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 9) (digits code) = true := by
  rw [← contextKeys009_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts009_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs009) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs009_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root009_exact]
  exact base_job_numeric_membership baseBoxes009 c.1 c.2.2.2 hj
    retainedDiagram root009 tree009 originalCover009 c.2.1 code hp.1 hc hk'

#print axioms jobs009_valid
#print axioms contexts009_valid
#print axioms contextKeys009_exact
#print axioms root009_exact
#print axioms class009_context_membership
end Snake9.Batch92
