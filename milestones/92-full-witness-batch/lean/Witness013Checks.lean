import Witness013Data
import Balanced013Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs013_valid : jobs013.all (baseJobValid baseBoxes013) = true := by
  decide +kernel

def contextValid013 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs013)

theorem contexts013_valid : contexts013.all contextValid013 = true := by
  decide +kernel

theorem contextKeys013_exact : contextKeys013 = recordedClassKeys 13 := by
  decide +kernel

theorem root013_exact : root013 = recordedClassRoot 13 := by
  decide +kernel

theorem class013_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 13) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 13) (digits code) = true := by
  rw [← contextKeys013_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts013_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs013) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs013_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root013_exact]
  exact base_job_numeric_membership baseBoxes013 c.1 c.2.2.2 hj
    retainedDiagram root013 tree013 originalCover013 c.2.1 code hp.1 hc hk'

#print axioms jobs013_valid
#print axioms contexts013_valid
#print axioms contextKeys013_exact
#print axioms root013_exact
#print axioms class013_context_membership
end Snake9.Batch92
