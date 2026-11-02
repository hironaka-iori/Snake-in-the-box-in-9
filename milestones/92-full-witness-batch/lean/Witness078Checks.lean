import Witness078Data
import Balanced078Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs078_valid : jobs078.all (baseJobValid baseBoxes078) = true := by
  decide +kernel

def contextValid078 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs078)

theorem contexts078_valid : contexts078.all contextValid078 = true := by
  decide +kernel

theorem contextKeys078_exact : contextKeys078 = recordedClassKeys 78 := by
  decide +kernel

theorem root078_exact : root078 = recordedClassRoot 78 := by
  decide +kernel

theorem class078_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 78) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 78) (digits code) = true := by
  rw [← contextKeys078_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts078_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs078) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs078_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root078_exact]
  exact base_job_numeric_membership baseBoxes078 c.1 c.2.2.2 hj
    retainedDiagram root078 tree078 originalCover078 c.2.1 code hp.1 hc hk'

#print axioms jobs078_valid
#print axioms contexts078_valid
#print axioms contextKeys078_exact
#print axioms root078_exact
#print axioms class078_context_membership
end Snake9.Batch92
