import Witness048Data
import Balanced048Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs048_valid : jobs048.all (baseJobValid baseBoxes048) = true := by
  decide +kernel

def contextValid048 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs048)

theorem contexts048_valid : contexts048.all contextValid048 = true := by
  decide +kernel

theorem contextKeys048_exact : contextKeys048 = recordedClassKeys 48 := by
  decide +kernel

theorem root048_exact : root048 = recordedClassRoot 48 := by
  decide +kernel

theorem class048_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 48) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 48) (digits code) = true := by
  rw [← contextKeys048_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts048_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs048) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs048_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root048_exact]
  exact base_job_numeric_membership baseBoxes048 c.1 c.2.2.2 hj
    retainedDiagram root048 tree048 originalCover048 c.2.1 code hp.1 hc hk'

#print axioms jobs048_valid
#print axioms contexts048_valid
#print axioms contextKeys048_exact
#print axioms root048_exact
#print axioms class048_context_membership
end Snake9.Batch92
