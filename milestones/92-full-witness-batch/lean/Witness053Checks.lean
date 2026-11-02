import Witness053Data
import Balanced053Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs053_valid : jobs053.all (baseJobValid baseBoxes053) = true := by
  decide +kernel

def contextValid053 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs053)

theorem contexts053_valid : contexts053.all contextValid053 = true := by
  decide +kernel

theorem contextKeys053_exact : contextKeys053 = recordedClassKeys 53 := by
  decide +kernel

theorem root053_exact : root053 = recordedClassRoot 53 := by
  decide +kernel

theorem class053_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 53) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 53) (digits code) = true := by
  rw [← contextKeys053_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts053_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs053) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs053_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root053_exact]
  exact base_job_numeric_membership baseBoxes053 c.1 c.2.2.2 hj
    retainedDiagram root053 tree053 originalCover053 c.2.1 code hp.1 hc hk'

#print axioms jobs053_valid
#print axioms contexts053_valid
#print axioms contextKeys053_exact
#print axioms root053_exact
#print axioms class053_context_membership
end Snake9.Batch92
