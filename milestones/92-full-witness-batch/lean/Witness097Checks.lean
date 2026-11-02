import Witness097Data
import Balanced097Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs097_valid : jobs097.all (baseJobValid baseBoxes097) = true := by
  decide +kernel

def contextValid097 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs097)

theorem contexts097_valid : contexts097.all contextValid097 = true := by
  decide +kernel

theorem contextKeys097_exact : contextKeys097 = recordedClassKeys 97 := by
  decide +kernel

theorem root097_exact : root097 = recordedClassRoot 97 := by
  decide +kernel

theorem class097_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 97) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 97) (digits code) = true := by
  rw [← contextKeys097_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts097_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs097) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs097_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root097_exact]
  exact base_job_numeric_membership baseBoxes097 c.1 c.2.2.2 hj
    retainedDiagram root097 tree097 originalCover097 c.2.1 code hp.1 hc hk'

#print axioms jobs097_valid
#print axioms contexts097_valid
#print axioms contextKeys097_exact
#print axioms root097_exact
#print axioms class097_context_membership
end Snake9.Batch92
