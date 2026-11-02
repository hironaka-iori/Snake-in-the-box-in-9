import Witness112Data
import Balanced112Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs112_valid : jobs112.all (baseJobValid baseBoxes112) = true := by
  decide +kernel

def contextValid112 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs112)

theorem contexts112_valid : contexts112.all contextValid112 = true := by
  decide +kernel

theorem contextKeys112_exact : contextKeys112 = recordedClassKeys 112 := by
  decide +kernel

theorem root112_exact : root112 = recordedClassRoot 112 := by
  decide +kernel

theorem class112_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 112) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 112) (digits code) = true := by
  rw [← contextKeys112_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts112_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs112) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs112_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root112_exact]
  exact base_job_numeric_membership baseBoxes112 c.1 c.2.2.2 hj
    retainedDiagram root112 tree112 originalCover112 c.2.1 code hp.1 hc hk'

#print axioms jobs112_valid
#print axioms contexts112_valid
#print axioms contextKeys112_exact
#print axioms root112_exact
#print axioms class112_context_membership
end Snake9.Batch92
