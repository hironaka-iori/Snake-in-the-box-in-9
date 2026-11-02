import Witness017Data
import Balanced017Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs017_valid : jobs017.all (baseJobValid baseBoxes017) = true := by
  decide +kernel

def contextValid017 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs017)

theorem contexts017_valid : contexts017.all contextValid017 = true := by
  decide +kernel

theorem contextKeys017_exact : contextKeys017 = recordedClassKeys 17 := by
  decide +kernel

theorem root017_exact : root017 = recordedClassRoot 17 := by
  decide +kernel

theorem class017_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 17) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 17) (digits code) = true := by
  rw [← contextKeys017_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts017_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs017) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs017_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root017_exact]
  exact base_job_numeric_membership baseBoxes017 c.1 c.2.2.2 hj
    retainedDiagram root017 tree017 originalCover017 c.2.1 code hp.1 hc hk'

#print axioms jobs017_valid
#print axioms contexts017_valid
#print axioms contextKeys017_exact
#print axioms root017_exact
#print axioms class017_context_membership
end Snake9.Batch92
