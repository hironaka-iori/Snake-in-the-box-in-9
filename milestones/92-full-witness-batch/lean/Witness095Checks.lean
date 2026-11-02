import Witness095Data
import Balanced095Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs095_valid : jobs095.all (baseJobValid baseBoxes095) = true := by
  decide +kernel

def contextValid095 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs095)

theorem contexts095_valid : contexts095.all contextValid095 = true := by
  decide +kernel

theorem contextKeys095_exact : contextKeys095 = recordedClassKeys 95 := by
  decide +kernel

theorem root095_exact : root095 = recordedClassRoot 95 := by
  decide +kernel

theorem class095_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 95) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 95) (digits code) = true := by
  rw [← contextKeys095_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts095_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs095) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs095_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root095_exact]
  exact base_job_numeric_membership baseBoxes095 c.1 c.2.2.2 hj
    retainedDiagram root095 tree095 originalCover095 c.2.1 code hp.1 hc hk'

#print axioms jobs095_valid
#print axioms contexts095_valid
#print axioms contextKeys095_exact
#print axioms root095_exact
#print axioms class095_context_membership
end Snake9.Batch92
