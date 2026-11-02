import Witness060Data
import Balanced060Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs060_valid : jobs060.all (baseJobValid baseBoxes060) = true := by
  decide +kernel

def contextValid060 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs060)

theorem contexts060_valid : contexts060.all contextValid060 = true := by
  decide +kernel

theorem contextKeys060_exact : contextKeys060 = recordedClassKeys 60 := by
  decide +kernel

theorem root060_exact : root060 = recordedClassRoot 60 := by
  decide +kernel

theorem class060_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 60) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 60) (digits code) = true := by
  rw [← contextKeys060_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts060_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs060) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs060_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root060_exact]
  exact base_job_numeric_membership baseBoxes060 c.1 c.2.2.2 hj
    retainedDiagram root060 tree060 originalCover060 c.2.1 code hp.1 hc hk'

#print axioms jobs060_valid
#print axioms contexts060_valid
#print axioms contextKeys060_exact
#print axioms root060_exact
#print axioms class060_context_membership
end Snake9.Batch92
