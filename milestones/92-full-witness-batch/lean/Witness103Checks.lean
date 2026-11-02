import Witness103Data
import Balanced103Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs103_valid : jobs103.all (baseJobValid baseBoxes103) = true := by
  decide +kernel

def contextValid103 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs103)

theorem contexts103_valid : contexts103.all contextValid103 = true := by
  decide +kernel

theorem contextKeys103_exact : contextKeys103 = recordedClassKeys 103 := by
  decide +kernel

theorem root103_exact : root103 = recordedClassRoot 103 := by
  decide +kernel

theorem class103_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 103) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 103) (digits code) = true := by
  rw [← contextKeys103_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts103_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs103) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs103_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root103_exact]
  exact base_job_numeric_membership baseBoxes103 c.1 c.2.2.2 hj
    retainedDiagram root103 tree103 originalCover103 c.2.1 code hp.1 hc hk'

#print axioms jobs103_valid
#print axioms contexts103_valid
#print axioms contextKeys103_exact
#print axioms root103_exact
#print axioms class103_context_membership
end Snake9.Batch92
