import Witness059Data
import Balanced059Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs059_valid : jobs059.all (baseJobValid baseBoxes059) = true := by
  decide +kernel

def contextValid059 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs059)

theorem contexts059_valid : contexts059.all contextValid059 = true := by
  decide +kernel

theorem contextKeys059_exact : contextKeys059 = recordedClassKeys 59 := by
  decide +kernel

theorem root059_exact : root059 = recordedClassRoot 59 := by
  decide +kernel

theorem class059_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 59) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 59) (digits code) = true := by
  rw [← contextKeys059_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts059_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs059) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs059_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root059_exact]
  exact base_job_numeric_membership baseBoxes059 c.1 c.2.2.2 hj
    retainedDiagram root059 tree059 originalCover059 c.2.1 code hp.1 hc hk'

#print axioms jobs059_valid
#print axioms contexts059_valid
#print axioms contextKeys059_exact
#print axioms root059_exact
#print axioms class059_context_membership
end Snake9.Batch92
