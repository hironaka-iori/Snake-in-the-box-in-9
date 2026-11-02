import Witness000Data
import Balanced000Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs000_valid : jobs000.all (baseJobValid baseBoxes000) = true := by
  decide +kernel

def contextValid000 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs000)

theorem contexts000_valid : contexts000.all contextValid000 = true := by
  decide +kernel

theorem contextKeys000_exact : contextKeys000 = recordedClassKeys 0 := by
  decide +kernel

theorem root000_exact : root000 = recordedClassRoot 0 := by
  decide +kernel

theorem class000_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 0) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 0) (digits code) = true := by
  rw [← contextKeys000_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts000_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs000) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs000_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root000_exact]
  exact base_job_numeric_membership baseBoxes000 c.1 c.2.2.2 hj
    retainedDiagram root000 tree000 originalCover000 c.2.1 code hp.1 hc hk'

#print axioms jobs000_valid
#print axioms contexts000_valid
#print axioms contextKeys000_exact
#print axioms root000_exact
#print axioms class000_context_membership
end Snake9.Batch92
