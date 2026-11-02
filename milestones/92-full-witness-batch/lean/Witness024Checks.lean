import Witness024Data
import Balanced024Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs024_valid : jobs024.all (baseJobValid baseBoxes024) = true := by
  decide +kernel

def contextValid024 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs024)

theorem contexts024_valid : contexts024.all contextValid024 = true := by
  decide +kernel

theorem contextKeys024_exact : contextKeys024 = recordedClassKeys 24 := by
  decide +kernel

theorem root024_exact : root024 = recordedClassRoot 24 := by
  decide +kernel

theorem class024_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 24) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 24) (digits code) = true := by
  rw [← contextKeys024_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts024_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs024) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs024_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root024_exact]
  exact base_job_numeric_membership baseBoxes024 c.1 c.2.2.2 hj
    retainedDiagram root024 tree024 originalCover024 c.2.1 code hp.1 hc hk'

#print axioms jobs024_valid
#print axioms contexts024_valid
#print axioms contextKeys024_exact
#print axioms root024_exact
#print axioms class024_context_membership
end Snake9.Batch92
