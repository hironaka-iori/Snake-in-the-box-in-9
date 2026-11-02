import Witness107Data
import Balanced107Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs107_valid : jobs107.all (baseJobValid baseBoxes107) = true := by
  decide +kernel

def contextValid107 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs107)

theorem contexts107_valid : contexts107.all contextValid107 = true := by
  decide +kernel

theorem contextKeys107_exact : contextKeys107 = recordedClassKeys 107 := by
  decide +kernel

theorem root107_exact : root107 = recordedClassRoot 107 := by
  decide +kernel

theorem class107_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 107) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 107) (digits code) = true := by
  rw [← contextKeys107_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts107_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs107) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs107_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root107_exact]
  exact base_job_numeric_membership baseBoxes107 c.1 c.2.2.2 hj
    retainedDiagram root107 tree107 originalCover107 c.2.1 code hp.1 hc hk'

#print axioms jobs107_valid
#print axioms contexts107_valid
#print axioms contextKeys107_exact
#print axioms root107_exact
#print axioms class107_context_membership
end Snake9.Batch92
