import Witness106Data
import Balanced106Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs106_valid : jobs106.all (baseJobValid baseBoxes106) = true := by
  decide +kernel

def contextValid106 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs106)

theorem contexts106_valid : contexts106.all contextValid106 = true := by
  decide +kernel

theorem contextKeys106_exact : contextKeys106 = recordedClassKeys 106 := by
  decide +kernel

theorem root106_exact : root106 = recordedClassRoot 106 := by
  decide +kernel

theorem class106_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 106) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 106) (digits code) = true := by
  rw [← contextKeys106_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts106_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs106) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs106_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root106_exact]
  exact base_job_numeric_membership baseBoxes106 c.1 c.2.2.2 hj
    retainedDiagram root106 tree106 originalCover106 c.2.1 code hp.1 hc hk'

#print axioms jobs106_valid
#print axioms contexts106_valid
#print axioms contextKeys106_exact
#print axioms root106_exact
#print axioms class106_context_membership
end Snake9.Batch92
