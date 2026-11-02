import Witness071Data
import Balanced071Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs071_valid : jobs071.all (baseJobValid baseBoxes071) = true := by
  decide +kernel

def contextValid071 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs071)

theorem contexts071_valid : contexts071.all contextValid071 = true := by
  decide +kernel

theorem contextKeys071_exact : contextKeys071 = recordedClassKeys 71 := by
  decide +kernel

theorem root071_exact : root071 = recordedClassRoot 71 := by
  decide +kernel

theorem class071_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 71) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 71) (digits code) = true := by
  rw [← contextKeys071_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts071_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs071) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs071_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root071_exact]
  exact base_job_numeric_membership baseBoxes071 c.1 c.2.2.2 hj
    retainedDiagram root071 tree071 originalCover071 c.2.1 code hp.1 hc hk'

#print axioms jobs071_valid
#print axioms contexts071_valid
#print axioms contextKeys071_exact
#print axioms root071_exact
#print axioms class071_context_membership
end Snake9.Batch92
