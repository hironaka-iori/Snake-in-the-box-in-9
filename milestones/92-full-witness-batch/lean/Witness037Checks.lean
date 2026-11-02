import Witness037Data
import Balanced037Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs037_valid : jobs037.all (baseJobValid baseBoxes037) = true := by
  decide +kernel

def contextValid037 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs037)

theorem contexts037_valid : contexts037.all contextValid037 = true := by
  decide +kernel

theorem contextKeys037_exact : contextKeys037 = recordedClassKeys 37 := by
  decide +kernel

theorem root037_exact : root037 = recordedClassRoot 37 := by
  decide +kernel

theorem class037_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 37) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 37) (digits code) = true := by
  rw [← contextKeys037_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts037_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs037) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs037_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root037_exact]
  exact base_job_numeric_membership baseBoxes037 c.1 c.2.2.2 hj
    retainedDiagram root037 tree037 originalCover037 c.2.1 code hp.1 hc hk'

#print axioms jobs037_valid
#print axioms contexts037_valid
#print axioms contextKeys037_exact
#print axioms root037_exact
#print axioms class037_context_membership
end Snake9.Batch92
