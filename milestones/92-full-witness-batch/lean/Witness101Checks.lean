import Witness101Data
import Balanced101Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs101_valid : jobs101.all (baseJobValid baseBoxes101) = true := by
  decide +kernel

def contextValid101 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs101)

theorem contexts101_valid : contexts101.all contextValid101 = true := by
  decide +kernel

theorem contextKeys101_exact : contextKeys101 = recordedClassKeys 101 := by
  decide +kernel

theorem root101_exact : root101 = recordedClassRoot 101 := by
  decide +kernel

theorem class101_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 101) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 101) (digits code) = true := by
  rw [← contextKeys101_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts101_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs101) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs101_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root101_exact]
  exact base_job_numeric_membership baseBoxes101 c.1 c.2.2.2 hj
    retainedDiagram root101 tree101 originalCover101 c.2.1 code hp.1 hc hk'

#print axioms jobs101_valid
#print axioms contexts101_valid
#print axioms contextKeys101_exact
#print axioms root101_exact
#print axioms class101_context_membership
end Snake9.Batch92
