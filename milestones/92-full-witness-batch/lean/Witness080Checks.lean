import Witness080Data
import Balanced080Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs080_valid : jobs080.all (baseJobValid baseBoxes080) = true := by
  decide +kernel

def contextValid080 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs080)

theorem contexts080_valid : contexts080.all contextValid080 = true := by
  decide +kernel

theorem contextKeys080_exact : contextKeys080 = recordedClassKeys 80 := by
  decide +kernel

theorem root080_exact : root080 = recordedClassRoot 80 := by
  decide +kernel

theorem class080_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 80) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 80) (digits code) = true := by
  rw [← contextKeys080_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts080_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs080) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs080_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root080_exact]
  exact base_job_numeric_membership baseBoxes080 c.1 c.2.2.2 hj
    retainedDiagram root080 tree080 originalCover080 c.2.1 code hp.1 hc hk'

#print axioms jobs080_valid
#print axioms contexts080_valid
#print axioms contextKeys080_exact
#print axioms root080_exact
#print axioms class080_context_membership
end Snake9.Batch92
