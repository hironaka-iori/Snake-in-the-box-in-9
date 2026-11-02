import Witness020Data
import Balanced020Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs020_valid : jobs020.all (baseJobValid baseBoxes020) = true := by
  decide +kernel

def contextValid020 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs020)

theorem contexts020_valid : contexts020.all contextValid020 = true := by
  decide +kernel

theorem contextKeys020_exact : contextKeys020 = recordedClassKeys 20 := by
  decide +kernel

theorem root020_exact : root020 = recordedClassRoot 20 := by
  decide +kernel

theorem class020_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 20) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 20) (digits code) = true := by
  rw [← contextKeys020_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts020_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs020) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs020_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root020_exact]
  exact base_job_numeric_membership baseBoxes020 c.1 c.2.2.2 hj
    retainedDiagram root020 tree020 originalCover020 c.2.1 code hp.1 hc hk'

#print axioms jobs020_valid
#print axioms contexts020_valid
#print axioms contextKeys020_exact
#print axioms root020_exact
#print axioms class020_context_membership
end Snake9.Batch92
