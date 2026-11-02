import Witness093Data
import Balanced093Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs093_valid : jobs093.all (baseJobValid baseBoxes093) = true := by
  decide +kernel

def contextValid093 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs093)

theorem contexts093_valid : contexts093.all contextValid093 = true := by
  decide +kernel

theorem contextKeys093_exact : contextKeys093 = recordedClassKeys 93 := by
  decide +kernel

theorem root093_exact : root093 = recordedClassRoot 93 := by
  decide +kernel

theorem class093_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 93) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 93) (digits code) = true := by
  rw [← contextKeys093_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts093_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs093) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs093_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root093_exact]
  exact base_job_numeric_membership baseBoxes093 c.1 c.2.2.2 hj
    retainedDiagram root093 tree093 originalCover093 c.2.1 code hp.1 hc hk'

#print axioms jobs093_valid
#print axioms contexts093_valid
#print axioms contextKeys093_exact
#print axioms root093_exact
#print axioms class093_context_membership
end Snake9.Batch92
