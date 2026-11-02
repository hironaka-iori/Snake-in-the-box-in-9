import Witness070Data
import Balanced070Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs070_valid : jobs070.all (baseJobValid baseBoxes070) = true := by
  decide +kernel

def contextValid070 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs070)

theorem contexts070_valid : contexts070.all contextValid070 = true := by
  decide +kernel

theorem contextKeys070_exact : contextKeys070 = recordedClassKeys 70 := by
  decide +kernel

theorem root070_exact : root070 = recordedClassRoot 70 := by
  decide +kernel

theorem class070_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 70) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 70) (digits code) = true := by
  rw [← contextKeys070_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts070_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs070) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs070_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root070_exact]
  exact base_job_numeric_membership baseBoxes070 c.1 c.2.2.2 hj
    retainedDiagram root070 tree070 originalCover070 c.2.1 code hp.1 hc hk'

#print axioms jobs070_valid
#print axioms contexts070_valid
#print axioms contextKeys070_exact
#print axioms root070_exact
#print axioms class070_context_membership
end Snake9.Batch92
