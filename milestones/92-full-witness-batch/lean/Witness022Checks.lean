import Witness022Data
import Balanced022Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs022_valid : jobs022.all (baseJobValid baseBoxes022) = true := by
  decide +kernel

def contextValid022 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs022)

theorem contexts022_valid : contexts022.all contextValid022 = true := by
  decide +kernel

theorem contextKeys022_exact : contextKeys022 = recordedClassKeys 22 := by
  decide +kernel

theorem root022_exact : root022 = recordedClassRoot 22 := by
  decide +kernel

theorem class022_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 22) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 22) (digits code) = true := by
  rw [← contextKeys022_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts022_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs022) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs022_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root022_exact]
  exact base_job_numeric_membership baseBoxes022 c.1 c.2.2.2 hj
    retainedDiagram root022 tree022 originalCover022 c.2.1 code hp.1 hc hk'

#print axioms jobs022_valid
#print axioms contexts022_valid
#print axioms contextKeys022_exact
#print axioms root022_exact
#print axioms class022_context_membership
end Snake9.Batch92
