import Witness016Data
import Balanced016Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs016_valid : jobs016.all (baseJobValid baseBoxes016) = true := by
  decide +kernel

def contextValid016 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs016)

theorem contexts016_valid : contexts016.all contextValid016 = true := by
  decide +kernel

theorem contextKeys016_exact : contextKeys016 = recordedClassKeys 16 := by
  decide +kernel

theorem root016_exact : root016 = recordedClassRoot 16 := by
  decide +kernel

theorem class016_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 16) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 16) (digits code) = true := by
  rw [← contextKeys016_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts016_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs016) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs016_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root016_exact]
  exact base_job_numeric_membership baseBoxes016 c.1 c.2.2.2 hj
    retainedDiagram root016 tree016 originalCover016 c.2.1 code hp.1 hc hk'

#print axioms jobs016_valid
#print axioms contexts016_valid
#print axioms contextKeys016_exact
#print axioms root016_exact
#print axioms class016_context_membership
end Snake9.Batch92
