import Witness019Data
import Balanced019Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs019_valid : jobs019.all (baseJobValid baseBoxes019) = true := by
  decide +kernel

def contextValid019 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs019)

theorem contexts019_valid : contexts019.all contextValid019 = true := by
  decide +kernel

theorem contextKeys019_exact : contextKeys019 = recordedClassKeys 19 := by
  decide +kernel

theorem root019_exact : root019 = recordedClassRoot 19 := by
  decide +kernel

theorem class019_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 19) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 19) (digits code) = true := by
  rw [← contextKeys019_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts019_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs019) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs019_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root019_exact]
  exact base_job_numeric_membership baseBoxes019 c.1 c.2.2.2 hj
    retainedDiagram root019 tree019 originalCover019 c.2.1 code hp.1 hc hk'

#print axioms jobs019_valid
#print axioms contexts019_valid
#print axioms contextKeys019_exact
#print axioms root019_exact
#print axioms class019_context_membership
end Snake9.Batch92
