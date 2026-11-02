import Witness021Data
import Balanced021Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs021_valid : jobs021.all (baseJobValid baseBoxes021) = true := by
  decide +kernel

def contextValid021 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs021)

theorem contexts021_valid : contexts021.all contextValid021 = true := by
  decide +kernel

theorem contextKeys021_exact : contextKeys021 = recordedClassKeys 21 := by
  decide +kernel

theorem root021_exact : root021 = recordedClassRoot 21 := by
  decide +kernel

theorem class021_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 21) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 21) (digits code) = true := by
  rw [← contextKeys021_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts021_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs021) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs021_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root021_exact]
  exact base_job_numeric_membership baseBoxes021 c.1 c.2.2.2 hj
    retainedDiagram root021 tree021 originalCover021 c.2.1 code hp.1 hc hk'

#print axioms jobs021_valid
#print axioms contexts021_valid
#print axioms contextKeys021_exact
#print axioms root021_exact
#print axioms class021_context_membership
end Snake9.Batch92
