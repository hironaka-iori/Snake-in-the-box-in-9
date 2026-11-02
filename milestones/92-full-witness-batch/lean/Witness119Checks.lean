import Witness119Data
import Balanced119Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs119_valid : jobs119.all (baseJobValid baseBoxes119) = true := by
  decide +kernel

def contextValid119 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs119)

theorem contexts119_valid : contexts119.all contextValid119 = true := by
  decide +kernel

theorem contextKeys119_exact : contextKeys119 = recordedClassKeys 119 := by
  decide +kernel

theorem root119_exact : root119 = recordedClassRoot 119 := by
  decide +kernel

theorem class119_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 119) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 119) (digits code) = true := by
  rw [← contextKeys119_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts119_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs119) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs119_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root119_exact]
  exact base_job_numeric_membership baseBoxes119 c.1 c.2.2.2 hj
    retainedDiagram root119 tree119 originalCover119 c.2.1 code hp.1 hc hk'

#print axioms jobs119_valid
#print axioms contexts119_valid
#print axioms contextKeys119_exact
#print axioms root119_exact
#print axioms class119_context_membership
end Snake9.Batch92
