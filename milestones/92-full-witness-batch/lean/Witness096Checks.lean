import Witness096Data
import Balanced096Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs096_valid : jobs096.all (baseJobValid baseBoxes096) = true := by
  decide +kernel

def contextValid096 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs096)

theorem contexts096_valid : contexts096.all contextValid096 = true := by
  decide +kernel

theorem contextKeys096_exact : contextKeys096 = recordedClassKeys 96 := by
  decide +kernel

theorem root096_exact : root096 = recordedClassRoot 96 := by
  decide +kernel

theorem class096_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 96) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 96) (digits code) = true := by
  rw [← contextKeys096_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts096_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs096) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs096_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root096_exact]
  exact base_job_numeric_membership baseBoxes096 c.1 c.2.2.2 hj
    retainedDiagram root096 tree096 originalCover096 c.2.1 code hp.1 hc hk'

#print axioms jobs096_valid
#print axioms contexts096_valid
#print axioms contextKeys096_exact
#print axioms root096_exact
#print axioms class096_context_membership
end Snake9.Batch92
