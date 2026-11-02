import Witness044Data
import Balanced044Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs044_valid : jobs044.all (baseJobValid baseBoxes044) = true := by
  decide +kernel

def contextValid044 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs044)

theorem contexts044_valid : contexts044.all contextValid044 = true := by
  decide +kernel

theorem contextKeys044_exact : contextKeys044 = recordedClassKeys 44 := by
  decide +kernel

theorem root044_exact : root044 = recordedClassRoot 44 := by
  decide +kernel

theorem class044_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 44) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 44) (digits code) = true := by
  rw [← contextKeys044_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts044_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs044) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs044_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root044_exact]
  exact base_job_numeric_membership baseBoxes044 c.1 c.2.2.2 hj
    retainedDiagram root044 tree044 originalCover044 c.2.1 code hp.1 hc hk'

#print axioms jobs044_valid
#print axioms contexts044_valid
#print axioms contextKeys044_exact
#print axioms root044_exact
#print axioms class044_context_membership
end Snake9.Batch92
