import Witness062Data
import Balanced062Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs062_valid : jobs062.all (baseJobValid baseBoxes062) = true := by
  decide +kernel

def contextValid062 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs062)

theorem contexts062_valid : contexts062.all contextValid062 = true := by
  decide +kernel

theorem contextKeys062_exact : contextKeys062 = recordedClassKeys 62 := by
  decide +kernel

theorem root062_exact : root062 = recordedClassRoot 62 := by
  decide +kernel

theorem class062_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 62) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 62) (digits code) = true := by
  rw [← contextKeys062_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts062_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs062) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs062_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root062_exact]
  exact base_job_numeric_membership baseBoxes062 c.1 c.2.2.2 hj
    retainedDiagram root062 tree062 originalCover062 c.2.1 code hp.1 hc hk'

#print axioms jobs062_valid
#print axioms contexts062_valid
#print axioms contextKeys062_exact
#print axioms root062_exact
#print axioms class062_context_membership
end Snake9.Batch92
