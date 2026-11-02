import Witness018Data
import Balanced018Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs018_valid : jobs018.all (baseJobValid baseBoxes018) = true := by
  decide +kernel

def contextValid018 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs018)

theorem contexts018_valid : contexts018.all contextValid018 = true := by
  decide +kernel

theorem contextKeys018_exact : contextKeys018 = recordedClassKeys 18 := by
  decide +kernel

theorem root018_exact : root018 = recordedClassRoot 18 := by
  decide +kernel

theorem class018_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 18) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 18) (digits code) = true := by
  rw [← contextKeys018_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts018_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs018) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs018_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root018_exact]
  exact base_job_numeric_membership baseBoxes018 c.1 c.2.2.2 hj
    retainedDiagram root018 tree018 originalCover018 c.2.1 code hp.1 hc hk'

#print axioms jobs018_valid
#print axioms contexts018_valid
#print axioms contextKeys018_exact
#print axioms root018_exact
#print axioms class018_context_membership
end Snake9.Batch92
