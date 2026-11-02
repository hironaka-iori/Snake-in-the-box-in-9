import Witness087Data
import Balanced087Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs087_valid : jobs087.all (baseJobValid baseBoxes087) = true := by
  decide +kernel

def contextValid087 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs087)

theorem contexts087_valid : contexts087.all contextValid087 = true := by
  decide +kernel

theorem contextKeys087_exact : contextKeys087 = recordedClassKeys 87 := by
  decide +kernel

theorem root087_exact : root087 = recordedClassRoot 87 := by
  decide +kernel

theorem class087_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 87) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 87) (digits code) = true := by
  rw [← contextKeys087_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts087_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs087) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs087_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root087_exact]
  exact base_job_numeric_membership baseBoxes087 c.1 c.2.2.2 hj
    retainedDiagram root087 tree087 originalCover087 c.2.1 code hp.1 hc hk'

#print axioms jobs087_valid
#print axioms contexts087_valid
#print axioms contextKeys087_exact
#print axioms root087_exact
#print axioms class087_context_membership
end Snake9.Batch92
