import Witness023Data
import Balanced023Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs023_valid : jobs023.all (baseJobValid baseBoxes023) = true := by
  decide +kernel

def contextValid023 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs023)

theorem contexts023_valid : contexts023.all contextValid023 = true := by
  decide +kernel

theorem contextKeys023_exact : contextKeys023 = recordedClassKeys 23 := by
  decide +kernel

theorem root023_exact : root023 = recordedClassRoot 23 := by
  decide +kernel

theorem class023_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 23) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 23) (digits code) = true := by
  rw [← contextKeys023_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts023_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs023) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs023_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root023_exact]
  exact base_job_numeric_membership baseBoxes023 c.1 c.2.2.2 hj
    retainedDiagram root023 tree023 originalCover023 c.2.1 code hp.1 hc hk'

#print axioms jobs023_valid
#print axioms contexts023_valid
#print axioms contextKeys023_exact
#print axioms root023_exact
#print axioms class023_context_membership
end Snake9.Batch92
