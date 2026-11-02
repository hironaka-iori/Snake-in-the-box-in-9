import Witness074Data
import Balanced074Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs074_valid : jobs074.all (baseJobValid baseBoxes074) = true := by
  decide +kernel

def contextValid074 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs074)

theorem contexts074_valid : contexts074.all contextValid074 = true := by
  decide +kernel

theorem contextKeys074_exact : contextKeys074 = recordedClassKeys 74 := by
  decide +kernel

theorem root074_exact : root074 = recordedClassRoot 74 := by
  decide +kernel

theorem class074_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 74) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 74) (digits code) = true := by
  rw [← contextKeys074_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts074_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs074) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs074_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root074_exact]
  exact base_job_numeric_membership baseBoxes074 c.1 c.2.2.2 hj
    retainedDiagram root074 tree074 originalCover074 c.2.1 code hp.1 hc hk'

#print axioms jobs074_valid
#print axioms contexts074_valid
#print axioms contextKeys074_exact
#print axioms root074_exact
#print axioms class074_context_membership
end Snake9.Batch92
