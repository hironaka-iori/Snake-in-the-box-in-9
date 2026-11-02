import Witness008Data
import Balanced008Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs008_valid : jobs008.all (baseJobValid baseBoxes008) = true := by
  decide +kernel

def contextValid008 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs008)

theorem contexts008_valid : contexts008.all contextValid008 = true := by
  decide +kernel

theorem contextKeys008_exact : contextKeys008 = recordedClassKeys 8 := by
  decide +kernel

theorem root008_exact : root008 = recordedClassRoot 8 := by
  decide +kernel

theorem class008_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 8) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 8) (digits code) = true := by
  rw [← contextKeys008_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts008_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs008) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs008_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root008_exact]
  exact base_job_numeric_membership baseBoxes008 c.1 c.2.2.2 hj
    retainedDiagram root008 tree008 originalCover008 c.2.1 code hp.1 hc hk'

#print axioms jobs008_valid
#print axioms contexts008_valid
#print axioms contextKeys008_exact
#print axioms root008_exact
#print axioms class008_context_membership
end Snake9.Batch92
