import Witness108Data
import Balanced108Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs108_valid : jobs108.all (baseJobValid baseBoxes108) = true := by
  decide +kernel

def contextValid108 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs108)

theorem contexts108_valid : contexts108.all contextValid108 = true := by
  decide +kernel

theorem contextKeys108_exact : contextKeys108 = recordedClassKeys 108 := by
  decide +kernel

theorem root108_exact : root108 = recordedClassRoot 108 := by
  decide +kernel

theorem class108_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 108) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 108) (digits code) = true := by
  rw [← contextKeys108_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts108_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs108) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs108_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root108_exact]
  exact base_job_numeric_membership baseBoxes108 c.1 c.2.2.2 hj
    retainedDiagram root108 tree108 originalCover108 c.2.1 code hp.1 hc hk'

#print axioms jobs108_valid
#print axioms contexts108_valid
#print axioms contextKeys108_exact
#print axioms root108_exact
#print axioms class108_context_membership
end Snake9.Batch92
