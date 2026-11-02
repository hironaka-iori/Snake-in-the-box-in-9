import Witness091Data
import Balanced091Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs091_valid : jobs091.all (baseJobValid baseBoxes091) = true := by
  decide +kernel

def contextValid091 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs091)

theorem contexts091_valid : contexts091.all contextValid091 = true := by
  decide +kernel

theorem contextKeys091_exact : contextKeys091 = recordedClassKeys 91 := by
  decide +kernel

theorem root091_exact : root091 = recordedClassRoot 91 := by
  decide +kernel

theorem class091_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 91) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 91) (digits code) = true := by
  rw [← contextKeys091_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts091_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs091) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs091_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root091_exact]
  exact base_job_numeric_membership baseBoxes091 c.1 c.2.2.2 hj
    retainedDiagram root091 tree091 originalCover091 c.2.1 code hp.1 hc hk'

#print axioms jobs091_valid
#print axioms contexts091_valid
#print axioms contextKeys091_exact
#print axioms root091_exact
#print axioms class091_context_membership
end Snake9.Batch92
