import Witness038Data
import Balanced038Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs038_valid : jobs038.all (baseJobValid baseBoxes038) = true := by
  decide +kernel

def contextValid038 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs038)

theorem contexts038_valid : contexts038.all contextValid038 = true := by
  decide +kernel

theorem contextKeys038_exact : contextKeys038 = recordedClassKeys 38 := by
  decide +kernel

theorem root038_exact : root038 = recordedClassRoot 38 := by
  decide +kernel

theorem class038_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 38) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 38) (digits code) = true := by
  rw [← contextKeys038_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts038_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs038) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs038_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root038_exact]
  exact base_job_numeric_membership baseBoxes038 c.1 c.2.2.2 hj
    retainedDiagram root038 tree038 originalCover038 c.2.1 code hp.1 hc hk'

#print axioms jobs038_valid
#print axioms contexts038_valid
#print axioms contextKeys038_exact
#print axioms root038_exact
#print axioms class038_context_membership
end Snake9.Batch92
