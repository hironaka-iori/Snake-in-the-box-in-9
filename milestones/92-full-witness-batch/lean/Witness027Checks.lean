import Witness027Data
import Balanced027Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs027_valid : jobs027.all (baseJobValid baseBoxes027) = true := by
  decide +kernel

def contextValid027 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs027)

theorem contexts027_valid : contexts027.all contextValid027 = true := by
  decide +kernel

theorem contextKeys027_exact : contextKeys027 = recordedClassKeys 27 := by
  decide +kernel

theorem root027_exact : root027 = recordedClassRoot 27 := by
  decide +kernel

theorem class027_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 27) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 27) (digits code) = true := by
  rw [← contextKeys027_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts027_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs027) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs027_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root027_exact]
  exact base_job_numeric_membership baseBoxes027 c.1 c.2.2.2 hj
    retainedDiagram root027 tree027 originalCover027 c.2.1 code hp.1 hc hk'

#print axioms jobs027_valid
#print axioms contexts027_valid
#print axioms contextKeys027_exact
#print axioms root027_exact
#print axioms class027_context_membership
end Snake9.Batch92
