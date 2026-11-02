import Witness041Data
import Balanced041Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs041_valid : jobs041.all (baseJobValid baseBoxes041) = true := by
  decide +kernel

def contextValid041 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs041)

theorem contexts041_valid : contexts041.all contextValid041 = true := by
  decide +kernel

theorem contextKeys041_exact : contextKeys041 = recordedClassKeys 41 := by
  decide +kernel

theorem root041_exact : root041 = recordedClassRoot 41 := by
  decide +kernel

theorem class041_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 41) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 41) (digits code) = true := by
  rw [← contextKeys041_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts041_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs041) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs041_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root041_exact]
  exact base_job_numeric_membership baseBoxes041 c.1 c.2.2.2 hj
    retainedDiagram root041 tree041 originalCover041 c.2.1 code hp.1 hc hk'

#print axioms jobs041_valid
#print axioms contexts041_valid
#print axioms contextKeys041_exact
#print axioms root041_exact
#print axioms class041_context_membership
end Snake9.Batch92
