import Witness026Data
import Balanced026Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs026_valid : jobs026.all (baseJobValid baseBoxes026) = true := by
  decide +kernel

def contextValid026 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs026)

theorem contexts026_valid : contexts026.all contextValid026 = true := by
  decide +kernel

theorem contextKeys026_exact : contextKeys026 = recordedClassKeys 26 := by
  decide +kernel

theorem root026_exact : root026 = recordedClassRoot 26 := by
  decide +kernel

theorem class026_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 26) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 26) (digits code) = true := by
  rw [← contextKeys026_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts026_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs026) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs026_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root026_exact]
  exact base_job_numeric_membership baseBoxes026 c.1 c.2.2.2 hj
    retainedDiagram root026 tree026 originalCover026 c.2.1 code hp.1 hc hk'

#print axioms jobs026_valid
#print axioms contexts026_valid
#print axioms contextKeys026_exact
#print axioms root026_exact
#print axioms class026_context_membership
end Snake9.Batch92
