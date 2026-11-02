import Witness111Data
import Balanced111Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs111_valid : jobs111.all (baseJobValid baseBoxes111) = true := by
  decide +kernel

def contextValid111 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs111)

theorem contexts111_valid : contexts111.all contextValid111 = true := by
  decide +kernel

theorem contextKeys111_exact : contextKeys111 = recordedClassKeys 111 := by
  decide +kernel

theorem root111_exact : root111 = recordedClassRoot 111 := by
  decide +kernel

theorem class111_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 111) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 111) (digits code) = true := by
  rw [← contextKeys111_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts111_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs111) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs111_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root111_exact]
  exact base_job_numeric_membership baseBoxes111 c.1 c.2.2.2 hj
    retainedDiagram root111 tree111 originalCover111 c.2.1 code hp.1 hc hk'

#print axioms jobs111_valid
#print axioms contexts111_valid
#print axioms contextKeys111_exact
#print axioms root111_exact
#print axioms class111_context_membership
end Snake9.Batch92
