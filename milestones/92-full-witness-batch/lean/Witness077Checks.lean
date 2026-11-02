import Witness077Data
import Balanced077Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs077_valid : jobs077.all (baseJobValid baseBoxes077) = true := by
  decide +kernel

def contextValid077 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs077)

theorem contexts077_valid : contexts077.all contextValid077 = true := by
  decide +kernel

theorem contextKeys077_exact : contextKeys077 = recordedClassKeys 77 := by
  decide +kernel

theorem root077_exact : root077 = recordedClassRoot 77 := by
  decide +kernel

theorem class077_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 77) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 77) (digits code) = true := by
  rw [← contextKeys077_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts077_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs077) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs077_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root077_exact]
  exact base_job_numeric_membership baseBoxes077 c.1 c.2.2.2 hj
    retainedDiagram root077 tree077 originalCover077 c.2.1 code hp.1 hc hk'

#print axioms jobs077_valid
#print axioms contexts077_valid
#print axioms contextKeys077_exact
#print axioms root077_exact
#print axioms class077_context_membership
end Snake9.Batch92
