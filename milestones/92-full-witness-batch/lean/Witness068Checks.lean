import Witness068Data
import Balanced068Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs068_valid : jobs068.all (baseJobValid baseBoxes068) = true := by
  decide +kernel

def contextValid068 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs068)

theorem contexts068_valid : contexts068.all contextValid068 = true := by
  decide +kernel

theorem contextKeys068_exact : contextKeys068 = recordedClassKeys 68 := by
  decide +kernel

theorem root068_exact : root068 = recordedClassRoot 68 := by
  decide +kernel

theorem class068_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 68) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 68) (digits code) = true := by
  rw [← contextKeys068_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts068_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs068) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs068_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root068_exact]
  exact base_job_numeric_membership baseBoxes068 c.1 c.2.2.2 hj
    retainedDiagram root068 tree068 originalCover068 c.2.1 code hp.1 hc hk'

#print axioms jobs068_valid
#print axioms contexts068_valid
#print axioms contextKeys068_exact
#print axioms root068_exact
#print axioms class068_context_membership
end Snake9.Batch92
