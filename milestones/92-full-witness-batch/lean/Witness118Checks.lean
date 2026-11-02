import Witness118Data
import Balanced118Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs118_valid : jobs118.all (baseJobValid baseBoxes118) = true := by
  decide +kernel

def contextValid118 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs118)

theorem contexts118_valid : contexts118.all contextValid118 = true := by
  decide +kernel

theorem contextKeys118_exact : contextKeys118 = recordedClassKeys 118 := by
  decide +kernel

theorem root118_exact : root118 = recordedClassRoot 118 := by
  decide +kernel

theorem class118_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 118) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 118) (digits code) = true := by
  rw [← contextKeys118_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts118_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs118) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs118_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root118_exact]
  exact base_job_numeric_membership baseBoxes118 c.1 c.2.2.2 hj
    retainedDiagram root118 tree118 originalCover118 c.2.1 code hp.1 hc hk'

#print axioms jobs118_valid
#print axioms contexts118_valid
#print axioms contextKeys118_exact
#print axioms root118_exact
#print axioms class118_context_membership
end Snake9.Batch92
