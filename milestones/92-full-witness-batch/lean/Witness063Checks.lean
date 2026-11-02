import Witness063Data
import Balanced063Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs063_valid : jobs063.all (baseJobValid baseBoxes063) = true := by
  decide +kernel

def contextValid063 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs063)

theorem contexts063_valid : contexts063.all contextValid063 = true := by
  decide +kernel

theorem contextKeys063_exact : contextKeys063 = recordedClassKeys 63 := by
  decide +kernel

theorem root063_exact : root063 = recordedClassRoot 63 := by
  decide +kernel

theorem class063_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 63) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 63) (digits code) = true := by
  rw [← contextKeys063_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts063_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs063) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs063_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root063_exact]
  exact base_job_numeric_membership baseBoxes063 c.1 c.2.2.2 hj
    retainedDiagram root063 tree063 originalCover063 c.2.1 code hp.1 hc hk'

#print axioms jobs063_valid
#print axioms contexts063_valid
#print axioms contextKeys063_exact
#print axioms root063_exact
#print axioms class063_context_membership
end Snake9.Batch92
