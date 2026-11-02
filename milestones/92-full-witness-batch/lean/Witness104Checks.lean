import Witness104Data
import Balanced104Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs104_valid : jobs104.all (baseJobValid baseBoxes104) = true := by
  decide +kernel

def contextValid104 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs104)

theorem contexts104_valid : contexts104.all contextValid104 = true := by
  decide +kernel

theorem contextKeys104_exact : contextKeys104 = recordedClassKeys 104 := by
  decide +kernel

theorem root104_exact : root104 = recordedClassRoot 104 := by
  decide +kernel

theorem class104_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 104) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 104) (digits code) = true := by
  rw [← contextKeys104_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts104_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs104) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs104_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root104_exact]
  exact base_job_numeric_membership baseBoxes104 c.1 c.2.2.2 hj
    retainedDiagram root104 tree104 originalCover104 c.2.1 code hp.1 hc hk'

#print axioms jobs104_valid
#print axioms contexts104_valid
#print axioms contextKeys104_exact
#print axioms root104_exact
#print axioms class104_context_membership
end Snake9.Batch92
