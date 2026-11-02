import Witness092Data
import Balanced092Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs092_valid : jobs092.all (baseJobValid baseBoxes092) = true := by
  decide +kernel

def contextValid092 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs092)

theorem contexts092_valid : contexts092.all contextValid092 = true := by
  decide +kernel

theorem contextKeys092_exact : contextKeys092 = recordedClassKeys 92 := by
  decide +kernel

theorem root092_exact : root092 = recordedClassRoot 92 := by
  decide +kernel

theorem class092_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 92) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 92) (digits code) = true := by
  rw [← contextKeys092_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts092_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs092) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs092_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root092_exact]
  exact base_job_numeric_membership baseBoxes092 c.1 c.2.2.2 hj
    retainedDiagram root092 tree092 originalCover092 c.2.1 code hp.1 hc hk'

#print axioms jobs092_valid
#print axioms contexts092_valid
#print axioms contextKeys092_exact
#print axioms root092_exact
#print axioms class092_context_membership
end Snake9.Batch92
