import Witness030Data
import Balanced030Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs030_valid : jobs030.all (baseJobValid baseBoxes030) = true := by
  decide +kernel

def contextValid030 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs030)

theorem contexts030_valid : contexts030.all contextValid030 = true := by
  decide +kernel

theorem contextKeys030_exact : contextKeys030 = recordedClassKeys 30 := by
  decide +kernel

theorem root030_exact : root030 = recordedClassRoot 30 := by
  decide +kernel

theorem class030_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 30) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 30) (digits code) = true := by
  rw [← contextKeys030_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts030_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs030) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs030_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root030_exact]
  exact base_job_numeric_membership baseBoxes030 c.1 c.2.2.2 hj
    retainedDiagram root030 tree030 originalCover030 c.2.1 code hp.1 hc hk'

#print axioms jobs030_valid
#print axioms contexts030_valid
#print axioms contextKeys030_exact
#print axioms root030_exact
#print axioms class030_context_membership
end Snake9.Batch92
