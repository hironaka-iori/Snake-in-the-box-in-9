import Witness010Data
import Balanced010Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs010_valid : jobs010.all (baseJobValid baseBoxes010) = true := by
  decide +kernel

def contextValid010 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs010)

theorem contexts010_valid : contexts010.all contextValid010 = true := by
  decide +kernel

theorem contextKeys010_exact : contextKeys010 = recordedClassKeys 10 := by
  decide +kernel

theorem root010_exact : root010 = recordedClassRoot 10 := by
  decide +kernel

theorem class010_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 10) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 10) (digits code) = true := by
  rw [← contextKeys010_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts010_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs010) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs010_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root010_exact]
  exact base_job_numeric_membership baseBoxes010 c.1 c.2.2.2 hj
    retainedDiagram root010 tree010 originalCover010 c.2.1 code hp.1 hc hk'

#print axioms jobs010_valid
#print axioms contexts010_valid
#print axioms contextKeys010_exact
#print axioms root010_exact
#print axioms class010_context_membership
end Snake9.Batch92
