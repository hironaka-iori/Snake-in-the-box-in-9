import Witness001Data
import Balanced001Checks
import Class001WitnessChecks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs001_valid : jobs001.all (baseJobValid baseBoxes001) = true := by
  change Snake9.Witness90.class001Jobs.all Snake9.Witness90.class001JobValid = true
  exact Snake9.Witness90.class001_jobs_valid

def contextValid001 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs001)

theorem contexts001_valid : contexts001.all contextValid001 = true := by
  decide +kernel

theorem contextKeys001_exact : contextKeys001 = recordedClassKeys 1 := by
  decide +kernel

theorem root001_exact : root001 = recordedClassRoot 1 := by
  decide +kernel

theorem class001_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 1) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 1) (digits code) = true := by
  rw [← contextKeys001_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts001_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs001) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs001_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root001_exact]
  exact base_job_numeric_membership baseBoxes001 c.1 c.2.2.2 hj
    retainedDiagram root001 tree001 originalCover001 c.2.1 code hp.1 hc hk'

#print axioms jobs001_valid
#print axioms contexts001_valid
#print axioms contextKeys001_exact
#print axioms root001_exact
#print axioms class001_context_membership
end Snake9.Batch92
