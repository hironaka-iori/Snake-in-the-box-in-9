import Witness121Data
import Balanced121Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

theorem jobs121_valid : jobs121.all (baseJobValid baseBoxes121) = true := by
  decide +kernel

def contextValid121 (c : Nat × Nat × Nat × List Witness) : Bool :=
  decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs121)

theorem contexts121_valid : contexts121.all contextValid121 = true := by
  decide +kernel

theorem contextKeys121_exact : contextKeys121 = recordedClassKeys 121 := by
  decide +kernel

theorem root121_exact : root121 = recordedClassRoot 121 := by
  decide +kernel

theorem class121_context_membership (di q code : Nat)
    (hm : (di,q) ∈ recordedClassKeys 121) (hc : code < 46656)
    (hk : numericKeep q di code = true) :
    diagramEval retainedDiagram (recordedClassRoot 121) (digits code) = true := by
  rw [← contextKeys121_exact] at hm
  obtain ⟨c,hcxt,heq⟩ := List.mem_map.mp hm
  have hd : c.1 = di := congrArg Prod.fst heq
  have hq : c.2.1 = q := congrArg Prod.snd heq
  have ht := List.all_eq_true.mp contexts121_valid c hcxt
  change decide (c.2.1 < 75 ∧ (c.1,c.2.2.2) ∈ jobs121) = true at ht
  have hp := of_decide_eq_true ht
  have hj := List.all_eq_true.mp jobs121_valid (c.1,c.2.2.2) hp.2
  have hk' : numericKeep c.2.1 c.1 code = true := by simpa only [hd,hq] using hk
  rw [← root121_exact]
  exact base_job_numeric_membership baseBoxes121 c.1 c.2.2.2 hj
    retainedDiagram root121 tree121 originalCover121 c.2.1 code hp.1 hc hk'

#print axioms jobs121_valid
#print axioms contexts121_valid
#print axioms contextKeys121_exact
#print axioms root121_exact
#print axioms class121_context_membership
end Snake9.Batch92
