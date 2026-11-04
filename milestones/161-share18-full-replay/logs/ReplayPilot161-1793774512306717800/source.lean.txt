import CheckpointConsequence160
import ReplaySteps161_0000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (TreeTrue)
theorem pilot_true (τ : Nat → Bool)
    (h : Snake9.LocalWindow.cnfTrue τ Snake9.LocalWindow.ShareWindow144.cnf = true) : TreeTrue τ start32 := by
  have h0 : TreeTrue τ start0 := Snake9.Checkpoint160.afterPrefix_true τ h
  exact steps0 τ h0
#print axioms pilot_true
end Snake9.ReplayFull161
