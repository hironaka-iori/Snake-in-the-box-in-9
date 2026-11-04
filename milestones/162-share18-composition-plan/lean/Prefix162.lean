import CheckpointConsequence160
import ReplaySteps161_0000
import ReplaySteps161_0001
import ReplaySteps161_0002
import ReplaySteps161_0003
set_option maxHeartbeats 0
set_option Elab.async false
namespace Snake9.ReplayPrefix162
open Snake9.Lrat144 (TreeTrue)
open Snake9.ReplayFull161
theorem checked_prefix_true (τ : Nat → Bool)
    (h : Snake9.LocalWindow.cnfTrue τ Snake9.LocalWindow.ShareWindow144.cnf = true) :
    TreeTrue τ start128 := by
  have h0 : TreeTrue τ start0 := Snake9.Checkpoint160.afterPrefix_true τ h
  have h32 : TreeTrue τ start32 := steps0 τ h0
  have h64 : TreeTrue τ start64 := steps1 τ h32
  have h96 : TreeTrue τ start96 := steps2 τ h64
  have h128 : TreeTrue τ start128 := steps3 τ h96
  exact h128
#print axioms checked_prefix_true
end Snake9.ReplayPrefix162
