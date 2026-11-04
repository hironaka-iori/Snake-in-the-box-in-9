import CheckpointConsequence160
import ReplaySteps161_0000
import ReplaySteps161_0001
import ReplaySteps161_0002
import ReplaySteps161_0003
import ReplaySteps161_0004
import ReplaySteps161_0005
import ReplaySteps161_0006
import ReplaySteps161_0007
import ReplaySteps161_0008
import ReplaySteps161_0009
import ReplaySteps161_0010
import ReplaySteps161_0011
import ReplaySteps161_0012
import ReplaySteps161_0013
set_option maxHeartbeats 0
set_option Elab.async false
namespace Snake9.ReplayPrefix163
open Snake9.Lrat144 (TreeTrue)
open Snake9.ReplayFull161
theorem checked_prefix_true (τ : Nat → Bool)
    (h : Snake9.LocalWindow.cnfTrue τ Snake9.LocalWindow.ShareWindow144.cnf = true) :
    TreeTrue τ start448 := by
  have h0 : TreeTrue τ start0 := Snake9.Checkpoint160.afterPrefix_true τ h
  have h32 : TreeTrue τ start32 := steps0 τ h0
  have h64 : TreeTrue τ start64 := steps1 τ h32
  have h96 : TreeTrue τ start96 := steps2 τ h64
  have h128 : TreeTrue τ start128 := steps3 τ h96
  have h160 : TreeTrue τ start160 := steps4 τ h128
  have h192 : TreeTrue τ start192 := steps5 τ h160
  have h224 : TreeTrue τ start224 := steps6 τ h192
  have h256 : TreeTrue τ start256 := steps7 τ h224
  have h288 : TreeTrue τ start288 := steps8 τ h256
  have h320 : TreeTrue τ start320 := steps9 τ h288
  have h352 : TreeTrue τ start352 := steps10 τ h320
  have h384 : TreeTrue τ start384 := steps11 τ h352
  have h416 : TreeTrue τ start416 := steps12 τ h384
  have h448 : TreeTrue τ start448 := steps13 τ h416
  exact h448
#print axioms checked_prefix_true
end Snake9.ReplayPrefix163
