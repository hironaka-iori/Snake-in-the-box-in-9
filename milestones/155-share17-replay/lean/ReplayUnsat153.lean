import ReplayAssembly153
import ReplaySteps153_0000
import ReplaySteps153_0001
import ReplaySteps153_0002
import ReplaySteps153_0003
import ReplaySteps153_0004
import ReplaySteps153_0005
import ReplaySteps153_0006
import ReplaySteps153_0007
import ReplaySteps153_0008
import ReplaySteps153_0009
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull153
open Snake9.Lrat153Replay (TreeTrue unsat_of_raw)
theorem unsat : Snake9.LocalWindow.Unsat Snake9.LocalWindow.ShareWindow153.cnf := by
  apply unsat_of_raw
  intro τ h
  have h0 : TreeTrue τ start0 := Snake9.ReplayData153.start_true τ h
  have h32 : TreeTrue τ start32 := steps0 τ h0
  have h64 : TreeTrue τ start64 := steps1 τ h32
  have h96 : TreeTrue τ start96 := steps2 τ h64
  have h128 : TreeTrue τ start128 := steps3 τ h96
  have h160 : TreeTrue τ start160 := steps4 τ h128
  have h192 : TreeTrue τ start192 := steps5 τ h160
  have h224 : TreeTrue τ start224 := steps6 τ h192
  have h256 : TreeTrue τ start256 := steps7 τ h224
  have h288 : TreeTrue τ start288 := steps8 τ h256
  exact steps9 τ h288
#print axioms unsat
end Snake9.ReplayFull153
