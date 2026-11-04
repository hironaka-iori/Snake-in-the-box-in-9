import ReplayAssembly153
import ReplayPilotCheck153
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayPilot153
theorem prefix_true (τ : Nat → Bool)
    (h : Snake9.LocalWindow.cnfTrue τ Snake9.LocalWindow.ShareWindow153.cnf = true) :
    Snake9.Lrat153Replay.TreeTrue τ afterPrefix :=
  Snake9.LratFast153Replay.cp_true τ prefix_check (Snake9.ReplayData153.start_true τ h)
#print axioms prefix_true
end Snake9.ReplayPilot153
