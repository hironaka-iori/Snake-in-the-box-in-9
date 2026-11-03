import ReplayAssembly150
import ReplayPilotCheck150
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayPilot150
theorem prefix_true (τ : Nat → Bool)
    (h : Snake9.LocalWindow.cnfTrue τ Snake9.LocalWindow.ShareWindow150.cnf = true) :
    Snake9.Lrat150Replay.TreeTrue τ afterPrefix :=
  Snake9.LratFast150Replay.cp_true τ prefix_check (Snake9.ReplayData150.start_true τ h)
#print axioms prefix_true
end Snake9.ReplayPilot150
