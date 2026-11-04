import CheckpointCheck160
import PrefixAssoc146
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace Snake9.Checkpoint160
theorem afterPrefix_true (τ : Nat → Bool)
    (h : Snake9.LocalWindow.cnfTrue τ Snake9.LocalWindow.ShareWindow144.cnf = true) :
    Snake9.Lrat144.TreeTrue τ afterPrefix :=
  Snake9.LratFast144.cpOk_true τ (Snake9.PrefixAssoc146.checked_prefix_true τ h)
    afterPrefix checkpoint_ok
#print axioms afterPrefix_true
end Snake9.Checkpoint160
