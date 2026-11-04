import ReplayCheck153_00288
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull153
open Snake9.Lrat153Replay (TreeTrue)
open Snake9.LratFast153Replay
theorem steps9 (τ : Nat → Bool) (h288 : TreeTrue τ start288) : False := by
  have h289 : TreeTrue τ start289 := replay_true τ ok288 h288
  exact final_false τ ok289 h289
#print axioms steps9
end Snake9.ReplayFull153
