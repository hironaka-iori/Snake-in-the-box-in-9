import ReplayCheck161_02400
import ReplayCheck161_02404
import ReplayCheck161_02408
import ReplayCheck161_02412
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (TreeTrue)
open Snake9.LratFast144
theorem steps75 (τ : Nat → Bool) (h2400 : TreeTrue τ start2400) : False := by
  have h2401 : TreeTrue τ start2401 := replay_true τ ok2400 h2400
  have h2402 : TreeTrue τ start2402 := replay_true τ ok2401 h2401
  have h2403 : TreeTrue τ start2403 := replay_true τ ok2402 h2402
  have h2404 : TreeTrue τ start2404 := replay_true τ ok2403 h2403
  have h2405 : TreeTrue τ start2405 := replay_true τ ok2404 h2404
  have h2406 : TreeTrue τ start2406 := replay_true τ ok2405 h2405
  have h2407 : TreeTrue τ start2407 := replay_true τ ok2406 h2406
  have h2408 : TreeTrue τ start2408 := replay_true τ ok2407 h2407
  have h2409 : TreeTrue τ start2409 := replay_true τ ok2408 h2408
  have h2410 : TreeTrue τ start2410 := replay_true τ ok2409 h2409
  have h2411 : TreeTrue τ start2411 := replay_true τ ok2410 h2410
  have h2412 : TreeTrue τ start2412 := replay_true τ ok2411 h2411
  have h2413 : TreeTrue τ start2413 := replay_true τ ok2412 h2412
  have h2414 : TreeTrue τ start2414 := replay_true τ ok2413 h2413
  exact final_false τ ok2414 h2414
#print axioms steps75
end Snake9.ReplayFull161
