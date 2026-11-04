import ReplayCheck161_00448
import ReplayCheck161_00452
import ReplayCheck161_00456
import ReplayCheck161_00460
import ReplayCheck161_00464
import ReplayCheck161_00468
import ReplayCheck161_00472
import ReplayCheck161_00476
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (TreeTrue)
open Snake9.LratFast144
theorem steps14 (τ : Nat → Bool) (h448 : TreeTrue τ start448) : TreeTrue τ start480 := by
  have h449 : TreeTrue τ start449 := replay_true τ ok448 h448
  have h450 : TreeTrue τ start450 := replay_true τ ok449 h449
  have h451 : TreeTrue τ start451 := replay_true τ ok450 h450
  have h452 : TreeTrue τ start452 := replay_true τ ok451 h451
  have h453 : TreeTrue τ start453 := replay_true τ ok452 h452
  have h454 : TreeTrue τ start454 := replay_true τ ok453 h453
  have h455 : TreeTrue τ start455 := replay_true τ ok454 h454
  have h456 : TreeTrue τ start456 := replay_true τ ok455 h455
  have h457 : TreeTrue τ start457 := replay_true τ ok456 h456
  have h458 : TreeTrue τ start458 := replay_true τ ok457 h457
  have h459 : TreeTrue τ start459 := replay_true τ ok458 h458
  have h460 : TreeTrue τ start460 := replay_true τ ok459 h459
  have h461 : TreeTrue τ start461 := replay_true τ ok460 h460
  have h462 : TreeTrue τ start462 := replay_true τ ok461 h461
  have h463 : TreeTrue τ start463 := replay_true τ ok462 h462
  have h464 : TreeTrue τ start464 := replay_true τ ok463 h463
  have h465 : TreeTrue τ start465 := replay_true τ ok464 h464
  have h466 : TreeTrue τ start466 := replay_true τ ok465 h465
  have h467 : TreeTrue τ start467 := replay_true τ ok466 h466
  have h468 : TreeTrue τ start468 := replay_true τ ok467 h467
  have h469 : TreeTrue τ start469 := replay_true τ ok468 h468
  have h470 : TreeTrue τ start470 := replay_true τ ok469 h469
  have h471 : TreeTrue τ start471 := replay_true τ ok470 h470
  have h472 : TreeTrue τ start472 := replay_true τ ok471 h471
  have h473 : TreeTrue τ start473 := replay_true τ ok472 h472
  have h474 : TreeTrue τ start474 := replay_true τ ok473 h473
  have h475 : TreeTrue τ start475 := replay_true τ ok474 h474
  have h476 : TreeTrue τ start476 := replay_true τ ok475 h475
  have h477 : TreeTrue τ start477 := replay_true τ ok476 h476
  have h478 : TreeTrue τ start478 := replay_true τ ok477 h477
  have h479 : TreeTrue τ start479 := replay_true τ ok478 h478
  have h480 : TreeTrue τ start480 := cp_true τ ok479 h479
  exact h480
#print axioms steps14
end Snake9.ReplayFull161
