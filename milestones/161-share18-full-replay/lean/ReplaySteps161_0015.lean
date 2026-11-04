import ReplayCheck161_00480
import ReplayCheck161_00484
import ReplayCheck161_00488
import ReplayCheck161_00492
import ReplayCheck161_00496
import ReplayCheck161_00500
import ReplayCheck161_00504
import ReplayCheck161_00508
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (TreeTrue)
open Snake9.LratFast144
theorem steps15 (τ : Nat → Bool) (h480 : TreeTrue τ start480) : TreeTrue τ start512 := by
  have h481 : TreeTrue τ start481 := replay_true τ ok480 h480
  have h482 : TreeTrue τ start482 := replay_true τ ok481 h481
  have h483 : TreeTrue τ start483 := replay_true τ ok482 h482
  have h484 : TreeTrue τ start484 := replay_true τ ok483 h483
  have h485 : TreeTrue τ start485 := replay_true τ ok484 h484
  have h486 : TreeTrue τ start486 := replay_true τ ok485 h485
  have h487 : TreeTrue τ start487 := replay_true τ ok486 h486
  have h488 : TreeTrue τ start488 := replay_true τ ok487 h487
  have h489 : TreeTrue τ start489 := replay_true τ ok488 h488
  have h490 : TreeTrue τ start490 := replay_true τ ok489 h489
  have h491 : TreeTrue τ start491 := replay_true τ ok490 h490
  have h492 : TreeTrue τ start492 := replay_true τ ok491 h491
  have h493 : TreeTrue τ start493 := replay_true τ ok492 h492
  have h494 : TreeTrue τ start494 := replay_true τ ok493 h493
  have h495 : TreeTrue τ start495 := replay_true τ ok494 h494
  have h496 : TreeTrue τ start496 := replay_true τ ok495 h495
  have h497 : TreeTrue τ start497 := replay_true τ ok496 h496
  have h498 : TreeTrue τ start498 := replay_true τ ok497 h497
  have h499 : TreeTrue τ start499 := replay_true τ ok498 h498
  have h500 : TreeTrue τ start500 := replay_true τ ok499 h499
  have h501 : TreeTrue τ start501 := replay_true τ ok500 h500
  have h502 : TreeTrue τ start502 := replay_true τ ok501 h501
  have h503 : TreeTrue τ start503 := replay_true τ ok502 h502
  have h504 : TreeTrue τ start504 := replay_true τ ok503 h503
  have h505 : TreeTrue τ start505 := replay_true τ ok504 h504
  have h506 : TreeTrue τ start506 := replay_true τ ok505 h505
  have h507 : TreeTrue τ start507 := replay_true τ ok506 h506
  have h508 : TreeTrue τ start508 := replay_true τ ok507 h507
  have h509 : TreeTrue τ start509 := replay_true τ ok508 h508
  have h510 : TreeTrue τ start510 := replay_true τ ok509 h509
  have h511 : TreeTrue τ start511 := replay_true τ ok510 h510
  have h512 : TreeTrue τ start512 := cp_true τ ok511 h511
  exact h512
#print axioms steps15
end Snake9.ReplayFull161
