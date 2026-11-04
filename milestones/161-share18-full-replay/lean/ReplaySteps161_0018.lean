import ReplayCheck161_00576
import ReplayCheck161_00580
import ReplayCheck161_00584
import ReplayCheck161_00588
import ReplayCheck161_00592
import ReplayCheck161_00596
import ReplayCheck161_00600
import ReplayCheck161_00604
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (TreeTrue)
open Snake9.LratFast144
theorem steps18 (τ : Nat → Bool) (h576 : TreeTrue τ start576) : TreeTrue τ start608 := by
  have h577 : TreeTrue τ start577 := replay_true τ ok576 h576
  have h578 : TreeTrue τ start578 := replay_true τ ok577 h577
  have h579 : TreeTrue τ start579 := replay_true τ ok578 h578
  have h580 : TreeTrue τ start580 := replay_true τ ok579 h579
  have h581 : TreeTrue τ start581 := replay_true τ ok580 h580
  have h582 : TreeTrue τ start582 := replay_true τ ok581 h581
  have h583 : TreeTrue τ start583 := replay_true τ ok582 h582
  have h584 : TreeTrue τ start584 := replay_true τ ok583 h583
  have h585 : TreeTrue τ start585 := replay_true τ ok584 h584
  have h586 : TreeTrue τ start586 := replay_true τ ok585 h585
  have h587 : TreeTrue τ start587 := replay_true τ ok586 h586
  have h588 : TreeTrue τ start588 := replay_true τ ok587 h587
  have h589 : TreeTrue τ start589 := replay_true τ ok588 h588
  have h590 : TreeTrue τ start590 := replay_true τ ok589 h589
  have h591 : TreeTrue τ start591 := replay_true τ ok590 h590
  have h592 : TreeTrue τ start592 := replay_true τ ok591 h591
  have h593 : TreeTrue τ start593 := replay_true τ ok592 h592
  have h594 : TreeTrue τ start594 := replay_true τ ok593 h593
  have h595 : TreeTrue τ start595 := replay_true τ ok594 h594
  have h596 : TreeTrue τ start596 := replay_true τ ok595 h595
  have h597 : TreeTrue τ start597 := replay_true τ ok596 h596
  have h598 : TreeTrue τ start598 := replay_true τ ok597 h597
  have h599 : TreeTrue τ start599 := replay_true τ ok598 h598
  have h600 : TreeTrue τ start600 := replay_true τ ok599 h599
  have h601 : TreeTrue τ start601 := replay_true τ ok600 h600
  have h602 : TreeTrue τ start602 := replay_true τ ok601 h601
  have h603 : TreeTrue τ start603 := replay_true τ ok602 h602
  have h604 : TreeTrue τ start604 := replay_true τ ok603 h603
  have h605 : TreeTrue τ start605 := replay_true τ ok604 h604
  have h606 : TreeTrue τ start606 := replay_true τ ok605 h605
  have h607 : TreeTrue τ start607 := replay_true τ ok606 h606
  have h608 : TreeTrue τ start608 := cp_true τ ok607 h607
  exact h608
#print axioms steps18
end Snake9.ReplayFull161
