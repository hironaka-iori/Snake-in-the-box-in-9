import ReplayCheck161_00608
import ReplayCheck161_00612
import ReplayCheck161_00616
import ReplayCheck161_00620
import ReplayCheck161_00624
import ReplayCheck161_00628
import ReplayCheck161_00632
import ReplayCheck161_00636
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (TreeTrue)
open Snake9.LratFast144
theorem steps19 (τ : Nat → Bool) (h608 : TreeTrue τ start608) : TreeTrue τ start640 := by
  have h609 : TreeTrue τ start609 := replay_true τ ok608 h608
  have h610 : TreeTrue τ start610 := replay_true τ ok609 h609
  have h611 : TreeTrue τ start611 := replay_true τ ok610 h610
  have h612 : TreeTrue τ start612 := replay_true τ ok611 h611
  have h613 : TreeTrue τ start613 := replay_true τ ok612 h612
  have h614 : TreeTrue τ start614 := replay_true τ ok613 h613
  have h615 : TreeTrue τ start615 := replay_true τ ok614 h614
  have h616 : TreeTrue τ start616 := replay_true τ ok615 h615
  have h617 : TreeTrue τ start617 := replay_true τ ok616 h616
  have h618 : TreeTrue τ start618 := replay_true τ ok617 h617
  have h619 : TreeTrue τ start619 := replay_true τ ok618 h618
  have h620 : TreeTrue τ start620 := replay_true τ ok619 h619
  have h621 : TreeTrue τ start621 := replay_true τ ok620 h620
  have h622 : TreeTrue τ start622 := replay_true τ ok621 h621
  have h623 : TreeTrue τ start623 := replay_true τ ok622 h622
  have h624 : TreeTrue τ start624 := replay_true τ ok623 h623
  have h625 : TreeTrue τ start625 := replay_true τ ok624 h624
  have h626 : TreeTrue τ start626 := replay_true τ ok625 h625
  have h627 : TreeTrue τ start627 := replay_true τ ok626 h626
  have h628 : TreeTrue τ start628 := replay_true τ ok627 h627
  have h629 : TreeTrue τ start629 := replay_true τ ok628 h628
  have h630 : TreeTrue τ start630 := replay_true τ ok629 h629
  have h631 : TreeTrue τ start631 := replay_true τ ok630 h630
  have h632 : TreeTrue τ start632 := replay_true τ ok631 h631
  have h633 : TreeTrue τ start633 := replay_true τ ok632 h632
  have h634 : TreeTrue τ start634 := replay_true τ ok633 h633
  have h635 : TreeTrue τ start635 := replay_true τ ok634 h634
  have h636 : TreeTrue τ start636 := replay_true τ ok635 h635
  have h637 : TreeTrue τ start637 := replay_true τ ok636 h636
  have h638 : TreeTrue τ start638 := replay_true τ ok637 h637
  have h639 : TreeTrue τ start639 := replay_true τ ok638 h638
  have h640 : TreeTrue τ start640 := cp_true τ ok639 h639
  exact h640
#print axioms steps19
end Snake9.ReplayFull161
