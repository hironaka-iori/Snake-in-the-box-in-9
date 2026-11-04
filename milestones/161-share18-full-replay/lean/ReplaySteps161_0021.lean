import ReplayCheck161_00672
import ReplayCheck161_00676
import ReplayCheck161_00680
import ReplayCheck161_00684
import ReplayCheck161_00688
import ReplayCheck161_00692
import ReplayCheck161_00696
import ReplayCheck161_00700
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (TreeTrue)
open Snake9.LratFast144
theorem steps21 (τ : Nat → Bool) (h672 : TreeTrue τ start672) : TreeTrue τ start704 := by
  have h673 : TreeTrue τ start673 := replay_true τ ok672 h672
  have h674 : TreeTrue τ start674 := replay_true τ ok673 h673
  have h675 : TreeTrue τ start675 := replay_true τ ok674 h674
  have h676 : TreeTrue τ start676 := replay_true τ ok675 h675
  have h677 : TreeTrue τ start677 := replay_true τ ok676 h676
  have h678 : TreeTrue τ start678 := replay_true τ ok677 h677
  have h679 : TreeTrue τ start679 := replay_true τ ok678 h678
  have h680 : TreeTrue τ start680 := replay_true τ ok679 h679
  have h681 : TreeTrue τ start681 := replay_true τ ok680 h680
  have h682 : TreeTrue τ start682 := replay_true τ ok681 h681
  have h683 : TreeTrue τ start683 := replay_true τ ok682 h682
  have h684 : TreeTrue τ start684 := replay_true τ ok683 h683
  have h685 : TreeTrue τ start685 := replay_true τ ok684 h684
  have h686 : TreeTrue τ start686 := replay_true τ ok685 h685
  have h687 : TreeTrue τ start687 := replay_true τ ok686 h686
  have h688 : TreeTrue τ start688 := replay_true τ ok687 h687
  have h689 : TreeTrue τ start689 := replay_true τ ok688 h688
  have h690 : TreeTrue τ start690 := replay_true τ ok689 h689
  have h691 : TreeTrue τ start691 := replay_true τ ok690 h690
  have h692 : TreeTrue τ start692 := replay_true τ ok691 h691
  have h693 : TreeTrue τ start693 := replay_true τ ok692 h692
  have h694 : TreeTrue τ start694 := replay_true τ ok693 h693
  have h695 : TreeTrue τ start695 := replay_true τ ok694 h694
  have h696 : TreeTrue τ start696 := replay_true τ ok695 h695
  have h697 : TreeTrue τ start697 := replay_true τ ok696 h696
  have h698 : TreeTrue τ start698 := replay_true τ ok697 h697
  have h699 : TreeTrue τ start699 := replay_true τ ok698 h698
  have h700 : TreeTrue τ start700 := replay_true τ ok699 h699
  have h701 : TreeTrue τ start701 := replay_true τ ok700 h700
  have h702 : TreeTrue τ start702 := replay_true τ ok701 h701
  have h703 : TreeTrue τ start703 := replay_true τ ok702 h702
  have h704 : TreeTrue τ start704 := cp_true τ ok703 h703
  exact h704
#print axioms steps21
end Snake9.ReplayFull161
