import ReplayCheck161_00736
import ReplayCheck161_00740
import ReplayCheck161_00744
import ReplayCheck161_00748
import ReplayCheck161_00752
import ReplayCheck161_00756
import ReplayCheck161_00760
import ReplayCheck161_00764
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (TreeTrue)
open Snake9.LratFast144
theorem steps23 (τ : Nat → Bool) (h736 : TreeTrue τ start736) : TreeTrue τ start768 := by
  have h737 : TreeTrue τ start737 := replay_true τ ok736 h736
  have h738 : TreeTrue τ start738 := replay_true τ ok737 h737
  have h739 : TreeTrue τ start739 := replay_true τ ok738 h738
  have h740 : TreeTrue τ start740 := replay_true τ ok739 h739
  have h741 : TreeTrue τ start741 := replay_true τ ok740 h740
  have h742 : TreeTrue τ start742 := replay_true τ ok741 h741
  have h743 : TreeTrue τ start743 := replay_true τ ok742 h742
  have h744 : TreeTrue τ start744 := replay_true τ ok743 h743
  have h745 : TreeTrue τ start745 := replay_true τ ok744 h744
  have h746 : TreeTrue τ start746 := replay_true τ ok745 h745
  have h747 : TreeTrue τ start747 := replay_true τ ok746 h746
  have h748 : TreeTrue τ start748 := replay_true τ ok747 h747
  have h749 : TreeTrue τ start749 := replay_true τ ok748 h748
  have h750 : TreeTrue τ start750 := replay_true τ ok749 h749
  have h751 : TreeTrue τ start751 := replay_true τ ok750 h750
  have h752 : TreeTrue τ start752 := replay_true τ ok751 h751
  have h753 : TreeTrue τ start753 := replay_true τ ok752 h752
  have h754 : TreeTrue τ start754 := replay_true τ ok753 h753
  have h755 : TreeTrue τ start755 := replay_true τ ok754 h754
  have h756 : TreeTrue τ start756 := replay_true τ ok755 h755
  have h757 : TreeTrue τ start757 := replay_true τ ok756 h756
  have h758 : TreeTrue τ start758 := replay_true τ ok757 h757
  have h759 : TreeTrue τ start759 := replay_true τ ok758 h758
  have h760 : TreeTrue τ start760 := replay_true τ ok759 h759
  have h761 : TreeTrue τ start761 := replay_true τ ok760 h760
  have h762 : TreeTrue τ start762 := replay_true τ ok761 h761
  have h763 : TreeTrue τ start763 := replay_true τ ok762 h762
  have h764 : TreeTrue τ start764 := replay_true τ ok763 h763
  have h765 : TreeTrue τ start765 := replay_true τ ok764 h764
  have h766 : TreeTrue τ start766 := replay_true τ ok765 h765
  have h767 : TreeTrue τ start767 := replay_true τ ok766 h766
  have h768 : TreeTrue τ start768 := cp_true τ ok767 h767
  exact h768
#print axioms steps23
end Snake9.ReplayFull161
