import ReplayCheck161_01728
import ReplayCheck161_01732
import ReplayCheck161_01736
import ReplayCheck161_01740
import ReplayCheck161_01744
import ReplayCheck161_01748
import ReplayCheck161_01752
import ReplayCheck161_01756
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (TreeTrue)
open Snake9.LratFast144
theorem steps54 (τ : Nat → Bool) (h1728 : TreeTrue τ start1728) : TreeTrue τ start1760 := by
  have h1729 : TreeTrue τ start1729 := replay_true τ ok1728 h1728
  have h1730 : TreeTrue τ start1730 := replay_true τ ok1729 h1729
  have h1731 : TreeTrue τ start1731 := replay_true τ ok1730 h1730
  have h1732 : TreeTrue τ start1732 := replay_true τ ok1731 h1731
  have h1733 : TreeTrue τ start1733 := replay_true τ ok1732 h1732
  have h1734 : TreeTrue τ start1734 := replay_true τ ok1733 h1733
  have h1735 : TreeTrue τ start1735 := replay_true τ ok1734 h1734
  have h1736 : TreeTrue τ start1736 := replay_true τ ok1735 h1735
  have h1737 : TreeTrue τ start1737 := replay_true τ ok1736 h1736
  have h1738 : TreeTrue τ start1738 := replay_true τ ok1737 h1737
  have h1739 : TreeTrue τ start1739 := replay_true τ ok1738 h1738
  have h1740 : TreeTrue τ start1740 := replay_true τ ok1739 h1739
  have h1741 : TreeTrue τ start1741 := replay_true τ ok1740 h1740
  have h1742 : TreeTrue τ start1742 := replay_true τ ok1741 h1741
  have h1743 : TreeTrue τ start1743 := replay_true τ ok1742 h1742
  have h1744 : TreeTrue τ start1744 := replay_true τ ok1743 h1743
  have h1745 : TreeTrue τ start1745 := replay_true τ ok1744 h1744
  have h1746 : TreeTrue τ start1746 := replay_true τ ok1745 h1745
  have h1747 : TreeTrue τ start1747 := replay_true τ ok1746 h1746
  have h1748 : TreeTrue τ start1748 := replay_true τ ok1747 h1747
  have h1749 : TreeTrue τ start1749 := replay_true τ ok1748 h1748
  have h1750 : TreeTrue τ start1750 := replay_true τ ok1749 h1749
  have h1751 : TreeTrue τ start1751 := replay_true τ ok1750 h1750
  have h1752 : TreeTrue τ start1752 := replay_true τ ok1751 h1751
  have h1753 : TreeTrue τ start1753 := replay_true τ ok1752 h1752
  have h1754 : TreeTrue τ start1754 := replay_true τ ok1753 h1753
  have h1755 : TreeTrue τ start1755 := replay_true τ ok1754 h1754
  have h1756 : TreeTrue τ start1756 := replay_true τ ok1755 h1755
  have h1757 : TreeTrue τ start1757 := replay_true τ ok1756 h1756
  have h1758 : TreeTrue τ start1758 := replay_true τ ok1757 h1757
  have h1759 : TreeTrue τ start1759 := replay_true τ ok1758 h1758
  have h1760 : TreeTrue τ start1760 := cp_true τ ok1759 h1759
  exact h1760
#print axioms steps54
end Snake9.ReplayFull161
