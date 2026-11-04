import ReplayCheck161_01760
import ReplayCheck161_01764
import ReplayCheck161_01768
import ReplayCheck161_01772
import ReplayCheck161_01776
import ReplayCheck161_01780
import ReplayCheck161_01784
import ReplayCheck161_01788
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (TreeTrue)
open Snake9.LratFast144
theorem steps55 (τ : Nat → Bool) (h1760 : TreeTrue τ start1760) : TreeTrue τ start1792 := by
  have h1761 : TreeTrue τ start1761 := replay_true τ ok1760 h1760
  have h1762 : TreeTrue τ start1762 := replay_true τ ok1761 h1761
  have h1763 : TreeTrue τ start1763 := replay_true τ ok1762 h1762
  have h1764 : TreeTrue τ start1764 := replay_true τ ok1763 h1763
  have h1765 : TreeTrue τ start1765 := replay_true τ ok1764 h1764
  have h1766 : TreeTrue τ start1766 := replay_true τ ok1765 h1765
  have h1767 : TreeTrue τ start1767 := replay_true τ ok1766 h1766
  have h1768 : TreeTrue τ start1768 := replay_true τ ok1767 h1767
  have h1769 : TreeTrue τ start1769 := replay_true τ ok1768 h1768
  have h1770 : TreeTrue τ start1770 := replay_true τ ok1769 h1769
  have h1771 : TreeTrue τ start1771 := replay_true τ ok1770 h1770
  have h1772 : TreeTrue τ start1772 := replay_true τ ok1771 h1771
  have h1773 : TreeTrue τ start1773 := replay_true τ ok1772 h1772
  have h1774 : TreeTrue τ start1774 := replay_true τ ok1773 h1773
  have h1775 : TreeTrue τ start1775 := replay_true τ ok1774 h1774
  have h1776 : TreeTrue τ start1776 := replay_true τ ok1775 h1775
  have h1777 : TreeTrue τ start1777 := replay_true τ ok1776 h1776
  have h1778 : TreeTrue τ start1778 := replay_true τ ok1777 h1777
  have h1779 : TreeTrue τ start1779 := replay_true τ ok1778 h1778
  have h1780 : TreeTrue τ start1780 := replay_true τ ok1779 h1779
  have h1781 : TreeTrue τ start1781 := replay_true τ ok1780 h1780
  have h1782 : TreeTrue τ start1782 := replay_true τ ok1781 h1781
  have h1783 : TreeTrue τ start1783 := replay_true τ ok1782 h1782
  have h1784 : TreeTrue τ start1784 := replay_true τ ok1783 h1783
  have h1785 : TreeTrue τ start1785 := replay_true τ ok1784 h1784
  have h1786 : TreeTrue τ start1786 := replay_true τ ok1785 h1785
  have h1787 : TreeTrue τ start1787 := replay_true τ ok1786 h1786
  have h1788 : TreeTrue τ start1788 := replay_true τ ok1787 h1787
  have h1789 : TreeTrue τ start1789 := replay_true τ ok1788 h1788
  have h1790 : TreeTrue τ start1790 := replay_true τ ok1789 h1789
  have h1791 : TreeTrue τ start1791 := replay_true τ ok1790 h1790
  have h1792 : TreeTrue τ start1792 := cp_true τ ok1791 h1791
  exact h1792
#print axioms steps55
end Snake9.ReplayFull161
