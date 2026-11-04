import ReplayCheck161_01792
import ReplayCheck161_01796
import ReplayCheck161_01800
import ReplayCheck161_01804
import ReplayCheck161_01808
import ReplayCheck161_01812
import ReplayCheck161_01816
import ReplayCheck161_01820
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (TreeTrue)
open Snake9.LratFast144
theorem steps56 (τ : Nat → Bool) (h1792 : TreeTrue τ start1792) : TreeTrue τ start1824 := by
  have h1793 : TreeTrue τ start1793 := replay_true τ ok1792 h1792
  have h1794 : TreeTrue τ start1794 := replay_true τ ok1793 h1793
  have h1795 : TreeTrue τ start1795 := replay_true τ ok1794 h1794
  have h1796 : TreeTrue τ start1796 := replay_true τ ok1795 h1795
  have h1797 : TreeTrue τ start1797 := replay_true τ ok1796 h1796
  have h1798 : TreeTrue τ start1798 := replay_true τ ok1797 h1797
  have h1799 : TreeTrue τ start1799 := replay_true τ ok1798 h1798
  have h1800 : TreeTrue τ start1800 := replay_true τ ok1799 h1799
  have h1801 : TreeTrue τ start1801 := replay_true τ ok1800 h1800
  have h1802 : TreeTrue τ start1802 := replay_true τ ok1801 h1801
  have h1803 : TreeTrue τ start1803 := replay_true τ ok1802 h1802
  have h1804 : TreeTrue τ start1804 := replay_true τ ok1803 h1803
  have h1805 : TreeTrue τ start1805 := replay_true τ ok1804 h1804
  have h1806 : TreeTrue τ start1806 := replay_true τ ok1805 h1805
  have h1807 : TreeTrue τ start1807 := replay_true τ ok1806 h1806
  have h1808 : TreeTrue τ start1808 := replay_true τ ok1807 h1807
  have h1809 : TreeTrue τ start1809 := replay_true τ ok1808 h1808
  have h1810 : TreeTrue τ start1810 := replay_true τ ok1809 h1809
  have h1811 : TreeTrue τ start1811 := replay_true τ ok1810 h1810
  have h1812 : TreeTrue τ start1812 := replay_true τ ok1811 h1811
  have h1813 : TreeTrue τ start1813 := replay_true τ ok1812 h1812
  have h1814 : TreeTrue τ start1814 := replay_true τ ok1813 h1813
  have h1815 : TreeTrue τ start1815 := replay_true τ ok1814 h1814
  have h1816 : TreeTrue τ start1816 := replay_true τ ok1815 h1815
  have h1817 : TreeTrue τ start1817 := replay_true τ ok1816 h1816
  have h1818 : TreeTrue τ start1818 := replay_true τ ok1817 h1817
  have h1819 : TreeTrue τ start1819 := replay_true τ ok1818 h1818
  have h1820 : TreeTrue τ start1820 := replay_true τ ok1819 h1819
  have h1821 : TreeTrue τ start1821 := replay_true τ ok1820 h1820
  have h1822 : TreeTrue τ start1822 := replay_true τ ok1821 h1821
  have h1823 : TreeTrue τ start1823 := replay_true τ ok1822 h1822
  have h1824 : TreeTrue τ start1824 := cp_true τ ok1823 h1823
  exact h1824
#print axioms steps56
end Snake9.ReplayFull161
