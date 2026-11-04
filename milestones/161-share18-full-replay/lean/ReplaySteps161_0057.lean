import ReplayCheck161_01824
import ReplayCheck161_01828
import ReplayCheck161_01832
import ReplayCheck161_01836
import ReplayCheck161_01840
import ReplayCheck161_01844
import ReplayCheck161_01848
import ReplayCheck161_01852
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (TreeTrue)
open Snake9.LratFast144
theorem steps57 (τ : Nat → Bool) (h1824 : TreeTrue τ start1824) : TreeTrue τ start1856 := by
  have h1825 : TreeTrue τ start1825 := replay_true τ ok1824 h1824
  have h1826 : TreeTrue τ start1826 := replay_true τ ok1825 h1825
  have h1827 : TreeTrue τ start1827 := replay_true τ ok1826 h1826
  have h1828 : TreeTrue τ start1828 := replay_true τ ok1827 h1827
  have h1829 : TreeTrue τ start1829 := replay_true τ ok1828 h1828
  have h1830 : TreeTrue τ start1830 := replay_true τ ok1829 h1829
  have h1831 : TreeTrue τ start1831 := replay_true τ ok1830 h1830
  have h1832 : TreeTrue τ start1832 := replay_true τ ok1831 h1831
  have h1833 : TreeTrue τ start1833 := replay_true τ ok1832 h1832
  have h1834 : TreeTrue τ start1834 := replay_true τ ok1833 h1833
  have h1835 : TreeTrue τ start1835 := replay_true τ ok1834 h1834
  have h1836 : TreeTrue τ start1836 := replay_true τ ok1835 h1835
  have h1837 : TreeTrue τ start1837 := replay_true τ ok1836 h1836
  have h1838 : TreeTrue τ start1838 := replay_true τ ok1837 h1837
  have h1839 : TreeTrue τ start1839 := replay_true τ ok1838 h1838
  have h1840 : TreeTrue τ start1840 := replay_true τ ok1839 h1839
  have h1841 : TreeTrue τ start1841 := replay_true τ ok1840 h1840
  have h1842 : TreeTrue τ start1842 := replay_true τ ok1841 h1841
  have h1843 : TreeTrue τ start1843 := replay_true τ ok1842 h1842
  have h1844 : TreeTrue τ start1844 := replay_true τ ok1843 h1843
  have h1845 : TreeTrue τ start1845 := replay_true τ ok1844 h1844
  have h1846 : TreeTrue τ start1846 := replay_true τ ok1845 h1845
  have h1847 : TreeTrue τ start1847 := replay_true τ ok1846 h1846
  have h1848 : TreeTrue τ start1848 := replay_true τ ok1847 h1847
  have h1849 : TreeTrue τ start1849 := replay_true τ ok1848 h1848
  have h1850 : TreeTrue τ start1850 := replay_true τ ok1849 h1849
  have h1851 : TreeTrue τ start1851 := replay_true τ ok1850 h1850
  have h1852 : TreeTrue τ start1852 := replay_true τ ok1851 h1851
  have h1853 : TreeTrue τ start1853 := replay_true τ ok1852 h1852
  have h1854 : TreeTrue τ start1854 := replay_true τ ok1853 h1853
  have h1855 : TreeTrue τ start1855 := replay_true τ ok1854 h1854
  have h1856 : TreeTrue τ start1856 := cp_true τ ok1855 h1855
  exact h1856
#print axioms steps57
end Snake9.ReplayFull161
