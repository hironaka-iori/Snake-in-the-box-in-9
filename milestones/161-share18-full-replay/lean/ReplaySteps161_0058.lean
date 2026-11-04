import ReplayCheck161_01856
import ReplayCheck161_01860
import ReplayCheck161_01864
import ReplayCheck161_01868
import ReplayCheck161_01872
import ReplayCheck161_01876
import ReplayCheck161_01880
import ReplayCheck161_01884
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (TreeTrue)
open Snake9.LratFast144
theorem steps58 (τ : Nat → Bool) (h1856 : TreeTrue τ start1856) : TreeTrue τ start1888 := by
  have h1857 : TreeTrue τ start1857 := replay_true τ ok1856 h1856
  have h1858 : TreeTrue τ start1858 := replay_true τ ok1857 h1857
  have h1859 : TreeTrue τ start1859 := replay_true τ ok1858 h1858
  have h1860 : TreeTrue τ start1860 := replay_true τ ok1859 h1859
  have h1861 : TreeTrue τ start1861 := replay_true τ ok1860 h1860
  have h1862 : TreeTrue τ start1862 := replay_true τ ok1861 h1861
  have h1863 : TreeTrue τ start1863 := replay_true τ ok1862 h1862
  have h1864 : TreeTrue τ start1864 := replay_true τ ok1863 h1863
  have h1865 : TreeTrue τ start1865 := replay_true τ ok1864 h1864
  have h1866 : TreeTrue τ start1866 := replay_true τ ok1865 h1865
  have h1867 : TreeTrue τ start1867 := replay_true τ ok1866 h1866
  have h1868 : TreeTrue τ start1868 := replay_true τ ok1867 h1867
  have h1869 : TreeTrue τ start1869 := replay_true τ ok1868 h1868
  have h1870 : TreeTrue τ start1870 := replay_true τ ok1869 h1869
  have h1871 : TreeTrue τ start1871 := replay_true τ ok1870 h1870
  have h1872 : TreeTrue τ start1872 := replay_true τ ok1871 h1871
  have h1873 : TreeTrue τ start1873 := replay_true τ ok1872 h1872
  have h1874 : TreeTrue τ start1874 := replay_true τ ok1873 h1873
  have h1875 : TreeTrue τ start1875 := replay_true τ ok1874 h1874
  have h1876 : TreeTrue τ start1876 := replay_true τ ok1875 h1875
  have h1877 : TreeTrue τ start1877 := replay_true τ ok1876 h1876
  have h1878 : TreeTrue τ start1878 := replay_true τ ok1877 h1877
  have h1879 : TreeTrue τ start1879 := replay_true τ ok1878 h1878
  have h1880 : TreeTrue τ start1880 := replay_true τ ok1879 h1879
  have h1881 : TreeTrue τ start1881 := replay_true τ ok1880 h1880
  have h1882 : TreeTrue τ start1882 := replay_true τ ok1881 h1881
  have h1883 : TreeTrue τ start1883 := replay_true τ ok1882 h1882
  have h1884 : TreeTrue τ start1884 := replay_true τ ok1883 h1883
  have h1885 : TreeTrue τ start1885 := replay_true τ ok1884 h1884
  have h1886 : TreeTrue τ start1886 := replay_true τ ok1885 h1885
  have h1887 : TreeTrue τ start1887 := replay_true τ ok1886 h1886
  have h1888 : TreeTrue τ start1888 := cp_true τ ok1887 h1887
  exact h1888
#print axioms steps58
end Snake9.ReplayFull161
