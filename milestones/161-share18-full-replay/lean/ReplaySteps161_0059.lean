import ReplayCheck161_01888
import ReplayCheck161_01892
import ReplayCheck161_01896
import ReplayCheck161_01900
import ReplayCheck161_01904
import ReplayCheck161_01908
import ReplayCheck161_01912
import ReplayCheck161_01916
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (TreeTrue)
open Snake9.LratFast144
theorem steps59 (τ : Nat → Bool) (h1888 : TreeTrue τ start1888) : TreeTrue τ start1920 := by
  have h1889 : TreeTrue τ start1889 := replay_true τ ok1888 h1888
  have h1890 : TreeTrue τ start1890 := replay_true τ ok1889 h1889
  have h1891 : TreeTrue τ start1891 := replay_true τ ok1890 h1890
  have h1892 : TreeTrue τ start1892 := replay_true τ ok1891 h1891
  have h1893 : TreeTrue τ start1893 := replay_true τ ok1892 h1892
  have h1894 : TreeTrue τ start1894 := replay_true τ ok1893 h1893
  have h1895 : TreeTrue τ start1895 := replay_true τ ok1894 h1894
  have h1896 : TreeTrue τ start1896 := replay_true τ ok1895 h1895
  have h1897 : TreeTrue τ start1897 := replay_true τ ok1896 h1896
  have h1898 : TreeTrue τ start1898 := replay_true τ ok1897 h1897
  have h1899 : TreeTrue τ start1899 := replay_true τ ok1898 h1898
  have h1900 : TreeTrue τ start1900 := replay_true τ ok1899 h1899
  have h1901 : TreeTrue τ start1901 := replay_true τ ok1900 h1900
  have h1902 : TreeTrue τ start1902 := replay_true τ ok1901 h1901
  have h1903 : TreeTrue τ start1903 := replay_true τ ok1902 h1902
  have h1904 : TreeTrue τ start1904 := replay_true τ ok1903 h1903
  have h1905 : TreeTrue τ start1905 := replay_true τ ok1904 h1904
  have h1906 : TreeTrue τ start1906 := replay_true τ ok1905 h1905
  have h1907 : TreeTrue τ start1907 := replay_true τ ok1906 h1906
  have h1908 : TreeTrue τ start1908 := replay_true τ ok1907 h1907
  have h1909 : TreeTrue τ start1909 := replay_true τ ok1908 h1908
  have h1910 : TreeTrue τ start1910 := replay_true τ ok1909 h1909
  have h1911 : TreeTrue τ start1911 := replay_true τ ok1910 h1910
  have h1912 : TreeTrue τ start1912 := replay_true τ ok1911 h1911
  have h1913 : TreeTrue τ start1913 := replay_true τ ok1912 h1912
  have h1914 : TreeTrue τ start1914 := replay_true τ ok1913 h1913
  have h1915 : TreeTrue τ start1915 := replay_true τ ok1914 h1914
  have h1916 : TreeTrue τ start1916 := replay_true τ ok1915 h1915
  have h1917 : TreeTrue τ start1917 := replay_true τ ok1916 h1916
  have h1918 : TreeTrue τ start1918 := replay_true τ ok1917 h1917
  have h1919 : TreeTrue τ start1919 := replay_true τ ok1918 h1918
  have h1920 : TreeTrue τ start1920 := cp_true τ ok1919 h1919
  exact h1920
#print axioms steps59
end Snake9.ReplayFull161
