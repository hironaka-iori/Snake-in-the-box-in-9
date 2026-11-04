import ReplayCheck161_01920
import ReplayCheck161_01924
import ReplayCheck161_01928
import ReplayCheck161_01932
import ReplayCheck161_01936
import ReplayCheck161_01940
import ReplayCheck161_01944
import ReplayCheck161_01948
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (TreeTrue)
open Snake9.LratFast144
theorem steps60 (τ : Nat → Bool) (h1920 : TreeTrue τ start1920) : TreeTrue τ start1952 := by
  have h1921 : TreeTrue τ start1921 := replay_true τ ok1920 h1920
  have h1922 : TreeTrue τ start1922 := replay_true τ ok1921 h1921
  have h1923 : TreeTrue τ start1923 := replay_true τ ok1922 h1922
  have h1924 : TreeTrue τ start1924 := replay_true τ ok1923 h1923
  have h1925 : TreeTrue τ start1925 := replay_true τ ok1924 h1924
  have h1926 : TreeTrue τ start1926 := replay_true τ ok1925 h1925
  have h1927 : TreeTrue τ start1927 := replay_true τ ok1926 h1926
  have h1928 : TreeTrue τ start1928 := replay_true τ ok1927 h1927
  have h1929 : TreeTrue τ start1929 := replay_true τ ok1928 h1928
  have h1930 : TreeTrue τ start1930 := replay_true τ ok1929 h1929
  have h1931 : TreeTrue τ start1931 := replay_true τ ok1930 h1930
  have h1932 : TreeTrue τ start1932 := replay_true τ ok1931 h1931
  have h1933 : TreeTrue τ start1933 := replay_true τ ok1932 h1932
  have h1934 : TreeTrue τ start1934 := replay_true τ ok1933 h1933
  have h1935 : TreeTrue τ start1935 := replay_true τ ok1934 h1934
  have h1936 : TreeTrue τ start1936 := replay_true τ ok1935 h1935
  have h1937 : TreeTrue τ start1937 := replay_true τ ok1936 h1936
  have h1938 : TreeTrue τ start1938 := replay_true τ ok1937 h1937
  have h1939 : TreeTrue τ start1939 := replay_true τ ok1938 h1938
  have h1940 : TreeTrue τ start1940 := replay_true τ ok1939 h1939
  have h1941 : TreeTrue τ start1941 := replay_true τ ok1940 h1940
  have h1942 : TreeTrue τ start1942 := replay_true τ ok1941 h1941
  have h1943 : TreeTrue τ start1943 := replay_true τ ok1942 h1942
  have h1944 : TreeTrue τ start1944 := replay_true τ ok1943 h1943
  have h1945 : TreeTrue τ start1945 := replay_true τ ok1944 h1944
  have h1946 : TreeTrue τ start1946 := replay_true τ ok1945 h1945
  have h1947 : TreeTrue τ start1947 := replay_true τ ok1946 h1946
  have h1948 : TreeTrue τ start1948 := replay_true τ ok1947 h1947
  have h1949 : TreeTrue τ start1949 := replay_true τ ok1948 h1948
  have h1950 : TreeTrue τ start1950 := replay_true τ ok1949 h1949
  have h1951 : TreeTrue τ start1951 := replay_true τ ok1950 h1950
  have h1952 : TreeTrue τ start1952 := cp_true τ ok1951 h1951
  exact h1952
#print axioms steps60
end Snake9.ReplayFull161
