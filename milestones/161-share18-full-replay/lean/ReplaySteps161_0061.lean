import ReplayCheck161_01952
import ReplayCheck161_01956
import ReplayCheck161_01960
import ReplayCheck161_01964
import ReplayCheck161_01968
import ReplayCheck161_01972
import ReplayCheck161_01976
import ReplayCheck161_01980
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (TreeTrue)
open Snake9.LratFast144
theorem steps61 (τ : Nat → Bool) (h1952 : TreeTrue τ start1952) : TreeTrue τ start1984 := by
  have h1953 : TreeTrue τ start1953 := replay_true τ ok1952 h1952
  have h1954 : TreeTrue τ start1954 := replay_true τ ok1953 h1953
  have h1955 : TreeTrue τ start1955 := replay_true τ ok1954 h1954
  have h1956 : TreeTrue τ start1956 := replay_true τ ok1955 h1955
  have h1957 : TreeTrue τ start1957 := replay_true τ ok1956 h1956
  have h1958 : TreeTrue τ start1958 := replay_true τ ok1957 h1957
  have h1959 : TreeTrue τ start1959 := replay_true τ ok1958 h1958
  have h1960 : TreeTrue τ start1960 := replay_true τ ok1959 h1959
  have h1961 : TreeTrue τ start1961 := replay_true τ ok1960 h1960
  have h1962 : TreeTrue τ start1962 := replay_true τ ok1961 h1961
  have h1963 : TreeTrue τ start1963 := replay_true τ ok1962 h1962
  have h1964 : TreeTrue τ start1964 := replay_true τ ok1963 h1963
  have h1965 : TreeTrue τ start1965 := replay_true τ ok1964 h1964
  have h1966 : TreeTrue τ start1966 := replay_true τ ok1965 h1965
  have h1967 : TreeTrue τ start1967 := replay_true τ ok1966 h1966
  have h1968 : TreeTrue τ start1968 := replay_true τ ok1967 h1967
  have h1969 : TreeTrue τ start1969 := replay_true τ ok1968 h1968
  have h1970 : TreeTrue τ start1970 := replay_true τ ok1969 h1969
  have h1971 : TreeTrue τ start1971 := replay_true τ ok1970 h1970
  have h1972 : TreeTrue τ start1972 := replay_true τ ok1971 h1971
  have h1973 : TreeTrue τ start1973 := replay_true τ ok1972 h1972
  have h1974 : TreeTrue τ start1974 := replay_true τ ok1973 h1973
  have h1975 : TreeTrue τ start1975 := replay_true τ ok1974 h1974
  have h1976 : TreeTrue τ start1976 := replay_true τ ok1975 h1975
  have h1977 : TreeTrue τ start1977 := replay_true τ ok1976 h1976
  have h1978 : TreeTrue τ start1978 := replay_true τ ok1977 h1977
  have h1979 : TreeTrue τ start1979 := replay_true τ ok1978 h1978
  have h1980 : TreeTrue τ start1980 := replay_true τ ok1979 h1979
  have h1981 : TreeTrue τ start1981 := replay_true τ ok1980 h1980
  have h1982 : TreeTrue τ start1982 := replay_true τ ok1981 h1981
  have h1983 : TreeTrue τ start1983 := replay_true τ ok1982 h1982
  have h1984 : TreeTrue τ start1984 := cp_true τ ok1983 h1983
  exact h1984
#print axioms steps61
end Snake9.ReplayFull161
