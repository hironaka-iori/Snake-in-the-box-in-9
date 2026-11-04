import ReplayCheck161_02048
import ReplayCheck161_02052
import ReplayCheck161_02056
import ReplayCheck161_02060
import ReplayCheck161_02064
import ReplayCheck161_02068
import ReplayCheck161_02072
import ReplayCheck161_02076
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (TreeTrue)
open Snake9.LratFast144
theorem steps64 (τ : Nat → Bool) (h2048 : TreeTrue τ start2048) : TreeTrue τ start2080 := by
  have h2049 : TreeTrue τ start2049 := replay_true τ ok2048 h2048
  have h2050 : TreeTrue τ start2050 := replay_true τ ok2049 h2049
  have h2051 : TreeTrue τ start2051 := replay_true τ ok2050 h2050
  have h2052 : TreeTrue τ start2052 := replay_true τ ok2051 h2051
  have h2053 : TreeTrue τ start2053 := replay_true τ ok2052 h2052
  have h2054 : TreeTrue τ start2054 := replay_true τ ok2053 h2053
  have h2055 : TreeTrue τ start2055 := replay_true τ ok2054 h2054
  have h2056 : TreeTrue τ start2056 := replay_true τ ok2055 h2055
  have h2057 : TreeTrue τ start2057 := replay_true τ ok2056 h2056
  have h2058 : TreeTrue τ start2058 := replay_true τ ok2057 h2057
  have h2059 : TreeTrue τ start2059 := replay_true τ ok2058 h2058
  have h2060 : TreeTrue τ start2060 := replay_true τ ok2059 h2059
  have h2061 : TreeTrue τ start2061 := replay_true τ ok2060 h2060
  have h2062 : TreeTrue τ start2062 := replay_true τ ok2061 h2061
  have h2063 : TreeTrue τ start2063 := replay_true τ ok2062 h2062
  have h2064 : TreeTrue τ start2064 := replay_true τ ok2063 h2063
  have h2065 : TreeTrue τ start2065 := replay_true τ ok2064 h2064
  have h2066 : TreeTrue τ start2066 := replay_true τ ok2065 h2065
  have h2067 : TreeTrue τ start2067 := replay_true τ ok2066 h2066
  have h2068 : TreeTrue τ start2068 := replay_true τ ok2067 h2067
  have h2069 : TreeTrue τ start2069 := replay_true τ ok2068 h2068
  have h2070 : TreeTrue τ start2070 := replay_true τ ok2069 h2069
  have h2071 : TreeTrue τ start2071 := replay_true τ ok2070 h2070
  have h2072 : TreeTrue τ start2072 := replay_true τ ok2071 h2071
  have h2073 : TreeTrue τ start2073 := replay_true τ ok2072 h2072
  have h2074 : TreeTrue τ start2074 := replay_true τ ok2073 h2073
  have h2075 : TreeTrue τ start2075 := replay_true τ ok2074 h2074
  have h2076 : TreeTrue τ start2076 := replay_true τ ok2075 h2075
  have h2077 : TreeTrue τ start2077 := replay_true τ ok2076 h2076
  have h2078 : TreeTrue τ start2078 := replay_true τ ok2077 h2077
  have h2079 : TreeTrue τ start2079 := replay_true τ ok2078 h2078
  have h2080 : TreeTrue τ start2080 := cp_true τ ok2079 h2079
  exact h2080
#print axioms steps64
end Snake9.ReplayFull161
