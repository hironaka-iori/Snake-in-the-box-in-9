import ReplayCheck161_02080
import ReplayCheck161_02084
import ReplayCheck161_02088
import ReplayCheck161_02092
import ReplayCheck161_02096
import ReplayCheck161_02100
import ReplayCheck161_02104
import ReplayCheck161_02108
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (TreeTrue)
open Snake9.LratFast144
theorem steps65 (τ : Nat → Bool) (h2080 : TreeTrue τ start2080) : TreeTrue τ start2112 := by
  have h2081 : TreeTrue τ start2081 := replay_true τ ok2080 h2080
  have h2082 : TreeTrue τ start2082 := replay_true τ ok2081 h2081
  have h2083 : TreeTrue τ start2083 := replay_true τ ok2082 h2082
  have h2084 : TreeTrue τ start2084 := replay_true τ ok2083 h2083
  have h2085 : TreeTrue τ start2085 := replay_true τ ok2084 h2084
  have h2086 : TreeTrue τ start2086 := replay_true τ ok2085 h2085
  have h2087 : TreeTrue τ start2087 := replay_true τ ok2086 h2086
  have h2088 : TreeTrue τ start2088 := replay_true τ ok2087 h2087
  have h2089 : TreeTrue τ start2089 := replay_true τ ok2088 h2088
  have h2090 : TreeTrue τ start2090 := replay_true τ ok2089 h2089
  have h2091 : TreeTrue τ start2091 := replay_true τ ok2090 h2090
  have h2092 : TreeTrue τ start2092 := replay_true τ ok2091 h2091
  have h2093 : TreeTrue τ start2093 := replay_true τ ok2092 h2092
  have h2094 : TreeTrue τ start2094 := replay_true τ ok2093 h2093
  have h2095 : TreeTrue τ start2095 := replay_true τ ok2094 h2094
  have h2096 : TreeTrue τ start2096 := replay_true τ ok2095 h2095
  have h2097 : TreeTrue τ start2097 := replay_true τ ok2096 h2096
  have h2098 : TreeTrue τ start2098 := replay_true τ ok2097 h2097
  have h2099 : TreeTrue τ start2099 := replay_true τ ok2098 h2098
  have h2100 : TreeTrue τ start2100 := replay_true τ ok2099 h2099
  have h2101 : TreeTrue τ start2101 := replay_true τ ok2100 h2100
  have h2102 : TreeTrue τ start2102 := replay_true τ ok2101 h2101
  have h2103 : TreeTrue τ start2103 := replay_true τ ok2102 h2102
  have h2104 : TreeTrue τ start2104 := replay_true τ ok2103 h2103
  have h2105 : TreeTrue τ start2105 := replay_true τ ok2104 h2104
  have h2106 : TreeTrue τ start2106 := replay_true τ ok2105 h2105
  have h2107 : TreeTrue τ start2107 := replay_true τ ok2106 h2106
  have h2108 : TreeTrue τ start2108 := replay_true τ ok2107 h2107
  have h2109 : TreeTrue τ start2109 := replay_true τ ok2108 h2108
  have h2110 : TreeTrue τ start2110 := replay_true τ ok2109 h2109
  have h2111 : TreeTrue τ start2111 := replay_true τ ok2110 h2110
  have h2112 : TreeTrue τ start2112 := cp_true τ ok2111 h2111
  exact h2112
#print axioms steps65
end Snake9.ReplayFull161
