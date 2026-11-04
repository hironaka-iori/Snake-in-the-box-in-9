import ReplayCheck161_02112
import ReplayCheck161_02116
import ReplayCheck161_02120
import ReplayCheck161_02124
import ReplayCheck161_02128
import ReplayCheck161_02132
import ReplayCheck161_02136
import ReplayCheck161_02140
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (TreeTrue)
open Snake9.LratFast144
theorem steps66 (τ : Nat → Bool) (h2112 : TreeTrue τ start2112) : TreeTrue τ start2144 := by
  have h2113 : TreeTrue τ start2113 := replay_true τ ok2112 h2112
  have h2114 : TreeTrue τ start2114 := replay_true τ ok2113 h2113
  have h2115 : TreeTrue τ start2115 := replay_true τ ok2114 h2114
  have h2116 : TreeTrue τ start2116 := replay_true τ ok2115 h2115
  have h2117 : TreeTrue τ start2117 := replay_true τ ok2116 h2116
  have h2118 : TreeTrue τ start2118 := replay_true τ ok2117 h2117
  have h2119 : TreeTrue τ start2119 := replay_true τ ok2118 h2118
  have h2120 : TreeTrue τ start2120 := replay_true τ ok2119 h2119
  have h2121 : TreeTrue τ start2121 := replay_true τ ok2120 h2120
  have h2122 : TreeTrue τ start2122 := replay_true τ ok2121 h2121
  have h2123 : TreeTrue τ start2123 := replay_true τ ok2122 h2122
  have h2124 : TreeTrue τ start2124 := replay_true τ ok2123 h2123
  have h2125 : TreeTrue τ start2125 := replay_true τ ok2124 h2124
  have h2126 : TreeTrue τ start2126 := replay_true τ ok2125 h2125
  have h2127 : TreeTrue τ start2127 := replay_true τ ok2126 h2126
  have h2128 : TreeTrue τ start2128 := replay_true τ ok2127 h2127
  have h2129 : TreeTrue τ start2129 := replay_true τ ok2128 h2128
  have h2130 : TreeTrue τ start2130 := replay_true τ ok2129 h2129
  have h2131 : TreeTrue τ start2131 := replay_true τ ok2130 h2130
  have h2132 : TreeTrue τ start2132 := replay_true τ ok2131 h2131
  have h2133 : TreeTrue τ start2133 := replay_true τ ok2132 h2132
  have h2134 : TreeTrue τ start2134 := replay_true τ ok2133 h2133
  have h2135 : TreeTrue τ start2135 := replay_true τ ok2134 h2134
  have h2136 : TreeTrue τ start2136 := replay_true τ ok2135 h2135
  have h2137 : TreeTrue τ start2137 := replay_true τ ok2136 h2136
  have h2138 : TreeTrue τ start2138 := replay_true τ ok2137 h2137
  have h2139 : TreeTrue τ start2139 := replay_true τ ok2138 h2138
  have h2140 : TreeTrue τ start2140 := replay_true τ ok2139 h2139
  have h2141 : TreeTrue τ start2141 := replay_true τ ok2140 h2140
  have h2142 : TreeTrue τ start2142 := replay_true τ ok2141 h2141
  have h2143 : TreeTrue τ start2143 := replay_true τ ok2142 h2142
  have h2144 : TreeTrue τ start2144 := cp_true τ ok2143 h2143
  exact h2144
#print axioms steps66
end Snake9.ReplayFull161
