import ReplayCheck161_02144
import ReplayCheck161_02148
import ReplayCheck161_02152
import ReplayCheck161_02156
import ReplayCheck161_02160
import ReplayCheck161_02164
import ReplayCheck161_02168
import ReplayCheck161_02172
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (TreeTrue)
open Snake9.LratFast144
theorem steps67 (τ : Nat → Bool) (h2144 : TreeTrue τ start2144) : TreeTrue τ start2176 := by
  have h2145 : TreeTrue τ start2145 := replay_true τ ok2144 h2144
  have h2146 : TreeTrue τ start2146 := replay_true τ ok2145 h2145
  have h2147 : TreeTrue τ start2147 := replay_true τ ok2146 h2146
  have h2148 : TreeTrue τ start2148 := replay_true τ ok2147 h2147
  have h2149 : TreeTrue τ start2149 := replay_true τ ok2148 h2148
  have h2150 : TreeTrue τ start2150 := replay_true τ ok2149 h2149
  have h2151 : TreeTrue τ start2151 := replay_true τ ok2150 h2150
  have h2152 : TreeTrue τ start2152 := replay_true τ ok2151 h2151
  have h2153 : TreeTrue τ start2153 := replay_true τ ok2152 h2152
  have h2154 : TreeTrue τ start2154 := replay_true τ ok2153 h2153
  have h2155 : TreeTrue τ start2155 := replay_true τ ok2154 h2154
  have h2156 : TreeTrue τ start2156 := replay_true τ ok2155 h2155
  have h2157 : TreeTrue τ start2157 := replay_true τ ok2156 h2156
  have h2158 : TreeTrue τ start2158 := replay_true τ ok2157 h2157
  have h2159 : TreeTrue τ start2159 := replay_true τ ok2158 h2158
  have h2160 : TreeTrue τ start2160 := replay_true τ ok2159 h2159
  have h2161 : TreeTrue τ start2161 := replay_true τ ok2160 h2160
  have h2162 : TreeTrue τ start2162 := replay_true τ ok2161 h2161
  have h2163 : TreeTrue τ start2163 := replay_true τ ok2162 h2162
  have h2164 : TreeTrue τ start2164 := replay_true τ ok2163 h2163
  have h2165 : TreeTrue τ start2165 := replay_true τ ok2164 h2164
  have h2166 : TreeTrue τ start2166 := replay_true τ ok2165 h2165
  have h2167 : TreeTrue τ start2167 := replay_true τ ok2166 h2166
  have h2168 : TreeTrue τ start2168 := replay_true τ ok2167 h2167
  have h2169 : TreeTrue τ start2169 := replay_true τ ok2168 h2168
  have h2170 : TreeTrue τ start2170 := replay_true τ ok2169 h2169
  have h2171 : TreeTrue τ start2171 := replay_true τ ok2170 h2170
  have h2172 : TreeTrue τ start2172 := replay_true τ ok2171 h2171
  have h2173 : TreeTrue τ start2173 := replay_true τ ok2172 h2172
  have h2174 : TreeTrue τ start2174 := replay_true τ ok2173 h2173
  have h2175 : TreeTrue τ start2175 := replay_true τ ok2174 h2174
  have h2176 : TreeTrue τ start2176 := cp_true τ ok2175 h2175
  exact h2176
#print axioms steps67
end Snake9.ReplayFull161
