import ReplayCheck161_02176
import ReplayCheck161_02180
import ReplayCheck161_02184
import ReplayCheck161_02188
import ReplayCheck161_02192
import ReplayCheck161_02196
import ReplayCheck161_02200
import ReplayCheck161_02204
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (TreeTrue)
open Snake9.LratFast144
theorem steps68 (τ : Nat → Bool) (h2176 : TreeTrue τ start2176) : TreeTrue τ start2208 := by
  have h2177 : TreeTrue τ start2177 := replay_true τ ok2176 h2176
  have h2178 : TreeTrue τ start2178 := replay_true τ ok2177 h2177
  have h2179 : TreeTrue τ start2179 := replay_true τ ok2178 h2178
  have h2180 : TreeTrue τ start2180 := replay_true τ ok2179 h2179
  have h2181 : TreeTrue τ start2181 := replay_true τ ok2180 h2180
  have h2182 : TreeTrue τ start2182 := replay_true τ ok2181 h2181
  have h2183 : TreeTrue τ start2183 := replay_true τ ok2182 h2182
  have h2184 : TreeTrue τ start2184 := replay_true τ ok2183 h2183
  have h2185 : TreeTrue τ start2185 := replay_true τ ok2184 h2184
  have h2186 : TreeTrue τ start2186 := replay_true τ ok2185 h2185
  have h2187 : TreeTrue τ start2187 := replay_true τ ok2186 h2186
  have h2188 : TreeTrue τ start2188 := replay_true τ ok2187 h2187
  have h2189 : TreeTrue τ start2189 := replay_true τ ok2188 h2188
  have h2190 : TreeTrue τ start2190 := replay_true τ ok2189 h2189
  have h2191 : TreeTrue τ start2191 := replay_true τ ok2190 h2190
  have h2192 : TreeTrue τ start2192 := replay_true τ ok2191 h2191
  have h2193 : TreeTrue τ start2193 := replay_true τ ok2192 h2192
  have h2194 : TreeTrue τ start2194 := replay_true τ ok2193 h2193
  have h2195 : TreeTrue τ start2195 := replay_true τ ok2194 h2194
  have h2196 : TreeTrue τ start2196 := replay_true τ ok2195 h2195
  have h2197 : TreeTrue τ start2197 := replay_true τ ok2196 h2196
  have h2198 : TreeTrue τ start2198 := replay_true τ ok2197 h2197
  have h2199 : TreeTrue τ start2199 := replay_true τ ok2198 h2198
  have h2200 : TreeTrue τ start2200 := replay_true τ ok2199 h2199
  have h2201 : TreeTrue τ start2201 := replay_true τ ok2200 h2200
  have h2202 : TreeTrue τ start2202 := replay_true τ ok2201 h2201
  have h2203 : TreeTrue τ start2203 := replay_true τ ok2202 h2202
  have h2204 : TreeTrue τ start2204 := replay_true τ ok2203 h2203
  have h2205 : TreeTrue τ start2205 := replay_true τ ok2204 h2204
  have h2206 : TreeTrue τ start2206 := replay_true τ ok2205 h2205
  have h2207 : TreeTrue τ start2207 := replay_true τ ok2206 h2206
  have h2208 : TreeTrue τ start2208 := cp_true τ ok2207 h2207
  exact h2208
#print axioms steps68
end Snake9.ReplayFull161
