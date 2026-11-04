import ReplayCheck161_02208
import ReplayCheck161_02212
import ReplayCheck161_02216
import ReplayCheck161_02220
import ReplayCheck161_02224
import ReplayCheck161_02228
import ReplayCheck161_02232
import ReplayCheck161_02236
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (TreeTrue)
open Snake9.LratFast144
theorem steps69 (τ : Nat → Bool) (h2208 : TreeTrue τ start2208) : TreeTrue τ start2240 := by
  have h2209 : TreeTrue τ start2209 := replay_true τ ok2208 h2208
  have h2210 : TreeTrue τ start2210 := replay_true τ ok2209 h2209
  have h2211 : TreeTrue τ start2211 := replay_true τ ok2210 h2210
  have h2212 : TreeTrue τ start2212 := replay_true τ ok2211 h2211
  have h2213 : TreeTrue τ start2213 := replay_true τ ok2212 h2212
  have h2214 : TreeTrue τ start2214 := replay_true τ ok2213 h2213
  have h2215 : TreeTrue τ start2215 := replay_true τ ok2214 h2214
  have h2216 : TreeTrue τ start2216 := replay_true τ ok2215 h2215
  have h2217 : TreeTrue τ start2217 := replay_true τ ok2216 h2216
  have h2218 : TreeTrue τ start2218 := replay_true τ ok2217 h2217
  have h2219 : TreeTrue τ start2219 := replay_true τ ok2218 h2218
  have h2220 : TreeTrue τ start2220 := replay_true τ ok2219 h2219
  have h2221 : TreeTrue τ start2221 := replay_true τ ok2220 h2220
  have h2222 : TreeTrue τ start2222 := replay_true τ ok2221 h2221
  have h2223 : TreeTrue τ start2223 := replay_true τ ok2222 h2222
  have h2224 : TreeTrue τ start2224 := replay_true τ ok2223 h2223
  have h2225 : TreeTrue τ start2225 := replay_true τ ok2224 h2224
  have h2226 : TreeTrue τ start2226 := replay_true τ ok2225 h2225
  have h2227 : TreeTrue τ start2227 := replay_true τ ok2226 h2226
  have h2228 : TreeTrue τ start2228 := replay_true τ ok2227 h2227
  have h2229 : TreeTrue τ start2229 := replay_true τ ok2228 h2228
  have h2230 : TreeTrue τ start2230 := replay_true τ ok2229 h2229
  have h2231 : TreeTrue τ start2231 := replay_true τ ok2230 h2230
  have h2232 : TreeTrue τ start2232 := replay_true τ ok2231 h2231
  have h2233 : TreeTrue τ start2233 := replay_true τ ok2232 h2232
  have h2234 : TreeTrue τ start2234 := replay_true τ ok2233 h2233
  have h2235 : TreeTrue τ start2235 := replay_true τ ok2234 h2234
  have h2236 : TreeTrue τ start2236 := replay_true τ ok2235 h2235
  have h2237 : TreeTrue τ start2237 := replay_true τ ok2236 h2236
  have h2238 : TreeTrue τ start2238 := replay_true τ ok2237 h2237
  have h2239 : TreeTrue τ start2239 := replay_true τ ok2238 h2238
  have h2240 : TreeTrue τ start2240 := cp_true τ ok2239 h2239
  exact h2240
#print axioms steps69
end Snake9.ReplayFull161
