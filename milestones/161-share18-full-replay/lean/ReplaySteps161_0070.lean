import ReplayCheck161_02240
import ReplayCheck161_02244
import ReplayCheck161_02248
import ReplayCheck161_02252
import ReplayCheck161_02256
import ReplayCheck161_02260
import ReplayCheck161_02264
import ReplayCheck161_02268
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (TreeTrue)
open Snake9.LratFast144
theorem steps70 (τ : Nat → Bool) (h2240 : TreeTrue τ start2240) : TreeTrue τ start2272 := by
  have h2241 : TreeTrue τ start2241 := replay_true τ ok2240 h2240
  have h2242 : TreeTrue τ start2242 := replay_true τ ok2241 h2241
  have h2243 : TreeTrue τ start2243 := replay_true τ ok2242 h2242
  have h2244 : TreeTrue τ start2244 := replay_true τ ok2243 h2243
  have h2245 : TreeTrue τ start2245 := replay_true τ ok2244 h2244
  have h2246 : TreeTrue τ start2246 := replay_true τ ok2245 h2245
  have h2247 : TreeTrue τ start2247 := replay_true τ ok2246 h2246
  have h2248 : TreeTrue τ start2248 := replay_true τ ok2247 h2247
  have h2249 : TreeTrue τ start2249 := replay_true τ ok2248 h2248
  have h2250 : TreeTrue τ start2250 := replay_true τ ok2249 h2249
  have h2251 : TreeTrue τ start2251 := replay_true τ ok2250 h2250
  have h2252 : TreeTrue τ start2252 := replay_true τ ok2251 h2251
  have h2253 : TreeTrue τ start2253 := replay_true τ ok2252 h2252
  have h2254 : TreeTrue τ start2254 := replay_true τ ok2253 h2253
  have h2255 : TreeTrue τ start2255 := replay_true τ ok2254 h2254
  have h2256 : TreeTrue τ start2256 := replay_true τ ok2255 h2255
  have h2257 : TreeTrue τ start2257 := replay_true τ ok2256 h2256
  have h2258 : TreeTrue τ start2258 := replay_true τ ok2257 h2257
  have h2259 : TreeTrue τ start2259 := replay_true τ ok2258 h2258
  have h2260 : TreeTrue τ start2260 := replay_true τ ok2259 h2259
  have h2261 : TreeTrue τ start2261 := replay_true τ ok2260 h2260
  have h2262 : TreeTrue τ start2262 := replay_true τ ok2261 h2261
  have h2263 : TreeTrue τ start2263 := replay_true τ ok2262 h2262
  have h2264 : TreeTrue τ start2264 := replay_true τ ok2263 h2263
  have h2265 : TreeTrue τ start2265 := replay_true τ ok2264 h2264
  have h2266 : TreeTrue τ start2266 := replay_true τ ok2265 h2265
  have h2267 : TreeTrue τ start2267 := replay_true τ ok2266 h2266
  have h2268 : TreeTrue τ start2268 := replay_true τ ok2267 h2267
  have h2269 : TreeTrue τ start2269 := replay_true τ ok2268 h2268
  have h2270 : TreeTrue τ start2270 := replay_true τ ok2269 h2269
  have h2271 : TreeTrue τ start2271 := replay_true τ ok2270 h2270
  have h2272 : TreeTrue τ start2272 := cp_true τ ok2271 h2271
  exact h2272
#print axioms steps70
end Snake9.ReplayFull161
