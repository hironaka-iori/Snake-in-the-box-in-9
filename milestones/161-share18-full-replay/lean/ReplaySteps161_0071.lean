import ReplayCheck161_02272
import ReplayCheck161_02276
import ReplayCheck161_02280
import ReplayCheck161_02284
import ReplayCheck161_02288
import ReplayCheck161_02292
import ReplayCheck161_02296
import ReplayCheck161_02300
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (TreeTrue)
open Snake9.LratFast144
theorem steps71 (τ : Nat → Bool) (h2272 : TreeTrue τ start2272) : TreeTrue τ start2304 := by
  have h2273 : TreeTrue τ start2273 := replay_true τ ok2272 h2272
  have h2274 : TreeTrue τ start2274 := replay_true τ ok2273 h2273
  have h2275 : TreeTrue τ start2275 := replay_true τ ok2274 h2274
  have h2276 : TreeTrue τ start2276 := replay_true τ ok2275 h2275
  have h2277 : TreeTrue τ start2277 := replay_true τ ok2276 h2276
  have h2278 : TreeTrue τ start2278 := replay_true τ ok2277 h2277
  have h2279 : TreeTrue τ start2279 := replay_true τ ok2278 h2278
  have h2280 : TreeTrue τ start2280 := replay_true τ ok2279 h2279
  have h2281 : TreeTrue τ start2281 := replay_true τ ok2280 h2280
  have h2282 : TreeTrue τ start2282 := replay_true τ ok2281 h2281
  have h2283 : TreeTrue τ start2283 := replay_true τ ok2282 h2282
  have h2284 : TreeTrue τ start2284 := replay_true τ ok2283 h2283
  have h2285 : TreeTrue τ start2285 := replay_true τ ok2284 h2284
  have h2286 : TreeTrue τ start2286 := replay_true τ ok2285 h2285
  have h2287 : TreeTrue τ start2287 := replay_true τ ok2286 h2286
  have h2288 : TreeTrue τ start2288 := replay_true τ ok2287 h2287
  have h2289 : TreeTrue τ start2289 := replay_true τ ok2288 h2288
  have h2290 : TreeTrue τ start2290 := replay_true τ ok2289 h2289
  have h2291 : TreeTrue τ start2291 := replay_true τ ok2290 h2290
  have h2292 : TreeTrue τ start2292 := replay_true τ ok2291 h2291
  have h2293 : TreeTrue τ start2293 := replay_true τ ok2292 h2292
  have h2294 : TreeTrue τ start2294 := replay_true τ ok2293 h2293
  have h2295 : TreeTrue τ start2295 := replay_true τ ok2294 h2294
  have h2296 : TreeTrue τ start2296 := replay_true τ ok2295 h2295
  have h2297 : TreeTrue τ start2297 := replay_true τ ok2296 h2296
  have h2298 : TreeTrue τ start2298 := replay_true τ ok2297 h2297
  have h2299 : TreeTrue τ start2299 := replay_true τ ok2298 h2298
  have h2300 : TreeTrue τ start2300 := replay_true τ ok2299 h2299
  have h2301 : TreeTrue τ start2301 := replay_true τ ok2300 h2300
  have h2302 : TreeTrue τ start2302 := replay_true τ ok2301 h2301
  have h2303 : TreeTrue τ start2303 := replay_true τ ok2302 h2302
  have h2304 : TreeTrue τ start2304 := cp_true τ ok2303 h2303
  exact h2304
#print axioms steps71
end Snake9.ReplayFull161
