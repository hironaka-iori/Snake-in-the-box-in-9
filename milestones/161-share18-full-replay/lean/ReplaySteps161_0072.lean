import ReplayCheck161_02304
import ReplayCheck161_02308
import ReplayCheck161_02312
import ReplayCheck161_02316
import ReplayCheck161_02320
import ReplayCheck161_02324
import ReplayCheck161_02328
import ReplayCheck161_02332
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (TreeTrue)
open Snake9.LratFast144
theorem steps72 (τ : Nat → Bool) (h2304 : TreeTrue τ start2304) : TreeTrue τ start2336 := by
  have h2305 : TreeTrue τ start2305 := replay_true τ ok2304 h2304
  have h2306 : TreeTrue τ start2306 := replay_true τ ok2305 h2305
  have h2307 : TreeTrue τ start2307 := replay_true τ ok2306 h2306
  have h2308 : TreeTrue τ start2308 := replay_true τ ok2307 h2307
  have h2309 : TreeTrue τ start2309 := replay_true τ ok2308 h2308
  have h2310 : TreeTrue τ start2310 := replay_true τ ok2309 h2309
  have h2311 : TreeTrue τ start2311 := replay_true τ ok2310 h2310
  have h2312 : TreeTrue τ start2312 := replay_true τ ok2311 h2311
  have h2313 : TreeTrue τ start2313 := replay_true τ ok2312 h2312
  have h2314 : TreeTrue τ start2314 := replay_true τ ok2313 h2313
  have h2315 : TreeTrue τ start2315 := replay_true τ ok2314 h2314
  have h2316 : TreeTrue τ start2316 := replay_true τ ok2315 h2315
  have h2317 : TreeTrue τ start2317 := replay_true τ ok2316 h2316
  have h2318 : TreeTrue τ start2318 := replay_true τ ok2317 h2317
  have h2319 : TreeTrue τ start2319 := replay_true τ ok2318 h2318
  have h2320 : TreeTrue τ start2320 := replay_true τ ok2319 h2319
  have h2321 : TreeTrue τ start2321 := replay_true τ ok2320 h2320
  have h2322 : TreeTrue τ start2322 := replay_true τ ok2321 h2321
  have h2323 : TreeTrue τ start2323 := replay_true τ ok2322 h2322
  have h2324 : TreeTrue τ start2324 := replay_true τ ok2323 h2323
  have h2325 : TreeTrue τ start2325 := replay_true τ ok2324 h2324
  have h2326 : TreeTrue τ start2326 := replay_true τ ok2325 h2325
  have h2327 : TreeTrue τ start2327 := replay_true τ ok2326 h2326
  have h2328 : TreeTrue τ start2328 := replay_true τ ok2327 h2327
  have h2329 : TreeTrue τ start2329 := replay_true τ ok2328 h2328
  have h2330 : TreeTrue τ start2330 := replay_true τ ok2329 h2329
  have h2331 : TreeTrue τ start2331 := replay_true τ ok2330 h2330
  have h2332 : TreeTrue τ start2332 := replay_true τ ok2331 h2331
  have h2333 : TreeTrue τ start2333 := replay_true τ ok2332 h2332
  have h2334 : TreeTrue τ start2334 := replay_true τ ok2333 h2333
  have h2335 : TreeTrue τ start2335 := replay_true τ ok2334 h2334
  have h2336 : TreeTrue τ start2336 := cp_true τ ok2335 h2335
  exact h2336
#print axioms steps72
end Snake9.ReplayFull161
