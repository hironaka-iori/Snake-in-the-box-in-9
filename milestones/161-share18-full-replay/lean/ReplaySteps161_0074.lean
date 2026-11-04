import ReplayCheck161_02368
import ReplayCheck161_02372
import ReplayCheck161_02376
import ReplayCheck161_02380
import ReplayCheck161_02384
import ReplayCheck161_02388
import ReplayCheck161_02392
import ReplayCheck161_02396
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (TreeTrue)
open Snake9.LratFast144
theorem steps74 (τ : Nat → Bool) (h2368 : TreeTrue τ start2368) : TreeTrue τ start2400 := by
  have h2369 : TreeTrue τ start2369 := replay_true τ ok2368 h2368
  have h2370 : TreeTrue τ start2370 := replay_true τ ok2369 h2369
  have h2371 : TreeTrue τ start2371 := replay_true τ ok2370 h2370
  have h2372 : TreeTrue τ start2372 := replay_true τ ok2371 h2371
  have h2373 : TreeTrue τ start2373 := replay_true τ ok2372 h2372
  have h2374 : TreeTrue τ start2374 := replay_true τ ok2373 h2373
  have h2375 : TreeTrue τ start2375 := replay_true τ ok2374 h2374
  have h2376 : TreeTrue τ start2376 := replay_true τ ok2375 h2375
  have h2377 : TreeTrue τ start2377 := replay_true τ ok2376 h2376
  have h2378 : TreeTrue τ start2378 := replay_true τ ok2377 h2377
  have h2379 : TreeTrue τ start2379 := replay_true τ ok2378 h2378
  have h2380 : TreeTrue τ start2380 := replay_true τ ok2379 h2379
  have h2381 : TreeTrue τ start2381 := replay_true τ ok2380 h2380
  have h2382 : TreeTrue τ start2382 := replay_true τ ok2381 h2381
  have h2383 : TreeTrue τ start2383 := replay_true τ ok2382 h2382
  have h2384 : TreeTrue τ start2384 := replay_true τ ok2383 h2383
  have h2385 : TreeTrue τ start2385 := replay_true τ ok2384 h2384
  have h2386 : TreeTrue τ start2386 := replay_true τ ok2385 h2385
  have h2387 : TreeTrue τ start2387 := replay_true τ ok2386 h2386
  have h2388 : TreeTrue τ start2388 := replay_true τ ok2387 h2387
  have h2389 : TreeTrue τ start2389 := replay_true τ ok2388 h2388
  have h2390 : TreeTrue τ start2390 := replay_true τ ok2389 h2389
  have h2391 : TreeTrue τ start2391 := replay_true τ ok2390 h2390
  have h2392 : TreeTrue τ start2392 := replay_true τ ok2391 h2391
  have h2393 : TreeTrue τ start2393 := replay_true τ ok2392 h2392
  have h2394 : TreeTrue τ start2394 := replay_true τ ok2393 h2393
  have h2395 : TreeTrue τ start2395 := replay_true τ ok2394 h2394
  have h2396 : TreeTrue τ start2396 := replay_true τ ok2395 h2395
  have h2397 : TreeTrue τ start2397 := replay_true τ ok2396 h2396
  have h2398 : TreeTrue τ start2398 := replay_true τ ok2397 h2397
  have h2399 : TreeTrue τ start2399 := replay_true τ ok2398 h2398
  have h2400 : TreeTrue τ start2400 := cp_true τ ok2399 h2399
  exact h2400
#print axioms steps74
end Snake9.ReplayFull161
