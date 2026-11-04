import ReplayCheck161_02336
import ReplayCheck161_02340
import ReplayCheck161_02344
import ReplayCheck161_02348
import ReplayCheck161_02352
import ReplayCheck161_02356
import ReplayCheck161_02360
import ReplayCheck161_02364
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (TreeTrue)
open Snake9.LratFast144
theorem steps73 (τ : Nat → Bool) (h2336 : TreeTrue τ start2336) : TreeTrue τ start2368 := by
  have h2337 : TreeTrue τ start2337 := replay_true τ ok2336 h2336
  have h2338 : TreeTrue τ start2338 := replay_true τ ok2337 h2337
  have h2339 : TreeTrue τ start2339 := replay_true τ ok2338 h2338
  have h2340 : TreeTrue τ start2340 := replay_true τ ok2339 h2339
  have h2341 : TreeTrue τ start2341 := replay_true τ ok2340 h2340
  have h2342 : TreeTrue τ start2342 := replay_true τ ok2341 h2341
  have h2343 : TreeTrue τ start2343 := replay_true τ ok2342 h2342
  have h2344 : TreeTrue τ start2344 := replay_true τ ok2343 h2343
  have h2345 : TreeTrue τ start2345 := replay_true τ ok2344 h2344
  have h2346 : TreeTrue τ start2346 := replay_true τ ok2345 h2345
  have h2347 : TreeTrue τ start2347 := replay_true τ ok2346 h2346
  have h2348 : TreeTrue τ start2348 := replay_true τ ok2347 h2347
  have h2349 : TreeTrue τ start2349 := replay_true τ ok2348 h2348
  have h2350 : TreeTrue τ start2350 := replay_true τ ok2349 h2349
  have h2351 : TreeTrue τ start2351 := replay_true τ ok2350 h2350
  have h2352 : TreeTrue τ start2352 := replay_true τ ok2351 h2351
  have h2353 : TreeTrue τ start2353 := replay_true τ ok2352 h2352
  have h2354 : TreeTrue τ start2354 := replay_true τ ok2353 h2353
  have h2355 : TreeTrue τ start2355 := replay_true τ ok2354 h2354
  have h2356 : TreeTrue τ start2356 := replay_true τ ok2355 h2355
  have h2357 : TreeTrue τ start2357 := replay_true τ ok2356 h2356
  have h2358 : TreeTrue τ start2358 := replay_true τ ok2357 h2357
  have h2359 : TreeTrue τ start2359 := replay_true τ ok2358 h2358
  have h2360 : TreeTrue τ start2360 := replay_true τ ok2359 h2359
  have h2361 : TreeTrue τ start2361 := replay_true τ ok2360 h2360
  have h2362 : TreeTrue τ start2362 := replay_true τ ok2361 h2361
  have h2363 : TreeTrue τ start2363 := replay_true τ ok2362 h2362
  have h2364 : TreeTrue τ start2364 := replay_true τ ok2363 h2363
  have h2365 : TreeTrue τ start2365 := replay_true τ ok2364 h2364
  have h2366 : TreeTrue τ start2366 := replay_true τ ok2365 h2365
  have h2367 : TreeTrue τ start2367 := replay_true τ ok2366 h2366
  have h2368 : TreeTrue τ start2368 := cp_true τ ok2367 h2367
  exact h2368
#print axioms steps73
end Snake9.ReplayFull161
