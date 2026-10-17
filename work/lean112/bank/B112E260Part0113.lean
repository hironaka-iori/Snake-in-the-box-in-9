import B112E260Part0112
namespace B112E260
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c9335 : List Lit := [(1003, false), (865, true), (1122, true), (206, true), (7, true), (1002, false), (499, true), (403, true), (849, false), (216, true)]
theorem step9335 (p : Nat → Bool) (h : Constraints p) : clause p c9335 = true :=
  Snake9.LocalRup.prove_clause [c9057, c4650] c9335 (by decide) p (sat_cons (step9057 p h) (sat_cons (step4650 p h) (sat_nil p)))
def c9336 : List Lit := [(38, false), (49, false), (2, false)]
theorem step9336 (p : Nat → Bool) (h : Constraints p) : clause p c9336 = true :=
  Snake9.LocalRup.prove_clause [c8285, c4159] c9336 (by decide) p (sat_cons (step8285 p h) (sat_cons (step4159 p h) (sat_nil p)))
def c9337 : List Lit := [(4, true), (49, false), (2, false), (129, true)]
theorem step9337 (p : Nat → Bool) (h : Constraints p) : clause p c9337 = true :=
  Snake9.LocalRup.prove_clause [c8285, c4452] c9337 (by decide) p (sat_cons (step8285 p h) (sat_cons (step4452 p h) (sat_nil p)))
def c9338 : List Lit := [(2, false), (56, false), (21, false), (129, true)]
theorem step9338 (p : Nat → Bool) (h : Constraints p) : clause p c9338 = true :=
  Snake9.LocalRup.prove_clause [c8285, c4444] c9338 (by decide) p (sat_cons (step8285 p h) (sat_cons (step4444 p h) (sat_nil p)))
def c9339 : List Lit := [(38, false), (56, false), (2, false)]
theorem step9339 (p : Nat → Bool) (h : Constraints p) : clause p c9339 = true :=
  Snake9.LocalRup.prove_clause [c8285, c4230] c9339 (by decide) p (sat_cons (step8285 p h) (sat_cons (step4230 p h) (sat_nil p)))
def c9340 : List Lit := [(43, true), (56, false), (7, true), (910, false), (341, true)]
theorem step9340 (p : Nat → Bool) (h : Constraints p) : clause p c9340 = true :=
  Snake9.LocalRup.prove_clause [c8285, c4641] c9340 (by decide) p (sat_cons (step8285 p h) (sat_cons (step4641 p h) (sat_nil p)))
def c9341 : List Lit := [(49, false), (43, true), (178, false)]
theorem step9341 (p : Nat → Bool) (h : Constraints p) : clause p c9341 = true :=
  Snake9.LocalRup.prove_clause [c8286, c4843] c9341 (by decide) p (sat_cons (step8286 p h) (sat_cons (step4843 p h) (sat_nil p)))
def c9342 : List Lit := [(73, true), (1121, true), (881, false), (62, false), (849, false), (877, true), (956, true), (501, true), (957, true)]
theorem step9342 (p : Nat → Bool) (h : Constraints p) : clause p c9342 = true :=
  Snake9.LocalRup.prove_clause [c9057, c4840] c9342 (by decide) p (sat_cons (step9057 p h) (sat_cons (step4840 p h) (sat_nil p)))
def c9343 : List Lit := [(859, false), (864, true), (934, true), (49, true), (178, true), (854, false)]
theorem step9343 (p : Nat → Bool) (h : Constraints p) : clause p c9343 = true :=
  Snake9.LocalRup.prove_clause [c9057, c4013] c9343 (by decide) p (sat_cons (step9057 p h) (sat_cons (step4013 p h) (sat_nil p)))
def c9344 : List Lit := [(856, true), (15, false)]
theorem step9344 (p : Nat → Bool) (h : Constraints p) : clause p c9344 = true :=
  Snake9.LocalRup.prove_clause [c9057, c3995] c9344 (by decide) p (sat_cons (step9057 p h) (sat_cons (step3995 p h) (sat_nil p)))
def c9345 : List Lit := [(863, true), (849, false)]
theorem step9345 (p : Nat → Bool) (h : Constraints p) : clause p c9345 = true :=
  Snake9.LocalRup.prove_clause [c9057, c3988] c9345 (by decide) p (sat_cons (step9057 p h) (sat_cons (step3988 p h) (sat_nil p)))
def c9346 : List Lit := [(48, false), (28, false), (854, false), (865, true)]
theorem step9346 (p : Nat → Bool) (h : Constraints p) : clause p c9346 = true :=
  Snake9.LocalRup.prove_clause [c9057, c4143] c9346 (by decide) p (sat_cons (step9057 p h) (sat_cons (step4143 p h) (sat_nil p)))
def c9347 : List Lit := [(89, false), (865, true), (854, false), (849, false)]
theorem step9347 (p : Nat → Bool) (h : Constraints p) : clause p c9347 = true :=
  Snake9.LocalRup.prove_clause [c9057, c4190] c9347 (by decide) p (sat_cons (step9057 p h) (sat_cons (step4190 p h) (sat_nil p)))
def c9348 : List Lit := [(1, false), (898, true), (851, false), (877, false), (871, false)]
theorem step9348 (p : Nat → Bool) (h : Constraints p) : clause p c9348 = true :=
  Snake9.LocalRup.prove_clause [c9057, c4441] c9348 (by decide) p (sat_cons (step9057 p h) (sat_cons (step4441 p h) (sat_nil p)))
def c9349 : List Lit := [(897, true), (48, false), (877, false), (886, false), (873, false)]
theorem step9349 (p : Nat → Bool) (h : Constraints p) : clause p c9349 = true :=
  Snake9.LocalRup.prove_clause [c9057, c4863] c9349 (by decide) p (sat_cons (step9057 p h) (sat_cons (step4863 p h) (sat_nil p)))
def c9350 : List Lit := [(898, true), (871, false), (881, false), (854, false), (864, false), (849, false)]
theorem step9350 (p : Nat → Bool) (h : Constraints p) : clause p c9350 = true :=
  Snake9.LocalRup.prove_clause [c9057, c4431] c9350 (by decide) p (sat_cons (step9057 p h) (sat_cons (step4431 p h) (sat_nil p)))
def c9351 : List Lit := [(897, true), (48, false), (854, false)]
theorem step9351 (p : Nat → Bool) (h : Constraints p) : clause p c9351 = true :=
  Snake9.LocalRup.prove_clause [c9057, c4144] c9351 (by decide) p (sat_cons (step9057 p h) (sat_cons (step4144 p h) (sat_nil p)))
def c9352 : List Lit := [(48, false), (898, true), (882, false), (854, false)]
theorem step9352 (p : Nat → Bool) (h : Constraints p) : clause p c9352 = true :=
  Snake9.LocalRup.prove_clause [c9057, c4009] c9352 (by decide) p (sat_cons (step9057 p h) (sat_cons (step4009 p h) (sat_nil p)))
def c9353 : List Lit := [(1, false), (89, false), (857, true)]
theorem step9353 (p : Nat → Bool) (h : Constraints p) : clause p c9353 = true :=
  Snake9.LocalRup.prove_clause [c9057, c4125] c9353 (by decide) p (sat_cons (step9057 p h) (sat_cons (step4125 p h) (sat_nil p)))
def c9354 : List Lit := [(864, true), (28, false), (849, false)]
theorem step9354 (p : Nat → Bool) (h : Constraints p) : clause p c9354 = true :=
  Snake9.LocalRup.prove_clause [c9057, c4807] c9354 (by decide) p (sat_cons (step9057 p h) (sat_cons (step4807 p h) (sat_nil p)))
def c9355 : List Lit := [(89, false), (864, true), (849, false)]
theorem step9355 (p : Nat → Bool) (h : Constraints p) : clause p c9355 = true :=
  Snake9.LocalRup.prove_clause [c9057, c4123] c9355 (by decide) p (sat_cons (step9057 p h) (sat_cons (step4123 p h) (sat_nil p)))
def c9356 : List Lit := [(886, true), (48, false), (877, false), (882, true)]
theorem step9356 (p : Nat → Bool) (h : Constraints p) : clause p c9356 = true :=
  Snake9.LocalRup.prove_clause [c9057, c4142] c9356 (by decide) p (sat_cons (step9057 p h) (sat_cons (step4142 p h) (sat_nil p)))
def c9357 : List Lit := [(860, false), (871, false), (881, false), (899, true), (855, false), (849, false)]
theorem step9357 (p : Nat → Bool) (h : Constraints p) : clause p c9357 = true :=
  Snake9.LocalRup.prove_clause [c9057, c4834] c9357 (by decide) p (sat_cons (step9057 p h) (sat_cons (step4834 p h) (sat_nil p)))
def c9358 : List Lit := [(48, false), (1, true), (887, true), (882, false), (854, false), (899, true), (56, false)]
theorem step9358 (p : Nat → Bool) (h : Constraints p) : clause p c9358 = true :=
  Snake9.LocalRup.prove_clause [c9057, c5489] c9358 (by decide) p (sat_cons (step9057 p h) (sat_cons (step5489 p h) (sat_nil p)))
def c9359 : List Lit := [(48, false), (866, true), (15, false), (849, false), (854, false)]
theorem step9359 (p : Nat → Bool) (h : Constraints p) : clause p c9359 = true :=
  Snake9.LocalRup.prove_clause [c9057, c6265] c9359 (by decide) p (sat_cons (step9057 p h) (sat_cons (step6265 p h) (sat_nil p)))
def c9360 : List Lit := [(864, true), (849, false), (858, false), (15, false)]
theorem step9360 (p : Nat → Bool) (h : Constraints p) : clause p c9360 = true :=
  Snake9.LocalRup.prove_clause [c9057, c6024] c9360 (by decide) p (sat_cons (step9057 p h) (sat_cons (step6024 p h) (sat_nil p)))
def c9361 : List Lit := [(48, false), (882, true), (899, true), (854, false), (877, false), (849, false)]
theorem step9361 (p : Nat → Bool) (h : Constraints p) : clause p c9361 = true :=
  Snake9.LocalRup.prove_clause [c9057, c6422] c9361 (by decide) p (sat_cons (step9057 p h) (sat_cons (step6422 p h) (sat_nil p)))
def c9362 : List Lit := [(897, true), (48, false), (877, false), (886, false)]
theorem step9362 (p : Nat → Bool) (h : Constraints p) : clause p c9362 = true :=
  Snake9.LocalRup.prove_clause [c9057, c5464] c9362 (by decide) p (sat_cons (step9057 p h) (sat_cons (step5464 p h) (sat_nil p)))
def c9363 : List Lit := [(48, false), (28, false), (866, true), (849, false), (854, false)]
theorem step9363 (p : Nat → Bool) (h : Constraints p) : clause p c9363 = true :=
  Snake9.LocalRup.prove_clause [c9057, c6252] c9363 (by decide) p (sat_cons (step9057 p h) (sat_cons (step6252 p h) (sat_nil p)))
def c9364 : List Lit := [(887, false), (15, false), (898, false), (62, false), (955, false), (48, false), (501, true)]
theorem step9364 (p : Nat → Bool) (h : Constraints p) : clause p c9364 = true :=
  Snake9.LocalRup.prove_clause [c9057, c5388] c9364 (by decide) p (sat_cons (step9057 p h) (sat_cons (step5388 p h) (sat_nil p)))
def c9365 : List Lit := [(28, true), (956, false), (15, false), (849, false), (501, true), (157, true), (854, false)]
theorem step9365 (p : Nat → Bool) (h : Constraints p) : clause p c9365 = true :=
  Snake9.LocalRup.prove_clause [c9057, c6189] c9365 (by decide) p (sat_cons (step9057 p h) (sat_cons (step6189 p h) (sat_nil p)))
def c9366 : List Lit := [(501, true), (48, false), (849, false), (28, false), (1122, true), (866, true), (62, false)]
theorem step9366 (p : Nat → Bool) (h : Constraints p) : clause p c9366 = true :=
  Snake9.LocalRup.prove_clause [c9057, c6351] c9366 (by decide) p (sat_cons (step9057 p h) (sat_cons (step6351 p h) (sat_nil p)))
def c9367 : List Lit := [(10, true), (864, true), (854, false), (28, false)]
theorem step9367 (p : Nat → Bool) (h : Constraints p) : clause p c9367 = true :=
  Snake9.LocalRup.prove_clause [c9057, c6119] c9367 (by decide) p (sat_cons (step9057 p h) (sat_cons (step6119 p h) (sat_nil p)))
def c9368 : List Lit := [(856, true), (888, true), (877, false), (871, false)]
theorem step9368 (p : Nat → Bool) (h : Constraints p) : clause p c9368 = true :=
  Snake9.LocalRup.prove_clause [c9057, c5146] c9368 (by decide) p (sat_cons (step9057 p h) (sat_cons (step5146 p h) (sat_nil p)))
def c9369 : List Lit := [(897, true), (871, false), (858, false), (849, false)]
theorem step9369 (p : Nat → Bool) (h : Constraints p) : clause p c9369 = true :=
  Snake9.LocalRup.prove_clause [c9057, c6572] c9369 (by decide) p (sat_cons (step9057 p h) (sat_cons (step6572 p h) (sat_nil p)))
def c9370 : List Lit := [(898, true), (871, false), (881, false), (849, false), (28, false)]
theorem step9370 (p : Nat → Bool) (h : Constraints p) : clause p c9370 = true :=
  Snake9.LocalRup.prove_clause [c9057, c6585] c9370 (by decide) p (sat_cons (step9057 p h) (sat_cons (step6585 p h) (sat_nil p)))
def c9371 : List Lit := [(42, true), (7, false), (51, false)]
theorem step9371 (p : Nat → Bool) (h : Constraints p) : clause p c9371 = true :=
  Snake9.LocalRup.prove_clause [c8286, c5075] c9371 (by decide) p (sat_cons (step8286 p h) (sat_cons (step5075 p h) (sat_nil p)))
def c9372 : List Lit := [(897, true), (28, false), (881, false), (849, false)]
theorem step9372 (p : Nat → Bool) (h : Constraints p) : clause p c9372 = true :=
  Snake9.LocalRup.prove_clause [c9057, c6607] c9372 (by decide) p (sat_cons (step9057 p h) (sat_cons (step6607 p h) (sat_nil p)))
def c9373 : List Lit := [(41, true), (15, false), (62, false), (899, true), (877, false), (5, true), (852, false), (1121, true), (7, true), (51, false)]
theorem step9373 (p : Nat → Bool) (h : Constraints p) : clause p c9373 = true :=
  Snake9.LocalRup.prove_clause [c9057, c5054] c9373 (by decide) p (sat_cons (step9057 p h) (sat_cons (step5054 p h) (sat_nil p)))
def c9374 : List Lit := [(43, true), (56, false), (17, true), (42, false), (343, true)]
theorem step9374 (p : Nat → Bool) (h : Constraints p) : clause p c9374 = true :=
  Snake9.LocalRup.prove_clause [c8290, c5179] c9374 (by decide) p (sat_cons (step8290 p h) (sat_cons (step5179 p h) (sat_nil p)))
def c9375 : List Lit := [(49, true), (930, true), (877, false), (178, true), (15, true)]
theorem step9375 (p : Nat → Bool) (h : Constraints p) : clause p c9375 = true :=
  Snake9.LocalRup.prove_clause [c9057, c8285, c5068] c9375 (by decide) p (sat_cons (step9057 p h) (sat_cons (step8285 p h) (sat_cons (step5068 p h) (sat_nil p))))
def c9376 : List Lit := [(930, true), (49, true), (62, false), (15, true), (178, true)]
theorem step9376 (p : Nat → Bool) (h : Constraints p) : clause p c9376 = true :=
  Snake9.LocalRup.prove_clause [c8285, c5065] c9376 (by decide) p (sat_cons (step8285 p h) (sat_cons (step5065 p h) (sat_nil p)))
def c9377 : List Lit := [(10, true), (863, true), (28, false)]
theorem step9377 (p : Nat → Bool) (h : Constraints p) : clause p c9377 = true :=
  Snake9.LocalRup.prove_clause [c9057, c6112] c9377 (by decide) p (sat_cons (step9057 p h) (sat_cons (step6112 p h) (sat_nil p)))
def c9378 : List Lit := [(957, false), (62, false), (887, false), (501, true), (896, false)]
theorem step9378 (p : Nat → Bool) (h : Constraints p) : clause p c9378 = true :=
  Snake9.LocalRup.prove_clause [c9057, c5116] c9378 (by decide) p (sat_cons (step9057 p h) (sat_cons (step5116 p h) (sat_nil p)))
def c9379 : List Lit := [(897, true), (10, true), (873, false), (849, false), (854, false)]
theorem step9379 (p : Nat → Bool) (h : Constraints p) : clause p c9379 = true :=
  Snake9.LocalRup.prove_clause [c9057, c5994] c9379 (by decide) p (sat_cons (step9057 p h) (sat_cons (step5994 p h) (sat_nil p)))
def c9380 : List Lit := [(865, true), (855, false), (856, false), (15, false)]
theorem step9380 (p : Nat → Bool) (h : Constraints p) : clause p c9380 = true :=
  Snake9.LocalRup.prove_clause [c9057, c6102] c9380 (by decide) p (sat_cons (step9057 p h) (sat_cons (step6102 p h) (sat_nil p)))
def c9381 : List Lit := [(32, true), (17, true), (62, false)]
theorem step9381 (p : Nat → Bool) (h : Constraints p) : clause p c9381 = true :=
  Snake9.LocalRup.prove_clause [c8285, c5440] c9381 (by decide) p (sat_cons (step8285 p h) (sat_cons (step5440 p h) (sat_nil p)))
def c9382 : List Lit := [(1, false), (933, true), (51, true), (175, true)]
theorem step9382 (p : Nat → Bool) (h : Constraints p) : clause p c9382 = true :=
  Snake9.LocalRup.prove_clause [c9057, c7032] c9382 (by decide) p (sat_cons (step9057 p h) (sat_cons (step7032 p h) (sat_nil p)))
def c9383 : List Lit := [(932, true), (1, false)]
theorem step9383 (p : Nat → Bool) (h : Constraints p) : clause p c9383 = true :=
  Snake9.LocalRup.prove_clause [c9057, c7051] c9383 (by decide) p (sat_cons (step9057 p h) (sat_cons (step7051 p h) (sat_nil p)))
def c9384 : List Lit := [(1, false), (6, false), (1122, true), (62, false), (51, false), (15, false)]
theorem step9384 (p : Nat → Bool) (h : Constraints p) : clause p c9384 = true :=
  Snake9.LocalRup.prove_clause [c9057, c7054] c9384 (by decide) p (sat_cons (step9057 p h) (sat_cons (step7054 p h) (sat_nil p)))
def c9385 : List Lit := [(501, true), (1122, true), (955, false), (849, false), (6, false), (887, false), (62, false)]
theorem step9385 (p : Nat → Bool) (h : Constraints p) : clause p c9385 = true :=
  Snake9.LocalRup.prove_clause [c9057, c7056] c9385 (by decide) p (sat_cons (step9057 p h) (sat_cons (step7056 p h) (sat_nil p)))
def c9386 : List Lit := [(48, false), (857, true), (899, true), (882, false), (854, false), (849, false)]
theorem step9386 (p : Nat → Bool) (h : Constraints p) : clause p c9386 = true :=
  Snake9.LocalRup.prove_clause [c9057, c7079] c9386 (by decide) p (sat_cons (step9057 p h) (sat_cons (step7079 p h) (sat_nil p)))
def c9387 : List Lit := [(15, false), (1, false), (886, false), (1122, true), (854, true), (947, true), (48, true), (943, true), (62, true), (6, false), (21, false), (5, true)]
theorem step9387 (p : Nat → Bool) (h : Constraints p) : clause p c9387 = true :=
  Snake9.LocalRup.prove_clause [c9057, c7103] c9387 (by decide) p (sat_cons (step9057 p h) (sat_cons (step7103 p h) (sat_nil p)))
def c9388 : List Lit := [(856, true), (28, false)]
theorem step9388 (p : Nat → Bool) (h : Constraints p) : clause p c9388 = true :=
  Snake9.LocalRup.prove_clause [c9057, c7108] c9388 (by decide) p (sat_cons (step9057 p h) (sat_cons (step7108 p h) (sat_nil p)))
def c9389 : List Lit := [(501, true), (887, false), (62, false), (28, true), (955, false), (311, true), (854, false), (941, true), (48, false)]
theorem step9389 (p : Nat → Bool) (h : Constraints p) : clause p c9389 = true :=
  Snake9.LocalRup.prove_clause [c9057, c8287, c7226] c9389 (by decide) p (sat_cons (step9057 p h) (sat_cons (step8287 p h) (sat_cons (step7226 p h) (sat_nil p))))
def c9390 : List Lit := [(48, false), (855, false), (865, true)]
theorem step9390 (p : Nat → Bool) (h : Constraints p) : clause p c9390 = true :=
  Snake9.LocalRup.prove_clause [c9057, c7228] c9390 (by decide) p (sat_cons (step9057 p h) (sat_cons (step7228 p h) (sat_nil p)))
def c9391 : List Lit := [(863, true), (15, false)]
theorem step9391 (p : Nat → Bool) (h : Constraints p) : clause p c9391 = true :=
  Snake9.LocalRup.prove_clause [c9057, c7240] c9391 (by decide) p (sat_cons (step9057 p h) (sat_cons (step7240 p h) (sat_nil p)))
def c9392 : List Lit := [(375, false), (30, false), (28, true), (877, true), (956, false), (874, true), (1122, true), (62, false)]
theorem step9392 (p : Nat → Bool) (h : Constraints p) : clause p c9392 = true :=
  Snake9.LocalRup.prove_clause [c9057, c7249] c9392 (by decide) p (sat_cons (step9057 p h) (sat_cons (step7249 p h) (sat_nil p)))
def c9393 : List Lit := [(40, true), (7, false), (5, false), (134, true)]
theorem step9393 (p : Nat → Bool) (h : Constraints p) : clause p c9393 = true :=
  Snake9.LocalRup.prove_clause [c8286, c7651] c9393 (by decide) p (sat_cons (step8286 p h) (sat_cons (step7651 p h) (sat_nil p)))
def c9394 : List Lit := [(883, false), (871, false), (854, false), (899, true)]
theorem step9394 (p : Nat → Bool) (h : Constraints p) : clause p c9394 = true :=
  Snake9.LocalRup.prove_clause [c9057, c7768] c9394 (by decide) p (sat_cons (step9057 p h) (sat_cons (step7768 p h) (sat_nil p)))
def c9395 : List Lit := [(898, true), (882, false), (854, false), (871, false)]
theorem step9395 (p : Nat → Bool) (h : Constraints p) : clause p c9395 = true :=
  Snake9.LocalRup.prove_clause [c9057, c7769] c9395 (by decide) p (sat_cons (step9057 p h) (sat_cons (step7769 p h) (sat_nil p)))
def c9396 : List Lit := [(897, true), (871, false), (854, false), (881, false)]
theorem step9396 (p : Nat → Bool) (h : Constraints p) : clause p c9396 = true :=
  Snake9.LocalRup.prove_clause [c9057, c7774] c9396 (by decide) p (sat_cons (step9057 p h) (sat_cons (step7774 p h) (sat_nil p)))
def c9397 : List Lit := [(897, true), (881, false), (849, false), (854, false)]
theorem step9397 (p : Nat → Bool) (h : Constraints p) : clause p c9397 = true :=
  Snake9.LocalRup.prove_clause [c9057, c7811] c9397 (by decide) p (sat_cons (step9057 p h) (sat_cons (step7811 p h) (sat_nil p)))
def c9398 : List Lit := [(864, true), (849, false), (854, false)]
theorem step9398 (p : Nat → Bool) (h : Constraints p) : clause p c9398 = true :=
  Snake9.LocalRup.prove_clause [c9057, c7817] c9398 (by decide) p (sat_cons (step9057 p h) (sat_cons (step7817 p h) (sat_nil p)))
end B112E260
