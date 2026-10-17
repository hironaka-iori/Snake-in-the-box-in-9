import B112E260Part0111
namespace B112E260
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c9271 : List Lit := [(1, false), (28, false), (15, false)]
theorem step9271 (p : Nat → Bool) (h : Constraints p) : clause p c9271 = true :=
  Snake9.LocalRup.prove_clause [c9057, c86] c9271 (by decide) p (sat_cons (step9057 p h) (sat_cons (step86 p h) (sat_nil p)))
def c9272 : List Lit := [(12, false), (48, false), (15, false)]
theorem step9272 (p : Nat → Bool) (h : Constraints p) : clause p c9272 = true :=
  Snake9.LocalRup.prove_clause [c9057, c103] c9272 (by decide) p (sat_cons (step9057 p h) (sat_cons (step103 p h) (sat_nil p)))
def c9273 : List Lit := [(1, false), (48, false), (15, false)]
theorem step9273 (p : Nat → Bool) (h : Constraints p) : clause p c9273 = true :=
  Snake9.LocalRup.prove_clause [c9057, c87] c9273 (by decide) p (sat_cons (step9057 p h) (sat_cons (step87 p h) (sat_nil p)))
def c9274 : List Lit := [(857, true), (48, false), (15, false)]
theorem step9274 (p : Nat → Bool) (h : Constraints p) : clause p c9274 = true :=
  Snake9.LocalRup.prove_clause [c9057, c2591] c9274 (by decide) p (sat_cons (step9057 p h) (sat_cons (step2591 p h) (sat_nil p)))
def c9275 : List Lit := [(32, true), (908, false)]
theorem step9275 (p : Nat → Bool) (h : Constraints p) : clause p c9275 = true :=
  Snake9.LocalRup.prove_clause [c8287, c1284] c9275 (by decide) p (sat_cons (step8287 p h) (sat_cons (step1284 p h) (sat_nil p)))
def c9276 : List Lit := [(29, false), (178, true), (51, false)]
theorem step9276 (p : Nat → Bool) (h : Constraints p) : clause p c9276 = true :=
  Snake9.LocalRup.prove_clause [c9057, c2590] c9276 (by decide) p (sat_cons (step9057 p h) (sat_cons (step2590 p h) (sat_nil p)))
def c9277 : List Lit := [(889, false), (898, true)]
theorem step9277 (p : Nat → Bool) (h : Constraints p) : clause p c9277 = true :=
  Snake9.LocalRup.prove_clause [c9058, c1246] c9277 (by decide) p (sat_cons (step9058 p h) (sat_cons (step1246 p h) (sat_nil p)))
def c9278 : List Lit := [(67, true), (28, false), (155, true)]
theorem step9278 (p : Nat → Bool) (h : Constraints p) : clause p c9278 = true :=
  Snake9.LocalRup.prove_clause [c9057, c2652] c9278 (by decide) p (sat_cons (step9057 p h) (sat_cons (step2652 p h) (sat_nil p)))
def c9279 : List Lit := [(855, false), (864, true)]
theorem step9279 (p : Nat → Bool) (h : Constraints p) : clause p c9279 = true :=
  Snake9.LocalRup.prove_clause [c9057, c2651] c9279 (by decide) p (sat_cons (step9057 p h) (sat_cons (step2651 p h) (sat_nil p)))
def c9280 : List Lit := [(48, false), (28, false), (10, false)]
theorem step9280 (p : Nat → Bool) (h : Constraints p) : clause p c9280 = true :=
  Snake9.LocalRup.prove_clause [c9057, c99] c9280 (by decide) p (sat_cons (step9057 p h) (sat_cons (step99 p h) (sat_nil p)))
def c9281 : List Lit := [(12, false), (28, false), (48, false)]
theorem step9281 (p : Nat → Bool) (h : Constraints p) : clause p c9281 = true :=
  Snake9.LocalRup.prove_clause [c9057, c105] c9281 (by decide) p (sat_cons (step9057 p h) (sat_cons (step105 p h) (sat_nil p)))
def c9282 : List Lit := [(1, false), (48, false), (28, false)]
theorem step9282 (p : Nat → Bool) (h : Constraints p) : clause p c9282 = true :=
  Snake9.LocalRup.prove_clause [c9057, c89] c9282 (by decide) p (sat_cons (step9057 p h) (sat_cons (step89 p h) (sat_nil p)))
def c9283 : List Lit := [(12, false), (1, false), (48, false)]
theorem step9283 (p : Nat → Bool) (h : Constraints p) : clause p c9283 = true :=
  Snake9.LocalRup.prove_clause [c9057, c84] c9283 (by decide) p (sat_cons (step9057 p h) (sat_cons (step84 p h) (sat_nil p)))
def c9284 : List Lit := [(1, false), (10, false), (28, false)]
theorem step9284 (p : Nat → Bool) (h : Constraints p) : clause p c9284 = true :=
  Snake9.LocalRup.prove_clause [c9057, c79] c9284 (by decide) p (sat_cons (step9057 p h) (sat_cons (step79 p h) (sat_nil p)))
def c9285 : List Lit := [(12, false), (1, false), (28, false)]
theorem step9285 (p : Nat → Bool) (h : Constraints p) : clause p c9285 = true :=
  Snake9.LocalRup.prove_clause [c9057, c83] c9285 (by decide) p (sat_cons (step9057 p h) (sat_cons (step83 p h) (sat_nil p)))
def c9286 : List Lit := [(1, false), (48, false), (10, false)]
theorem step9286 (p : Nat → Bool) (h : Constraints p) : clause p c9286 = true :=
  Snake9.LocalRup.prove_clause [c9057, c80] c9286 (by decide) p (sat_cons (step9057 p h) (sat_cons (step80 p h) (sat_nil p)))
def c9287 : List Lit := [(12, false), (1, false), (15, false)]
theorem step9287 (p : Nat → Bool) (h : Constraints p) : clause p c9287 = true :=
  Snake9.LocalRup.prove_clause [c9057, c82] c9287 (by decide) p (sat_cons (step9057 p h) (sat_cons (step82 p h) (sat_nil p)))
def c9288 : List Lit := [(1, true), (28, true), (12, true), (15, true), (48, true), (89, true)]
theorem step9288 (p : Nat → Bool) (h : Constraints p) : clause p c9288 = true :=
  Snake9.LocalRup.prove_clause [c9057, c2332] c9288 (by decide) p (sat_cons (step9057 p h) (sat_cons (step2332 p h) (sat_nil p)))
def c9289 : List Lit := [(37, false), (48, false), (34, true)]
theorem step9289 (p : Nat → Bool) (h : Constraints p) : clause p c9289 = true :=
  Snake9.LocalRup.prove_clause [c8285, c2525] c9289 (by decide) p (sat_cons (step8285 p h) (sat_cons (step2525 p h) (sat_nil p)))
def c9290 : List Lit := [(110, false), (44, true), (43, false)]
theorem step9290 (p : Nat → Bool) (h : Constraints p) : clause p c9290 = true :=
  Snake9.LocalRup.prove_clause [c8286, c2589] c9290 (by decide) p (sat_cons (step8286 p h) (sat_cons (step2589 p h) (sat_nil p)))
def c9291 : List Lit := [(888, false), (897, true)]
theorem step9291 (p : Nat → Bool) (h : Constraints p) : clause p c9291 = true :=
  Snake9.LocalRup.prove_clause [c9058, c1245] c9291 (by decide) p (sat_cons (step9058 p h) (sat_cons (step1245 p h) (sat_nil p)))
def c9292 : List Lit := [(46, true), (44, true)]
theorem step9292 (p : Nat → Bool) (h : Constraints p) : clause p c9292 = true :=
  Snake9.LocalRup.prove_clause [c8288, c1291] c9292 (by decide) p (sat_cons (step8288 p h) (sat_cons (step1291 p h) (sat_nil p)))
def c9293 : List Lit := [(913, false), (915, false)]
theorem step9293 (p : Nat → Bool) (h : Constraints p) : clause p c9293 = true :=
  Snake9.LocalRup.prove_clause [c8286, c1295] c9293 (by decide) p (sat_cons (step8286 p h) (sat_cons (step1295 p h) (sat_nil p)))
def c9294 : List Lit := [(856, true), (1, false)]
theorem step9294 (p : Nat → Bool) (h : Constraints p) : clause p c9294 = true :=
  Snake9.LocalRup.prove_clause [c9057, c2985] c9294 (by decide) p (sat_cons (step9057 p h) (sat_cons (step2985 p h) (sat_nil p)))
def c9295 : List Lit := [(43, false), (40, true), (7, false)]
theorem step9295 (p : Nat → Bool) (h : Constraints p) : clause p c9295 = true :=
  Snake9.LocalRup.prove_clause [c8286, c2834] c9295 (by decide) p (sat_cons (step8286 p h) (sat_cons (step2834 p h) (sat_nil p)))
def c9296 : List Lit := [(933, true), (37, true), (175, true), (51, true)]
theorem step9296 (p : Nat → Bool) (h : Constraints p) : clause p c9296 = true :=
  Snake9.LocalRup.prove_clause [c9059, c2984] c9296 (by decide) p (sat_cons (step9059 p h) (sat_cons (step2984 p h) (sat_nil p)))
def c9297 : List Lit := [(1, false), (857, true), (15, false)]
theorem step9297 (p : Nat → Bool) (h : Constraints p) : clause p c9297 = true :=
  Snake9.LocalRup.prove_clause [c9057, c2911] c9297 (by decide) p (sat_cons (step9057 p h) (sat_cons (step2911 p h) (sat_nil p)))
def c9298 : List Lit := [(44, true), (43, false), (7, false)]
theorem step9298 (p : Nat → Bool) (h : Constraints p) : clause p c9298 = true :=
  Snake9.LocalRup.prove_clause [c8286, c3140] c9298 (by decide) p (sat_cons (step8286 p h) (sat_cons (step3140 p h) (sat_nil p)))
def c9299 : List Lit := [(41, false), (42, true), (51, false)]
theorem step9299 (p : Nat → Bool) (h : Constraints p) : clause p c9299 = true :=
  Snake9.LocalRup.prove_clause [c8286, c3177] c9299 (by decide) p (sat_cons (step8286 p h) (sat_cons (step3177 p h) (sat_nil p)))
def c9300 : List Lit := [(89, false), (864, true), (854, false)]
theorem step9300 (p : Nat → Bool) (h : Constraints p) : clause p c9300 = true :=
  Snake9.LocalRup.prove_clause [c9057, c3840] c9300 (by decide) p (sat_cons (step9057 p h) (sat_cons (step3840 p h) (sat_nil p)))
def c9301 : List Lit := [(89, false), (856, true)]
theorem step9301 (p : Nat → Bool) (h : Constraints p) : clause p c9301 = true :=
  Snake9.LocalRup.prove_clause [c9057, c3340] c9301 (by decide) p (sat_cons (step9057 p h) (sat_cons (step3340 p h) (sat_nil p)))
def c9302 : List Lit := [(856, true), (48, false)]
theorem step9302 (p : Nat → Bool) (h : Constraints p) : clause p c9302 = true :=
  Snake9.LocalRup.prove_clause [c9057, c3754] c9302 (by decide) p (sat_cons (step9057 p h) (sat_cons (step3754 p h) (sat_nil p)))
def c9303 : List Lit := [(89, false), (48, false), (857, true)]
theorem step9303 (p : Nat → Bool) (h : Constraints p) : clause p c9303 = true :=
  Snake9.LocalRup.prove_clause [c9057, c3853] c9303 (by decide) p (sat_cons (step9057 p h) (sat_cons (step3853 p h) (sat_nil p)))
def c9304 : List Lit := [(48, false), (864, true), (854, false)]
theorem step9304 (p : Nat → Bool) (h : Constraints p) : clause p c9304 = true :=
  Snake9.LocalRup.prove_clause [c9057, c3784] c9304 (by decide) p (sat_cons (step9057 p h) (sat_cons (step3784 p h) (sat_nil p)))
def c9305 : List Lit := [(89, false), (857, true), (15, false)]
theorem step9305 (p : Nat → Bool) (h : Constraints p) : clause p c9305 = true :=
  Snake9.LocalRup.prove_clause [c9057, c3339] c9305 (by decide) p (sat_cons (step9057 p h) (sat_cons (step3339 p h) (sat_nil p)))
def c9306 : List Lit := [(38, false), (2, false), (915, false)]
theorem step9306 (p : Nat → Bool) (h : Constraints p) : clause p c9306 = true :=
  Snake9.LocalRup.prove_clause [c8285, c3411] c9306 (by decide) p (sat_cons (step8285 p h) (sat_cons (step3411 p h) (sat_nil p)))
def c9307 : List Lit := [(89, false), (857, true), (28, false)]
theorem step9307 (p : Nat → Bool) (h : Constraints p) : clause p c9307 = true :=
  Snake9.LocalRup.prove_clause [c9057, c3452] c9307 (by decide) p (sat_cons (step9057 p h) (sat_cons (step3452 p h) (sat_nil p)))
def c9308 : List Lit := [(863, true), (854, false)]
theorem step9308 (p : Nat → Bool) (h : Constraints p) : clause p c9308 = true :=
  Snake9.LocalRup.prove_clause [c9057, c3337] c9308 (by decide) p (sat_cons (step9057 p h) (sat_cons (step3337 p h) (sat_nil p)))
def c9309 : List Lit := [(67, true), (29, false)]
theorem step9309 (p : Nat → Bool) (h : Constraints p) : clause p c9309 = true :=
  Snake9.LocalRup.prove_clause [c9057, c3438] c9309 (by decide) p (sat_cons (step9057 p h) (sat_cons (step3438 p h) (sat_nil p)))
def c9310 : List Lit := [(49, false), (169, true), (40, true), (62, false)]
theorem step9310 (p : Nat → Bool) (h : Constraints p) : clause p c9310 = true :=
  Snake9.LocalRup.prove_clause [c8286, c3394] c9310 (by decide) p (sat_cons (step8286 p h) (sat_cons (step3394 p h) (sat_nil p)))
def c9311 : List Lit := [(43, true), (56, false), (915, false), (169, true)]
theorem step9311 (p : Nat → Bool) (h : Constraints p) : clause p c9311 = true :=
  Snake9.LocalRup.prove_clause [c8285, c3382] c9311 (by decide) p (sat_cons (step8285 p h) (sat_cons (step3382 p h) (sat_nil p)))
def c9312 : List Lit := [(42, true), (43, true), (51, false)]
theorem step9312 (p : Nat → Bool) (h : Constraints p) : clause p c9312 = true :=
  Snake9.LocalRup.prove_clause [c8286, c3747] c9312 (by decide) p (sat_cons (step8286 p h) (sat_cons (step3747 p h) (sat_nil p)))
def c9313 : List Lit := [(66, false), (28, false), (155, true), (71, false)]
theorem step9313 (p : Nat → Bool) (h : Constraints p) : clause p c9313 = true :=
  Snake9.LocalRup.prove_clause [c9057, c3369] c9313 (by decide) p (sat_cons (step9057 p h) (sat_cons (step3369 p h) (sat_nil p)))
def c9314 : List Lit := [(1, false), (48, false), (921, true), (854, false)]
theorem step9314 (p : Nat → Bool) (h : Constraints p) : clause p c9314 = true :=
  Snake9.LocalRup.prove_clause [c9057, c3787] c9314 (by decide) p (sat_cons (step9057 p h) (sat_cons (step3787 p h) (sat_nil p)))
def c9315 : List Lit := [(955, true), (932, false), (51, true), (175, true), (34, true)]
theorem step9315 (p : Nat → Bool) (h : Constraints p) : clause p c9315 = true :=
  Snake9.LocalRup.prove_clause [c9057, c6889] c9315 (by decide) p (sat_cons (step9057 p h) (sat_cons (step6889 p h) (sat_nil p)))
def c9316 : List Lit := [(855, false), (865, true), (28, false), (12, true)]
theorem step9316 (p : Nat → Bool) (h : Constraints p) : clause p c9316 = true :=
  Snake9.LocalRup.prove_clause [c9057, c3428] c9316 (by decide) p (sat_cons (step9057 p h) (sat_cons (step3428 p h) (sat_nil p)))
def c9317 : List Lit := [(44, true), (178, true), (51, false)]
theorem step9317 (p : Nat → Bool) (h : Constraints p) : clause p c9317 = true :=
  Snake9.LocalRup.prove_clause [c8286, c4642] c9317 (by decide) p (sat_cons (step8286 p h) (sat_cons (step4642 p h) (sat_nil p)))
def c9318 : List Lit := [(16, true), (44, true), (7, false), (169, true)]
theorem step9318 (p : Nat → Bool) (h : Constraints p) : clause p c9318 = true :=
  Snake9.LocalRup.prove_clause [c8286, c4802] c9318 (by decide) p (sat_cons (step8286 p h) (sat_cons (step4802 p h) (sat_nil p)))
def c9319 : List Lit := [(887, true), (864, true), (877, false), (16, true)]
theorem step9319 (p : Nat → Bool) (h : Constraints p) : clause p c9319 = true :=
  Snake9.LocalRup.prove_clause [c9057, c4084] c9319 (by decide) p (sat_cons (step9057 p h) (sat_cons (step4084 p h) (sat_nil p)))
def c9320 : List Lit := [(864, true), (48, false), (15, false)]
theorem step9320 (p : Nat → Bool) (h : Constraints p) : clause p c9320 = true :=
  Snake9.LocalRup.prove_clause [c9057, c4073] c9320 (by decide) p (sat_cons (step9057 p h) (sat_cons (step4073 p h) (sat_nil p)))
def c9321 : List Lit := [(865, true), (28, false), (849, false), (15, false)]
theorem step9321 (p : Nat → Bool) (h : Constraints p) : clause p c9321 = true :=
  Snake9.LocalRup.prove_clause [c9057, c3994] c9321 (by decide) p (sat_cons (step9057 p h) (sat_cons (step3994 p h) (sat_nil p)))
def c9322 : List Lit := [(864, true), (28, false), (15, false)]
theorem step9322 (p : Nat → Bool) (h : Constraints p) : clause p c9322 = true :=
  Snake9.LocalRup.prove_clause [c9057, c4074] c9322 (by decide) p (sat_cons (step9057 p h) (sat_cons (step4074 p h) (sat_nil p)))
def c9323 : List Lit := [(1, false), (898, true), (15, false), (873, false), (851, false), (877, false)]
theorem step9323 (p : Nat → Bool) (h : Constraints p) : clause p c9323 = true :=
  Snake9.LocalRup.prove_clause [c9057, c4440] c9323 (by decide) p (sat_cons (step9057 p h) (sat_cons (step4440 p h) (sat_nil p)))
def c9324 : List Lit := [(48, false), (865, true), (854, false), (15, false)]
theorem step9324 (p : Nat → Bool) (h : Constraints p) : clause p c9324 = true :=
  Snake9.LocalRup.prove_clause [c9057, c4454] c9324 (by decide) p (sat_cons (step9057 p h) (sat_cons (step4454 p h) (sat_nil p)))
def c9325 : List Lit := [(48, false), (877, false), (899, true), (849, false), (873, false), (15, false)]
theorem step9325 (p : Nat → Bool) (h : Constraints p) : clause p c9325 = true :=
  Snake9.LocalRup.prove_clause [c9057, c4804] c9325 (by decide) p (sat_cons (step9057 p h) (sat_cons (step4804 p h) (sat_nil p)))
def c9326 : List Lit := [(865, true), (849, false), (854, false), (15, false)]
theorem step9326 (p : Nat → Bool) (h : Constraints p) : clause p c9326 = true :=
  Snake9.LocalRup.prove_clause [c9057, c4353] c9326 (by decide) p (sat_cons (step9057 p h) (sat_cons (step4353 p h) (sat_nil p)))
def c9327 : List Lit := [(854, true), (24, false), (62, false)]
theorem step9327 (p : Nat → Bool) (h : Constraints p) : clause p c9327 = true :=
  Snake9.LocalRup.prove_clause [c9057, c4119] c9327 (by decide) p (sat_cons (step9057 p h) (sat_cons (step4119 p h) (sat_nil p)))
def c9328 : List Lit := [(7, false), (24, false), (134, true), (62, false)]
theorem step9328 (p : Nat → Bool) (h : Constraints p) : clause p c9328 = true :=
  Snake9.LocalRup.prove_clause [c8286, c4747] c9328 (by decide) p (sat_cons (step8286 p h) (sat_cons (step4747 p h) (sat_nil p)))
def c9329 : List Lit := [(42, true), (7, false), (173, true), (5, false)]
theorem step9329 (p : Nat → Bool) (h : Constraints p) : clause p c9329 = true :=
  Snake9.LocalRup.prove_clause [c8286, c4767] c9329 (by decide) p (sat_cons (step8286 p h) (sat_cons (step4767 p h) (sat_nil p)))
def c9330 : List Lit := [(932, true), (7, false), (175, true), (169, true)]
theorem step9330 (p : Nat → Bool) (h : Constraints p) : clause p c9330 = true :=
  Snake9.LocalRup.prove_clause [c8285, c4480] c9330 (by decide) p (sat_cons (step8285 p h) (sat_cons (step4480 p h) (sat_nil p)))
def c9331 : List Lit := [(43, false), (7, false), (62, false), (134, true)]
theorem step9331 (p : Nat → Bool) (h : Constraints p) : clause p c9331 = true :=
  Snake9.LocalRup.prove_clause [c8286, c4844] c9331 (by decide) p (sat_cons (step8286 p h) (sat_cons (step4844 p h) (sat_nil p)))
def c9332 : List Lit := [(928, true), (36, false), (51, false), (42, true)]
theorem step9332 (p : Nat → Bool) (h : Constraints p) : clause p c9332 = true :=
  Snake9.LocalRup.prove_clause [c8286, c4544] c9332 (by decide) p (sat_cons (step8286 p h) (sat_cons (step4544 p h) (sat_nil p)))
def c9333 : List Lit := [(42, true), (933, true), (17, false), (175, true), (178, true), (16, false), (36, false), (53, false)]
theorem step9333 (p : Nat → Bool) (h : Constraints p) : clause p c9333 = true :=
  Snake9.LocalRup.prove_clause [c8286, c4177] c9333 (by decide) p (sat_cons (step8286 p h) (sat_cons (step4177 p h) (sat_nil p)))
def c9334 : List Lit := [(852, false), (48, false), (854, false), (899, true), (882, false)]
theorem step9334 (p : Nat → Bool) (h : Constraints p) : clause p c9334 = true :=
  Snake9.LocalRup.prove_clause [c9057, c4630] c9334 (by decide) p (sat_cons (step9057 p h) (sat_cons (step4630 p h) (sat_nil p)))
end B112E260
