import B112E203Part0032
namespace B112E203
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c3385 : List Lit := [(919, true)]
theorem step3385 (p : Nat → Bool) (h : Constraints p) : clause p c3385 = true :=
  Snake9.LocalRup.prove_clause [c3384, c2969, c2033] c3385 (by decide) p (sat_cons (step3384 p h) (sat_cons (step2969 p h) (sat_cons (step2033 p h) (sat_nil p))))
def c3386 : List Lit := [(1055, false)]
theorem step3386 (p : Nat → Bool) (h : Constraints p) : clause p c3386 = true :=
  Snake9.LocalRup.prove_clause [c3385, c1573] c3386 (by decide) p (sat_cons (step3385 p h) (sat_cons (step1573 p h) (sat_nil p)))
def c3387 : List Lit := [(1033, false)]
theorem step3387 (p : Nat → Bool) (h : Constraints p) : clause p c3387 = true :=
  Snake9.LocalRup.prove_clause [c3374, c3386, c3373, c3349, c3215, c2968, c3384, c3036, c1120, c1125, c1574, c2163, c2317, c3126, c818] c3387 (by decide) p (sat_cons (step3374 p h) (sat_cons (step3386 p h) (sat_cons (step3373 p h) (sat_cons (step3349 p h) (sat_cons (step3215 p h) (sat_cons (step2968 p h) (sat_cons (step3384 p h) (sat_cons (step3036 p h) (sat_cons (step1120 p h) (sat_cons (step1125 p h) (sat_cons (step1574 p h) (sat_cons (step2163 p h) (sat_cons (step2317 p h) (sat_cons (step3126 p h) (sat_cons (step818 p h) (sat_nil p))))))))))))))))
def c3388 : List Lit := [(1002, false)]
theorem step3388 (p : Nat → Bool) (h : Constraints p) : clause p c3388 = true :=
  Snake9.LocalRup.prove_clause [c3387, c1099] c3388 (by decide) p (sat_cons (step3387 p h) (sat_cons (step1099 p h) (sat_nil p)))
def c3389 : List Lit := [(96, true)]
theorem step3389 (p : Nat → Bool) (h : Constraints p) : clause p c3389 = true :=
  Snake9.LocalRup.prove_clause [c3387, c3368, c3328, c3388, c1063, c2684, c1071, c1056, c1077, c1058] c3389 (by decide) p (sat_cons (step3387 p h) (sat_cons (step3368 p h) (sat_cons (step3328 p h) (sat_cons (step3388 p h) (sat_cons (step1063 p h) (sat_cons (step2684 p h) (sat_cons (step1071 p h) (sat_cons (step1056 p h) (sat_cons (step1077 p h) (sat_cons (step1058 p h) (sat_nil p)))))))))))
def c3390 : List Lit := [(8, false)]
theorem step3390 (p : Nat → Bool) (h : Constraints p) : clause p c3390 = true :=
  Snake9.LocalRup.prove_clause [c3389, c3215, c3373, c331] c3390 (by decide) p (sat_cons (step3389 p h) (sat_cons (step3215 p h) (sat_cons (step3373 p h) (sat_cons (step331 p h) (sat_nil p)))))
def c3391 : List Lit := [(930, true)]
theorem step3391 (p : Nat → Bool) (h : Constraints p) : clause p c3391 = true :=
  Snake9.LocalRup.prove_clause [c3389, c3215, c3373, c1613] c3391 (by decide) p (sat_cons (step3389 p h) (sat_cons (step3215 p h) (sat_cons (step3373 p h) (sat_cons (step1613 p h) (sat_nil p)))))
def c3392 : List Lit := [(77, false)]
theorem step3392 (p : Nat → Bool) (h : Constraints p) : clause p c3392 = true :=
  Snake9.LocalRup.prove_clause [c3389, c3373, c3215, c351] c3392 (by decide) p (sat_cons (step3389 p h) (sat_cons (step3373 p h) (sat_cons (step3215 p h) (sat_cons (step351 p h) (sat_nil p)))))
def c3393 : List Lit := [(812, true)]
theorem step3393 (p : Nat → Bool) (h : Constraints p) : clause p c3393 = true :=
  Snake9.LocalRup.prove_clause [c3390, c3126] c3393 (by decide) p (sat_cons (step3390 p h) (sat_cons (step3126 p h) (sat_nil p)))
def c3394 : List Lit := [(933, true)]
theorem step3394 (p : Nat → Bool) (h : Constraints p) : clause p c3394 = true :=
  Snake9.LocalRup.prove_clause [c3391, c3349, c954] c3394 (by decide) p (sat_cons (step3391 p h) (sat_cons (step3349 p h) (sat_cons (step954 p h) (sat_nil p))))
def c3395 : List Lit := [(954, true)]
theorem step3395 (p : Nat → Bool) (h : Constraints p) : clause p c3395 = true :=
  Snake9.LocalRup.prove_clause [c3392, c3328, c3368, c2683] c3395 (by decide) p (sat_cons (step3392 p h) (sat_cons (step3328 p h) (sat_cons (step3368 p h) (sat_cons (step2683 p h) (sat_nil p)))))
def c3396 : List Lit := [(841, true)]
theorem step3396 (p : Nat → Bool) (h : Constraints p) : clause p c3396 = true :=
  Snake9.LocalRup.prove_clause [c3393, c3036, c818] c3396 (by decide) p (sat_cons (step3393 p h) (sat_cons (step3036 p h) (sat_cons (step818 p h) (sat_nil p))))
def c3397 : List Lit := [(967, true)]
theorem step3397 (p : Nat → Bool) (h : Constraints p) : clause p c3397 = true :=
  Snake9.LocalRup.prove_clause [c3395, c1560] c3397 (by decide) p (sat_cons (step3395 p h) (sat_cons (step1560 p h) (sat_nil p)))
def c3398 : List Lit := [(920, true)]
theorem step3398 (p : Nat → Bool) (h : Constraints p) : clause p c3398 = true :=
  Snake9.LocalRup.prove_clause [c3396, c3384, c2968, c2317] c3398 (by decide) p (sat_cons (step3396 p h) (sat_cons (step3384 p h) (sat_cons (step2968 p h) (sat_cons (step2317 p h) (sat_nil p)))))
def c3399 : List Lit := [(1054, false)]
theorem step3399 (p : Nat → Bool) (h : Constraints p) : clause p c3399 = true :=
  Snake9.LocalRup.prove_clause [c3398, c1574] c3399 (by decide) p (sat_cons (step3398 p h) (sat_cons (step1574 p h) (sat_nil p)))
def c3400 : List Lit := [(980, false)]
theorem step3400 (p : Nat → Bool) (h : Constraints p) : clause p c3400 = true :=
  Snake9.LocalRup.prove_clause [c3399, c1127] c3400 (by decide) p (sat_cons (step3399 p h) (sat_cons (step1127 p h) (sat_nil p)))
def c3401 : List Lit := [(945, true)]
theorem step3401 (p : Nat → Bool) (h : Constraints p) : clause p c3401 = true :=
  Snake9.LocalRup.prove_clause [c3394, c3329, c984] c3401 (by decide) p (sat_cons (step3394 p h) (sat_cons (step3329 p h) (sat_cons (step984 p h) (sat_nil p))))
def c3402 : List Lit := [(968, false)]
theorem step3402 (p : Nat → Bool) (h : Constraints p) : clause p c3402 = true :=
  Snake9.LocalRup.prove_clause [c3400, c3401, c1046] c3402 (by decide) p (sat_cons (step3400 p h) (sat_cons (step3401 p h) (sat_cons (step1046 p h) (sat_nil p))))
def c3403 : List Lit := [(946, false)]
theorem step3403 (p : Nat → Bool) (h : Constraints p) : clause p c3403 = true :=
  Snake9.LocalRup.prove_clause [c3400, c3397, c1049] c3403 (by decide) p (sat_cons (step3400 p h) (sat_cons (step3397 p h) (sat_cons (step1049 p h) (sat_nil p))))
def c3404 : List Lit := [(939, false)]
theorem step3404 (p : Nat → Bool) (h : Constraints p) : clause p c3404 = true :=
  Snake9.LocalRup.prove_clause [c3403, c3394, c985] c3404 (by decide) p (sat_cons (step3403 p h) (sat_cons (step3394 p h) (sat_cons (step985 p h) (sat_nil p))))
def c3405 : List Lit := [(68, true)]
theorem step3405 (p : Nat → Bool) (h : Constraints p) : clause p c3405 = true :=
  Snake9.LocalRup.prove_clause [c3404, c3328, c1387] c3405 (by decide) p (sat_cons (step3404 p h) (sat_cons (step3328 p h) (sat_cons (step1387 p h) (sat_nil p))))
def c3406 : List Lit := [(45, false)]
theorem step3406 (p : Nat → Bool) (h : Constraints p) : clause p c3406 = true :=
  Snake9.LocalRup.prove_clause [c3405, c3375, c3382, c3344] c3406 (by decide) p (sat_cons (step3405 p h) (sat_cons (step3375 p h) (sat_cons (step3382 p h) (sat_cons (step3344 p h) (sat_nil p)))))
def c3407 : List Lit := []
theorem step3407 (p : Nat → Bool) (h : Constraints p) : clause p c3407 = true :=
  Snake9.LocalRup.prove_clause [c3406, c3405, c3373, c3402, c3368, c3319] c3407 (by decide) p (sat_cons (step3406 p h) (sat_cons (step3405 p h) (sat_cons (step3373 p h) (sat_cons (step3402 p h) (sat_cons (step3368 p h) (sat_cons (step3319 p h) (sat_nil p)))))))
end B112E203
