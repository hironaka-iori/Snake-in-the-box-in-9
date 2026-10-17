import B112E081Part0031
namespace B112E081
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c3242 : List Lit := [(934, true)]
theorem step3242 (p : Nat → Bool) (h : Constraints p) : clause p c3242 = true :=
  Snake9.LocalRup.prove_clause [c3240, c3228, c3173, c2938] c3242 (by decide) p (sat_cons (step3240 p h) (sat_cons (step3228 p h) (sat_cons (step3173 p h) (sat_cons (step2938 p h) (sat_nil p)))))
def c3243 : List Lit := [(931, true)]
theorem step3243 (p : Nat → Bool) (h : Constraints p) : clause p c3243 = true :=
  Snake9.LocalRup.prove_clause [c3241, c942] c3243 (by decide) p (sat_cons (step3241 p h) (sat_cons (step942 p h) (sat_nil p)))
def c3244 : List Lit := [(939, true)]
theorem step3244 (p : Nat → Bool) (h : Constraints p) : clause p c3244 = true :=
  Snake9.LocalRup.prove_clause [c3242, c3239, c956] c3244 (by decide) p (sat_cons (step3242 p h) (sat_cons (step3239 p h) (sat_cons (step956 p h) (sat_nil p))))
def c3245 : List Lit := [(978, true)]
theorem step3245 (p : Nat → Bool) (h : Constraints p) : clause p c3245 = true :=
  Snake9.LocalRup.prove_clause [c3243, c3227, c3244, c3173, c2472] c3245 (by decide) p (sat_cons (step3243 p h) (sat_cons (step3227 p h) (sat_cons (step3244 p h) (sat_cons (step3173 p h) (sat_cons (step2472 p h) (sat_nil p))))))
def c3246 : List Lit := [(1034, false)]
theorem step3246 (p : Nat → Bool) (h : Constraints p) : clause p c3246 = true :=
  Snake9.LocalRup.prove_clause [c3245, c3021, c1130] c3246 (by decide) p (sat_cons (step3245 p h) (sat_cons (step3021 p h) (sat_cons (step1130 p h) (sat_nil p))))
def c3247 : List Lit := [(892, false)]
theorem step3247 (p : Nat → Bool) (h : Constraints p) : clause p c3247 = true :=
  Snake9.LocalRup.prove_clause [c3245, c3016, c2722] c3247 (by decide) p (sat_cons (step3245 p h) (sat_cons (step3016 p h) (sat_cons (step2722 p h) (sat_nil p))))
def c3248 : List Lit := [(1003, false)]
theorem step3248 (p : Nat → Bool) (h : Constraints p) : clause p c3248 = true :=
  Snake9.LocalRup.prove_clause [c3246, c1101] c3248 (by decide) p (sat_cons (step3246 p h) (sat_cons (step1101 p h) (sat_nil p)))
def c3249 : List Lit := [(886, false)]
theorem step3249 (p : Nat → Bool) (h : Constraints p) : clause p c3249 = true :=
  Snake9.LocalRup.prove_clause [c3247, c1230] c3249 (by decide) p (sat_cons (step3247 p h) (sat_cons (step1230 p h) (sat_nil p)))
def c3250 : List Lit := [(920, true), (55, false)]
theorem step3250 (p : Nat → Bool) (h : Constraints p) : clause p c3250 = true :=
  Snake9.LocalRup.prove_clause [c3018, c3016, c3014, c3206, c3234, c3173, c3248, c3229, c3227, c3228, c3154, c1098, c1095, c1089, c1086, c3113, c1964, c2002, c1564, c1978, c1762, c1346, c1181, c836, c1966, c1850, c1224, c842, c2081] c3250 (by decide) p (sat_cons (step3018 p h) (sat_cons (step3016 p h) (sat_cons (step3014 p h) (sat_cons (step3206 p h) (sat_cons (step3234 p h) (sat_cons (step3173 p h) (sat_cons (step3248 p h) (sat_cons (step3229 p h) (sat_cons (step3227 p h) (sat_cons (step3228 p h) (sat_cons (step3154 p h) (sat_cons (step1098 p h) (sat_cons (step1095 p h) (sat_cons (step1089 p h) (sat_cons (step1086 p h) (sat_cons (step3113 p h) (sat_cons (step1964 p h) (sat_cons (step2002 p h) (sat_cons (step1564 p h) (sat_cons (step1978 p h) (sat_cons (step1762 p h) (sat_cons (step1346 p h) (sat_cons (step1181 p h) (sat_cons (step836 p h) (sat_cons (step1966 p h) (sat_cons (step1850 p h) (sat_cons (step1224 p h) (sat_cons (step842 p h) (sat_cons (step2081 p h) (sat_nil p))))))))))))))))))))))))))))))
def c3251 : List Lit := [(55, false)]
theorem step3251 (p : Nat → Bool) (h : Constraints p) : clause p c3251 = true :=
  Snake9.LocalRup.prove_clause [c3238, c3242, c3206, c3243, c3175, c3227, c3173, c3154, c1859, c1097, c968, c3250, c1550, c1133, c1988, c1043, c973, c1533, c1658, c943, c1352] c3251 (by decide) p (sat_cons (step3238 p h) (sat_cons (step3242 p h) (sat_cons (step3206 p h) (sat_cons (step3243 p h) (sat_cons (step3175 p h) (sat_cons (step3227 p h) (sat_cons (step3173 p h) (sat_cons (step3154 p h) (sat_cons (step1859 p h) (sat_cons (step1097 p h) (sat_cons (step968 p h) (sat_cons (step3250 p h) (sat_cons (step1550 p h) (sat_cons (step1133 p h) (sat_cons (step1988 p h) (sat_cons (step1043 p h) (sat_cons (step973 p h) (sat_cons (step1533 p h) (sat_cons (step1658 p h) (sat_cons (step943 p h) (sat_cons (step1352 p h) (sat_nil p))))))))))))))))))))))
def c3252 : List Lit := [(882, true)]
theorem step3252 (p : Nat → Bool) (h : Constraints p) : clause p c3252 = true :=
  Snake9.LocalRup.prove_clause [c3251, c3230, c847] c3252 (by decide) p (sat_cons (step3251 p h) (sat_cons (step3230 p h) (sat_cons (step847 p h) (sat_nil p))))
def c3253 : List Lit := [(884, true)]
theorem step3253 (p : Nat → Bool) (h : Constraints p) : clause p c3253 = true :=
  Snake9.LocalRup.prove_clause [c3252, c849] c3253 (by decide) p (sat_cons (step3252 p h) (sat_cons (step849 p h) (sat_nil p)))
def c3254 : List Lit := [(52, true)]
theorem step3254 (p : Nat → Bool) (h : Constraints p) : clause p c3254 = true :=
  Snake9.LocalRup.prove_clause [c3252, c3247, c3227, c1893] c3254 (by decide) p (sat_cons (step3252 p h) (sat_cons (step3247 p h) (sat_cons (step3227 p h) (sat_cons (step1893 p h) (sat_nil p)))))
def c3255 : List Lit := [(880, false)]
theorem step3255 (p : Nat → Bool) (h : Constraints p) : clause p c3255 = true :=
  Snake9.LocalRup.prove_clause [c3252, c3249, c855] c3255 (by decide) p (sat_cons (step3252 p h) (sat_cons (step3249 p h) (sat_cons (step855 p h) (sat_nil p))))
def c3256 : List Lit := [(920, true)]
theorem step3256 (p : Nat → Bool) (h : Constraints p) : clause p c3256 = true :=
  Snake9.LocalRup.prove_clause [c3227, c3173, c3016, c3252, c3253, c3254, c1964, c1564, c852, c863, c843, c1224, c1297] c3256 (by decide) p (sat_cons (step3227 p h) (sat_cons (step3173 p h) (sat_cons (step3016 p h) (sat_cons (step3252 p h) (sat_cons (step3253 p h) (sat_cons (step3254 p h) (sat_cons (step1964 p h) (sat_cons (step1564 p h) (sat_cons (step852 p h) (sat_cons (step863 p h) (sat_cons (step843 p h) (sat_cons (step1224 p h) (sat_cons (step1297 p h) (sat_nil p))))))))))))))
def c3257 : List Lit := [(1054, false)]
theorem step3257 (p : Nat → Bool) (h : Constraints p) : clause p c3257 = true :=
  Snake9.LocalRup.prove_clause [c3256, c1550] c3257 (by decide) p (sat_cons (step3256 p h) (sat_cons (step1550 p h) (sat_nil p)))
def c3258 : List Lit := [(46, true)]
theorem step3258 (p : Nat → Bool) (h : Constraints p) : clause p c3258 = true :=
  Snake9.LocalRup.prove_clause [c3257, c3230, c3247, c3175, c3243, c3240, c3239, c3173, c3228, c3206, c3227, c3255, c3242, c3238, c3244, c3254, c2853, c2943, c1133, c2936, c1988, c2750, c2498, c957, c1043, c952, c972, c1253, c943] c3258 (by decide) p (sat_cons (step3257 p h) (sat_cons (step3230 p h) (sat_cons (step3247 p h) (sat_cons (step3175 p h) (sat_cons (step3243 p h) (sat_cons (step3240 p h) (sat_cons (step3239 p h) (sat_cons (step3173 p h) (sat_cons (step3228 p h) (sat_cons (step3206 p h) (sat_cons (step3227 p h) (sat_cons (step3255 p h) (sat_cons (step3242 p h) (sat_cons (step3238 p h) (sat_cons (step3244 p h) (sat_cons (step3254 p h) (sat_cons (step2853 p h) (sat_cons (step2943 p h) (sat_cons (step1133 p h) (sat_cons (step2936 p h) (sat_cons (step1988 p h) (sat_cons (step2750 p h) (sat_cons (step2498 p h) (sat_cons (step957 p h) (sat_cons (step1043 p h) (sat_cons (step952 p h) (sat_cons (step972 p h) (sat_cons (step1253 p h) (sat_cons (step943 p h) (sat_nil p))))))))))))))))))))))))))))))
def c3259 : List Lit := [(88, false)]
theorem step3259 (p : Nat → Bool) (h : Constraints p) : clause p c3259 = true :=
  Snake9.LocalRup.prove_clause [c3258, c3240, c3173, c201] c3259 (by decide) p (sat_cons (step3258 p h) (sat_cons (step3240 p h) (sat_cons (step3173 p h) (sat_cons (step201 p h) (sat_nil p)))))
def c3260 : List Lit := [(979, true)]
theorem step3260 (p : Nat → Bool) (h : Constraints p) : clause p c3260 = true :=
  Snake9.LocalRup.prove_clause [c3259, c3175, c3227, c3228, c3238, c3244, c3173, c3255, c3240, c2499] c3260 (by decide) p (sat_cons (step3259 p h) (sat_cons (step3175 p h) (sat_cons (step3227 p h) (sat_cons (step3228 p h) (sat_cons (step3238 p h) (sat_cons (step3244 p h) (sat_cons (step3173 p h) (sat_cons (step3255 p h) (sat_cons (step3240 p h) (sat_cons (step2499 p h) (sat_nil p)))))))))))
def c3261 : List Lit := [(1032, false)]
theorem step3261 (p : Nat → Bool) (h : Constraints p) : clause p c3261 = true :=
  Snake9.LocalRup.prove_clause [c3260, c3257, c1133] c3261 (by decide) p (sat_cons (step3260 p h) (sat_cons (step3257 p h) (sat_cons (step1133 p h) (sat_nil p))))
def c3262 : List Lit := [(1001, false)]
theorem step3262 (p : Nat → Bool) (h : Constraints p) : clause p c3262 = true :=
  Snake9.LocalRup.prove_clause [c3261, c1097] c3262 (by decide) p (sat_cons (step3261 p h) (sat_cons (step1097 p h) (sat_nil p)))
def c3263 : List Lit := [(997, false)]
theorem step3263 (p : Nat → Bool) (h : Constraints p) : clause p c3263 = true :=
  Snake9.LocalRup.prove_clause [c3262, c1074] c3263 (by decide) p (sat_cons (step3262 p h) (sat_cons (step1074 p h) (sat_nil p)))
def c3264 : List Lit := [(990, false)]
theorem step3264 (p : Nat → Bool) (h : Constraints p) : clause p c3264 = true :=
  Snake9.LocalRup.prove_clause [c3262, c1077] c3264 (by decide) p (sat_cons (step3262 p h) (sat_cons (step1077 p h) (sat_nil p)))
def c3265 : List Lit := [(995, false)]
theorem step3265 (p : Nat → Bool) (h : Constraints p) : clause p c3265 = true :=
  Snake9.LocalRup.prove_clause [c3263, c1068] c3265 (by decide) p (sat_cons (step3263 p h) (sat_cons (step1068 p h) (sat_nil p)))
def c3266 : List Lit := [(993, false)]
theorem step3266 (p : Nat → Bool) (h : Constraints p) : clause p c3266 = true :=
  Snake9.LocalRup.prove_clause [c3263, c1070] c3266 (by decide) p (sat_cons (step3263 p h) (sat_cons (step1070 p h) (sat_nil p)))
def c3267 : List Lit := [(988, false)]
theorem step3267 (p : Nat → Bool) (h : Constraints p) : clause p c3267 = true :=
  Snake9.LocalRup.prove_clause [c3264, c1057] c3267 (by decide) p (sat_cons (step3264 p h) (sat_cons (step1057 p h) (sat_nil p)))
def c3268 : List Lit := [(102, true)]
theorem step3268 (p : Nat → Bool) (h : Constraints p) : clause p c3268 = true :=
  Snake9.LocalRup.prove_clause [c3265, c1065] c3268 (by decide) p (sat_cons (step3265 p h) (sat_cons (step1065 p h) (sat_nil p)))
def c3269 : List Lit := [(95, true)]
theorem step3269 (p : Nat → Bool) (h : Constraints p) : clause p c3269 = true :=
  Snake9.LocalRup.prove_clause [c3266, c1063] c3269 (by decide) p (sat_cons (step3266 p h) (sat_cons (step1063 p h) (sat_nil p)))
def c3270 : List Lit := [(92, true)]
theorem step3270 (p : Nat → Bool) (h : Constraints p) : clause p c3270 = true :=
  Snake9.LocalRup.prove_clause [c3267, c1054] c3270 (by decide) p (sat_cons (step3267 p h) (sat_cons (step1054 p h) (sat_nil p)))
def c3271 : List Lit := [(89, true)]
theorem step3271 (p : Nat → Bool) (h : Constraints p) : clause p c3271 = true :=
  Snake9.LocalRup.prove_clause [c3267, c1055] c3271 (by decide) p (sat_cons (step3267 p h) (sat_cons (step1055 p h) (sat_nil p)))
def c3272 : List Lit := [(94, false)]
theorem step3272 (p : Nat → Bool) (h : Constraints p) : clause p c3272 = true :=
  Snake9.LocalRup.prove_clause [c3268, c3270, c3269, c493] c3272 (by decide) p (sat_cons (step3268 p h) (sat_cons (step3270 p h) (sat_cons (step3269 p h) (sat_cons (step493 p h) (sat_nil p)))))
def c3273 : List Lit := [(58, false)]
theorem step3273 (p : Nat → Bool) (h : Constraints p) : clause p c3273 = true :=
  Snake9.LocalRup.prove_clause [c3269, c3247, c3230, c3227, c3206, c2936] c3273 (by decide) p (sat_cons (step3269 p h) (sat_cons (step3247 p h) (sat_cons (step3230 p h) (sat_cons (step3227 p h) (sat_cons (step3206 p h) (sat_cons (step2936 p h) (sat_nil p)))))))
def c3274 : List Lit := [(90, false)]
theorem step3274 (p : Nat → Bool) (h : Constraints p) : clause p c3274 = true :=
  Snake9.LocalRup.prove_clause [c3271, c3254, c3269, c484] c3274 (by decide) p (sat_cons (step3271 p h) (sat_cons (step3254 p h) (sat_cons (step3269 p h) (sat_cons (step484 p h) (sat_nil p)))))
def c3275 : List Lit := []
theorem step3275 (p : Nat → Bool) (h : Constraints p) : clause p c3275 = true :=
  Snake9.LocalRup.prove_clause [c3274, c3272, c3273, c3269, c1496] c3275 (by decide) p (sat_cons (step3274 p h) (sat_cons (step3272 p h) (sat_cons (step3273 p h) (sat_cons (step3269 p h) (sat_cons (step1496 p h) (sat_nil p))))))
end B112E081
