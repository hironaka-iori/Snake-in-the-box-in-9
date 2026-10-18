import B112E078Part0048
namespace B112E078
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c4348 : List Lit := [(1503, false), (1492, true), (2, true), (1524, false), (57, true), (52, false), (1534, false)]
theorem step4348 (p : Nat → Bool) (h : Constraints p) : clause p c4348 = true :=
  Snake9.LocalRup.prove_clause [c4336, c4286, c4063, c4346, c946, c885, c865, c867, c937, c1974, c4327, c919, c1458, c1457, c277, c4110, c879, c866, c888, c4342, c922] c4348 (by decide) p (sat_cons (step4336 p h) (sat_cons (step4286 p h) (sat_cons (step4063 p h) (sat_cons (step4346 p h) (sat_cons (step946 p h) (sat_cons (step885 p h) (sat_cons (step865 p h) (sat_cons (step867 p h) (sat_cons (step937 p h) (sat_cons (step1974 p h) (sat_cons (step4327 p h) (sat_cons (step919 p h) (sat_cons (step1458 p h) (sat_cons (step1457 p h) (sat_cons (step277 p h) (sat_cons (step4110 p h) (sat_cons (step879 p h) (sat_cons (step866 p h) (sat_cons (step888 p h) (sat_cons (step4342 p h) (sat_cons (step922 p h) (sat_nil p))))))))))))))))))))))
def c4349 : List Lit := [(1492, true), (2, true), (1534, false), (1524, false), (57, true), (52, false)]
theorem step4349 (p : Nat → Bool) (h : Constraints p) : clause p c4349 = true :=
  Snake9.LocalRup.prove_clause [c4286, c4063, c4348, c844, c283, c274, c879, c4327, c888, c862, c922, c4342] c4349 (by decide) p (sat_cons (step4286 p h) (sat_cons (step4063 p h) (sat_cons (step4348 p h) (sat_cons (step844 p h) (sat_cons (step283 p h) (sat_cons (step274 p h) (sat_cons (step879 p h) (sat_cons (step4327 p h) (sat_cons (step888 p h) (sat_cons (step862 p h) (sat_cons (step922 p h) (sat_cons (step4342 p h) (sat_nil p)))))))))))))
def c4350 : List Lit := [(27, false), (1697, true), (1492, false), (49, true), (1534, false)]
theorem step4350 (p : Nat → Bool) (h : Constraints p) : clause p c4350 = true :=
  Snake9.LocalRup.prove_clause [c4063, c4286, c287, c3256, c3558, c4095] c4350 (by decide) p (sat_cons (step4063 p h) (sat_cons (step4286 p h) (sat_cons (step287 p h) (sat_cons (step3256 p h) (sat_cons (step3558 p h) (sat_cons (step4095 p h) (sat_nil p)))))))
def c4351 : List Lit := [(1492, false), (49, true), (57, true), (52, false), (1534, false)]
theorem step4351 (p : Nat → Bool) (h : Constraints p) : clause p c4351 = true :=
  Snake9.LocalRup.prove_clause [c4191, c4336, c4187, c4319, c4347, c2937, c885, c990, c988, c946, c1559, c4350, c844, c3307, c867, c922, c918, c1974, c1994, c888, c1457, c897, c4017, c902, c332, c893] c4351 (by decide) p (sat_cons (step4191 p h) (sat_cons (step4336 p h) (sat_cons (step4187 p h) (sat_cons (step4319 p h) (sat_cons (step4347 p h) (sat_cons (step2937 p h) (sat_cons (step885 p h) (sat_cons (step990 p h) (sat_cons (step988 p h) (sat_cons (step946 p h) (sat_cons (step1559 p h) (sat_cons (step4350 p h) (sat_cons (step844 p h) (sat_cons (step3307 p h) (sat_cons (step867 p h) (sat_cons (step922 p h) (sat_cons (step918 p h) (sat_cons (step1974 p h) (sat_cons (step1994 p h) (sat_cons (step888 p h) (sat_cons (step1457 p h) (sat_cons (step897 p h) (sat_cons (step4017 p h) (sat_cons (step902 p h) (sat_cons (step332 p h) (sat_cons (step893 p h) (sat_nil p)))))))))))))))))))))))))))
def c4352 : List Lit := [(1503, false), (2, false), (1523, false), (52, false), (1534, false)]
theorem step4352 (p : Nat → Bool) (h : Constraints p) : clause p c4352 = true :=
  Snake9.LocalRup.prove_clause [c4188, c4336, c4063, c4286, c1358, c868, c4345, c3264, c953, c274, c4344] c4352 (by decide) p (sat_cons (step4188 p h) (sat_cons (step4336 p h) (sat_cons (step4063 p h) (sat_cons (step4286 p h) (sat_cons (step1358 p h) (sat_cons (step868 p h) (sat_cons (step4345 p h) (sat_cons (step3264 p h) (sat_cons (step953 p h) (sat_cons (step274 p h) (sat_cons (step4344 p h) (sat_nil p))))))))))))
def c4353 : List Lit := [(49, true), (57, true), (52, false), (1534, false)]
theorem step4353 (p : Nat → Bool) (h : Constraints p) : clause p c4353 = true :=
  Snake9.LocalRup.prove_clause [c4063, c4286, c4201, c4336, c882, c4347, c4351, c4349, c1388, c1294, c4352, c844, c287, c274, c4338, c1844, c3987, c3989] c4353 (by decide) p (sat_cons (step4063 p h) (sat_cons (step4286 p h) (sat_cons (step4201 p h) (sat_cons (step4336 p h) (sat_cons (step882 p h) (sat_cons (step4347 p h) (sat_cons (step4351 p h) (sat_cons (step4349 p h) (sat_cons (step1388 p h) (sat_cons (step1294 p h) (sat_cons (step4352 p h) (sat_cons (step844 p h) (sat_cons (step287 p h) (sat_cons (step274 p h) (sat_cons (step4338 p h) (sat_cons (step1844 p h) (sat_cons (step3987 p h) (sat_cons (step3989 p h) (sat_nil p)))))))))))))))))))
def c4354 : List Lit := [(27, false), (1550, false), (49, false)]
theorem step4354 (p : Nat → Bool) (h : Constraints p) : clause p c4354 = true :=
  Snake9.LocalRup.prove_clause [c4063, c4286, c4319, c287, c274, c3422, c4337] c4354 (by decide) p (sat_cons (step4063 p h) (sat_cons (step4286 p h) (sat_cons (step4319 p h) (sat_cons (step287 p h) (sat_cons (step274 p h) (sat_cons (step3422 p h) (sat_cons (step4337 p h) (sat_nil p))))))))
def c4355 : List Lit := [(1552, false), (49, false)]
theorem step4355 (p : Nat → Bool) (h : Constraints p) : clause p c4355 = true :=
  Snake9.LocalRup.prove_clause [c4203, c4191, c4286, c4063, c4188, c4319, c973, c985, c1559, c4344, c1554, c281, c1136, c3422] c4355 (by decide) p (sat_cons (step4203 p h) (sat_cons (step4191 p h) (sat_cons (step4286 p h) (sat_cons (step4063 p h) (sat_cons (step4188 p h) (sat_cons (step4319 p h) (sat_cons (step973 p h) (sat_cons (step985 p h) (sat_cons (step1559 p h) (sat_cons (step4344 p h) (sat_cons (step1554 p h) (sat_cons (step281 p h) (sat_cons (step1136 p h) (sat_cons (step3422 p h) (sat_nil p)))))))))))))))
def c4356 : List Lit := [(49, false), (52, false)]
theorem step4356 (p : Nat → Bool) (h : Constraints p) : clause p c4356 = true :=
  Snake9.LocalRup.prove_clause [c4191, c4336, c3001, c1974, c862, c940, c4354, c844, c4355, c867, c953, c946, c868, c990, c4346, c1358] c4356 (by decide) p (sat_cons (step4191 p h) (sat_cons (step4336 p h) (sat_cons (step3001 p h) (sat_cons (step1974 p h) (sat_cons (step862 p h) (sat_cons (step940 p h) (sat_cons (step4354 p h) (sat_cons (step844 p h) (sat_cons (step4355 p h) (sat_cons (step867 p h) (sat_cons (step953 p h) (sat_cons (step946 p h) (sat_cons (step868 p h) (sat_cons (step990 p h) (sat_cons (step4346 p h) (sat_cons (step1358 p h) (sat_nil p)))))))))))))))))
def c4357 : List Lit := [(52, false), (1534, false)]
theorem step4357 (p : Nat → Bool) (h : Constraints p) : clause p c4357 = true :=
  Snake9.LocalRup.prove_clause [c4063, c4286, c4188, c4336, c4356, c882, c4353, c292, c289, c280, c286, c1844, c879, c844, c1135, c4352, c1553, c4266, c1560, c946, c3258, c867, c3336, c4327, c989] c4357 (by decide) p (sat_cons (step4063 p h) (sat_cons (step4286 p h) (sat_cons (step4188 p h) (sat_cons (step4336 p h) (sat_cons (step4356 p h) (sat_cons (step882 p h) (sat_cons (step4353 p h) (sat_cons (step292 p h) (sat_cons (step289 p h) (sat_cons (step280 p h) (sat_cons (step286 p h) (sat_cons (step1844 p h) (sat_cons (step879 p h) (sat_cons (step844 p h) (sat_cons (step1135 p h) (sat_cons (step4352 p h) (sat_cons (step1553 p h) (sat_cons (step4266 p h) (sat_cons (step1560 p h) (sat_cons (step946 p h) (sat_cons (step3258 p h) (sat_cons (step867 p h) (sat_cons (step3336 p h) (sat_cons (step4327 p h) (sat_cons (step989 p h) (sat_nil p))))))))))))))))))))))))))
def c4358 : List Lit := [(2, true), (1492, true), (27, true), (1503, false), (1524, false), (1534, false)]
theorem step4358 (p : Nat → Bool) (h : Constraints p) : clause p c4358 = true :=
  Snake9.LocalRup.prove_clause [c4336, c4063, c4286, c4201, c4346, c946, c867, c4327, c277, c281, c879, c1844, c888, c922, c4311, c4309, c4146] c4358 (by decide) p (sat_cons (step4336 p h) (sat_cons (step4063 p h) (sat_cons (step4286 p h) (sat_cons (step4201 p h) (sat_cons (step4346 p h) (sat_cons (step946 p h) (sat_cons (step867 p h) (sat_cons (step4327 p h) (sat_cons (step277 p h) (sat_cons (step281 p h) (sat_cons (step879 p h) (sat_cons (step1844 p h) (sat_cons (step888 p h) (sat_cons (step922 p h) (sat_cons (step4311 p h) (sat_cons (step4309 p h) (sat_cons (step4146 p h) (sat_nil p))))))))))))))))))
def c4359 : List Lit := [(1541, false), (1669, false), (1516, false)]
theorem step4359 (p : Nat → Bool) (h : Constraints p) : clause p c4359 = true :=
  Snake9.LocalRup.prove_clause [c4187, c4203, c4311, c947, c1589, c973, c1559] c4359 (by decide) p (sat_cons (step4187 p h) (sat_cons (step4203 p h) (sat_cons (step4311 p h) (sat_cons (step947 p h) (sat_cons (step1589 p h) (sat_cons (step973 p h) (sat_cons (step1559 p h) (sat_nil p))))))))
def c4360 : List Lit := [(1669, false), (1516, false), (1524, false), (1534, false)]
theorem step4360 (p : Nat → Bool) (h : Constraints p) : clause p c4360 = true :=
  Snake9.LocalRup.prove_clause [c4336, c4188, c4286, c4063, c4201, c4187, c946, c1135, c1553, c1560, c984, c4359, c922, c888, c879, c277, c3987, c3209, c978, c1589, c1559] c4360 (by decide) p (sat_cons (step4336 p h) (sat_cons (step4188 p h) (sat_cons (step4286 p h) (sat_cons (step4063 p h) (sat_cons (step4201 p h) (sat_cons (step4187 p h) (sat_cons (step946 p h) (sat_cons (step1135 p h) (sat_cons (step1553 p h) (sat_cons (step1560 p h) (sat_cons (step984 p h) (sat_cons (step4359 p h) (sat_cons (step922 p h) (sat_cons (step888 p h) (sat_cons (step879 p h) (sat_cons (step277 p h) (sat_cons (step3987 p h) (sat_cons (step3209 p h) (sat_cons (step978 p h) (sat_cons (step1589 p h) (sat_cons (step1559 p h) (sat_nil p))))))))))))))))))))))
def c4361 : List Lit := [(1669, true), (1503, false), (1524, false), (1534, false)]
theorem step4361 (p : Nat → Bool) (h : Constraints p) : clause p c4361 = true :=
  Snake9.LocalRup.prove_clause [c4286, c4063, c1844, c1861, c281, c879, c888, c922, c4311, c4289] c4361 (by decide) p (sat_cons (step4286 p h) (sat_cons (step4063 p h) (sat_cons (step1844 p h) (sat_cons (step1861 p h) (sat_cons (step281 p h) (sat_cons (step879 p h) (sat_cons (step888 p h) (sat_cons (step922 p h) (sat_cons (step4311 p h) (sat_cons (step4289 p h) (sat_nil p)))))))))))
def c4362 : List Lit := [(1492, false), (1503, false), (49, true), (1534, false)]
theorem step4362 (p : Nat → Bool) (h : Constraints p) : clause p c4362 = true :=
  Snake9.LocalRup.prove_clause [c4188, c4336, c4063, c4286, c4357, c883, c4361, c1135, c1553, c1560, c989, c3170, c3359] c4362 (by decide) p (sat_cons (step4188 p h) (sat_cons (step4336 p h) (sat_cons (step4063 p h) (sat_cons (step4286 p h) (sat_cons (step4357 p h) (sat_cons (step883 p h) (sat_cons (step4361 p h) (sat_cons (step1135 p h) (sat_cons (step1553 p h) (sat_cons (step1560 p h) (sat_cons (step989 p h) (sat_cons (step3170 p h) (sat_cons (step3359 p h) (sat_nil p))))))))))))))
def c4363 : List Lit := [(1503, false), (49, true), (1534, false)]
theorem step4363 (p : Nat → Bool) (h : Constraints p) : clause p c4363 = true :=
  Snake9.LocalRup.prove_clause [c4063, c4286, c4357, c883, c4361, c4360, c867, c1294, c4362, c4358, c4327, c274] c4363 (by decide) p (sat_cons (step4063 p h) (sat_cons (step4286 p h) (sat_cons (step4357 p h) (sat_cons (step883 p h) (sat_cons (step4361 p h) (sat_cons (step4360 p h) (sat_cons (step867 p h) (sat_cons (step1294 p h) (sat_cons (step4362 p h) (sat_cons (step4358 p h) (sat_cons (step4327 p h) (sat_cons (step274 p h) (sat_nil p)))))))))))))
def c4364 : List Lit := [(49, true), (1534, false)]
theorem step4364 (p : Nat → Bool) (h : Constraints p) : clause p c4364 = true :=
  Snake9.LocalRup.prove_clause [c4063, c4286, c4187, c4201, c4357, c883, c4363, c842, c844, c839, c287, c283, c274, c1844, c879, c4360, c888, c863, c922, c4311, c3289, c3991, c4327, c941, c862] c4364 (by decide) p (sat_cons (step4063 p h) (sat_cons (step4286 p h) (sat_cons (step4187 p h) (sat_cons (step4201 p h) (sat_cons (step4357 p h) (sat_cons (step883 p h) (sat_cons (step4363 p h) (sat_cons (step842 p h) (sat_cons (step844 p h) (sat_cons (step839 p h) (sat_cons (step287 p h) (sat_cons (step283 p h) (sat_cons (step274 p h) (sat_cons (step1844 p h) (sat_cons (step879 p h) (sat_cons (step4360 p h) (sat_cons (step888 p h) (sat_cons (step863 p h) (sat_cons (step922 p h) (sat_cons (step4311 p h) (sat_cons (step3289 p h) (sat_cons (step3991 p h) (sat_cons (step4327 p h) (sat_cons (step941 p h) (sat_cons (step862 p h) (sat_nil p))))))))))))))))))))))))))
def c4365 : List Lit := [(1503, true), (1669, false), (1534, false)]
theorem step4365 (p : Nat → Bool) (h : Constraints p) : clause p c4365 = true :=
  Snake9.LocalRup.prove_clause [c4063, c4187, c4286, c4188, c4336, c4364, c4357, c881, c842, c844, c839, c287, c283, c286, c274, c1253, c4354, c879, c940, c887, c862, c4327, c3169, c3289, c3298, c918] c4365 (by decide) p (sat_cons (step4063 p h) (sat_cons (step4187 p h) (sat_cons (step4286 p h) (sat_cons (step4188 p h) (sat_cons (step4336 p h) (sat_cons (step4364 p h) (sat_cons (step4357 p h) (sat_cons (step881 p h) (sat_cons (step842 p h) (sat_cons (step844 p h) (sat_cons (step839 p h) (sat_cons (step287 p h) (sat_cons (step283 p h) (sat_cons (step286 p h) (sat_cons (step274 p h) (sat_cons (step1253 p h) (sat_cons (step4354 p h) (sat_cons (step879 p h) (sat_cons (step940 p h) (sat_cons (step887 p h) (sat_cons (step862 p h) (sat_cons (step4327 p h) (sat_cons (step3169 p h) (sat_cons (step3289 p h) (sat_cons (step3298 p h) (sat_cons (step918 p h) (sat_nil p)))))))))))))))))))))))))))
def c4366 : List Lit := [(27, false), (1503, false), (1534, false)]
theorem step4366 (p : Nat → Bool) (h : Constraints p) : clause p c4366 = true :=
  Snake9.LocalRup.prove_clause [c4063, c4297, c4286, c4188, c4336, c865, c4364, c4357, c881, c287, c283, c286, c274, c1253, c4354, c879, c945, c940, c936, c887, c867, c866, c918, c4327, c2038, c3298] c4366 (by decide) p (sat_cons (step4063 p h) (sat_cons (step4297 p h) (sat_cons (step4286 p h) (sat_cons (step4188 p h) (sat_cons (step4336 p h) (sat_cons (step865 p h) (sat_cons (step4364 p h) (sat_cons (step4357 p h) (sat_cons (step881 p h) (sat_cons (step287 p h) (sat_cons (step283 p h) (sat_cons (step286 p h) (sat_cons (step274 p h) (sat_cons (step1253 p h) (sat_cons (step4354 p h) (sat_cons (step879 p h) (sat_cons (step945 p h) (sat_cons (step940 p h) (sat_cons (step936 p h) (sat_cons (step887 p h) (sat_cons (step867 p h) (sat_cons (step866 p h) (sat_cons (step918 p h) (sat_cons (step4327 p h) (sat_cons (step2038 p h) (sat_cons (step3298 p h) (sat_nil p)))))))))))))))))))))))))))
def c4367 : List Lit := [(1492, false), (1669, false), (1534, false)]
theorem step4367 (p : Nat → Bool) (h : Constraints p) : clause p c4367 = true :=
  Snake9.LocalRup.prove_clause [c4336, c4063, c4187, c4365, c4366, c865, c935, c4364, c3307, c3170, c988, c3321, c1559, c1589] c4367 (by decide) p (sat_cons (step4336 p h) (sat_cons (step4063 p h) (sat_cons (step4187 p h) (sat_cons (step4365 p h) (sat_cons (step4366 p h) (sat_cons (step865 p h) (sat_cons (step935 p h) (sat_cons (step4364 p h) (sat_cons (step3307 p h) (sat_cons (step3170 p h) (sat_cons (step988 p h) (sat_cons (step3321 p h) (sat_cons (step1559 p h) (sat_cons (step1589 p h) (sat_nil p)))))))))))))))
def c4368 : List Lit := [(40, true), (1541, true), (1669, false), (1534, false)]
theorem step4368 (p : Nat → Bool) (h : Constraints p) : clause p c4368 = true :=
  Snake9.LocalRup.prove_clause [c4201, c4336, c4187, c4319, c4286, c4063, c4367, c4365, c4366, c865, c935, c4364, c1388, c3321, c4146, c4346, c982, c946, c1558, c867, c3588, c4327, c3422, c281] c4368 (by decide) p (sat_cons (step4201 p h) (sat_cons (step4336 p h) (sat_cons (step4187 p h) (sat_cons (step4319 p h) (sat_cons (step4286 p h) (sat_cons (step4063 p h) (sat_cons (step4367 p h) (sat_cons (step4365 p h) (sat_cons (step4366 p h) (sat_cons (step865 p h) (sat_cons (step935 p h) (sat_cons (step4364 p h) (sat_cons (step1388 p h) (sat_cons (step3321 p h) (sat_cons (step4146 p h) (sat_cons (step4346 p h) (sat_cons (step982 p h) (sat_cons (step946 p h) (sat_cons (step1558 p h) (sat_cons (step867 p h) (sat_cons (step3588 p h) (sat_cons (step4327 p h) (sat_cons (step3422 p h) (sat_cons (step281 p h) (sat_nil p)))))))))))))))))))))))))
def c4369 : List Lit := [(5, false), (1550, false), (1503, false), (1669, false), (49, false)]
theorem step4369 (p : Nat → Bool) (h : Constraints p) : clause p c4369 = true :=
  Snake9.LocalRup.prove_clause [c4336, c4203, c4201, c4286, c4063, c4187, c4319, c4355, c953, c868, c1589, c1559, c983, c4146, c1294, c867, c946, c972, c3991, c1558, c281, c3588, c3422] c4369 (by decide) p (sat_cons (step4336 p h) (sat_cons (step4203 p h) (sat_cons (step4201 p h) (sat_cons (step4286 p h) (sat_cons (step4063 p h) (sat_cons (step4187 p h) (sat_cons (step4319 p h) (sat_cons (step4355 p h) (sat_cons (step953 p h) (sat_cons (step868 p h) (sat_cons (step1589 p h) (sat_cons (step1559 p h) (sat_cons (step983 p h) (sat_cons (step4146 p h) (sat_cons (step1294 p h) (sat_cons (step867 p h) (sat_cons (step946 p h) (sat_cons (step972 p h) (sat_cons (step3991 p h) (sat_cons (step1558 p h) (sat_cons (step281 p h) (sat_cons (step3588 p h) (sat_cons (step3422 p h) (sat_nil p))))))))))))))))))))))))
def c4370 : List Lit := [(1541, true), (1669, false), (1534, false)]
theorem step4370 (p : Nat → Bool) (h : Constraints p) : clause p c4370 = true :=
  Snake9.LocalRup.prove_clause [c4336, c4063, c4286, c4188, c4202, c4201, c4367, c4365, c1135, c1553, c1560, c4364, c4357, c881, c4368, c2038, c866, c940, c4369, c3228, c3385, c1294, c1179, c867, c1405, c946, c3229, c984, c823, c3813] c4370 (by decide) p (sat_cons (step4336 p h) (sat_cons (step4063 p h) (sat_cons (step4286 p h) (sat_cons (step4188 p h) (sat_cons (step4202 p h) (sat_cons (step4201 p h) (sat_cons (step4367 p h) (sat_cons (step4365 p h) (sat_cons (step1135 p h) (sat_cons (step1553 p h) (sat_cons (step1560 p h) (sat_cons (step4364 p h) (sat_cons (step4357 p h) (sat_cons (step881 p h) (sat_cons (step4368 p h) (sat_cons (step2038 p h) (sat_cons (step866 p h) (sat_cons (step940 p h) (sat_cons (step4369 p h) (sat_cons (step3228 p h) (sat_cons (step3385 p h) (sat_cons (step1294 p h) (sat_cons (step1179 p h) (sat_cons (step867 p h) (sat_cons (step1405 p h) (sat_cons (step946 p h) (sat_cons (step3229 p h) (sat_cons (step984 p h) (sat_cons (step823 p h) (sat_cons (step3813 p h) (sat_nil p)))))))))))))))))))))))))))))))
def c4371 : List Lit := [(1669, false), (1534, false)]
theorem step4371 (p : Nat → Bool) (h : Constraints p) : clause p c4371 = true :=
  Snake9.LocalRup.prove_clause [c4364, c4365, c865, c4370, c4311, c936, c4369] c4371 (by decide) p (sat_cons (step4364 p h) (sat_cons (step4365 p h) (sat_cons (step865 p h) (sat_cons (step4370 p h) (sat_cons (step4311 p h) (sat_cons (step936 p h) (sat_cons (step4369 p h) (sat_nil p))))))))
def c4372 : List Lit := [(1534, false)]
theorem step4372 (p : Nat → Bool) (h : Constraints p) : clause p c4372 = true :=
  Snake9.LocalRup.prove_clause [c4319, c4063, c4286, c4364, c1371, c1107, c4371, c1115, c1844, c1118, c1110, c1203, c1095, c1102, c1503, c1088, c483] c4372 (by decide) p (sat_cons (step4319 p h) (sat_cons (step4063 p h) (sat_cons (step4286 p h) (sat_cons (step4364 p h) (sat_cons (step1371 p h) (sat_cons (step1107 p h) (sat_cons (step4371 p h) (sat_cons (step1115 p h) (sat_cons (step1844 p h) (sat_cons (step1118 p h) (sat_cons (step1110 p h) (sat_cons (step1203 p h) (sat_cons (step1095 p h) (sat_cons (step1102 p h) (sat_cons (step1503 p h) (sat_cons (step1088 p h) (sat_cons (step483 p h) (sat_nil p))))))))))))))))))
def c4373 : List Lit := [(1532, false)]
theorem step4373 (p : Nat → Bool) (h : Constraints p) : clause p c4373 = true :=
  Snake9.LocalRup.prove_clause [c4372, c899] c4373 (by decide) p (sat_cons (step4372 p h) (sat_cons (step899 p h) (sat_nil p)))
def c4374 : List Lit := [(1662, true)]
theorem step4374 (p : Nat → Bool) (h : Constraints p) : clause p c4374 = true :=
  Snake9.LocalRup.prove_clause [c4373, c4319, c1255] c4374 (by decide) p (sat_cons (step4373 p h) (sat_cons (step4319 p h) (sat_cons (step1255 p h) (sat_nil p))))
def c4375 : List Lit := [(1664, true)]
theorem step4375 (p : Nat → Bool) (h : Constraints p) : clause p c4375 = true :=
  Snake9.LocalRup.prove_clause [c4374, c1107] c4375 (by decide) p (sat_cons (step4374 p h) (sat_cons (step1107 p h) (sat_nil p)))
def c4376 : List Lit := [(1669, true)]
theorem step4376 (p : Nat → Bool) (h : Constraints p) : clause p c4376 = true :=
  Snake9.LocalRup.prove_clause [c4375, c4319, c4373, c3380] c4376 (by decide) p (sat_cons (step4375 p h) (sat_cons (step4319 p h) (sat_cons (step4373 p h) (sat_cons (step3380 p h) (sat_nil p)))))
def c4377 : List Lit := [(1550, true), (5, false), (1503, false)]
theorem step4377 (p : Nat → Bool) (h : Constraints p) : clause p c4377 = true :=
  Snake9.LocalRup.prove_clause [c4187, c4376, c4297, c4201, c4063, c4286, c4319, c4373, c4336, c865, c935, c1589, c1559, c988, c945, c940, c867, c866, c1294, c4327, c2038, c4146, c281, c274, c3911] c4377 (by decide) p (sat_cons (step4187 p h) (sat_cons (step4376 p h) (sat_cons (step4297 p h) (sat_cons (step4201 p h) (sat_cons (step4063 p h) (sat_cons (step4286 p h) (sat_cons (step4319 p h) (sat_cons (step4373 p h) (sat_cons (step4336 p h) (sat_cons (step865 p h) (sat_cons (step935 p h) (sat_cons (step1589 p h) (sat_cons (step1559 p h) (sat_cons (step988 p h) (sat_cons (step945 p h) (sat_cons (step940 p h) (sat_cons (step867 p h) (sat_cons (step866 p h) (sat_cons (step1294 p h) (sat_cons (step4327 p h) (sat_cons (step2038 p h) (sat_cons (step4146 p h) (sat_cons (step281 p h) (sat_cons (step274 p h) (sat_cons (step3911 p h) (sat_nil p))))))))))))))))))))))))))
def c4378 : List Lit := [(5, false), (1503, false)]
theorem step4378 (p : Nat → Bool) (h : Constraints p) : clause p c4378 = true :=
  Snake9.LocalRup.prove_clause [c4336, c4203, c4201, c4376, c4286, c4063, c4187, c4373, c4319, c1589, c1559, c973, c953, c868, c4377, c983, c4146, c1294, c867, c946, c972, c3991, c1558, c281, c3588, c3446] c4378 (by decide) p (sat_cons (step4336 p h) (sat_cons (step4203 p h) (sat_cons (step4201 p h) (sat_cons (step4376 p h) (sat_cons (step4286 p h) (sat_cons (step4063 p h) (sat_cons (step4187 p h) (sat_cons (step4373 p h) (sat_cons (step4319 p h) (sat_cons (step1589 p h) (sat_cons (step1559 p h) (sat_cons (step973 p h) (sat_cons (step953 p h) (sat_cons (step868 p h) (sat_cons (step4377 p h) (sat_cons (step983 p h) (sat_cons (step4146 p h) (sat_cons (step1294 p h) (sat_cons (step867 p h) (sat_cons (step946 p h) (sat_cons (step972 p h) (sat_cons (step3991 p h) (sat_cons (step1558 p h) (sat_cons (step281 p h) (sat_cons (step3588 p h) (sat_cons (step3446 p h) (sat_nil p)))))))))))))))))))))))))))
def c4379 : List Lit := [(1492, true), (5, true), (1503, false)]
theorem step4379 (p : Nat → Bool) (h : Constraints p) : clause p c4379 = true :=
  Snake9.LocalRup.prove_clause [c4201, c4336, c4319, c4372, c4373, c4063, c4286, c4376, c3880, c1179, c280, c1405, c897, c3940, c1989, c946, c4006, c867, c1294] c4379 (by decide) p (sat_cons (step4201 p h) (sat_cons (step4336 p h) (sat_cons (step4319 p h) (sat_cons (step4372 p h) (sat_cons (step4373 p h) (sat_cons (step4063 p h) (sat_cons (step4286 p h) (sat_cons (step4376 p h) (sat_cons (step3880 p h) (sat_cons (step1179 p h) (sat_cons (step280 p h) (sat_cons (step1405 p h) (sat_cons (step897 p h) (sat_cons (step3940 p h) (sat_cons (step1989 p h) (sat_cons (step946 p h) (sat_cons (step4006 p h) (sat_cons (step867 p h) (sat_cons (step1294 p h) (sat_nil p))))))))))))))))))))
def c4380 : List Lit := [(1503, false)]
theorem step4380 (p : Nat → Bool) (h : Constraints p) : clause p c4380 = true :=
  Snake9.LocalRup.prove_clause [c4376, c4336, c4201, c4372, c4063, c4286, c4373, c4319, c4188, c865, c935, c4378, c4379, c3170, c988, c1388, c1559, c3536, c1554, c3446, c1136] c4380 (by decide) p (sat_cons (step4376 p h) (sat_cons (step4336 p h) (sat_cons (step4201 p h) (sat_cons (step4372 p h) (sat_cons (step4063 p h) (sat_cons (step4286 p h) (sat_cons (step4373 p h) (sat_cons (step4319 p h) (sat_cons (step4188 p h) (sat_cons (step865 p h) (sat_cons (step935 p h) (sat_cons (step4378 p h) (sat_cons (step4379 p h) (sat_cons (step3170 p h) (sat_cons (step988 p h) (sat_cons (step1388 p h) (sat_cons (step1559 p h) (sat_cons (step3536 p h) (sat_cons (step1554 p h) (sat_cons (step3446 p h) (sat_cons (step1136 p h) (sat_nil p))))))))))))))))))))))
def c4381 : List Lit := [(27, true)]
theorem step4381 (p : Nat → Bool) (h : Constraints p) : clause p c4381 = true :=
  Snake9.LocalRup.prove_clause [c4380, c844] c4381 (by decide) p (sat_cons (step4380 p h) (sat_cons (step844 p h) (sat_nil p)))
def c4382 : List Lit := [(109, false)]
theorem step4382 (p : Nat → Bool) (h : Constraints p) : clause p c4382 = true :=
  Snake9.LocalRup.prove_clause [c4381, c4286, c4063, c287] c4382 (by decide) p (sat_cons (step4381 p h) (sat_cons (step4286 p h) (sat_cons (step4063 p h) (sat_cons (step287 p h) (sat_nil p)))))
def c4383 : List Lit := [(57, false)]
theorem step4383 (p : Nat → Bool) (h : Constraints p) : clause p c4383 = true :=
  Snake9.LocalRup.prove_clause [c4381, c4286, c4063, c286] c4383 (by decide) p (sat_cons (step4381 p h) (sat_cons (step4286 p h) (sat_cons (step4063 p h) (sat_cons (step286 p h) (sat_nil p)))))
def c4384 : List Lit := [(8, false)]
theorem step4384 (p : Nat → Bool) (h : Constraints p) : clause p c4384 = true :=
  Snake9.LocalRup.prove_clause [c4381, c4286, c4063, c274] c4384 (by decide) p (sat_cons (step4381 p h) (sat_cons (step4286 p h) (sat_cons (step4063 p h) (sat_cons (step274 p h) (sat_nil p)))))
def c4385 : List Lit := [(1670, true)]
theorem step4385 (p : Nat → Bool) (h : Constraints p) : clause p c4385 = true :=
  Snake9.LocalRup.prove_clause [c4382, c4319, c4373, c3446] c4385 (by decide) p (sat_cons (step4382 p h) (sat_cons (step4319 p h) (sat_cons (step4373 p h) (sat_cons (step3446 p h) (sat_nil p)))))
def c4386 : List Lit := [(1531, true)]
theorem step4386 (p : Nat → Bool) (h : Constraints p) : clause p c4386 = true :=
  Snake9.LocalRup.prove_clause [c4383, c895] c4386 (by decide) p (sat_cons (step4383 p h) (sat_cons (step895 p h) (sat_nil p)))
def c4387 : List Lit := [(1550, false)]
theorem step4387 (p : Nat → Bool) (h : Constraints p) : clause p c4387 = true :=
  Snake9.LocalRup.prove_clause [c4385, c4384, c4337] c4387 (by decide) p (sat_cons (step4385 p h) (sat_cons (step4384 p h) (sat_cons (step4337 p h) (sat_nil p))))
def c4388 : List Lit := [(1529, false)]
theorem step4388 (p : Nat → Bool) (h : Constraints p) : clause p c4388 = true :=
  Snake9.LocalRup.prove_clause [c4386, c4372, c901] c4388 (by decide) p (sat_cons (step4386 p h) (sat_cons (step4372 p h) (sat_cons (step901 p h) (sat_nil p))))
def c4389 : List Lit := [(1515, false)]
theorem step4389 (p : Nat → Bool) (h : Constraints p) : clause p c4389 = true :=
  Snake9.LocalRup.prove_clause [c4387, c4336, c940] c4389 (by decide) p (sat_cons (step4387 p h) (sat_cons (step4336 p h) (sat_cons (step940 p h) (sat_nil p))))
def c4390 : List Lit := [(53, true)]
theorem step4390 (p : Nat → Bool) (h : Constraints p) : clause p c4390 = true :=
  Snake9.LocalRup.prove_clause [c4388, c893] c4390 (by decide) p (sat_cons (step4388 p h) (sat_cons (step893 p h) (sat_nil p)))
def c4391 : List Lit := [(1511, false)]
theorem step4391 (p : Nat → Bool) (h : Constraints p) : clause p c4391 = true :=
  Snake9.LocalRup.prove_clause [c4389, c862] c4391 (by decide) p (sat_cons (step4389 p h) (sat_cons (step862 p h) (sat_nil p)))
def c4392 : List Lit := [(1671, true)]
theorem step4392 (p : Nat → Bool) (h : Constraints p) : clause p c4392 = true :=
  Snake9.LocalRup.prove_clause [c4390, c4382, c4319, c4373, c3448] c4392 (by decide) p (sat_cons (step4390 p h) (sat_cons (step4382 p h) (sat_cons (step4319 p h) (sat_cons (step4373 p h) (sat_cons (step3448 p h) (sat_nil p))))))
def c4393 : List Lit := [(1492, true)]
theorem step4393 (p : Nat → Bool) (h : Constraints p) : clause p c4393 = true :=
  Snake9.LocalRup.prove_clause [c4391, c4384, c4327] c4393 (by decide) p (sat_cons (step4391 p h) (sat_cons (step4384 p h) (sat_cons (step4327 p h) (sat_nil p))))
def c4394 : List Lit := []
theorem step4394 (p : Nat → Bool) (h : Constraints p) : clause p c4394 = true :=
  Snake9.LocalRup.prove_clause [c4392, c4393, c4336, c3512] c4394 (by decide) p (sat_cons (step4392 p h) (sat_cons (step4393 p h) (sat_cons (step4336 p h) (sat_cons (step3512 p h) (sat_nil p)))))
end B112E078
