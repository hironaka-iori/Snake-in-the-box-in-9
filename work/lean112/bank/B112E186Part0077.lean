import B112E186Part0076
namespace B112E186
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c6328 : List Lit := [(97, false), (107, false)]
theorem step6328 (p : Nat → Bool) (h : Constraints p) : clause p c6328 = true :=
  Snake9.LocalRup.prove_clause [c6314, c5622, c350, c351, c1114] c6328 (by decide) p (sat_cons (step6314 p h) (sat_cons (step5622 p h) (sat_cons (step350 p h) (sat_cons (step351 p h) (sat_cons (step1114 p h) (sat_nil p))))))
def c6329 : List Lit := [(1610, true), (110, false), (1598, false), (51, true), (1643, true), (1749, true), (105, false), (112, false), (107, false)]
theorem step6329 (p : Nat → Bool) (h : Constraints p) : clause p c6329 = true :=
  Snake9.LocalRup.prove_clause [c6314, c5622, c6317, c1920, c1122, c1736, c1381, c1114, c5355, c1117, c5810, c1827, c4726, c948, c1000, c1004, c2317, c5788, c5685, c950, c1674, c1588, c1479, c5724, c3940, c1231] c6329 (by decide) p (sat_cons (step6314 p h) (sat_cons (step5622 p h) (sat_cons (step6317 p h) (sat_cons (step1920 p h) (sat_cons (step1122 p h) (sat_cons (step1736 p h) (sat_cons (step1381 p h) (sat_cons (step1114 p h) (sat_cons (step5355 p h) (sat_cons (step1117 p h) (sat_cons (step5810 p h) (sat_cons (step1827 p h) (sat_cons (step4726 p h) (sat_cons (step948 p h) (sat_cons (step1000 p h) (sat_cons (step1004 p h) (sat_cons (step2317 p h) (sat_cons (step5788 p h) (sat_cons (step5685 p h) (sat_cons (step950 p h) (sat_cons (step1674 p h) (sat_cons (step1588 p h) (sat_cons (step1479 p h) (sat_cons (step5724 p h) (sat_cons (step3940 p h) (sat_cons (step1231 p h) (sat_nil p)))))))))))))))))))))))))))
def c6330 : List Lit := [(100, true), (83, true)]
theorem step6330 (p : Nat → Bool) (h : Constraints p) : clause p c6330 = true :=
  Snake9.LocalRup.prove_clause [c6317, c6284, c5622, c6314, c6296, c6326, c6328, c1182, c1920, c5258, c1784, c1313, c3989, c1478, c1133, c4109, c4726, c948, c1122, c6327, c2093, c3960, c1200, c3988, c1279, c1318, c1736, c6061, c4891, c2029, c4030, c1666, c1381, c1114, c5355, c1117, c6329, c3984, c1916, c2497, c2883, c4117, c4182, c3482, c6288, c1560] c6330 (by decide) p (sat_cons (step6317 p h) (sat_cons (step6284 p h) (sat_cons (step5622 p h) (sat_cons (step6314 p h) (sat_cons (step6296 p h) (sat_cons (step6326 p h) (sat_cons (step6328 p h) (sat_cons (step1182 p h) (sat_cons (step1920 p h) (sat_cons (step5258 p h) (sat_cons (step1784 p h) (sat_cons (step1313 p h) (sat_cons (step3989 p h) (sat_cons (step1478 p h) (sat_cons (step1133 p h) (sat_cons (step4109 p h) (sat_cons (step4726 p h) (sat_cons (step948 p h) (sat_cons (step1122 p h) (sat_cons (step6327 p h) (sat_cons (step2093 p h) (sat_cons (step3960 p h) (sat_cons (step1200 p h) (sat_cons (step3988 p h) (sat_cons (step1279 p h) (sat_cons (step1318 p h) (sat_cons (step1736 p h) (sat_cons (step6061 p h) (sat_cons (step4891 p h) (sat_cons (step2029 p h) (sat_cons (step4030 p h) (sat_cons (step1666 p h) (sat_cons (step1381 p h) (sat_cons (step1114 p h) (sat_cons (step5355 p h) (sat_cons (step1117 p h) (sat_cons (step6329 p h) (sat_cons (step3984 p h) (sat_cons (step1916 p h) (sat_cons (step2497 p h) (sat_cons (step2883 p h) (sat_cons (step4117 p h) (sat_cons (step4182 p h) (sat_cons (step3482 p h) (sat_cons (step6288 p h) (sat_cons (step1560 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))
def c6331 : List Lit := [(1759, false), (1736, true), (112, false), (83, true)]
theorem step6331 (p : Nat → Bool) (h : Constraints p) : clause p c6331 = true :=
  Snake9.LocalRup.prove_clause [c5622, c6284, c6296, c1235, c6330, c1478, c6326, c1920, c5258, c1133, c4109, c1784, c1318, c1312, c6061, c2577, c4891, c1752, c1053, c5069, c1946, c1613, c1705, c6322, c1033, c1005, c5685, c2612, c1801, c3947, c1068, c1953, c6041, c1001] c6331 (by decide) p (sat_cons (step5622 p h) (sat_cons (step6284 p h) (sat_cons (step6296 p h) (sat_cons (step1235 p h) (sat_cons (step6330 p h) (sat_cons (step1478 p h) (sat_cons (step6326 p h) (sat_cons (step1920 p h) (sat_cons (step5258 p h) (sat_cons (step1133 p h) (sat_cons (step4109 p h) (sat_cons (step1784 p h) (sat_cons (step1318 p h) (sat_cons (step1312 p h) (sat_cons (step6061 p h) (sat_cons (step2577 p h) (sat_cons (step4891 p h) (sat_cons (step1752 p h) (sat_cons (step1053 p h) (sat_cons (step5069 p h) (sat_cons (step1946 p h) (sat_cons (step1613 p h) (sat_cons (step1705 p h) (sat_cons (step6322 p h) (sat_cons (step1033 p h) (sat_cons (step1005 p h) (sat_cons (step5685 p h) (sat_cons (step2612 p h) (sat_cons (step1801 p h) (sat_cons (step3947 p h) (sat_cons (step1068 p h) (sat_cons (step1953 p h) (sat_cons (step6041 p h) (sat_cons (step1001 p h) (sat_nil p)))))))))))))))))))))))))))))))))))
def c6332 : List Lit := [(1749, true), (112, false), (83, true)]
theorem step6332 (p : Nat → Bool) (h : Constraints p) : clause p c6332 = true :=
  Snake9.LocalRup.prove_clause [c6317, c6285, c5622, c6314, c6330, c1478, c6326, c1920, c5258, c1133, c1168, c1122, c1736, c6331, c3988, c2036, c1767, c1381, c1200, c1114, c5589] c6332 (by decide) p (sat_cons (step6317 p h) (sat_cons (step6285 p h) (sat_cons (step5622 p h) (sat_cons (step6314 p h) (sat_cons (step6330 p h) (sat_cons (step1478 p h) (sat_cons (step6326 p h) (sat_cons (step1920 p h) (sat_cons (step5258 p h) (sat_cons (step1133 p h) (sat_cons (step1168 p h) (sat_cons (step1122 p h) (sat_cons (step1736 p h) (sat_cons (step6331 p h) (sat_cons (step3988 p h) (sat_cons (step2036 p h) (sat_cons (step1767 p h) (sat_cons (step1381 p h) (sat_cons (step1200 p h) (sat_cons (step1114 p h) (sat_cons (step5589 p h) (sat_nil p))))))))))))))))))))))
def c6333 : List Lit := [(112, false), (83, true)]
theorem step6333 (p : Nat → Bool) (h : Constraints p) : clause p c6333 = true :=
  Snake9.LocalRup.prove_clause [c5622, c6284, c6296, c6330, c1478, c6326, c1920, c5258, c1133, c4109, c1784, c1313, c6332, c1988, c1279, c1318, c1312, c1767, c6061, c2577, c4891, c1752, c1200, c1053, c5069, c1946, c1613, c1705, c6322, c1033, c1981, c1005, c1046, c5685, c2612, c5772, c591, c1001, c1068, c6041] c6333 (by decide) p (sat_cons (step5622 p h) (sat_cons (step6284 p h) (sat_cons (step6296 p h) (sat_cons (step6330 p h) (sat_cons (step1478 p h) (sat_cons (step6326 p h) (sat_cons (step1920 p h) (sat_cons (step5258 p h) (sat_cons (step1133 p h) (sat_cons (step4109 p h) (sat_cons (step1784 p h) (sat_cons (step1313 p h) (sat_cons (step6332 p h) (sat_cons (step1988 p h) (sat_cons (step1279 p h) (sat_cons (step1318 p h) (sat_cons (step1312 p h) (sat_cons (step1767 p h) (sat_cons (step6061 p h) (sat_cons (step2577 p h) (sat_cons (step4891 p h) (sat_cons (step1752 p h) (sat_cons (step1200 p h) (sat_cons (step1053 p h) (sat_cons (step5069 p h) (sat_cons (step1946 p h) (sat_cons (step1613 p h) (sat_cons (step1705 p h) (sat_cons (step6322 p h) (sat_cons (step1033 p h) (sat_cons (step1981 p h) (sat_cons (step1005 p h) (sat_cons (step1046 p h) (sat_cons (step5685 p h) (sat_cons (step2612 p h) (sat_cons (step5772 p h) (sat_cons (step591 p h) (sat_cons (step1001 p h) (sat_cons (step1068 p h) (sat_cons (step6041 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))
def c6334 : List Lit := [(83, true)]
theorem step6334 (p : Nat → Bool) (h : Constraints p) : clause p c6334 = true :=
  Snake9.LocalRup.prove_clause [c6284, c6314, c5622, c1478, c6326, c1920, c5258, c1784, c1133, c1313, c4109, c1989, c1737, c6333, c4592, c6017, c1279, c1114, c1767, c1381, c1200, c1666, c1776] c6334 (by decide) p (sat_cons (step6284 p h) (sat_cons (step6314 p h) (sat_cons (step5622 p h) (sat_cons (step1478 p h) (sat_cons (step6326 p h) (sat_cons (step1920 p h) (sat_cons (step5258 p h) (sat_cons (step1784 p h) (sat_cons (step1133 p h) (sat_cons (step1313 p h) (sat_cons (step4109 p h) (sat_cons (step1989 p h) (sat_cons (step1737 p h) (sat_cons (step6333 p h) (sat_cons (step4592 p h) (sat_cons (step6017 p h) (sat_cons (step1279 p h) (sat_cons (step1114 p h) (sat_cons (step1767 p h) (sat_cons (step1381 p h) (sat_cons (step1200 p h) (sat_cons (step1666 p h) (sat_cons (step1776 p h) (sat_nil p))))))))))))))))))))))))
def c6335 : List Lit := [(1675, true)]
theorem step6335 (p : Nat → Bool) (h : Constraints p) : clause p c6335 = true :=
  Snake9.LocalRup.prove_clause [c6334, c5622, c4683] c6335 (by decide) p (sat_cons (step6334 p h) (sat_cons (step5622 p h) (sat_cons (step4683 p h) (sat_nil p))))
def c6336 : List Lit := [(48, false)]
theorem step6336 (p : Nat → Bool) (h : Constraints p) : clause p c6336 = true :=
  Snake9.LocalRup.prove_clause [c6334, c6314, c6139] c6336 (by decide) p (sat_cons (step6334 p h) (sat_cons (step6314 p h) (sat_cons (step6139 p h) (sat_nil p))))
def c6337 : List Lit := [(107, false)]
theorem step6337 (p : Nat → Bool) (h : Constraints p) : clause p c6337 = true :=
  Snake9.LocalRup.prove_clause [c6334, c5622, c6314, c4893] c6337 (by decide) p (sat_cons (step6334 p h) (sat_cons (step5622 p h) (sat_cons (step6314 p h) (sat_cons (step4893 p h) (sat_nil p)))))
def c6338 : List Lit := [(97, false)]
theorem step6338 (p : Nat → Bool) (h : Constraints p) : clause p c6338 = true :=
  Snake9.LocalRup.prove_clause [c6334, c6314, c6072] c6338 (by decide) p (sat_cons (step6334 p h) (sat_cons (step6314 p h) (sat_cons (step6072 p h) (sat_nil p))))
def c6339 : List Lit := [(1760, true)]
theorem step6339 (p : Nat → Bool) (h : Constraints p) : clause p c6339 = true :=
  Snake9.LocalRup.prove_clause [c6334, c6315] c6339 (by decide) p (sat_cons (step6334 p h) (sat_cons (step6315 p h) (sat_nil p)))
def c6340 : List Lit := [(1680, true)]
theorem step6340 (p : Nat → Bool) (h : Constraints p) : clause p c6340 = true :=
  Snake9.LocalRup.prove_clause [c6335, c5258] c6340 (by decide) p (sat_cons (step6335 p h) (sat_cons (step5258 p h) (sat_nil p)))
def c6341 : List Lit := [(1678, false)]
theorem step6341 (p : Nat → Bool) (h : Constraints p) : clause p c6341 = true :=
  Snake9.LocalRup.prove_clause [c6335, c6317, c1122] c6341 (by decide) p (sat_cons (step6335 p h) (sat_cons (step6317 p h) (sat_cons (step1122 p h) (sat_nil p))))
def c6342 : List Lit := [(1580, true)]
theorem step6342 (p : Nat → Bool) (h : Constraints p) : clause p c6342 = true :=
  Snake9.LocalRup.prove_clause [c6336, c948] c6342 (by decide) p (sat_cons (step6336 p h) (sat_cons (step948 p h) (sat_nil p)))
def c6343 : List Lit := [(1717, true)]
theorem step6343 (p : Nat → Bool) (h : Constraints p) : clause p c6343 = true :=
  Snake9.LocalRup.prove_clause [c6337, c1199] c6343 (by decide) p (sat_cons (step6337 p h) (sat_cons (step1199 p h) (sat_nil p)))
def c6344 : List Lit := [(1695, false)]
theorem step6344 (p : Nat → Bool) (h : Constraints p) : clause p c6344 = true :=
  Snake9.LocalRup.prove_clause [c6339, c6284, c1313] c6344 (by decide) p (sat_cons (step6339 p h) (sat_cons (step6284 p h) (sat_cons (step1313 p h) (sat_nil p))))
def c6345 : List Lit := [(1694, true)]
theorem step6345 (p : Nat → Bool) (h : Constraints p) : clause p c6345 = true :=
  Snake9.LocalRup.prove_clause [c6340, c1932] c6345 (by decide) p (sat_cons (step6340 p h) (sat_cons (step1932 p h) (sat_nil p)))
def c6346 : List Lit := [(1643, false)]
theorem step6346 (p : Nat → Bool) (h : Constraints p) : clause p c6346 = true :=
  Snake9.LocalRup.prove_clause [c6340, c6344, c5273] c6346 (by decide) p (sat_cons (step6340 p h) (sat_cons (step6344 p h) (sat_cons (step5273 p h) (sat_nil p))))
def c6347 : List Lit := [(70, true)]
theorem step6347 (p : Nat → Bool) (h : Constraints p) : clause p c6347 = true :=
  Snake9.LocalRup.prove_clause [c6340, c6344, c2625] c6347 (by decide) p (sat_cons (step6340 p h) (sat_cons (step6344 p h) (sat_cons (step2625 p h) (sat_nil p))))
def c6348 : List Lit := [(1761, false)]
theorem step6348 (p : Nat → Bool) (h : Constraints p) : clause p c6348 = true :=
  Snake9.LocalRup.prove_clause [c6345, c6284, c1308] c6348 (by decide) p (sat_cons (step6345 p h) (sat_cons (step6284 p h) (sat_cons (step1308 p h) (sat_nil p))))
def c6349 : List Lit := [(1780, true)]
theorem step6349 (p : Nat → Bool) (h : Constraints p) : clause p c6349 = true :=
  Snake9.LocalRup.prove_clause [c6345, c6339, c1307] c6349 (by decide) p (sat_cons (step6345 p h) (sat_cons (step6339 p h) (sat_cons (step1307 p h) (sat_nil p))))
def c6350 : List Lit := [(62, true)]
theorem step6350 (p : Nat → Bool) (h : Constraints p) : clause p c6350 = true :=
  Snake9.LocalRup.prove_clause [c6346, c1053] c6350 (by decide) p (sat_cons (step6346 p h) (sat_cons (step1053 p h) (sat_nil p)))
def c6351 : List Lit := [(60, true)]
theorem step6351 (p : Nat → Bool) (h : Constraints p) : clause p c6351 = true :=
  Snake9.LocalRup.prove_clause [c6346, c1054] c6351 (by decide) p (sat_cons (step6346 p h) (sat_cons (step1054 p h) (sat_nil p)))
def c6352 : List Lit := [(1598, true)]
theorem step6352 (p : Nat → Bool) (h : Constraints p) : clause p c6352 = true :=
  Snake9.LocalRup.prove_clause [c6346, c6342, c1519] c6352 (by decide) p (sat_cons (step6346 p h) (sat_cons (step6342 p h) (sat_cons (step1519 p h) (sat_nil p))))
def c6353 : List Lit := [(1513, true)]
theorem step6353 (p : Nat → Bool) (h : Constraints p) : clause p c6353 = true :=
  Snake9.LocalRup.prove_clause [c6347, c6296, c1946] c6353 (by decide) p (sat_cons (step6347 p h) (sat_cons (step6296 p h) (sat_cons (step1946 p h) (sat_nil p))))
def c6354 : List Lit := [(51, false)]
theorem step6354 (p : Nat → Bool) (h : Constraints p) : clause p c6354 = true :=
  Snake9.LocalRup.prove_clause [c6347, c6350, c6351, c1512] c6354 (by decide) p (sat_cons (step6347 p h) (sat_cons (step6350 p h) (sat_cons (step6351 p h) (sat_cons (step1512 p h) (sat_nil p)))))
def c6355 : List Lit := [(1727, false)]
theorem step6355 (p : Nat → Bool) (h : Constraints p) : clause p c6355 = true :=
  Snake9.LocalRup.prove_clause [c6348, c3992] c6355 (by decide) p (sat_cons (step6348 p h) (sat_cons (step3992 p h) (sat_nil p)))
def c6356 : List Lit := [(1632, false)]
theorem step6356 (p : Nat → Bool) (h : Constraints p) : clause p c6356 = true :=
  Snake9.LocalRup.prove_clause [c6349, c1752] c6356 (by decide) p (sat_cons (step6349 p h) (sat_cons (step1752 p h) (sat_nil p)))
def c6357 : List Lit := [(1545, true)]
theorem step6357 (p : Nat → Bool) (h : Constraints p) : clause p c6357 = true :=
  Snake9.LocalRup.prove_clause [c6353, c1705] c6357 (by decide) p (sat_cons (step6353 p h) (sat_cons (step1705 p h) (sat_nil p)))
def c6358 : List Lit := [(1611, false)]
theorem step6358 (p : Nat → Bool) (h : Constraints p) : clause p c6358 = true :=
  Snake9.LocalRup.prove_clause [c6357, c6356, c1033] c6358 (by decide) p (sat_cons (step6357 p h) (sat_cons (step6356 p h) (sat_cons (step1033 p h) (sat_nil p))))
def c6359 : List Lit := [(112, true), (100, false)]
theorem step6359 (p : Nat → Bool) (h : Constraints p) : clause p c6359 = true :=
  Snake9.LocalRup.prove_clause [c6354, c6350, c6348, c6338, c6343, c6296, c6340, c6284, c6337, c6347, c6346, c6339, c5069, c1613, c6322, c6123, c1284, c6094, c2823, c1982, c1000, c2633, c1953] c6359 (by decide) p (sat_cons (step6354 p h) (sat_cons (step6350 p h) (sat_cons (step6348 p h) (sat_cons (step6338 p h) (sat_cons (step6343 p h) (sat_cons (step6296 p h) (sat_cons (step6340 p h) (sat_cons (step6284 p h) (sat_cons (step6337 p h) (sat_cons (step6347 p h) (sat_cons (step6346 p h) (sat_cons (step6339 p h) (sat_cons (step5069 p h) (sat_cons (step1613 p h) (sat_cons (step6322 p h) (sat_cons (step6123 p h) (sat_cons (step1284 p h) (sat_cons (step6094 p h) (sat_cons (step2823 p h) (sat_cons (step1982 p h) (sat_cons (step1000 p h) (sat_cons (step2633 p h) (sat_cons (step1953 p h) (sat_nil p))))))))))))))))))))))))
def c6360 : List Lit := [(100, false)]
theorem step6360 (p : Nat → Bool) (h : Constraints p) : clause p c6360 = true :=
  Snake9.LocalRup.prove_clause [c6346, c6347, c6350, c6354, c6358, c6286, c6337, c6334, c6348, c6344, c6351, c6338, c6343, c6340, c6339, c6296, c5069, c1613, c6322, c1005, c6359, c386, c5685, c5233, c5366, c1068, c1284, c1806, c6094, c1982, c2823] c6360 (by decide) p (sat_cons (step6346 p h) (sat_cons (step6347 p h) (sat_cons (step6350 p h) (sat_cons (step6354 p h) (sat_cons (step6358 p h) (sat_cons (step6286 p h) (sat_cons (step6337 p h) (sat_cons (step6334 p h) (sat_cons (step6348 p h) (sat_cons (step6344 p h) (sat_cons (step6351 p h) (sat_cons (step6338 p h) (sat_cons (step6343 p h) (sat_cons (step6340 p h) (sat_cons (step6339 p h) (sat_cons (step6296 p h) (sat_cons (step5069 p h) (sat_cons (step1613 p h) (sat_cons (step6322 p h) (sat_cons (step1005 p h) (sat_cons (step6359 p h) (sat_cons (step386 p h) (sat_cons (step5685 p h) (sat_cons (step5233 p h) (sat_cons (step5366 p h) (sat_cons (step1068 p h) (sat_cons (step1284 p h) (sat_cons (step1806 p h) (sat_cons (step6094 p h) (sat_cons (step1982 p h) (sat_cons (step2823 p h) (sat_nil p))))))))))))))))))))))))))))))))
def c6361 : List Lit := [(1712, true)]
theorem step6361 (p : Nat → Bool) (h : Constraints p) : clause p c6361 = true :=
  Snake9.LocalRup.prove_clause [c6360, c6334, c1948] c6361 (by decide) p (sat_cons (step6360 p h) (sat_cons (step6334 p h) (sat_cons (step1948 p h) (sat_nil p))))
def c6362 : List Lit := [(112, true)]
theorem step6362 (p : Nat → Bool) (h : Constraints p) : clause p c6362 = true :=
  Snake9.LocalRup.prove_clause [c6360, c6348, c6334, c6338, c6337, c2637] c6362 (by decide) p (sat_cons (step6360 p h) (sat_cons (step6348 p h) (sat_cons (step6334 p h) (sat_cons (step6338 p h) (sat_cons (step6337 p h) (sat_cons (step2637 p h) (sat_nil p)))))))
def c6363 : List Lit := [(1726, true)]
theorem step6363 (p : Nat → Bool) (h : Constraints p) : clause p c6363 = true :=
  Snake9.LocalRup.prove_clause [c6360, c6343, c6338, c2093] c6363 (by decide) p (sat_cons (step6360 p h) (sat_cons (step6343 p h) (sat_cons (step6338 p h) (sat_cons (step2093 p h) (sat_nil p)))))
def c6364 : List Lit := [(1718, false)]
theorem step6364 (p : Nat → Bool) (h : Constraints p) : clause p c6364 = true :=
  Snake9.LocalRup.prove_clause [c6360, c6355, c6338, c2668] c6364 (by decide) p (sat_cons (step6360 p h) (sat_cons (step6355 p h) (sat_cons (step6338 p h) (sat_cons (step2668 p h) (sat_nil p)))))
def c6365 : List Lit := [(1721, false)]
theorem step6365 (p : Nat → Bool) (h : Constraints p) : clause p c6365 = true :=
  Snake9.LocalRup.prove_clause [c6361, c6355, c1218] c6365 (by decide) p (sat_cons (step6361 p h) (sat_cons (step6355 p h) (sat_cons (step1218 p h) (sat_nil p))))
def c6366 : List Lit := [(1749, false)]
theorem step6366 (p : Nat → Bool) (h : Constraints p) : clause p c6366 = true :=
  Snake9.LocalRup.prove_clause [c6363, c6348, c1284] c6366 (by decide) p (sat_cons (step6363 p h) (sat_cons (step6348 p h) (sat_cons (step1284 p h) (sat_nil p))))
def c6367 : List Lit := [(105, true)]
theorem step6367 (p : Nat → Bool) (h : Constraints p) : clause p c6367 = true :=
  Snake9.LocalRup.prove_clause [c6364, c6337, c1201] c6367 (by decide) p (sat_cons (step6364 p h) (sat_cons (step6337 p h) (sat_cons (step1201 p h) (sat_nil p))))
def c6368 : List Lit := [(1716, false)]
theorem step6368 (p : Nat → Bool) (h : Constraints p) : clause p c6368 = true :=
  Snake9.LocalRup.prove_clause [c6365, c6343, c1208] c6368 (by decide) p (sat_cons (step6365 p h) (sat_cons (step6343 p h) (sat_cons (step1208 p h) (sat_nil p))))
def c6369 : List Lit := [(1736, false)]
theorem step6369 (p : Nat → Bool) (h : Constraints p) : clause p c6369 = true :=
  Snake9.LocalRup.prove_clause [c6366, c1736] c6369 (by decide) p (sat_cons (step6366 p h) (sat_cons (step1736 p h) (sat_nil p)))
def c6370 : List Lit := [(1574, true)]
theorem step6370 (p : Nat → Bool) (h : Constraints p) : clause p c6370 = true :=
  Snake9.LocalRup.prove_clause [c6367, c6346, c6366, c6362, c5810] c6370 (by decide) p (sat_cons (step6367 p h) (sat_cons (step6346 p h) (sat_cons (step6366 p h) (sat_cons (step6362 p h) (sat_cons (step5810 p h) (sat_nil p))))))
def c6371 : List Lit := [(111, false)]
theorem step6371 (p : Nat → Bool) (h : Constraints p) : clause p c6371 = true :=
  Snake9.LocalRup.prove_clause [c6369, c6367, c1827] c6371 (by decide) p (sat_cons (step6369 p h) (sat_cons (step6367 p h) (sat_cons (step1827 p h) (sat_nil p))))
def c6372 : List Lit := [(1600, false)]
theorem step6372 (p : Nat → Bool) (h : Constraints p) : clause p c6372 = true :=
  Snake9.LocalRup.prove_clause [c6370, c6358, c1001] c6372 (by decide) p (sat_cons (step6370 p h) (sat_cons (step6358 p h) (sat_cons (step1001 p h) (sat_nil p))))
def c6373 : List Lit := [(1651, false)]
theorem step6373 (p : Nat → Bool) (h : Constraints p) : clause p c6373 = true :=
  Snake9.LocalRup.prove_clause [c6372, c6351, c6344, c6340, c1806] c6373 (by decide) p (sat_cons (step6372 p h) (sat_cons (step6351 p h) (sat_cons (step6344 p h) (sat_cons (step6340 p h) (sat_cons (step1806 p h) (sat_nil p))))))
def c6374 : List Lit := [(69, true)]
theorem step6374 (p : Nat → Bool) (h : Constraints p) : clause p c6374 = true :=
  Snake9.LocalRup.prove_clause [c6373, c1068] c6374 (by decide) p (sat_cons (step6373 p h) (sat_cons (step1068 p h) (sat_nil p)))
def c6375 : List Lit := [(1599, false)]
theorem step6375 (p : Nat → Bool) (h : Constraints p) : clause p c6375 = true :=
  Snake9.LocalRup.prove_clause [c6358, c6370, c6340, c6339, c6296, c6371, c6362, c5622, c6334, c1005, c1000, c5685, c2823, c1676, c2883, c294] c6375 (by decide) p (sat_cons (step6358 p h) (sat_cons (step6370 p h) (sat_cons (step6340 p h) (sat_cons (step6339 p h) (sat_cons (step6296 p h) (sat_cons (step6371 p h) (sat_cons (step6362 p h) (sat_cons (step5622 p h) (sat_cons (step6334 p h) (sat_cons (step1005 p h) (sat_cons (step1000 p h) (sat_cons (step5685 p h) (sat_cons (step2823 p h) (sat_cons (step1676 p h) (sat_cons (step2883 p h) (sat_cons (step294 p h) (sat_nil p)))))))))))))))))
def c6376 : List Lit := [(53, false)]
theorem step6376 (p : Nat → Bool) (h : Constraints p) : clause p c6376 = true :=
  Snake9.LocalRup.prove_clause [c6375, c6354, c6350, c6347, c6322] c6376 (by decide) p (sat_cons (step6375 p h) (sat_cons (step6354 p h) (sat_cons (step6350 p h) (sat_cons (step6347 p h) (sat_cons (step6322 p h) (sat_nil p))))))
def c6377 : List Lit := [(1588, false)]
theorem step6377 (p : Nat → Bool) (h : Constraints p) : clause p c6377 = true :=
  Snake9.LocalRup.prove_clause [c6375, c6342, c6354, c1903] c6377 (by decide) p (sat_cons (step6375 p h) (sat_cons (step6342 p h) (sat_cons (step6354 p h) (sat_cons (step1903 p h) (sat_nil p)))))
def c6378 : List Lit := [(92, false)]
theorem step6378 (p : Nat → Bool) (h : Constraints p) : clause p c6378 = true :=
  Snake9.LocalRup.prove_clause [c6377, c6368, c6376, c5492] c6378 (by decide) p (sat_cons (step6377 p h) (sat_cons (step6368 p h) (sat_cons (step6376 p h) (sat_cons (step5492 p h) (sat_nil p)))))
def c6379 : List Lit := [(91, true)]
theorem step6379 (p : Nat → Bool) (h : Constraints p) : clause p c6379 = true :=
  Snake9.LocalRup.prove_clause [c6378, c6341, c1117] c6379 (by decide) p (sat_cons (step6378 p h) (sat_cons (step6341 p h) (sat_cons (step1117 p h) (sat_nil p))))
def c6380 : List Lit := [(1534, true)]
theorem step6380 (p : Nat → Bool) (h : Constraints p) : clause p c6380 = true :=
  Snake9.LocalRup.prove_clause [c6379, c6334, c1928] c6380 (by decide) p (sat_cons (step6379 p h) (sat_cons (step6334 p h) (sat_cons (step1928 p h) (sat_nil p))))
def c6381 : List Lit := [(88, false)]
theorem step6381 (p : Nat → Bool) (h : Constraints p) : clause p c6381 = true :=
  Snake9.LocalRup.prove_clause [c6379, c6362, c6334, c385] c6381 (by decide) p (sat_cons (step6379 p h) (sat_cons (step6362 p h) (sat_cons (step6334 p h) (sat_cons (step385 p h) (sat_nil p)))))
def c6382 : List Lit := [(1610, false)]
theorem step6382 (p : Nat → Bool) (h : Constraints p) : clause p c6382 = true :=
  Snake9.LocalRup.prove_clause [c6380, c6296, c6339, c6340, c2823] c6382 (by decide) p (sat_cons (step6380 p h) (sat_cons (step6296 p h) (sat_cons (step6339 p h) (sat_cons (step6340 p h) (sat_cons (step2823 p h) (sat_nil p))))))
def c6383 : List Lit := [(35, true)]
theorem step6383 (p : Nat → Bool) (h : Constraints p) : clause p c6383 = true :=
  Snake9.LocalRup.prove_clause [c6381, c6362, c6374, c6338, c6337, c6286, c5233] c6383 (by decide) p (sat_cons (step6381 p h) (sat_cons (step6362 p h) (sat_cons (step6374 p h) (sat_cons (step6338 p h) (sat_cons (step6337 p h) (sat_cons (step6286 p h) (sat_cons (step5233 p h) (sat_nil p))))))))
def c6384 : List Lit := [(1575, false)]
theorem step6384 (p : Nat → Bool) (h : Constraints p) : clause p c6384 = true :=
  Snake9.LocalRup.prove_clause [c6382, c6352, c1004] c6384 (by decide) p (sat_cons (step6382 p h) (sat_cons (step6352 p h) (sat_cons (step1004 p h) (sat_nil p))))
def c6385 : List Lit := []
theorem step6385 (p : Nat → Bool) (h : Constraints p) : clause p c6385 = true :=
  Snake9.LocalRup.prove_clause [c6383, c6384, c6362, c5685] c6385 (by decide) p (sat_cons (step6383 p h) (sat_cons (step6384 p h) (sat_cons (step6362 p h) (sat_cons (step5685 p h) (sat_nil p)))))
end B112E186
