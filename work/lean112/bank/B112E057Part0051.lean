import B112E057Part0050
namespace B112E057
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c5289 : List Lit := [(26, false), (874, true), (4, true), (5, false), (73, false)]
theorem step5289 (p : Nat → Bool) (h : Constraints p) : clause p c5289 = true :=
  Snake9.LocalRup.prove_clause [c2103, c38, c1277, c1266] c5289 (by decide) p (sat_cons (step2103 p h) (sat_cons (step38 p h) (sat_cons (step1277 p h) (sat_cons (step1266 p h) (sat_nil p)))))
def c5290 : List Lit := [(1038, true), (1031, false), (88, false), (1075, true)]
theorem step5290 (p : Nat → Bool) (h : Constraints p) : clause p c5290 = true :=
  Snake9.LocalRup.prove_clause [c5231, c1570, c2081] c5290 (by decide) p (sat_cons (step5231 p h) (sat_cons (step1570 p h) (sat_cons (step2081 p h) (sat_nil p))))
def c5291 : List Lit := [(1061, true), (88, false), (1101, true), (1124, true), (1043, false)]
theorem step5291 (p : Nat → Bool) (h : Constraints p) : clause p c5291 = true :=
  Snake9.LocalRup.prove_clause [c1587, c1621, c2978, c1613, c2110, c1675, c1683, c1709, c5174, c1601, c1617, c1588, c1582, c1583, c2167, c756, c754, c3285, c1713, c1737, c4880] c5291 (by decide) p (sat_cons (step1587 p h) (sat_cons (step1621 p h) (sat_cons (step2978 p h) (sat_cons (step1613 p h) (sat_cons (step2110 p h) (sat_cons (step1675 p h) (sat_cons (step1683 p h) (sat_cons (step1709 p h) (sat_cons (step5174 p h) (sat_cons (step1601 p h) (sat_cons (step1617 p h) (sat_cons (step1588 p h) (sat_cons (step1582 p h) (sat_cons (step1583 p h) (sat_cons (step2167 p h) (sat_cons (step756 p h) (sat_cons (step754 p h) (sat_cons (step3285 p h) (sat_cons (step1713 p h) (sat_cons (step1737 p h) (sat_cons (step4880 p h) (sat_nil p))))))))))))))))))))))
def c5292 : List Lit := [(109, false), (1111, true), (117, true)]
theorem step5292 (p : Nat → Bool) (h : Constraints p) : clause p c5292 = true :=
  Snake9.LocalRup.prove_clause [c1731, c1724, c1729, c1726, c878, c2351] c5292 (by decide) p (sat_cons (step1731 p h) (sat_cons (step1724 p h) (sat_cons (step1729 p h) (sat_cons (step1726 p h) (sat_cons (step878 p h) (sat_cons (step2351 p h) (sat_nil p)))))))
def c5293 : List Lit := [(1111, true), (238, true), (125, false), (117, true), (113, false)]
theorem step5293 (p : Nat → Bool) (h : Constraints p) : clause p c5293 = true :=
  Snake9.LocalRup.prove_clause [c1729, c5292, c1727, c883, c909, c2357] c5293 (by decide) p (sat_cons (step1729 p h) (sat_cons (step5292 p h) (sat_cons (step1727 p h) (sat_cons (step883 p h) (sat_cons (step909 p h) (sat_cons (step2357 p h) (sat_nil p)))))))
def c5294 : List Lit := [(50, false), (112, false), (121, false), (59, false), (10, false), (15, false)]
theorem step5294 (p : Nat → Bool) (h : Constraints p) : clause p c5294 = true :=
  Snake9.LocalRup.prove_clause [c114, c393, c319, c2263] c5294 (by decide) p (sat_cons (step114 p h) (sat_cons (step393 p h) (sat_cons (step319 p h) (sat_cons (step2263 p h) (sat_nil p)))))
def c5295 : List Lit := [(891, true), (13, true), (10, false), (15, false)]
theorem step5295 (p : Nat → Bool) (h : Constraints p) : clause p c5295 = true :=
  Snake9.LocalRup.prove_clause [c1312, c1313, c2597, c185, c2226] c5295 (by decide) p (sat_cons (step1312 p h) (sat_cons (step1313 p h) (sat_cons (step2597 p h) (sat_cons (step185 p h) (sat_cons (step2226 p h) (sat_nil p))))))
def c5296 : List Lit := [(872, true), (2, false), (11, false), (869, false), (10, false)]
theorem step5296 (p : Nat → Bool) (h : Constraints p) : clause p c5296 = true :=
  Snake9.LocalRup.prove_clause [c2973, c1273, c7, c1265] c5296 (by decide) p (sat_cons (step2973 p h) (sat_cons (step1273 p h) (sat_cons (step7 p h) (sat_cons (step1265 p h) (sat_nil p)))))
def c5297 : List Lit := [(951, true), (42, true), (40, true), (931, false), (940, false), (956, true)]
theorem step5297 (p : Nat → Bool) (h : Constraints p) : clause p c5297 = true :=
  Snake9.LocalRup.prove_clause [c1391, c1397, c1413, c1431, c1427, c1398, c1414, c1393, c1405, c2506] c5297 (by decide) p (sat_cons (step1391 p h) (sat_cons (step1397 p h) (sat_cons (step1413 p h) (sat_cons (step1431 p h) (sat_cons (step1427 p h) (sat_cons (step1398 p h) (sat_cons (step1414 p h) (sat_cons (step1393 p h) (sat_cons (step1405 p h) (sat_cons (step2506 p h) (sat_nil p)))))))))))
def c5298 : List Lit := [(1053, false), (1043, false), (1073, true), (1027, false)]
theorem step5298 (p : Nat → Bool) (h : Constraints p) : clause p c5298 = true :=
  Snake9.LocalRup.prove_clause [c1558, c2084, c1636, c2978, c1643, c2085, c2882, c2970] c5298 (by decide) p (sat_cons (step1558 p h) (sat_cons (step2084 p h) (sat_cons (step1636 p h) (sat_cons (step2978 p h) (sat_cons (step1643 p h) (sat_cons (step2085 p h) (sat_cons (step2882 p h) (sat_cons (step2970 p h) (sat_nil p)))))))))
def c5299 : List Lit := [(867, true), (23, true), (40, true), (13, true), (10, false)]
theorem step5299 (p : Nat → Bool) (h : Constraints p) : clause p c5299 = true :=
  Snake9.LocalRup.prove_clause [c1264, c1265, c2196, c7] c5299 (by decide) p (sat_cons (step1264 p h) (sat_cons (step1265 p h) (sat_cons (step2196 p h) (sat_cons (step7 p h) (sat_nil p)))))
def c5300 : List Lit := [(1043, true), (1041, true), (70, false), (4, false), (13, true), (1027, false), (15, false)]
theorem step5300 (p : Nat → Bool) (h : Constraints p) : clause p c5300 = true :=
  Snake9.LocalRup.prove_clause [c1579, c1580, c457, c664, c4178, c2311, c628] c5300 (by decide) p (sat_cons (step1579 p h) (sat_cons (step1580 p h) (sat_cons (step457 p h) (sat_cons (step664 p h) (sat_cons (step4178 p h) (sat_cons (step2311 p h) (sat_cons (step628 p h) (sat_nil p))))))))
def c5301 : List Lit := [(103, false), (84, false), (1045, false), (1053, false), (1075, true), (1027, false), (15, false)]
theorem step5301 (p : Nat → Bool) (h : Constraints p) : clause p c5301 = true :=
  Snake9.LocalRup.prove_clause [c669, c671, c666, c5027, c1581, c1591] c5301 (by decide) p (sat_cons (step669 p h) (sat_cons (step671 p h) (sat_cons (step666 p h) (sat_cons (step5027 p h) (sat_cons (step1581 p h) (sat_cons (step1591 p h) (sat_nil p)))))))
def c5302 : List Lit := [(88, true), (1045, true), (1061, false), (1158, true), (1124, false)]
theorem step5302 (p : Nat → Bool) (h : Constraints p) : clause p c5302 = true :=
  Snake9.LocalRup.prove_clause [c1583, c1582, c3845, c4823, c1767, c1651, c1803] c5302 (by decide) p (sat_cons (step1583 p h) (sat_cons (step1582 p h) (sat_cons (step3845 p h) (sat_cons (step4823 p h) (sat_cons (step1767 p h) (sat_cons (step1651 p h) (sat_cons (step1803 p h) (sat_nil p))))))))
def c5303 : List Lit := [(1053, true), (1088, true), (30, false)]
theorem step5303 (p : Nat → Bool) (h : Constraints p) : clause p c5303 = true :=
  Snake9.LocalRup.prove_clause [c1597, c2110, c5205, c832, c1675, c1678, c1684] c5303 (by decide) p (sat_cons (step1597 p h) (sat_cons (step2110 p h) (sat_cons (step5205 p h) (sat_cons (step832 p h) (sat_cons (step1675 p h) (sat_cons (step1678 p h) (sat_cons (step1684 p h) (sat_nil p))))))))
def c5304 : List Lit := [(893, true), (23, false), (59, false)]
theorem step5304 (p : Nat → Bool) (h : Constraints p) : clause p c5304 = true :=
  Snake9.LocalRup.prove_clause [c1315, c1316, c209] c5304 (by decide) p (sat_cons (step1315 p h) (sat_cons (step1316 p h) (sat_cons (step209 p h) (sat_nil p))))
def c5305 : List Lit := [(910, true), (896, false), (30, true), (891, false), (13, true), (59, false)]
theorem step5305 (p : Nat → Bool) (h : Constraints p) : clause p c5305 = true :=
  Snake9.LocalRup.prove_clause [c1330, c1332, c1355, c1351, c1322, c1333, c2697, c1331] c5305 (by decide) p (sat_cons (step1330 p h) (sat_cons (step1332 p h) (sat_cons (step1355 p h) (sat_cons (step1351 p h) (sat_cons (step1322 p h) (sat_cons (step1333 p h) (sat_cons (step2697 p h) (sat_cons (step1331 p h) (sat_nil p)))))))))
def c5306 : List Lit := [(884, true), (13, true), (869, false), (10, false)]
theorem step5306 (p : Nat → Bool) (h : Constraints p) : clause p c5306 = true :=
  Snake9.LocalRup.prove_clause [c1301, c2897, c2924, c1282, c5296] c5306 (by decide) p (sat_cons (step1301 p h) (sat_cons (step2897 p h) (sat_cons (step2924 p h) (sat_cons (step1282 p h) (sat_cons (step5296 p h) (sat_nil p))))))
def c5307 : List Lit := [(40, false), (934, true), (4, false), (59, false)]
theorem step5307 (p : Nat → Bool) (h : Constraints p) : clause p c5307 = true :=
  Snake9.LocalRup.prove_clause [c295, c291, c1393] c5307 (by decide) p (sat_cons (step295 p h) (sat_cons (step291 p h) (sat_cons (step1393 p h) (sat_nil p))))
def c5308 : List Lit := [(1101, false), (1061, false), (73, true), (1055, false), (1029, false), (1107, false), (90, false), (114, true), (1043, false), (1025, false)]
theorem step5308 (p : Nat → Bool) (h : Constraints p) : clause p c5308 = true :=
  Snake9.LocalRup.prove_clause [c4887, c2833] c5308 (by decide) p (sat_cons (step4887 p h) (sat_cons (step2833 p h) (sat_nil p)))
def c5309 : List Lit := [(1135, false), (1075, false)]
theorem step5309 (p : Nat → Bool) (h : Constraints p) : clause p c5309 = true :=
  Snake9.LocalRup.prove_clause [c4887, c1810] c5309 (by decide) p (sat_cons (step4887 p h) (sat_cons (step1810 p h) (sat_nil p)))
def c5310 : List Lit := [(1078, false), (1132, false)]
theorem step5310 (p : Nat → Bool) (h : Constraints p) : clause p c5310 = true :=
  Snake9.LocalRup.prove_clause [c4887, c1823] c5310 (by decide) p (sat_cons (step4887 p h) (sat_cons (step1823 p h) (sat_nil p)))
def c5311 : List Lit := [(1137, false), (1073, false)]
theorem step5311 (p : Nat → Bool) (h : Constraints p) : clause p c5311 = true :=
  Snake9.LocalRup.prove_clause [c4887, c1799] c5311 (by decide) p (sat_cons (step4887 p h) (sat_cons (step1799 p h) (sat_nil p)))
def c5312 : List Lit := [(1139, false), (1071, false)]
theorem step5312 (p : Nat → Bool) (h : Constraints p) : clause p c5312 = true :=
  Snake9.LocalRup.prove_clause [c4887, c1789] c5312 (by decide) p (sat_cons (step4887 p h) (sat_cons (step1789 p h) (sat_nil p)))
def c5313 : List Lit := [(1138, false), (1072, false)]
theorem step5313 (p : Nat → Bool) (h : Constraints p) : clause p c5313 = true :=
  Snake9.LocalRup.prove_clause [c4887, c1794] c5313 (by decide) p (sat_cons (step4887 p h) (sat_cons (step1794 p h) (sat_nil p)))
def c5314 : List Lit := [(1087, false), (1075, false), (1124, false), (1032, false), (1045, false), (1055, false), (69, true), (90, false), (88, true)]
theorem step5314 (p : Nat → Bool) (h : Constraints p) : clause p c5314 = true :=
  Snake9.LocalRup.prove_clause [c4887, c2841] c5314 (by decide) p (sat_cons (step4887 p h) (sat_cons (step2841 p h) (sat_nil p)))
def c5315 : List Lit := [(1136, false), (1074, false)]
theorem step5315 (p : Nat → Bool) (h : Constraints p) : clause p c5315 = true :=
  Snake9.LocalRup.prove_clause [c4887, c1805] c5315 (by decide) p (sat_cons (step4887 p h) (sat_cons (step1805 p h) (sat_nil p)))
def c5316 : List Lit := [(1076, false), (1134, false)]
theorem step5316 (p : Nat → Bool) (h : Constraints p) : clause p c5316 = true :=
  Snake9.LocalRup.prove_clause [c4887, c1816] c5316 (by decide) p (sat_cons (step4887 p h) (sat_cons (step1816 p h) (sat_nil p)))
def c5317 : List Lit := [(1077, false), (1133, false)]
theorem step5317 (p : Nat → Bool) (h : Constraints p) : clause p c5317 = true :=
  Snake9.LocalRup.prove_clause [c4887, c1820] c5317 (by decide) p (sat_cons (step4887 p h) (sat_cons (step1820 p h) (sat_nil p)))
def c5318 : List Lit := [(1066, false), (1039, false)]
theorem step5318 (p : Nat → Bool) (h : Constraints p) : clause p c5318 = true :=
  Snake9.LocalRup.prove_clause [c4888, c1656] c5318 (by decide) p (sat_cons (step4888 p h) (sat_cons (step1656 p h) (sat_nil p)))
def c5319 : List Lit := [(985, false), (1005, true)]
theorem step5319 (p : Nat → Bool) (h : Constraints p) : clause p c5319 = true :=
  Snake9.LocalRup.prove_clause [c4885, c1518] c5319 (by decide) p (sat_cons (step4885 p h) (sat_cons (step1518 p h) (sat_nil p)))
def c5320 : List Lit := [(90, false), (88, true), (1045, false), (1124, false), (1096, true), (1087, false), (1055, false), (69, true), (1032, false)]
theorem step5320 (p : Nat → Bool) (h : Constraints p) : clause p c5320 = true :=
  Snake9.LocalRup.prove_clause [c4887, c2838] c5320 (by decide) p (sat_cons (step4887 p h) (sat_cons (step2838 p h) (sat_nil p)))
def c5321 : List Lit := [(88, true), (1051, true), (1124, false), (1040, false), (1075, false), (1134, false), (1055, false), (1087, false)]
theorem step5321 (p : Nat → Bool) (h : Constraints p) : clause p c5321 = true :=
  Snake9.LocalRup.prove_clause [c4887, c2818] c5321 (by decide) p (sat_cons (step4887 p h) (sat_cons (step2818 p h) (sat_nil p)))
def c5322 : List Lit := [(1065, false), (1040, false)]
theorem step5322 (p : Nat → Bool) (h : Constraints p) : clause p c5322 = true :=
  Snake9.LocalRup.prove_clause [c4888, c1663] c5322 (by decide) p (sat_cons (step4888 p h) (sat_cons (step1663 p h) (sat_nil p)))
def c5323 : List Lit := [(986, false), (1006, true)]
theorem step5323 (p : Nat → Bool) (h : Constraints p) : clause p c5323 = true :=
  Snake9.LocalRup.prove_clause [c4885, c1519] c5323 (by decide) p (sat_cons (step4885 p h) (sat_cons (step1519 p h) (sat_nil p)))
def c5324 : List Lit := [(1041, false), (1064, false)]
theorem step5324 (p : Nat → Bool) (h : Constraints p) : clause p c5324 = true :=
  Snake9.LocalRup.prove_clause [c4888, c1669] c5324 (by decide) p (sat_cons (step4888 p h) (sat_cons (step1669 p h) (sat_nil p)))
def c5325 : List Lit := [(987, false), (1007, true)]
theorem step5325 (p : Nat → Bool) (h : Constraints p) : clause p c5325 = true :=
  Snake9.LocalRup.prove_clause [c4885, c1520] c5325 (by decide) p (sat_cons (step4885 p h) (sat_cons (step1520 p h) (sat_nil p)))
def c5326 : List Lit := [(86, true), (79, false), (70, true), (1031, false), (76, true), (13, true), (95, true), (88, true), (89, true), (1124, false)]
theorem step5326 (p : Nat → Bool) (h : Constraints p) : clause p c5326 = true :=
  Snake9.LocalRup.prove_clause [c4887, c3603] c5326 (by decide) p (sat_cons (step4887 p h) (sat_cons (step3603 p h) (sat_nil p)))
def c5327 : List Lit := [(69, true), (1087, false), (1124, false), (89, true), (1045, false), (1043, false), (1076, true), (73, true), (1053, false), (1029, false)]
theorem step5327 (p : Nat → Bool) (h : Constraints p) : clause p c5327 = true :=
  Snake9.LocalRup.prove_clause [c4887, c3089] c5327 (by decide) p (sat_cons (step4887 p h) (sat_cons (step3089 p h) (sat_nil p)))
def c5328 : List Lit := [(1040, false), (89, true), (1053, false), (1124, false), (1087, false), (88, true), (1043, false)]
theorem step5328 (p : Nat → Bool) (h : Constraints p) : clause p c5328 = true :=
  Snake9.LocalRup.prove_clause [c4887, c3114] c5328 (by decide) p (sat_cons (step4887 p h) (sat_cons (step3114 p h) (sat_nil p)))
def c5329 : List Lit := [(69, true), (1051, false), (88, true), (70, true), (79, true), (1043, false), (1159, true), (1124, false), (1027, false), (1045, false)]
theorem step5329 (p : Nat → Bool) (h : Constraints p) : clause p c5329 = true :=
  Snake9.LocalRup.prove_clause [c4887, c3573] c5329 (by decide) p (sat_cons (step4887 p h) (sat_cons (step3573 p h) (sat_nil p)))
def c5330 : List Lit := [(1050, false), (1051, false), (1038, false), (23, true), (1124, false), (1095, false), (1064, false), (70, true)]
theorem step5330 (p : Nat → Bool) (h : Constraints p) : clause p c5330 = true :=
  Snake9.LocalRup.prove_clause [c4887, c3403] c5330 (by decide) p (sat_cons (step4887 p h) (sat_cons (step3403 p h) (sat_nil p)))
def c5331 : List Lit := [(1049, false), (1051, false), (1095, false), (70, true), (23, true), (1124, false), (1076, true), (1039, false)]
theorem step5331 (p : Nat → Bool) (h : Constraints p) : clause p c5331 = true :=
  Snake9.LocalRup.prove_clause [c4887, c3390] c5331 (by decide) p (sat_cons (step4887 p h) (sat_cons (step3390 p h) (sat_nil p)))
def c5332 : List Lit := [(88, true), (1088, false), (90, false), (1087, false), (1124, false), (1045, false), (69, true), (1043, false), (1055, false), (1032, false)]
theorem step5332 (p : Nat → Bool) (h : Constraints p) : clause p c5332 = true :=
  Snake9.LocalRup.prove_clause [c4887, c3095] c5332 (by decide) p (sat_cons (step4887 p h) (sat_cons (step3095 p h) (sat_nil p)))
def c5333 : List Lit := [(97, true), (88, true), (1032, false), (1124, false), (86, false), (1062, false), (69, true), (83, false), (1087, false)]
theorem step5333 (p : Nat → Bool) (h : Constraints p) : clause p c5333 = true :=
  Snake9.LocalRup.prove_clause [c4887, c3103] c5333 (by decide) p (sat_cons (step4887 p h) (sat_cons (step3103 p h) (sat_nil p)))
def c5334 : List Lit := [(1052, false), (1049, false), (1124, false), (1039, false), (1095, false)]
theorem step5334 (p : Nat → Bool) (h : Constraints p) : clause p c5334 = true :=
  Snake9.LocalRup.prove_clause [c4887, c3537] c5334 (by decide) p (sat_cons (step4887 p h) (sat_cons (step3537 p h) (sat_nil p)))
def c5335 : List Lit := [(1052, false), (1048, false), (95, true), (1095, false), (1124, false), (1039, false)]
theorem step5335 (p : Nat → Bool) (h : Constraints p) : clause p c5335 = true :=
  Snake9.LocalRup.prove_clause [c4887, c3542] c5335 (by decide) p (sat_cons (step4887 p h) (sat_cons (step3542 p h) (sat_nil p)))
def c5336 : List Lit := [(81, false), (69, false), (83, true), (95, true), (1031, false), (73, false), (79, false), (85, false), (89, true), (1095, false), (1124, false)]
theorem step5336 (p : Nat → Bool) (h : Constraints p) : clause p c5336 = true :=
  Snake9.LocalRup.prove_clause [c4887, c3549] c5336 (by decide) p (sat_cons (step4887 p h) (sat_cons (step3549 p h) (sat_nil p)))
def c5337 : List Lit := [(1052, false), (1049, false), (1038, false), (1095, false), (95, true), (1124, false)]
theorem step5337 (p : Nat → Bool) (h : Constraints p) : clause p c5337 = true :=
  Snake9.LocalRup.prove_clause [c4887, c3605] c5337 (by decide) p (sat_cons (step4887 p h) (sat_cons (step3605 p h) (sat_nil p)))
def c5338 : List Lit := [(97, true), (1084, false), (77, true), (1095, false), (1053, true), (1027, false), (1025, false), (1124, false), (1060, false)]
theorem step5338 (p : Nat → Bool) (h : Constraints p) : clause p c5338 = true :=
  Snake9.LocalRup.prove_clause [c4887, c3105] c5338 (by decide) p (sat_cons (step4887 p h) (sat_cons (step3105 p h) (sat_nil p)))
def c5339 : List Lit := [(69, true), (89, false), (1033, false), (86, false), (88, true), (1124, false), (1096, true), (1051, false), (73, true), (79, true)]
theorem step5339 (p : Nat → Bool) (h : Constraints p) : clause p c5339 = true :=
  Snake9.LocalRup.prove_clause [c4887, c4572] c5339 (by decide) p (sat_cons (step4887 p h) (sat_cons (step4572 p h) (sat_nil p)))
def c5340 : List Lit := [(1040, false), (1088, false), (1045, false), (1124, false), (1043, false), (1061, true), (88, true)]
theorem step5340 (p : Nat → Bool) (h : Constraints p) : clause p c5340 = true :=
  Snake9.LocalRup.prove_clause [c4887, c4163] c5340 (by decide) p (sat_cons (step4887 p h) (sat_cons (step4163 p h) (sat_nil p)))
def c5341 : List Lit := [(1051, false), (1056, true), (1040, false), (1124, false), (1048, false), (79, false), (1095, false)]
theorem step5341 (p : Nat → Bool) (h : Constraints p) : clause p c5341 = true :=
  Snake9.LocalRup.prove_clause [c4887, c3846] c5341 (by decide) p (sat_cons (step4887 p h) (sat_cons (step3846 p h) (sat_nil p)))
def c5342 : List Lit := [(89, true), (79, true), (13, true), (1124, false), (7, false), (1045, false), (1087, false), (73, true), (70, true), (1053, false), (88, true)]
theorem step5342 (p : Nat → Bool) (h : Constraints p) : clause p c5342 = true :=
  Snake9.LocalRup.prove_clause [c4887, c4034] c5342 (by decide) p (sat_cons (step4887 p h) (sat_cons (step4034 p h) (sat_nil p)))
def c5343 : List Lit := [(1041, false), (1045, false), (1053, false), (1124, false), (88, true), (1043, false)]
theorem step5343 (p : Nat → Bool) (h : Constraints p) : clause p c5343 = true :=
  Snake9.LocalRup.prove_clause [c4887, c4176] c5343 (by decide) p (sat_cons (step4887 p h) (sat_cons (step4176 p h) (sat_nil p)))
def c5344 : List Lit := [(1040, false), (1056, true), (1124, false), (1087, false), (1134, false), (1043, false), (88, true), (1053, false)]
theorem step5344 (p : Nat → Bool) (h : Constraints p) : clause p c5344 = true :=
  Snake9.LocalRup.prove_clause [c4887, c4180] c5344 (by decide) p (sat_cons (step4887 p h) (sat_cons (step4180 p h) (sat_nil p)))
def c5345 : List Lit := [(1040, false), (88, true), (1048, false), (1045, false), (89, true), (1053, false), (1124, false)]
theorem step5345 (p : Nat → Bool) (h : Constraints p) : clause p c5345 = true :=
  Snake9.LocalRup.prove_clause [c4887, c3857] c5345 (by decide) p (sat_cons (step4887 p h) (sat_cons (step3857 p h) (sat_nil p)))
def c5346 : List Lit := [(1048, false), (89, true), (1039, false), (1053, false), (1087, false), (88, true), (1045, false), (1124, false)]
theorem step5346 (p : Nat → Bool) (h : Constraints p) : clause p c5346 = true :=
  Snake9.LocalRup.prove_clause [c4887, c4021] c5346 (by decide) p (sat_cons (step4887 p h) (sat_cons (step4021 p h) (sat_nil p)))
def c5347 : List Lit := [(1040, false), (88, true), (1124, false), (1045, false), (95, true), (1043, false)]
theorem step5347 (p : Nat → Bool) (h : Constraints p) : clause p c5347 = true :=
  Snake9.LocalRup.prove_clause [c4887, c4181] c5347 (by decide) p (sat_cons (step4887 p h) (sat_cons (step4181 p h) (sat_nil p)))
def c5348 : List Lit := [(1040, false), (89, true), (1087, false), (1053, false), (1045, false), (1048, false), (88, true), (1063, true)]
theorem step5348 (p : Nat → Bool) (h : Constraints p) : clause p c5348 = true :=
  Snake9.LocalRup.prove_clause [c4887, c4552] c5348 (by decide) p (sat_cons (step4887 p h) (sat_cons (step4552 p h) (sat_nil p)))
def c5349 : List Lit := [(88, true), (1088, false), (89, true), (1048, false), (82, true), (1045, false), (1039, false), (1124, false)]
theorem step5349 (p : Nat → Bool) (h : Constraints p) : clause p c5349 = true :=
  Snake9.LocalRup.prove_clause [c4887, c4063] c5349 (by decide) p (sat_cons (step4887 p h) (sat_cons (step4063 p h) (sat_nil p)))
def c5350 : List Lit := [(1040, false), (1047, false), (79, false), (1096, false), (1075, true), (1051, false), (1124, false)]
theorem step5350 (p : Nat → Bool) (h : Constraints p) : clause p c5350 = true :=
  Snake9.LocalRup.prove_clause [c4887, c4564] c5350 (by decide) p (sat_cons (step4887 p h) (sat_cons (step4564 p h) (sat_nil p)))
def c5351 : List Lit := [(1040, false), (79, false), (1075, true), (1043, false), (88, true), (1124, false)]
theorem step5351 (p : Nat → Bool) (h : Constraints p) : clause p c5351 = true :=
  Snake9.LocalRup.prove_clause [c4887, c4589] c5351 (by decide) p (sat_cons (step4887 p h) (sat_cons (step4589 p h) (sat_nil p)))
def c5352 : List Lit := [(1040, false), (1052, false), (1124, false), (95, true), (1047, false), (1095, false)]
theorem step5352 (p : Nat → Bool) (h : Constraints p) : clause p c5352 = true :=
  Snake9.LocalRup.prove_clause [c4887, c3863] c5352 (by decide) p (sat_cons (step4887 p h) (sat_cons (step3863 p h) (sat_nil p)))
end B112E057
