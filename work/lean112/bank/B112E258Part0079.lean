import B112E258Part0078
namespace B112E258
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c6554 : List Lit := [(1647, true), (1528, true)]
theorem step6554 (p : Nat → Bool) (h : Constraints p) : clause p c6554 = true :=
  Snake9.LocalRup.prove_clause [c6522, c6274, c6381, c6543, c6271, c6288, c1992, c1146, c6229, c6535, c933, c1140, c947, c1011, c6553, c5274, c4917, c4999, c4393] c6554 (by decide) p (sat_cons (step6522 p h) (sat_cons (step6274 p h) (sat_cons (step6381 p h) (sat_cons (step6543 p h) (sat_cons (step6271 p h) (sat_cons (step6288 p h) (sat_cons (step1992 p h) (sat_cons (step1146 p h) (sat_cons (step6229 p h) (sat_cons (step6535 p h) (sat_cons (step933 p h) (sat_cons (step1140 p h) (sat_cons (step947 p h) (sat_cons (step1011 p h) (sat_cons (step6553 p h) (sat_cons (step5274 p h) (sat_cons (step4917 p h) (sat_cons (step4999 p h) (sat_cons (step4393 p h) (sat_nil p))))))))))))))))))))
def c6555 : List Lit := [(79, false), (1528, true)]
theorem step6555 (p : Nat → Bool) (h : Constraints p) : clause p c6555 = true :=
  Snake9.LocalRup.prove_clause [c5833, c6522, c6276, c6274, c6271, c6381, c6543, c6288, c1992, c1146, c1005, c2372, c1236, c967, c5274, c113, c5691, c4999, c927, c1140, c986, c988, c4917, c1017, c974, c4507, c6389] c6555 (by decide) p (sat_cons (step5833 p h) (sat_cons (step6522 p h) (sat_cons (step6276 p h) (sat_cons (step6274 p h) (sat_cons (step6271 p h) (sat_cons (step6381 p h) (sat_cons (step6543 p h) (sat_cons (step6288 p h) (sat_cons (step1992 p h) (sat_cons (step1146 p h) (sat_cons (step1005 p h) (sat_cons (step2372 p h) (sat_cons (step1236 p h) (sat_cons (step967 p h) (sat_cons (step5274 p h) (sat_cons (step113 p h) (sat_cons (step5691 p h) (sat_cons (step4999 p h) (sat_cons (step927 p h) (sat_cons (step1140 p h) (sat_cons (step986 p h) (sat_cons (step988 p h) (sat_cons (step4917 p h) (sat_cons (step1017 p h) (sat_cons (step974 p h) (sat_cons (step4507 p h) (sat_cons (step6389 p h) (sat_nil p))))))))))))))))))))))))))))
def c6556 : List Lit := [(23, false), (1622, true)]
theorem step6556 (p : Nat → Bool) (h : Constraints p) : clause p c6556 = true :=
  Snake9.LocalRup.prove_clause [c6274, c6543, c6381, c6550, c6271, c113, c5691, c135, c134, c1140, c1684, c1040, c1104, c1048, c1056, c4530, c6340] c6556 (by decide) p (sat_cons (step6274 p h) (sat_cons (step6543 p h) (sat_cons (step6381 p h) (sat_cons (step6550 p h) (sat_cons (step6271 p h) (sat_cons (step113 p h) (sat_cons (step5691 p h) (sat_cons (step135 p h) (sat_cons (step134 p h) (sat_cons (step1140 p h) (sat_cons (step1684 p h) (sat_cons (step1040 p h) (sat_cons (step1104 p h) (sat_cons (step1048 p h) (sat_cons (step1056 p h) (sat_cons (step4530 p h) (sat_cons (step6340 p h) (sat_nil p))))))))))))))))))
def c6557 : List Lit := [(1545, false), (1528, true)]
theorem step6557 (p : Nat → Bool) (h : Constraints p) : clause p c6557 = true :=
  Snake9.LocalRup.prove_clause [c6497, c6543, c5833, c6522, c5888, c6496, c2372, c1236, c6554, c1265, c967, c6288, c1992, c6556, c6083, c1048, c6555, c1139, c1140, c1991, c1954, c1423, c1417, c1060, c1266, c5988, c1036, c1291, c6449] c6557 (by decide) p (sat_cons (step6497 p h) (sat_cons (step6543 p h) (sat_cons (step5833 p h) (sat_cons (step6522 p h) (sat_cons (step5888 p h) (sat_cons (step6496 p h) (sat_cons (step2372 p h) (sat_cons (step1236 p h) (sat_cons (step6554 p h) (sat_cons (step1265 p h) (sat_cons (step967 p h) (sat_cons (step6288 p h) (sat_cons (step1992 p h) (sat_cons (step6556 p h) (sat_cons (step6083 p h) (sat_cons (step1048 p h) (sat_cons (step6555 p h) (sat_cons (step1139 p h) (sat_cons (step1140 p h) (sat_cons (step1991 p h) (sat_cons (step1954 p h) (sat_cons (step1423 p h) (sat_cons (step1417 p h) (sat_cons (step1060 p h) (sat_cons (step1266 p h) (sat_cons (step5988 p h) (sat_cons (step1036 p h) (sat_cons (step1291 p h) (sat_cons (step6449 p h) (sat_nil p))))))))))))))))))))))))))))))
def c6558 : List Lit := [(1602, true), (1528, true)]
theorem step6558 (p : Nat → Bool) (h : Constraints p) : clause p c6558 = true :=
  Snake9.LocalRup.prove_clause [c6277, c5833, c6549, c6271, c6381, c6543, c6275, c6497, c6288, c1992, c6556, c3290, c6557, c4943, c931, c2376, c1182, c2372, c1236, c6554, c1265, c967, c6083, c1048, c6340, c1056, c930, c1803, c408, c1553, c1180, c1418, c6091, c1278, c1954, c1104, c1057, c1684, c1050, c1838, c429, c1828, c6417, c1042, c1424, c2060, c6063, c1294, c1209, c6433] c6558 (by decide) p (sat_cons (step6277 p h) (sat_cons (step5833 p h) (sat_cons (step6549 p h) (sat_cons (step6271 p h) (sat_cons (step6381 p h) (sat_cons (step6543 p h) (sat_cons (step6275 p h) (sat_cons (step6497 p h) (sat_cons (step6288 p h) (sat_cons (step1992 p h) (sat_cons (step6556 p h) (sat_cons (step3290 p h) (sat_cons (step6557 p h) (sat_cons (step4943 p h) (sat_cons (step931 p h) (sat_cons (step2376 p h) (sat_cons (step1182 p h) (sat_cons (step2372 p h) (sat_cons (step1236 p h) (sat_cons (step6554 p h) (sat_cons (step1265 p h) (sat_cons (step967 p h) (sat_cons (step6083 p h) (sat_cons (step1048 p h) (sat_cons (step6340 p h) (sat_cons (step1056 p h) (sat_cons (step930 p h) (sat_cons (step1803 p h) (sat_cons (step408 p h) (sat_cons (step1553 p h) (sat_cons (step1180 p h) (sat_cons (step1418 p h) (sat_cons (step6091 p h) (sat_cons (step1278 p h) (sat_cons (step1954 p h) (sat_cons (step1104 p h) (sat_cons (step1057 p h) (sat_cons (step1684 p h) (sat_cons (step1050 p h) (sat_cons (step1838 p h) (sat_cons (step429 p h) (sat_cons (step1828 p h) (sat_cons (step6417 p h) (sat_cons (step1042 p h) (sat_cons (step1424 p h) (sat_cons (step2060 p h) (sat_cons (step6063 p h) (sat_cons (step1294 p h) (sat_cons (step1209 p h) (sat_cons (step6433 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))
def c6559 : List Lit := [(1677, true), (1528, true)]
theorem step6559 (p : Nat → Bool) (h : Constraints p) : clause p c6559 = true :=
  Snake9.LocalRup.prove_clause [c6277, c6275, c6543, c6549, c6271, c6381, c5833, c6497, c6288, c1992, c6556, c3290, c6557, c4943, c931, c2376, c1182, c930, c1803, c408, c1553, c1180, c2372, c1236, c6554, c1265, c1418, c1278, c1266, c6063, c1237, c1209, c6203, c6433, c1293] c6559 (by decide) p (sat_cons (step6277 p h) (sat_cons (step6275 p h) (sat_cons (step6543 p h) (sat_cons (step6549 p h) (sat_cons (step6271 p h) (sat_cons (step6381 p h) (sat_cons (step5833 p h) (sat_cons (step6497 p h) (sat_cons (step6288 p h) (sat_cons (step1992 p h) (sat_cons (step6556 p h) (sat_cons (step3290 p h) (sat_cons (step6557 p h) (sat_cons (step4943 p h) (sat_cons (step931 p h) (sat_cons (step2376 p h) (sat_cons (step1182 p h) (sat_cons (step930 p h) (sat_cons (step1803 p h) (sat_cons (step408 p h) (sat_cons (step1553 p h) (sat_cons (step1180 p h) (sat_cons (step2372 p h) (sat_cons (step1236 p h) (sat_cons (step6554 p h) (sat_cons (step1265 p h) (sat_cons (step1418 p h) (sat_cons (step1278 p h) (sat_cons (step1266 p h) (sat_cons (step6063 p h) (sat_cons (step1237 p h) (sat_cons (step1209 p h) (sat_cons (step6203 p h) (sat_cons (step6433 p h) (sat_cons (step1293 p h) (sat_nil p))))))))))))))))))))))))))))))))))))
def c6560 : List Lit := [(1528, true)]
theorem step6560 (p : Nat → Bool) (h : Constraints p) : clause p c6560 = true :=
  Snake9.LocalRup.prove_clause [c5888, c6275, c6497, c6551, c6276, c6549, c6543, c967, c6557, c1004, c990, c6558, c6559, c1423, c1424, c1991, c6088, c1128, c1134, c1293, c1294, c1955, c4679, c2443, c2060, c1061, c1042, c1050] c6560 (by decide) p (sat_cons (step5888 p h) (sat_cons (step6275 p h) (sat_cons (step6497 p h) (sat_cons (step6551 p h) (sat_cons (step6276 p h) (sat_cons (step6549 p h) (sat_cons (step6543 p h) (sat_cons (step967 p h) (sat_cons (step6557 p h) (sat_cons (step1004 p h) (sat_cons (step990 p h) (sat_cons (step6558 p h) (sat_cons (step6559 p h) (sat_cons (step1423 p h) (sat_cons (step1424 p h) (sat_cons (step1991 p h) (sat_cons (step6088 p h) (sat_cons (step1128 p h) (sat_cons (step1134 p h) (sat_cons (step1293 p h) (sat_cons (step1294 p h) (sat_cons (step1955 p h) (sat_cons (step4679 p h) (sat_cons (step2443 p h) (sat_cons (step2060 p h) (sat_cons (step1061 p h) (sat_cons (step1042 p h) (sat_cons (step1050 p h) (sat_nil p)))))))))))))))))))))))))))))
def c6561 : List Lit := [(1530, true)]
theorem step6561 (p : Nat → Bool) (h : Constraints p) : clause p c6561 = true :=
  Snake9.LocalRup.prove_clause [c6560, c969] c6561 (by decide) p (sat_cons (step6560 p h) (sat_cons (step969 p h) (sat_nil p)))
def c6562 : List Lit := [(1621, true)]
theorem step6562 (p : Nat → Bool) (h : Constraints p) : clause p c6562 = true :=
  Snake9.LocalRup.prove_clause [c6560, c6537] c6562 (by decide) p (sat_cons (step6560 p h) (sat_cons (step6537 p h) (sat_nil p)))
def c6563 : List Lit := [(1754, false)]
theorem step6563 (p : Nat → Bool) (h : Constraints p) : clause p c6563 = true :=
  Snake9.LocalRup.prove_clause [c6562, c1991] c6563 (by decide) p (sat_cons (step6562 p h) (sat_cons (step1991 p h) (sat_nil p)))
def c6564 : List Lit := [(1736, false)]
theorem step6564 (p : Nat → Bool) (h : Constraints p) : clause p c6564 = true :=
  Snake9.LocalRup.prove_clause [c6563, c5835, c1405] c6564 (by decide) p (sat_cons (step6563 p h) (sat_cons (step5835 p h) (sat_cons (step1405 p h) (sat_nil p))))
def c6565 : List Lit := [(1677, false)]
theorem step6565 (p : Nat → Bool) (h : Constraints p) : clause p c6565 = true :=
  Snake9.LocalRup.prove_clause [c6563, c5888, c1423] c6565 (by decide) p (sat_cons (step6563 p h) (sat_cons (step5888 p h) (sat_cons (step1423 p h) (sat_nil p))))
def c6566 : List Lit := [(1668, false)]
theorem step6566 (p : Nat → Bool) (h : Constraints p) : clause p c6566 = true :=
  Snake9.LocalRup.prove_clause [c6565, c5427] c6566 (by decide) p (sat_cons (step6565 p h) (sat_cons (step5427 p h) (sat_nil p)))
def c6567 : List Lit := [(1649, false)]
theorem step6567 (p : Nat → Bool) (h : Constraints p) : clause p c6567 = true :=
  Snake9.LocalRup.prove_clause [c6565, c5834, c1277] c6567 (by decide) p (sat_cons (step6565 p h) (sat_cons (step5834 p h) (sat_cons (step1277 p h) (sat_nil p))))
def c6568 : List Lit := [(99, false), (1686, true)]
theorem step6568 (p : Nat → Bool) (h : Constraints p) : clause p c6568 = true :=
  Snake9.LocalRup.prove_clause [c6543, c6274, c6560, c5613, c6522, c5888, c6565, c6566, c5833, c2527, c1237, c1242, c5428, c1266, c1416, c6229, c3049, c1992, c1209, c1146, c1215, c4912] c6568 (by decide) p (sat_cons (step6543 p h) (sat_cons (step6274 p h) (sat_cons (step6560 p h) (sat_cons (step5613 p h) (sat_cons (step6522 p h) (sat_cons (step5888 p h) (sat_cons (step6565 p h) (sat_cons (step6566 p h) (sat_cons (step5833 p h) (sat_cons (step2527 p h) (sat_cons (step1237 p h) (sat_cons (step1242 p h) (sat_cons (step5428 p h) (sat_cons (step1266 p h) (sat_cons (step1416 p h) (sat_cons (step6229 p h) (sat_cons (step3049 p h) (sat_cons (step1992 p h) (sat_cons (step1209 p h) (sat_cons (step1146 p h) (sat_cons (step1215 p h) (sat_cons (step4912 p h) (sat_nil p)))))))))))))))))))))))
def c6569 : List Lit := [(1734, true)]
theorem step6569 (p : Nat → Bool) (h : Constraints p) : clause p c6569 = true :=
  Snake9.LocalRup.prove_clause [c6497, c6496, c5988, c6088, c1291, c1293, c6568] c6569 (by decide) p (sat_cons (step6497 p h) (sat_cons (step6496 p h) (sat_cons (step5988 p h) (sat_cons (step6088 p h) (sat_cons (step1291 p h) (sat_cons (step1293 p h) (sat_cons (step6568 p h) (sat_nil p))))))))
def c6570 : List Lit := [(1676, false)]
theorem step6570 (p : Nat → Bool) (h : Constraints p) : clause p c6570 = true :=
  Snake9.LocalRup.prove_clause [c6569, c6563, c1417] c6570 (by decide) p (sat_cons (step6569 p h) (sat_cons (step6563 p h) (sat_cons (step1417 p h) (sat_nil p))))
def c6571 : List Lit := [(1667, false)]
theorem step6571 (p : Nat → Bool) (h : Constraints p) : clause p c6571 = true :=
  Snake9.LocalRup.prove_clause [c6570, c5428] c6571 (by decide) p (sat_cons (step6570 p h) (sat_cons (step5428 p h) (sat_nil p)))
def c6572 : List Lit := [(1662, false)]
theorem step6572 (p : Nat → Bool) (h : Constraints p) : clause p c6572 = true :=
  Snake9.LocalRup.prove_clause [c6571, c5833, c1237] c6572 (by decide) p (sat_cons (step6571 p h) (sat_cons (step5833 p h) (sat_cons (step1237 p h) (sat_nil p))))
def c6573 : List Lit := [(1661, false), (1508, false), (1652, false)]
theorem step6573 (p : Nat → Bool) (h : Constraints p) : clause p c6573 = true :=
  Snake9.LocalRup.prove_clause [c5833, c6571, c6569, c5613, c6560, c6274, c6543, c6522, c1236, c1241, c5421, c1215, c1410, c4912, c1992, c1146] c6573 (by decide) p (sat_cons (step5833 p h) (sat_cons (step6571 p h) (sat_cons (step6569 p h) (sat_cons (step5613 p h) (sat_cons (step6560 p h) (sat_cons (step6274 p h) (sat_cons (step6543 p h) (sat_cons (step6522 p h) (sat_cons (step1236 p h) (sat_cons (step1241 p h) (sat_cons (step5421 p h) (sat_cons (step1215 p h) (sat_cons (step1410 p h) (sat_cons (step4912 p h) (sat_cons (step1992 p h) (sat_cons (step1146 p h) (sat_nil p)))))))))))))))))
def c6574 : List Lit := [(1508, false), (1652, false)]
theorem step6574 (p : Nat → Bool) (h : Constraints p) : clause p c6574 = true :=
  Snake9.LocalRup.prove_clause [c6543, c6274, c6560, c5613, c6522, c6563, c5835, c6496, c5578, c6573, c2489, c4897, c1291, c1293, c6341, c1404, c1411, c1992, c5421, c1146, c1240, c4912, c1215] c6574 (by decide) p (sat_cons (step6543 p h) (sat_cons (step6274 p h) (sat_cons (step6560 p h) (sat_cons (step5613 p h) (sat_cons (step6522 p h) (sat_cons (step6563 p h) (sat_cons (step5835 p h) (sat_cons (step6496 p h) (sat_cons (step5578 p h) (sat_cons (step6573 p h) (sat_cons (step2489 p h) (sat_cons (step4897 p h) (sat_cons (step1291 p h) (sat_cons (step1293 p h) (sat_cons (step6341 p h) (sat_cons (step1404 p h) (sat_cons (step1411 p h) (sat_cons (step1992 p h) (sat_cons (step5421 p h) (sat_cons (step1146 p h) (sat_cons (step1240 p h) (sat_cons (step4912 p h) (sat_cons (step1215 p h) (sat_nil p))))))))))))))))))))))))
def c6575 : List Lit := [(1652, false)]
theorem step6575 (p : Nat → Bool) (h : Constraints p) : clause p c6575 = true :=
  Snake9.LocalRup.prove_clause [c5834, c6570, c6569, c6381, c6543, c6574, c6229, c1264, c1265, c1410, c1240, c1992, c1215, c6556, c5274] c6575 (by decide) p (sat_cons (step5834 p h) (sat_cons (step6570 p h) (sat_cons (step6569 p h) (sat_cons (step6381 p h) (sat_cons (step6543 p h) (sat_cons (step6574 p h) (sat_cons (step6229 p h) (sat_cons (step1264 p h) (sat_cons (step1265 p h) (sat_cons (step1410 p h) (sat_cons (step1240 p h) (sat_cons (step1992 p h) (sat_cons (step1215 p h) (sat_cons (step6556 p h) (sat_cons (step5274 p h) (sat_nil p))))))))))))))))
def c6576 : List Lit := [(82, true)]
theorem step6576 (p : Nat → Bool) (h : Constraints p) : clause p c6576 = true :=
  Snake9.LocalRup.prove_clause [c6575, c1209] c6576 (by decide) p (sat_cons (step6575 p h) (sat_cons (step1209 p h) (sat_nil p)))
def c6577 : List Lit := [(23, true), (1691, false)]
theorem step6577 (p : Nat → Bool) (h : Constraints p) : clause p c6577 = true :=
  Snake9.LocalRup.prove_clause [c6381, c6543, c6576, c6497, c6567, c5834, c6563, c6496, c5833, c3290, c1803, c1180, c408, c1553, c1603, c6433, c4567, c1411, c1291, c5421, c2489, c1236] c6577 (by decide) p (sat_cons (step6381 p h) (sat_cons (step6543 p h) (sat_cons (step6576 p h) (sat_cons (step6497 p h) (sat_cons (step6567 p h) (sat_cons (step5834 p h) (sat_cons (step6563 p h) (sat_cons (step6496 p h) (sat_cons (step5833 p h) (sat_cons (step3290 p h) (sat_cons (step1803 p h) (sat_cons (step1180 p h) (sat_cons (step408 p h) (sat_cons (step1553 p h) (sat_cons (step1603 p h) (sat_cons (step6433 p h) (sat_cons (step4567 p h) (sat_cons (step1411 p h) (sat_cons (step1291 p h) (sat_cons (step5421 p h) (sat_cons (step2489 p h) (sat_cons (step1236 p h) (sat_nil p)))))))))))))))))))))))
def c6578 : List Lit := [(1691, false)]
theorem step6578 (p : Nat → Bool) (h : Constraints p) : clause p c6578 = true :=
  Snake9.LocalRup.prove_clause [c6381, c6543, c6561, c6523, c6570, c5833, c6274, c6577, c113, c4999, c6556, c927, c987, c1992, c1018, c5268, c948, c6229, c936] c6578 (by decide) p (sat_cons (step6381 p h) (sat_cons (step6543 p h) (sat_cons (step6561 p h) (sat_cons (step6523 p h) (sat_cons (step6570 p h) (sat_cons (step5833 p h) (sat_cons (step6274 p h) (sat_cons (step6577 p h) (sat_cons (step113 p h) (sat_cons (step4999 p h) (sat_cons (step6556 p h) (sat_cons (step927 p h) (sat_cons (step987 p h) (sat_cons (step1992 p h) (sat_cons (step1018 p h) (sat_cons (step5268 p h) (sat_cons (step948 p h) (sat_cons (step6229 p h) (sat_cons (step936 p h) (sat_nil p))))))))))))))))))))
def c6579 : List Lit := [(99, true)]
theorem step6579 (p : Nat → Bool) (h : Constraints p) : clause p c6579 = true :=
  Snake9.LocalRup.prove_clause [c6578, c1293] c6579 (by decide) p (sat_cons (step6578 p h) (sat_cons (step1293 p h) (sat_nil p)))
def c6580 : List Lit := [(98, true)]
theorem step6580 (p : Nat → Bool) (h : Constraints p) : clause p c6580 = true :=
  Snake9.LocalRup.prove_clause [c6578, c1294] c6580 (by decide) p (sat_cons (step6578 p h) (sat_cons (step1294 p h) (sat_nil p)))
def c6581 : List Lit := [(1661, true)]
theorem step6581 (p : Nat → Bool) (h : Constraints p) : clause p c6581 = true :=
  Snake9.LocalRup.prove_clause [c6579, c5578, c4897] c6581 (by decide) p (sat_cons (step6579 p h) (sat_cons (step5578 p h) (sat_cons (step4897 p h) (sat_nil p))))
def c6582 : List Lit := [(1686, true)]
theorem step6582 (p : Nat → Bool) (h : Constraints p) : clause p c6582 = true :=
  Snake9.LocalRup.prove_clause [c6579, c6568] c6582 (by decide) p (sat_cons (step6579 p h) (sat_cons (step6568 p h) (sat_nil p)))
def c6583 : List Lit := [(86, true)]
theorem step6583 (p : Nat → Bool) (h : Constraints p) : clause p c6583 = true :=
  Snake9.LocalRup.prove_clause [c6579, c6572, c6361] c6583 (by decide) p (sat_cons (step6579 p h) (sat_cons (step6572 p h) (sat_cons (step6361 p h) (sat_nil p))))
def c6584 : List Lit := [(88, true)]
theorem step6584 (p : Nat → Bool) (h : Constraints p) : clause p c6584 = true :=
  Snake9.LocalRup.prove_clause [c6579, c6576, c6572, c5618] c6584 (by decide) p (sat_cons (step6579 p h) (sat_cons (step6576 p h) (sat_cons (step6572 p h) (sat_cons (step5618 p h) (sat_nil p)))))
def c6585 : List Lit := [(87, false)]
theorem step6585 (p : Nat → Bool) (h : Constraints p) : clause p c6585 = true :=
  Snake9.LocalRup.prove_clause [c6580, c6576, c6584, c483] c6585 (by decide) p (sat_cons (step6580 p h) (sat_cons (step6576 p h) (sat_cons (step6584 p h) (sat_cons (step483 p h) (sat_nil p)))))
def c6586 : List Lit := [(1666, true)]
theorem step6586 (p : Nat → Bool) (h : Constraints p) : clause p c6586 = true :=
  Snake9.LocalRup.prove_clause [c6581, c5833, c1236] c6586 (by decide) p (sat_cons (step6581 p h) (sat_cons (step5833 p h) (sat_cons (step1236 p h) (sat_nil p))))
def c6587 : List Lit := [(1689, true)]
theorem step6587 (p : Nat → Bool) (h : Constraints p) : clause p c6587 = true :=
  Snake9.LocalRup.prove_clause [c6582, c6496, c1291] c6587 (by decide) p (sat_cons (step6582 p h) (sat_cons (step6496 p h) (sat_cons (step1291 p h) (sat_nil p))))
def c6588 : List Lit := [(1647, false)]
theorem step6588 (p : Nat → Bool) (h : Constraints p) : clause p c6588 = true :=
  Snake9.LocalRup.prove_clause [c6586, c6570, c1265] c6588 (by decide) p (sat_cons (step6586 p h) (sat_cons (step6570 p h) (sat_cons (step1265 p h) (sat_nil p))))
def c6589 : List Lit := [(110, false)]
theorem step6589 (p : Nat → Bool) (h : Constraints p) : clause p c6589 = true :=
  Snake9.LocalRup.prove_clause [c6587, c6564, c6576, c5655] c6589 (by decide) p (sat_cons (step6587 p h) (sat_cons (step6564 p h) (sat_cons (step6576 p h) (sat_cons (step5655 p h) (sat_nil p)))))
def c6590 : List Lit := [(64, false)]
theorem step6590 (p : Nat → Bool) (h : Constraints p) : clause p c6590 = true :=
  Snake9.LocalRup.prove_clause [c6588, c6576, c2786] c6590 (by decide) p (sat_cons (step6588 p h) (sat_cons (step6576 p h) (sat_cons (step2786 p h) (sat_nil p))))
def c6591 : List Lit := [(83, false)]
theorem step6591 (p : Nat → Bool) (h : Constraints p) : clause p c6591 = true :=
  Snake9.LocalRup.prove_clause [c6588, c6576, c6583, c5619] c6591 (by decide) p (sat_cons (step6588 p h) (sat_cons (step6576 p h) (sat_cons (step6583 p h) (sat_cons (step5619 p h) (sat_nil p)))))
def c6592 : List Lit := []
theorem step6592 (p : Nat → Bool) (h : Constraints p) : clause p c6592 = true :=
  Snake9.LocalRup.prove_clause [c6589, c6590, c6591, c6576, c6585, c1877] c6592 (by decide) p (sat_cons (step6589 p h) (sat_cons (step6590 p h) (sat_cons (step6591 p h) (sat_cons (step6576 p h) (sat_cons (step6585 p h) (sat_cons (step1877 p h) (sat_nil p)))))))
end B112E258
