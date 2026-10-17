import B112E019Part0150
namespace B112E019
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c11470 : List Lit := [(1737, true), (113, false), (109, true)]
theorem step11470 (p : Nat → Bool) (h : Constraints p) : clause p c11470 = true :=
  Snake9.LocalRup.prove_clause [c11440, c10377, c11443, c11454, c11297, c11452, c11442, c11467, c8568, c562, c1883, c9618, c5644, c7984, c1722, c1715, c9617, c1676, c3955, c6698, c8569, c11366] c11470 (by decide) p (sat_cons (step11440 p h) (sat_cons (step10377 p h) (sat_cons (step11443 p h) (sat_cons (step11454 p h) (sat_cons (step11297 p h) (sat_cons (step11452 p h) (sat_cons (step11442 p h) (sat_cons (step11467 p h) (sat_cons (step8568 p h) (sat_cons (step562 p h) (sat_cons (step1883 p h) (sat_cons (step9618 p h) (sat_cons (step5644 p h) (sat_cons (step7984 p h) (sat_cons (step1722 p h) (sat_cons (step1715 p h) (sat_cons (step9617 p h) (sat_cons (step1676 p h) (sat_cons (step3955 p h) (sat_cons (step6698 p h) (sat_cons (step8569 p h) (sat_cons (step11366 p h) (sat_nil p)))))))))))))))))))))))
def c11471 : List Lit := [(113, false), (109, true)]
theorem step11471 (p : Nat → Bool) (h : Constraints p) : clause p c11471 = true :=
  Snake9.LocalRup.prove_clause [c11440, c11452, c11443, c10377, c8568, c565, c11470, c2165, c7097, c10950, c2542, c1292, c6697, c5031, c3707, c1324, c4082, c1316, c1333, c10790] c11471 (by decide) p (sat_cons (step11440 p h) (sat_cons (step11452 p h) (sat_cons (step11443 p h) (sat_cons (step10377 p h) (sat_cons (step8568 p h) (sat_cons (step565 p h) (sat_cons (step11470 p h) (sat_cons (step2165 p h) (sat_cons (step7097 p h) (sat_cons (step10950 p h) (sat_cons (step2542 p h) (sat_cons (step1292 p h) (sat_cons (step6697 p h) (sat_cons (step5031 p h) (sat_cons (step3707 p h) (sat_cons (step1324 p h) (sat_cons (step4082 p h) (sat_cons (step1316 p h) (sat_cons (step1333 p h) (sat_cons (step10790 p h) (sat_nil p)))))))))))))))))))))
def c11472 : List Lit := [(1694, true), (1594, true), (417, false)]
theorem step11472 (p : Nat → Bool) (h : Constraints p) : clause p c11472 = true :=
  Snake9.LocalRup.prove_clause [c11452, c10086, c1169, c2542, c2146, c1292, c7956] c11472 (by decide) p (sat_cons (step11452 p h) (sat_cons (step10086 p h) (sat_cons (step1169 p h) (sat_cons (step2542 p h) (sat_cons (step2146 p h) (sat_cons (step1292 p h) (sat_cons (step7956 p h) (sat_nil p))))))))
def c11473 : List Lit := [(109, true)]
theorem step11473 (p : Nat → Bool) (h : Constraints p) : clause p c11473 = true :=
  Snake9.LocalRup.prove_clause [c10377, c11443, c11297, c11442, c11217, c11440, c11452, c8568, c5930, c562, c566, c1637, c8571, c2166, c11471, c1599, c1601, c1604, c1633, c1595, c8695, c9455, c1105, c11472] c11473 (by decide) p (sat_cons (step10377 p h) (sat_cons (step11443 p h) (sat_cons (step11297 p h) (sat_cons (step11442 p h) (sat_cons (step11217 p h) (sat_cons (step11440 p h) (sat_cons (step11452 p h) (sat_cons (step8568 p h) (sat_cons (step5930 p h) (sat_cons (step562 p h) (sat_cons (step566 p h) (sat_cons (step1637 p h) (sat_cons (step8571 p h) (sat_cons (step2166 p h) (sat_cons (step11471 p h) (sat_cons (step1599 p h) (sat_cons (step1601 p h) (sat_cons (step1604 p h) (sat_cons (step1633 p h) (sat_cons (step1595 p h) (sat_cons (step8695 p h) (sat_cons (step9455 p h) (sat_cons (step1105 p h) (sat_cons (step11472 p h) (sat_nil p)))))))))))))))))))))))))
def c11474 : List Lit := [(1716, true), (1694, false)]
theorem step11474 (p : Nat → Bool) (h : Constraints p) : clause p c11474 = true :=
  Snake9.LocalRup.prove_clause [c11454, c11452, c11442, c11440, c11443, c10377, c11217, c11473, c11468, c1670, c7984, c10704, c3423, c8502, c1598, c8500] c11474 (by decide) p (sat_cons (step11454 p h) (sat_cons (step11452 p h) (sat_cons (step11442 p h) (sat_cons (step11440 p h) (sat_cons (step11443 p h) (sat_cons (step10377 p h) (sat_cons (step11217 p h) (sat_cons (step11473 p h) (sat_cons (step11468 p h) (sat_cons (step1670 p h) (sat_cons (step7984 p h) (sat_cons (step10704 p h) (sat_cons (step3423 p h) (sat_cons (step8502 p h) (sat_cons (step1598 p h) (sat_cons (step8500 p h) (sat_nil p)))))))))))))))))
def c11475 : List Lit := [(1688, false), (1694, false), (1737, true), (80, true), (113, false)]
theorem step11475 (p : Nat → Bool) (h : Constraints p) : clause p c11475 = true :=
  Snake9.LocalRup.prove_clause [c11297, c11454, c11467, c11452, c11442, c10377, c11440, c11217, c11473, c11468, c11474, c1722, c9617, c1616, c1637, c8471, c1606, c10121, c9618, c1479, c1715, c1482, c1676, c11366, c6698, c5644, c9623, c323, c8502, c8500] c11475 (by decide) p (sat_cons (step11297 p h) (sat_cons (step11454 p h) (sat_cons (step11467 p h) (sat_cons (step11452 p h) (sat_cons (step11442 p h) (sat_cons (step10377 p h) (sat_cons (step11440 p h) (sat_cons (step11217 p h) (sat_cons (step11473 p h) (sat_cons (step11468 p h) (sat_cons (step11474 p h) (sat_cons (step1722 p h) (sat_cons (step9617 p h) (sat_cons (step1616 p h) (sat_cons (step1637 p h) (sat_cons (step8471 p h) (sat_cons (step1606 p h) (sat_cons (step10121 p h) (sat_cons (step9618 p h) (sat_cons (step1479 p h) (sat_cons (step1715 p h) (sat_cons (step1482 p h) (sat_cons (step1676 p h) (sat_cons (step11366 p h) (sat_cons (step6698 p h) (sat_cons (step5644 p h) (sat_cons (step9623 p h) (sat_cons (step323 p h) (sat_cons (step8502 p h) (sat_cons (step8500 p h) (sat_nil p)))))))))))))))))))))))))))))))
def c11476 : List Lit := [(112, false), (1694, false)]
theorem step11476 (p : Nat → Bool) (h : Constraints p) : clause p c11476 = true :=
  Snake9.LocalRup.prove_clause [c11440, c10377, c11443, c11217, c11473, c11452, c8512, c566, c323, c9623] c11476 (by decide) p (sat_cons (step11440 p h) (sat_cons (step10377 p h) (sat_cons (step11443 p h) (sat_cons (step11217 p h) (sat_cons (step11473 p h) (sat_cons (step11452 p h) (sat_cons (step8512 p h) (sat_cons (step566 p h) (sat_cons (step323 p h) (sat_cons (step9623 p h) (sat_nil p)))))))))))
def c11477 : List Lit := [(1694, false), (1737, true), (113, false), (80, true)]
theorem step11477 (p : Nat → Bool) (h : Constraints p) : clause p c11477 = true :=
  Snake9.LocalRup.prove_clause [c11475, c1598, c11476] c11477 (by decide) p (sat_cons (step11475 p h) (sat_cons (step1598 p h) (sat_cons (step11476 p h) (sat_nil p))))
def c11478 : List Lit := [(1682, true), (1646, true), (110, false), (80, true), (113, false)]
theorem step11478 (p : Nat → Bool) (h : Constraints p) : clause p c11478 = true :=
  Snake9.LocalRup.prove_clause [c11440, c11442, c11444, c11452, c11473, c11467, c10704, c6685, c707, c11366, c1479, c1482] c11478 (by decide) p (sat_cons (step11440 p h) (sat_cons (step11442 p h) (sat_cons (step11444 p h) (sat_cons (step11452 p h) (sat_cons (step11473 p h) (sat_cons (step11467 p h) (sat_cons (step10704 p h) (sat_cons (step6685 p h) (sat_cons (step707 p h) (sat_cons (step11366 p h) (sat_cons (step1479 p h) (sat_cons (step1482 p h) (sat_nil p)))))))))))))
def c11479 : List Lit := [(1646, true), (1694, true), (80, true), (113, false)]
theorem step11479 (p : Nat → Bool) (h : Constraints p) : clause p c11479 = true :=
  Snake9.LocalRup.prove_clause [c11217, c11468, c11469, c11452, c11297, c11454, c11440, c11473, c1608, c2814, c1609, c742, c775, c831, c1611, c4051, c6827, c9618, c4035, c6620, c11132, c11478, c1670, c1714, c2166, c6614, c11472, c1328, c1105, c1318, c9642, c698, c1441, c9616] c11479 (by decide) p (sat_cons (step11217 p h) (sat_cons (step11468 p h) (sat_cons (step11469 p h) (sat_cons (step11452 p h) (sat_cons (step11297 p h) (sat_cons (step11454 p h) (sat_cons (step11440 p h) (sat_cons (step11473 p h) (sat_cons (step1608 p h) (sat_cons (step2814 p h) (sat_cons (step1609 p h) (sat_cons (step742 p h) (sat_cons (step775 p h) (sat_cons (step831 p h) (sat_cons (step1611 p h) (sat_cons (step4051 p h) (sat_cons (step6827 p h) (sat_cons (step9618 p h) (sat_cons (step4035 p h) (sat_cons (step6620 p h) (sat_cons (step11132 p h) (sat_cons (step11478 p h) (sat_cons (step1670 p h) (sat_cons (step1714 p h) (sat_cons (step2166 p h) (sat_cons (step6614 p h) (sat_cons (step11472 p h) (sat_cons (step1328 p h) (sat_cons (step1105 p h) (sat_cons (step1318 p h) (sat_cons (step9642 p h) (sat_cons (step698 p h) (sat_cons (step1441 p h) (sat_cons (step9616 p h) (sat_nil p)))))))))))))))))))))))))))))))))))
def c11480 : List Lit := [(1737, true), (80, true), (113, false)]
theorem step11480 (p : Nat → Bool) (h : Constraints p) : clause p c11480 = true :=
  Snake9.LocalRup.prove_clause [c11440, c10377, c11442, c11452, c11458, c11477, c11479, c9617, c1721, c1722, c2166, c7984, c11472, c5644, c1105, c9623, c1068, c1050, c1065, c1056] c11480 (by decide) p (sat_cons (step11440 p h) (sat_cons (step10377 p h) (sat_cons (step11442 p h) (sat_cons (step11452 p h) (sat_cons (step11458 p h) (sat_cons (step11477 p h) (sat_cons (step11479 p h) (sat_cons (step9617 p h) (sat_cons (step1721 p h) (sat_cons (step1722 p h) (sat_cons (step2166 p h) (sat_cons (step7984 p h) (sat_cons (step11472 p h) (sat_cons (step5644 p h) (sat_cons (step1105 p h) (sat_cons (step9623 p h) (sat_cons (step1068 p h) (sat_cons (step1050 p h) (sat_cons (step1065 p h) (sat_cons (step1056 p h) (sat_nil p)))))))))))))))))))))
def c11481 : List Lit := [(1593, true), (113, false)]
theorem step11481 (p : Nat → Bool) (h : Constraints p) : clause p c11481 = true :=
  Snake9.LocalRup.prove_clause [c10377, c11468, c11473, c11217, c2149, c7097, c10950, c2400, c2542, c4035, c1291, c11476, c1598, c10124, c3994, c4961, c2399, c1333, c1389, c4082] c11481 (by decide) p (sat_cons (step10377 p h) (sat_cons (step11468 p h) (sat_cons (step11473 p h) (sat_cons (step11217 p h) (sat_cons (step2149 p h) (sat_cons (step7097 p h) (sat_cons (step10950 p h) (sat_cons (step2400 p h) (sat_cons (step2542 p h) (sat_cons (step4035 p h) (sat_cons (step1291 p h) (sat_cons (step11476 p h) (sat_cons (step1598 p h) (sat_cons (step10124 p h) (sat_cons (step3994 p h) (sat_cons (step4961 p h) (sat_cons (step2399 p h) (sat_cons (step1333 p h) (sat_cons (step1389 p h) (sat_cons (step4082 p h) (sat_nil p)))))))))))))))))))))
def c11482 : List Lit := [(80, false)]
theorem step11482 (p : Nat → Bool) (h : Constraints p) : clause p c11482 = true :=
  Snake9.LocalRup.prove_clause [c10377, c11443, c11440, c11441, c11442, c11452, c11468, c11217, c11473, c11298, c562, c3541, c570, c9623, c9674, c1428, c7984, c1598, c323, c1050, c2047, c1422, c1423, c8502, c8369, c1056, c8500, c1611, c1065, c1608, c4051, c1068, c2128, c354, c707, c1105, c1045, c1479, c11472, c1043, c2166, c1040, c1714, c3581, c9618, c648, c1496, c1476, c1485] c11482 (by decide) p (sat_cons (step10377 p h) (sat_cons (step11443 p h) (sat_cons (step11440 p h) (sat_cons (step11441 p h) (sat_cons (step11442 p h) (sat_cons (step11452 p h) (sat_cons (step11468 p h) (sat_cons (step11217 p h) (sat_cons (step11473 p h) (sat_cons (step11298 p h) (sat_cons (step562 p h) (sat_cons (step3541 p h) (sat_cons (step570 p h) (sat_cons (step9623 p h) (sat_cons (step9674 p h) (sat_cons (step1428 p h) (sat_cons (step7984 p h) (sat_cons (step1598 p h) (sat_cons (step323 p h) (sat_cons (step1050 p h) (sat_cons (step2047 p h) (sat_cons (step1422 p h) (sat_cons (step1423 p h) (sat_cons (step8502 p h) (sat_cons (step8369 p h) (sat_cons (step1056 p h) (sat_cons (step8500 p h) (sat_cons (step1611 p h) (sat_cons (step1065 p h) (sat_cons (step1608 p h) (sat_cons (step4051 p h) (sat_cons (step1068 p h) (sat_cons (step2128 p h) (sat_cons (step354 p h) (sat_cons (step707 p h) (sat_cons (step1105 p h) (sat_cons (step1045 p h) (sat_cons (step1479 p h) (sat_cons (step11472 p h) (sat_cons (step1043 p h) (sat_cons (step2166 p h) (sat_cons (step1040 p h) (sat_cons (step1714 p h) (sat_cons (step3581 p h) (sat_cons (step9618 p h) (sat_cons (step648 p h) (sat_cons (step1496 p h) (sat_cons (step1476 p h) (sat_cons (step1485 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))
def c11483 : List Lit := [(113, false)]
theorem step11483 (p : Nat → Bool) (h : Constraints p) : clause p c11483 = true :=
  Snake9.LocalRup.prove_clause [c11482, c11481, c11480, c2165] c11483 (by decide) p (sat_cons (step11482 p h) (sat_cons (step11481 p h) (sat_cons (step11480 p h) (sat_cons (step2165 p h) (sat_nil p)))))
def c11484 : List Lit := [(1688, true)]
theorem step11484 (p : Nat → Bool) (h : Constraints p) : clause p c11484 = true :=
  Snake9.LocalRup.prove_clause [c11483, c1597] c11484 (by decide) p (sat_cons (step11483 p h) (sat_cons (step1597 p h) (sat_nil p)))
def c11485 : List Lit := [(1645, true)]
theorem step11485 (p : Nat → Bool) (h : Constraints p) : clause p c11485 = true :=
  Snake9.LocalRup.prove_clause [c11484, c11217, c11297, c11473, c11482, c8471] c11485 (by decide) p (sat_cons (step11484 p h) (sat_cons (step11217 p h) (sat_cons (step11297 p h) (sat_cons (step11473 p h) (sat_cons (step11482 p h) (sat_cons (step8471 p h) (sat_nil p)))))))
def c11486 : List Lit := [(1655, true)]
theorem step11486 (p : Nat → Bool) (h : Constraints p) : clause p c11486 = true :=
  Snake9.LocalRup.prove_clause [c11485, c9618] c11486 (by decide) p (sat_cons (step11485 p h) (sat_cons (step9618 p h) (sat_nil p)))
def c11487 : List Lit := [(1694, false)]
theorem step11487 (p : Nat → Bool) (h : Constraints p) : clause p c11487 = true :=
  Snake9.LocalRup.prove_clause [c11473, c11483, c11435, c11476, c1599] c11487 (by decide) p (sat_cons (step11473 p h) (sat_cons (step11483 p h) (sat_cons (step11435 p h) (sat_cons (step11476 p h) (sat_cons (step1599 p h) (sat_nil p))))))
def c11488 : List Lit := [(116, true)]
theorem step11488 (p : Nat → Bool) (h : Constraints p) : clause p c11488 = true :=
  Snake9.LocalRup.prove_clause [c11487, c1608] c11488 (by decide) p (sat_cons (step11487 p h) (sat_cons (step1608 p h) (sat_nil p)))
def c11489 : List Lit := [(115, true)]
theorem step11489 (p : Nat → Bool) (h : Constraints p) : clause p c11489 = true :=
  Snake9.LocalRup.prove_clause [c11487, c1609] c11489 (by decide) p (sat_cons (step11487 p h) (sat_cons (step1609 p h) (sat_nil p)))
def c11490 : List Lit := [(50, true)]
theorem step11490 (p : Nat → Bool) (h : Constraints p) : clause p c11490 = true :=
  Snake9.LocalRup.prove_clause [c11489, c11488, c11468, c6851] c11490 (by decide) p (sat_cons (step11489 p h) (sat_cons (step11488 p h) (sat_cons (step11468 p h) (sat_cons (step6851 p h) (sat_nil p)))))
def c11491 : List Lit := [(1551, true)]
theorem step11491 (p : Nat → Bool) (h : Constraints p) : clause p c11491 = true :=
  Snake9.LocalRup.prove_clause [c11490, c11489, c1928] c11491 (by decide) p (sat_cons (step11490 p h) (sat_cons (step11489 p h) (sat_cons (step1928 p h) (sat_nil p))))
def c11492 : List Lit := [(63, true)]
theorem step11492 (p : Nat → Bool) (h : Constraints p) : clause p c11492 = true :=
  Snake9.LocalRup.prove_clause [c11452, c11440, c11483, c11473, c1427, c9678, c9623, c1450, c2040, c1050, c326, c9622, c2125, c1433, c1051, c344] c11492 (by decide) p (sat_cons (step11452 p h) (sat_cons (step11440 p h) (sat_cons (step11483 p h) (sat_cons (step11473 p h) (sat_cons (step1427 p h) (sat_cons (step9678 p h) (sat_cons (step9623 p h) (sat_cons (step1450 p h) (sat_cons (step2040 p h) (sat_cons (step1050 p h) (sat_cons (step326 p h) (sat_cons (step9622 p h) (sat_cons (step2125 p h) (sat_cons (step1433 p h) (sat_cons (step1051 p h) (sat_cons (step344 p h) (sat_nil p)))))))))))))))))
def c11493 : List Lit := [(1674, true)]
theorem step11493 (p : Nat → Bool) (h : Constraints p) : clause p c11493 = true :=
  Snake9.LocalRup.prove_clause [c11492, c10377, c11442, c5644] c11493 (by decide) p (sat_cons (step11492 p h) (sat_cons (step10377 p h) (sat_cons (step11442 p h) (sat_cons (step5644 p h) (sat_nil p)))))
def c11494 : List Lit := [(112, false)]
theorem step11494 (p : Nat → Bool) (h : Constraints p) : clause p c11494 = true :=
  Snake9.LocalRup.prove_clause [c11492, c10377, c11443, c566] c11494 (by decide) p (sat_cons (step11492 p h) (sat_cons (step10377 p h) (sat_cons (step11443 p h) (sat_cons (step566 p h) (sat_nil p)))))
def c11495 : List Lit := [(1716, true)]
theorem step11495 (p : Nat → Bool) (h : Constraints p) : clause p c11495 = true :=
  Snake9.LocalRup.prove_clause [c11493, c11452, c11442, c7984] c11495 (by decide) p (sat_cons (step11493 p h) (sat_cons (step11452 p h) (sat_cons (step11442 p h) (sat_cons (step7984 p h) (sat_nil p)))))
def c11496 : List Lit := [(1689, true)]
theorem step11496 (p : Nat → Bool) (h : Constraints p) : clause p c11496 = true :=
  Snake9.LocalRup.prove_clause [c11494, c11483, c1599] c11496 (by decide) p (sat_cons (step11494 p h) (sat_cons (step11483 p h) (sat_cons (step1599 p h) (sat_nil p))))
def c11497 : List Lit := [(1736, true)]
theorem step11497 (p : Nat → Bool) (h : Constraints p) : clause p c11497 = true :=
  Snake9.LocalRup.prove_clause [c11495, c11486, c1714] c11497 (by decide) p (sat_cons (step11495 p h) (sat_cons (step11486 p h) (sat_cons (step1714 p h) (sat_nil p))))
def c11498 : List Lit := [(48, false)]
theorem step11498 (p : Nat → Bool) (h : Constraints p) : clause p c11498 = true :=
  Snake9.LocalRup.prove_clause [c11496, c11473, c11436] c11498 (by decide) p (sat_cons (step11496 p h) (sat_cons (step11473 p h) (sat_cons (step11436 p h) (sat_nil p))))
def c11499 : List Lit := [(1594, false)]
theorem step11499 (p : Nat → Bool) (h : Constraints p) : clause p c11499 = true :=
  Snake9.LocalRup.prove_clause [c11497, c2166] c11499 (by decide) p (sat_cons (step11497 p h) (sat_cons (step2166 p h) (sat_nil p)))
def c11500 : List Lit := [(1549, true)]
theorem step11500 (p : Nat → Bool) (h : Constraints p) : clause p c11500 = true :=
  Snake9.LocalRup.prove_clause [c11498, c1316] c11500 (by decide) p (sat_cons (step11498 p h) (sat_cons (step1316 p h) (sat_nil p)))
def c11501 : List Lit := [(1555, false)]
theorem step11501 (p : Nat → Bool) (h : Constraints p) : clause p c11501 = true :=
  Snake9.LocalRup.prove_clause [c11499, c6614] c11501 (by decide) p (sat_cons (step11499 p h) (sat_cons (step6614 p h) (sat_nil p)))
def c11502 : List Lit := [(1554, true)]
theorem step11502 (p : Nat → Bool) (h : Constraints p) : clause p c11502 = true :=
  Snake9.LocalRup.prove_clause [c11500, c11491, c1325] c11502 (by decide) p (sat_cons (step11500 p h) (sat_cons (step11491 p h) (sat_cons (step1325 p h) (sat_nil p))))
def c11503 : List Lit := [(1550, false)]
theorem step11503 (p : Nat → Bool) (h : Constraints p) : clause p c11503 = true :=
  Snake9.LocalRup.prove_clause [c11501, c11491, c1328] c11503 (by decide) p (sat_cons (step11501 p h) (sat_cons (step11491 p h) (sat_cons (step1328 p h) (sat_nil p))))
def c11504 : List Lit := [(46, true)]
theorem step11504 (p : Nat → Bool) (h : Constraints p) : clause p c11504 = true :=
  Snake9.LocalRup.prove_clause [c11503, c11498, c1318] c11504 (by decide) p (sat_cons (step11503 p h) (sat_cons (step11498 p h) (sat_cons (step1318 p h) (sat_nil p))))
def c11505 : List Lit := [(1593, true)]
theorem step11505 (p : Nat → Bool) (h : Constraints p) : clause p c11505 = true :=
  Snake9.LocalRup.prove_clause [c11502, c6976] c11505 (by decide) p (sat_cons (step11502 p h) (sat_cons (step6976 p h) (sat_nil p)))
def c11506 : List Lit := [(1543, false)]
theorem step11506 (p : Nat → Bool) (h : Constraints p) : clause p c11506 = true :=
  Snake9.LocalRup.prove_clause [c11502, c11499, c6655] c11506 (by decide) p (sat_cons (step11502 p h) (sat_cons (step11499 p h) (sat_cons (step6655 p h) (sat_nil p))))
def c11507 : List Lit := [(1737, false)]
theorem step11507 (p : Nat → Bool) (h : Constraints p) : clause p c11507 = true :=
  Snake9.LocalRup.prove_clause [c11505, c2165] c11507 (by decide) p (sat_cons (step11505 p h) (sat_cons (step2165 p h) (sat_nil p)))
def c11508 : List Lit := [(1536, false)]
theorem step11508 (p : Nat → Bool) (h : Constraints p) : clause p c11508 = true :=
  Snake9.LocalRup.prove_clause [c11506, c2542] c11508 (by decide) p (sat_cons (step11506 p h) (sat_cons (step2542 p h) (sat_nil p)))
def c11509 : List Lit := [(1656, false)]
theorem step11509 (p : Nat → Bool) (h : Constraints p) : clause p c11509 = true :=
  Snake9.LocalRup.prove_clause [c11507, c11495, c1722] c11509 (by decide) p (sat_cons (step11507 p h) (sat_cons (step11495 p h) (sat_cons (step1722 p h) (sat_nil p))))
def c11510 : List Lit := [(44, true)]
theorem step11510 (p : Nat → Bool) (h : Constraints p) : clause p c11510 = true :=
  Snake9.LocalRup.prove_clause [c11508, c1291] c11510 (by decide) p (sat_cons (step11508 p h) (sat_cons (step1291 p h) (sat_nil p)))
def c11511 : List Lit := [(1646, false)]
theorem step11511 (p : Nat → Bool) (h : Constraints p) : clause p c11511 = true :=
  Snake9.LocalRup.prove_clause [c11509, c9617] c11511 (by decide) p (sat_cons (step11509 p h) (sat_cons (step9617 p h) (sat_nil p)))
def c11512 : List Lit := [(87, true)]
theorem step11512 (p : Nat → Bool) (h : Constraints p) : clause p c11512 = true :=
  Snake9.LocalRup.prove_clause [c11510, c11482, c11297, c11488, c11511, c3572] c11512 (by decide) p (sat_cons (step11510 p h) (sat_cons (step11482 p h) (sat_cons (step11297 p h) (sat_cons (step11488 p h) (sat_cons (step11511 p h) (sat_cons (step3572 p h) (sat_nil p)))))))
def c11513 : List Lit := []
theorem step11513 (p : Nat → Bool) (h : Constraints p) : clause p c11513 = true :=
  Snake9.LocalRup.prove_clause [c11512, c11511, c11504, c11297, c11482, c11452, c11132] c11513 (by decide) p (sat_cons (step11512 p h) (sat_cons (step11511 p h) (sat_cons (step11504 p h) (sat_cons (step11297 p h) (sat_cons (step11482 p h) (sat_cons (step11452 p h) (sat_cons (step11132 p h) (sat_nil p))))))))
end B112E019
