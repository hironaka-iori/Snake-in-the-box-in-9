import B112E024Part0001
namespace B112E024
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1490 : List Lit := [(1682, true), (108, true), (85, false), (86, false)]
theorem step1490 (p : Nat → Bool) (h : Constraints p) : clause p c1490 = true :=
  Snake9.LocalRup.prove_clause [c1195, c1206, c1204, c1197, c1198, c1199, c386, c1479] c1490 (by decide) p (sat_cons (step1195 p h) (sat_cons (step1206 p h) (sat_cons (step1204 p h) (sat_cons (step1197 p h) (sat_cons (step1198 p h) (sat_cons (step1199 p h) (sat_cons (step386 p h) (sat_cons (step1479 p h) (sat_nil p)))))))))
def c1491 : List Lit := [(1539, true), (19, false), (89, false), (54, true)]
theorem step1491 (p : Nat → Bool) (h : Constraints p) : clause p c1491 = true :=
  Snake9.LocalRup.prove_clause [c601, c938, c949, c947, c940, c941, c942, c1472, c1344, c431, c254] c1491 (by decide) p (sat_cons (step601 p h) (sat_cons (step938 p h) (sat_cons (step949 p h) (sat_cons (step947 p h) (sat_cons (step940 p h) (sat_cons (step941 p h) (sat_cons (step942 p h) (sat_cons (step1472 p h) (sat_cons (step1344 p h) (sat_cons (step431 p h) (sat_cons (step254 p h) (sat_nil p))))))))))))
def c1492 : List Lit := [(105, true), (1666, true), (19, false), (83, true), (89, false), (88, true)]
theorem step1492 (p : Nat → Bool) (h : Constraints p) : clause p c1492 = true :=
  Snake9.LocalRup.prove_clause [c616, c1165, c1161, c1167, c1163, c1158, c436, c507, c429] c1492 (by decide) p (sat_cons (step616 p h) (sat_cons (step1165 p h) (sat_cons (step1161 p h) (sat_cons (step1167 p h) (sat_cons (step1163 p h) (sat_cons (step1158 p h) (sat_cons (step436 p h) (sat_cons (step507 p h) (sat_cons (step429 p h) (sat_nil p))))))))))
def c1493 : List Lit := [(108, false), (105, false), (88, true), (81, false)]
theorem step1493 (p : Nat → Bool) (h : Constraints p) : clause p c1493 = true :=
  Snake9.LocalRup.prove_clause [c624, c537, c522] c1493 (by decide) p (sat_cons (step624 p h) (sat_cons (step537 p h) (sat_cons (step522 p h) (sat_nil p))))
def c1494 : List Lit := [(105, false), (1682, true), (88, true), (81, false)]
theorem step1494 (p : Nat → Bool) (h : Constraints p) : clause p c1494 = true :=
  Snake9.LocalRup.prove_clause [c626, c1206, c1493, c1195, c1197, c1204, c1198, c1199, c540, c552, c548] c1494 (by decide) p (sat_cons (step626 p h) (sat_cons (step1206 p h) (sat_cons (step1493 p h) (sat_cons (step1195 p h) (sat_cons (step1197 p h) (sat_cons (step1204 p h) (sat_cons (step1198 p h) (sat_cons (step1199 p h) (sat_cons (step540 p h) (sat_cons (step552 p h) (sat_cons (step548 p h) (sat_nil p))))))))))))
def c1495 : List Lit := [(92, false), (107, false), (17, false), (86, false)]
theorem step1495 (p : Nat → Bool) (h : Constraints p) : clause p c1495 = true :=
  Snake9.LocalRup.prove_clause [c623, c367, c369, c534] c1495 (by decide) p (sat_cons (step623 p h) (sat_cons (step367 p h) (sat_cons (step369 p h) (sat_cons (step534 p h) (sat_nil p)))))
def c1496 : List Lit := [(92, true), (1654, true), (19, false), (83, true), (89, false), (88, true)]
theorem step1496 (p : Nat → Bool) (h : Constraints p) : clause p c1496 = true :=
  Snake9.LocalRup.prove_clause [c616, c617, c430, c449, c435, c1146] c1496 (by decide) p (sat_cons (step616 p h) (sat_cons (step617 p h) (sat_cons (step430 p h) (sat_cons (step449 p h) (sat_cons (step435 p h) (sat_cons (step1146 p h) (sat_nil p)))))))
def c1497 : List Lit := [(1654, true), (19, false), (83, true), (86, false), (89, false), (88, true)]
theorem step1497 (p : Nat → Bool) (h : Constraints p) : clause p c1497 = true :=
  Snake9.LocalRup.prove_clause [c1496, c452, c453, c1146] c1497 (by decide) p (sat_cons (step1496 p h) (sat_cons (step452 p h) (sat_cons (step453 p h) (sat_cons (step1146 p h) (sat_nil p)))))
def c1498 : List Lit := [(1519, true), (20, false), (13, false)]
theorem step1498 (p : Nat → Bool) (h : Constraints p) : clause p c1498 = true :=
  Snake9.LocalRup.prove_clause [c911, c1414, c1434, c1438, c913, c1405, c889, c886] c1498 (by decide) p (sat_cons (step911 p h) (sat_cons (step1414 p h) (sat_cons (step1434 p h) (sat_cons (step1438 p h) (sat_cons (step913 p h) (sat_cons (step1405 p h) (sat_cons (step889 p h) (sat_cons (step886 p h) (sat_nil p)))))))))
def c1499 : List Lit := [(1553, true), (1539, true), (54, true)]
theorem step1499 (p : Nat → Bool) (h : Constraints p) : clause p c1499 = true :=
  Snake9.LocalRup.prove_clause [c594, c938, c946, c949, c940, c947, c941, c1472, c237, c927, c930, c957, c1344, c978, c911, c1414, c1434, c1438, c910, c913, c209, c973, c889, c1415, c886, c925, c210] c1499 (by decide) p (sat_cons (step594 p h) (sat_cons (step938 p h) (sat_cons (step946 p h) (sat_cons (step949 p h) (sat_cons (step940 p h) (sat_cons (step947 p h) (sat_cons (step941 p h) (sat_cons (step1472 p h) (sat_cons (step237 p h) (sat_cons (step927 p h) (sat_cons (step930 p h) (sat_cons (step957 p h) (sat_cons (step1344 p h) (sat_cons (step978 p h) (sat_cons (step911 p h) (sat_cons (step1414 p h) (sat_cons (step1434 p h) (sat_cons (step1438 p h) (sat_cons (step910 p h) (sat_cons (step913 p h) (sat_cons (step209 p h) (sat_cons (step973 p h) (sat_cons (step889 p h) (sat_cons (step1415 p h) (sat_cons (step886 p h) (sat_cons (step925 p h) (sat_cons (step210 p h) (sat_nil p))))))))))))))))))))))))))))
def c1500 : List Lit := [(18, false), (14, false), (88, true), (81, false)]
theorem step1500 (p : Nat → Bool) (h : Constraints p) : clause p c1500 = true :=
  Snake9.LocalRup.prove_clause [c583, c98, c39] c1500 (by decide) p (sat_cons (step583 p h) (sat_cons (step98 p h) (sat_cons (step39 p h) (sat_nil p))))
def c1501 : List Lit := [(1481, false), (54, true), (1575, true)]
theorem step1501 (p : Nat → Bool) (h : Constraints p) : clause p c1501 = true :=
  Snake9.LocalRup.prove_clause [c1399, c1362, c19, c938, c865, c1006, c1468, c949, c947, c940, c941, c1469, c1472, c236, c784, c785, c1499, c1013, c870, c812, c808, c1470, c795, c791, c793, c797, c6, c789] c1501 (by decide) p (sat_cons (step1399 p h) (sat_cons (step1362 p h) (sat_cons (step19 p h) (sat_cons (step938 p h) (sat_cons (step865 p h) (sat_cons (step1006 p h) (sat_cons (step1468 p h) (sat_cons (step949 p h) (sat_cons (step947 p h) (sat_cons (step940 p h) (sat_cons (step941 p h) (sat_cons (step1469 p h) (sat_cons (step1472 p h) (sat_cons (step236 p h) (sat_cons (step784 p h) (sat_cons (step785 p h) (sat_cons (step1499 p h) (sat_cons (step1013 p h) (sat_cons (step870 p h) (sat_cons (step812 p h) (sat_cons (step808 p h) (sat_cons (step1470 p h) (sat_cons (step795 p h) (sat_cons (step791 p h) (sat_cons (step793 p h) (sat_cons (step797 p h) (sat_cons (step6 p h) (sat_cons (step789 p h) (sat_nil p)))))))))))))))))))))))))))))
def c1502 : List Lit := [(13, false), (12, true), (1476, true), (14, false), (19, false), (85, false), (81, false)]
theorem step1502 (p : Nat → Bool) (h : Constraints p) : clause p c1502 = true :=
  Snake9.LocalRup.prove_clause [c581, c840, c73, c324, c52, c53, c88, c830, c831, c838, c124, c833] c1502 (by decide) p (sat_cons (step581 p h) (sat_cons (step840 p h) (sat_cons (step73 p h) (sat_cons (step324 p h) (sat_cons (step52 p h) (sat_cons (step53 p h) (sat_cons (step88 p h) (sat_cons (step830 p h) (sat_cons (step831 p h) (sat_cons (step838 p h) (sat_cons (step124 p h) (sat_cons (step833 p h) (sat_nil p)))))))))))))
def c1503 : List Lit := [(11, true), (1453, true)]
theorem step1503 (p : Nat → Bool) (h : Constraints p) : clause p c1503 = true :=
  Snake9.LocalRup.prove_clause [c1362, c19, c795, c791, c793, c797, c6, c789] c1503 (by decide) p (sat_cons (step1362 p h) (sat_cons (step19 p h) (sat_cons (step795 p h) (sat_cons (step791 p h) (sat_cons (step793 p h) (sat_cons (step797 p h) (sat_cons (step6 p h) (sat_cons (step789 p h) (sat_nil p)))))))))
def c1504 : List Lit := [(1452, true)]
theorem step1504 (p : Nat → Bool) (h : Constraints p) : clause p c1504 = true :=
  Snake9.LocalRup.prove_clause [c1362, c19, c794, c796, c792, c789, c6] c1504 (by decide) p (sat_cons (step1362 p h) (sat_cons (step19 p h) (sat_cons (step794 p h) (sat_cons (step796 p h) (sat_cons (step792 p h) (sat_cons (step789 p h) (sat_cons (step6 p h) (sat_nil p))))))))
def c1505 : List Lit := [(1453, true), (1446, true)]
theorem step1505 (p : Nat → Bool) (h : Constraints p) : clause p c1505 = true :=
  Snake9.LocalRup.prove_clause [c580, c1398, c1503, c784, c30, c31, c787, c1318] c1505 (by decide) p (sat_cons (step580 p h) (sat_cons (step1398 p h) (sat_cons (step1503 p h) (sat_cons (step784 p h) (sat_cons (step30 p h) (sat_cons (step31 p h) (sat_cons (step787 p h) (sat_cons (step1318 p h) (sat_nil p)))))))))
def c1506 : List Lit := [(1458, true)]
theorem step1506 (p : Nat → Bool) (h : Constraints p) : clause p c1506 = true :=
  Snake9.LocalRup.prove_clause [c1504, c1362, c19, c580, c804, c812, c1505, c808, c785, c786, c784, c4, c5, c789, c798, c793, c31, c12] c1506 (by decide) p (sat_cons (step1504 p h) (sat_cons (step1362 p h) (sat_cons (step19 p h) (sat_cons (step580 p h) (sat_cons (step804 p h) (sat_cons (step812 p h) (sat_cons (step1505 p h) (sat_cons (step808 p h) (sat_cons (step785 p h) (sat_cons (step786 p h) (sat_cons (step784 p h) (sat_cons (step4 p h) (sat_cons (step5 p h) (sat_cons (step789 p h) (sat_cons (step798 p h) (sat_cons (step793 p h) (sat_cons (step31 p h) (sat_cons (step12 p h) (sat_nil p)))))))))))))))))))
def c1507 : List Lit := [(1490, true)]
theorem step1507 (p : Nat → Bool) (h : Constraints p) : clause p c1507 = true :=
  Snake9.LocalRup.prove_clause [c1506, c1397, c868] c1507 (by decide) p (sat_cons (step1506 p h) (sat_cons (step1397 p h) (sat_cons (step868 p h) (sat_nil p))))
def c1508 : List Lit := [(1655, true), (86, false), (85, false)]
theorem step1508 (p : Nat → Bool) (h : Constraints p) : clause p c1508 = true :=
  Snake9.LocalRup.prove_clause [c1147, c1148, c347, c1429] c1508 (by decide) p (sat_cons (step1147 p h) (sat_cons (step1148 p h) (sat_cons (step347 p h) (sat_cons (step1429 p h) (sat_nil p)))))
def c1509 : List Lit := [(54, true), (1539, true), (85, false)]
theorem step1509 (p : Nat → Bool) (h : Constraints p) : clause p c1509 = true :=
  Snake9.LocalRup.prove_clause [c949, c938, c940, c947, c941, c1472, c243] c1509 (by decide) p (sat_cons (step949 p h) (sat_cons (step938 p h) (sat_cons (step940 p h) (sat_cons (step947 p h) (sat_cons (step941 p h) (sat_cons (step1472 p h) (sat_cons (step243 p h) (sat_nil p))))))))
def c1510 : List Lit := [(1481, true), (1468, false), (18, true), (14, false), (86, false)]
theorem step1510 (p : Nat → Bool) (h : Constraints p) : clause p c1510 = true :=
  Snake9.LocalRup.prove_clause [c1463, c92, c853, c1453] c1510 (by decide) p (sat_cons (step1463 p h) (sat_cons (step92 p h) (sat_cons (step853 p h) (sat_cons (step1453 p h) (sat_nil p)))))
def c1511 : List Lit := [(9, true), (1, false), (15, true)]
theorem step1511 (p : Nat → Bool) (h : Constraints p) : clause p c1511 = true :=
  Snake9.LocalRup.prove_clause [c577, c2] c1511 (by decide) p (sat_cons (step577 p h) (sat_cons (step2 p h) (sat_nil p)))
def c1512 : List Lit := [(4, true), (1, false), (15, true)]
theorem step1512 (p : Nat → Bool) (h : Constraints p) : clause p c1512 = true :=
  Snake9.LocalRup.prove_clause [c577, c3] c1512 (by decide) p (sat_cons (step577 p h) (sat_cons (step3 p h) (sat_nil p)))
def c1513 : List Lit := [(3, false), (6, false)]
theorem step1513 (p : Nat → Bool) (h : Constraints p) : clause p c1513 = true :=
  Snake9.LocalRup.prove_clause [c19, c1362, c4] c1513 (by decide) p (sat_cons (step19 p h) (sat_cons (step1362 p h) (sat_cons (step4 p h) (sat_nil p))))
def c1514 : List Lit := [(3, false), (10, false)]
theorem step1514 (p : Nat → Bool) (h : Constraints p) : clause p c1514 = true :=
  Snake9.LocalRup.prove_clause [c19, c1362, c5] c1514 (by decide) p (sat_cons (step19 p h) (sat_cons (step1362 p h) (sat_cons (step5 p h) (sat_nil p))))
def c1515 : List Lit := [(6, false), (10, false)]
theorem step1515 (p : Nat → Bool) (h : Constraints p) : clause p c1515 = true :=
  Snake9.LocalRup.prove_clause [c19, c1362, c6] c1515 (by decide) p (sat_cons (step19 p h) (sat_cons (step1362 p h) (sat_cons (step6 p h) (sat_nil p))))
def c1516 : List Lit := [(6, true), (123, true), (10, true), (3, true)]
theorem step1516 (p : Nat → Bool) (h : Constraints p) : clause p c1516 = true :=
  Snake9.LocalRup.prove_clause [c1362, c7] c1516 (by decide) p (sat_cons (step1362 p h) (sat_cons (step7 p h) (sat_nil p)))
def c1517 : List Lit := [(7, false), (4, false), (3, false)]
theorem step1517 (p : Nat → Bool) (h : Constraints p) : clause p c1517 = true :=
  Snake9.LocalRup.prove_clause [c1362, c8] c1517 (by decide) p (sat_cons (step1362 p h) (sat_cons (step8 p h) (sat_nil p)))
def c1518 : List Lit := [(4, false), (16, false), (3, false)]
theorem step1518 (p : Nat → Bool) (h : Constraints p) : clause p c1518 = true :=
  Snake9.LocalRup.prove_clause [c1362, c9] c1518 (by decide) p (sat_cons (step1362 p h) (sat_cons (step9 p h) (sat_nil p)))
def c1519 : List Lit := [(7, false), (16, false), (3, false)]
theorem step1519 (p : Nat → Bool) (h : Constraints p) : clause p c1519 = true :=
  Snake9.LocalRup.prove_clause [c1362, c10] c1519 (by decide) p (sat_cons (step1362 p h) (sat_cons (step10 p h) (sat_nil p)))
def c1520 : List Lit := [(51, false), (16, false), (3, false)]
theorem step1520 (p : Nat → Bool) (h : Constraints p) : clause p c1520 = true :=
  Snake9.LocalRup.prove_clause [c1362, c11] c1520 (by decide) p (sat_cons (step1362 p h) (sat_cons (step11 p h) (sat_nil p)))
def c1521 : List Lit := [(6, false), (7, true)]
theorem step1521 (p : Nat → Bool) (h : Constraints p) : clause p c1521 = true :=
  Snake9.LocalRup.prove_clause [c578, c20] c1521 (by decide) p (sat_cons (step578 p h) (sat_cons (step20 p h) (sat_nil p)))
def c1522 : List Lit := [(8, false), (7, true)]
theorem step1522 (p : Nat → Bool) (h : Constraints p) : clause p c1522 = true :=
  Snake9.LocalRup.prove_clause [c579, c22] c1522 (by decide) p (sat_cons (step579 p h) (sat_cons (step22 p h) (sat_nil p)))
def c1523 : List Lit := [(8, false), (4, true)]
theorem step1523 (p : Nat → Bool) (h : Constraints p) : clause p c1523 = true :=
  Snake9.LocalRup.prove_clause [c579, c23] c1523 (by decide) p (sat_cons (step579 p h) (sat_cons (step23 p h) (sat_nil p)))
def c1524 : List Lit := [(11, false), (9, true)]
theorem step1524 (p : Nat → Bool) (h : Constraints p) : clause p c1524 = true :=
  Snake9.LocalRup.prove_clause [c580, c30] c1524 (by decide) p (sat_cons (step580 p h) (sat_cons (step30 p h) (sat_nil p)))
def c1525 : List Lit := [(11, false), (4, true)]
theorem step1525 (p : Nat → Bool) (h : Constraints p) : clause p c1525 = true :=
  Snake9.LocalRup.prove_clause [c580, c31] c1525 (by decide) p (sat_cons (step580 p h) (sat_cons (step31 p h) (sat_nil p)))
def c1526 : List Lit := [(23, true), (16, true), (82, true), (15, true), (13, false)]
theorem step1526 (p : Nat → Bool) (h : Constraints p) : clause p c1526 = true :=
  Snake9.LocalRup.prove_clause [c581, c50] c1526 (by decide) p (sat_cons (step581 p h) (sat_cons (step50 p h) (sat_nil p)))
def c1527 : List Lit := [(23, true), (16, true), (82, true), (12, true), (13, false)]
theorem step1527 (p : Nat → Bool) (h : Constraints p) : clause p c1527 = true :=
  Snake9.LocalRup.prove_clause [c581, c51] c1527 (by decide) p (sat_cons (step581 p h) (sat_cons (step51 p h) (sat_nil p)))
def c1528 : List Lit := [(82, true), (23, true), (15, true), (12, true), (13, false)]
theorem step1528 (p : Nat → Bool) (h : Constraints p) : clause p c1528 = true :=
  Snake9.LocalRup.prove_clause [c581, c52] c1528 (by decide) p (sat_cons (step581 p h) (sat_cons (step52 p h) (sat_nil p)))
def c1529 : List Lit := [(16, true), (82, true), (13, false), (15, true), (12, true)]
theorem step1529 (p : Nat → Bool) (h : Constraints p) : clause p c1529 = true :=
  Snake9.LocalRup.prove_clause [c581, c53] c1529 (by decide) p (sat_cons (step581 p h) (sat_cons (step53 p h) (sat_nil p)))
def c1530 : List Lit := [(23, true), (16, true), (12, true), (13, false), (15, true)]
theorem step1530 (p : Nat → Bool) (h : Constraints p) : clause p c1530 = true :=
  Snake9.LocalRup.prove_clause [c581, c54] c1530 (by decide) p (sat_cons (step581 p h) (sat_cons (step54 p h) (sat_nil p)))
def c1531 : List Lit := [(15, true), (32, true), (14, false), (12, true), (24, true), (83, true)]
theorem step1531 (p : Nat → Bool) (h : Constraints p) : clause p c1531 = true :=
  Snake9.LocalRup.prove_clause [c582, c60] c1531 (by decide) p (sat_cons (step582 p h) (sat_cons (step60 p h) (sat_nil p)))
def c1532 : List Lit := [(15, true), (24, true), (12, true), (14, false), (83, true), (17, true)]
theorem step1532 (p : Nat → Bool) (h : Constraints p) : clause p c1532 = true :=
  Snake9.LocalRup.prove_clause [c582, c61] c1532 (by decide) p (sat_cons (step582 p h) (sat_cons (step61 p h) (sat_nil p)))
def c1533 : List Lit := [(24, true), (32, true), (12, true), (14, false), (17, true), (15, true)]
theorem step1533 (p : Nat → Bool) (h : Constraints p) : clause p c1533 = true :=
  Snake9.LocalRup.prove_clause [c582, c62] c1533 (by decide) p (sat_cons (step582 p h) (sat_cons (step62 p h) (sat_nil p)))
def c1534 : List Lit := [(27, true), (18, false), (88, true)]
theorem step1534 (p : Nat → Bool) (h : Constraints p) : clause p c1534 = true :=
  Snake9.LocalRup.prove_clause [c583, c97] c1534 (by decide) p (sat_cons (step583 p h) (sat_cons (step97 p h) (sat_nil p)))
def c1535 : List Lit := [(12, true), (18, false), (88, true)]
theorem step1535 (p : Nat → Bool) (h : Constraints p) : clause p c1535 = true :=
  Snake9.LocalRup.prove_clause [c583, c98] c1535 (by decide) p (sat_cons (step583 p h) (sat_cons (step98 p h) (sat_nil p)))
def c1536 : List Lit := [(27, true), (12, true), (18, false)]
theorem step1536 (p : Nat → Bool) (h : Constraints p) : clause p c1536 = true :=
  Snake9.LocalRup.prove_clause [c583, c99] c1536 (by decide) p (sat_cons (step583 p h) (sat_cons (step99 p h) (sat_nil p)))
def c1537 : List Lit := [(21, true), (38, true), (19, false), (90, true)]
theorem step1537 (p : Nat → Bool) (h : Constraints p) : clause p c1537 = true :=
  Snake9.LocalRup.prove_clause [c584, c102] c1537 (by decide) p (sat_cons (step584 p h) (sat_cons (step102 p h) (sat_nil p)))
def c1538 : List Lit := [(38, true), (90, true), (19, false), (15, true)]
theorem step1538 (p : Nat → Bool) (h : Constraints p) : clause p c1538 = true :=
  Snake9.LocalRup.prove_clause [c584, c103] c1538 (by decide) p (sat_cons (step584 p h) (sat_cons (step103 p h) (sat_nil p)))
def c1539 : List Lit := [(21, true), (90, true), (19, false), (15, true)]
theorem step1539 (p : Nat → Bool) (h : Constraints p) : clause p c1539 = true :=
  Snake9.LocalRup.prove_clause [c584, c104] c1539 (by decide) p (sat_cons (step584 p h) (sat_cons (step104 p h) (sat_nil p)))
def c1540 : List Lit := [(21, true), (38, true), (19, false), (15, true)]
theorem step1540 (p : Nat → Bool) (h : Constraints p) : clause p c1540 = true :=
  Snake9.LocalRup.prove_clause [c584, c105] c1540 (by decide) p (sat_cons (step584 p h) (sat_cons (step105 p h) (sat_nil p)))
def c1541 : List Lit := [(29, true), (21, true), (20, false)]
theorem step1541 (p : Nat → Bool) (h : Constraints p) : clause p c1541 = true :=
  Snake9.LocalRup.prove_clause [c585, c107] c1541 (by decide) p (sat_cons (step585 p h) (sat_cons (step107 p h) (sat_nil p)))
def c1542 : List Lit := [(29, true), (16, true), (20, false)]
theorem step1542 (p : Nat → Bool) (h : Constraints p) : clause p c1542 = true :=
  Snake9.LocalRup.prove_clause [c585, c108] c1542 (by decide) p (sat_cons (step585 p h) (sat_cons (step108 p h) (sat_nil p)))
def c1543 : List Lit := [(21, true), (16, true), (20, false)]
theorem step1543 (p : Nat → Bool) (h : Constraints p) : clause p c1543 = true :=
  Snake9.LocalRup.prove_clause [c585, c109] c1543 (by decide) p (sat_cons (step585 p h) (sat_cons (step109 p h) (sat_nil p)))
def c1544 : List Lit := [(23, true), (27, true), (24, true), (22, false)]
theorem step1544 (p : Nat → Bool) (h : Constraints p) : clause p c1544 = true :=
  Snake9.LocalRup.prove_clause [c586, c120] c1544 (by decide) p (sat_cons (step586 p h) (sat_cons (step120 p h) (sat_nil p)))
def c1545 : List Lit := [(27, true), (24, true), (22, false), (12, true)]
theorem step1545 (p : Nat → Bool) (h : Constraints p) : clause p c1545 = true :=
  Snake9.LocalRup.prove_clause [c586, c121] c1545 (by decide) p (sat_cons (step586 p h) (sat_cons (step121 p h) (sat_nil p)))
def c1546 : List Lit := [(23, true), (27, true), (22, false), (12, true)]
theorem step1546 (p : Nat → Bool) (h : Constraints p) : clause p c1546 = true :=
  Snake9.LocalRup.prove_clause [c586, c122] c1546 (by decide) p (sat_cons (step586 p h) (sat_cons (step122 p h) (sat_nil p)))
def c1547 : List Lit := [(23, true), (24, true), (22, false), (12, true)]
theorem step1547 (p : Nat → Bool) (h : Constraints p) : clause p c1547 = true :=
  Snake9.LocalRup.prove_clause [c586, c123] c1547 (by decide) p (sat_cons (step586 p h) (sat_cons (step123 p h) (sat_nil p)))
def c1548 : List Lit := [(95, true), (15, true), (25, false), (24, true)]
theorem step1548 (p : Nat → Bool) (h : Constraints p) : clause p c1548 = true :=
  Snake9.LocalRup.prove_clause [c587, c138] c1548 (by decide) p (sat_cons (step587 p h) (sat_cons (step138 p h) (sat_nil p)))
def c1549 : List Lit := [(95, true), (23, true), (15, true), (25, false)]
theorem step1549 (p : Nat → Bool) (h : Constraints p) : clause p c1549 = true :=
  Snake9.LocalRup.prove_clause [c587, c139] c1549 (by decide) p (sat_cons (step587 p h) (sat_cons (step139 p h) (sat_nil p)))
def c1550 : List Lit := [(23, true), (15, true), (25, false), (24, true)]
theorem step1550 (p : Nat → Bool) (h : Constraints p) : clause p c1550 = true :=
  Snake9.LocalRup.prove_clause [c587, c140] c1550 (by decide) p (sat_cons (step587 p h) (sat_cons (step140 p h) (sat_nil p)))
def c1551 : List Lit := [(24, true), (30, true), (26, false)]
theorem step1551 (p : Nat → Bool) (h : Constraints p) : clause p c1551 = true :=
  Snake9.LocalRup.prove_clause [c588, c142] c1551 (by decide) p (sat_cons (step588 p h) (sat_cons (step142 p h) (sat_nil p)))
def c1552 : List Lit := [(30, true), (26, false), (17, true)]
theorem step1552 (p : Nat → Bool) (h : Constraints p) : clause p c1552 = true :=
  Snake9.LocalRup.prove_clause [c588, c143] c1552 (by decide) p (sat_cons (step588 p h) (sat_cons (step143 p h) (sat_nil p)))
def c1553 : List Lit := [(24, true), (26, false), (17, true)]
theorem step1553 (p : Nat → Bool) (h : Constraints p) : clause p c1553 = true :=
  Snake9.LocalRup.prove_clause [c588, c144] c1553 (by decide) p (sat_cons (step588 p h) (sat_cons (step144 p h) (sat_nil p)))
end B112E024
