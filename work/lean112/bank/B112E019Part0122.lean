import B112E019Part0121
namespace B112E019
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c9614 : List Lit := [(1715, false), (116, true), (1681, true), (1736, true), (100, true), (112, false), (107, true), (99, false), (80, true), (1627, true), (118, true), (1622, false), (41, true)]
theorem step9614 (p : Nat → Bool) (h : Constraints p) : clause p c9614 = true :=
  Snake9.TreeRup.prove_clause [c8368, c1466, c1468, c397, c1866, c1239, c1462, c2290, c1288, c1721, c1535, c2385, c1496, c5511, c1333, c1334, c9612, c1480, c1481, c1482, c1485, c1495, c1500, c1476, c1477, c1534, c1542, c1469, c394, c469, c1713, c1459, c1467, c2167, c9343, c461, c1088, c1091, c4538, c1093, c2133, c290, c1098, c1086, c1103, c4142, c1083, c1169, c1364, c442, c2146, c1398, c646, c640, c1030, c1032, c1267, c3861, c2020, c1949, c5503, c1391] c9614 (by decide) p (sat_cons (step8368 p h) (sat_cons (step1466 p h) (sat_cons (step1468 p h) (sat_cons (step397 p h) (sat_cons (step1866 p h) (sat_cons (step1239 p h) (sat_cons (step1462 p h) (sat_cons (step2290 p h) (sat_cons (step1288 p h) (sat_cons (step1721 p h) (sat_cons (step1535 p h) (sat_cons (step2385 p h) (sat_cons (step1496 p h) (sat_cons (step5511 p h) (sat_cons (step1333 p h) (sat_cons (step1334 p h) (sat_cons (step9612 p h) (sat_cons (step1480 p h) (sat_cons (step1481 p h) (sat_cons (step1482 p h) (sat_cons (step1485 p h) (sat_cons (step1495 p h) (sat_cons (step1500 p h) (sat_cons (step1476 p h) (sat_cons (step1477 p h) (sat_cons (step1534 p h) (sat_cons (step1542 p h) (sat_cons (step1469 p h) (sat_cons (step394 p h) (sat_cons (step469 p h) (sat_cons (step1713 p h) (sat_cons (step1459 p h) (sat_cons (step1467 p h) (sat_cons (step2167 p h) (sat_cons (step9343 p h) (sat_cons (step461 p h) (sat_cons (step1088 p h) (sat_cons (step1091 p h) (sat_cons (step4538 p h) (sat_cons (step1093 p h) (sat_cons (step2133 p h) (sat_cons (step290 p h) (sat_cons (step1098 p h) (sat_cons (step1086 p h) (sat_cons (step1103 p h) (sat_cons (step4142 p h) (sat_cons (step1083 p h) (sat_cons (step1169 p h) (sat_cons (step1364 p h) (sat_cons (step442 p h) (sat_cons (step2146 p h) (sat_cons (step1398 p h) (sat_cons (step646 p h) (sat_cons (step640 p h) (sat_cons (step1030 p h) (sat_cons (step1032 p h) (sat_cons (step1267 p h) (sat_cons (step3861 p h) (sat_cons (step2020 p h) (sat_cons (step1949 p h) (sat_cons (step5503 p h) (sat_cons (step1391 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c9615 : List Lit := [(74, true), (1686, true), (63, true), (1623, true), (387, true), (116, false)]
theorem step9615 (p : Nat → Bool) (h : Constraints p) : clause p c9615 = true :=
  Snake9.LocalRup.prove_clause [c8365, c2336] c9615 (by decide) p (sat_cons (step8365 p h) (sat_cons (step2336 p h) (sat_nil p)))
def c9616 : List Lit := [(69, true), (1613, true)]
theorem step9616 (p : Nat → Bool) (h : Constraints p) : clause p c9616 = true :=
  Snake9.LocalRup.prove_clause [c8365, c1432] c9616 (by decide) p (sat_cons (step8365 p h) (sat_cons (step1432 p h) (sat_nil p)))
def c9617 : List Lit := [(1646, false), (1656, true)]
theorem step9617 (p : Nat → Bool) (h : Constraints p) : clause p c9617 = true :=
  Snake9.LocalRup.prove_clause [c8381, c1528] c9617 (by decide) p (sat_cons (step8381 p h) (sat_cons (step1528 p h) (sat_nil p)))
def c9618 : List Lit := [(1645, false), (1655, true)]
theorem step9618 (p : Nat → Bool) (h : Constraints p) : clause p c9618 = true :=
  Snake9.LocalRup.prove_clause [c8381, c1527] c9618 (by decide) p (sat_cons (step8381 p h) (sat_cons (step1527 p h) (sat_nil p)))
def c9619 : List Lit := [(77, false), (76, true), (118, true)]
theorem step9619 (p : Nat → Bool) (h : Constraints p) : clause p c9619 = true :=
  Snake9.LocalRup.prove_clause [c8365, c2046] c9619 (by decide) p (sat_cons (step8365 p h) (sat_cons (step2046 p h) (sat_nil p)))
def c9620 : List Lit := [(164, true), (159, true), (185, true), (187, true), (193, true), (210, true), (241, true), (169, true), (152, true), (139, true), (123, true), (239, true), (140, true), (173, true), (172, true), (132, true), (130, true), (156, true), (154, true), (145, true), (216, true), (219, true), (192, true), (224, true), (208, true), (213, true), (128, true), (234, true), (149, true), (162, true), (142, true), (137, true), (126, true), (233, true), (231, true), (202, true), (201, true), (182, true), (236, true), (179, true), (212, true), (167, true), (175, true), (176, true), (165, true), (135, true), (147, true), (228, true), (196, true), (190, true), (237, true), (184, true), (157, true), (206, true), (223, true), (203, true), (197, true), (220, true)]
theorem step9620 (p : Nat → Bool) (h : Constraints p) : clause p c9620 = true :=
  Snake9.LocalRup.prove_clause [c8366, c1862] c9620 (by decide) p (sat_cons (step8366 p h) (sat_cons (step1862 p h) (sat_nil p)))
def c9621 : List Lit := [(1615, false), (1618, true)]
theorem step9621 (p : Nat → Bool) (h : Constraints p) : clause p c9621 = true :=
  Snake9.LocalRup.prove_clause [c8367, c1440] c9621 (by decide) p (sat_cons (step8367 p h) (sat_cons (step1440 p h) (sat_nil p)))
def c9622 : List Lit := [(1614, false), (1617, true)]
theorem step9622 (p : Nat → Bool) (h : Constraints p) : clause p c9622 = true :=
  Snake9.LocalRup.prove_clause [c8367, c1439] c9622 (by decide) p (sat_cons (step8367 p h) (sat_cons (step1439 p h) (sat_nil p)))
def c9623 : List Lit := [(63, true), (1622, true), (190, true)]
theorem step9623 (p : Nat → Bool) (h : Constraints p) : clause p c9623 = true :=
  Snake9.LocalRup.prove_clause [c8365, c1944] c9623 (by decide) p (sat_cons (step8365 p h) (sat_cons (step1944 p h) (sat_nil p)))
def c9624 : List Lit := [(1610, false), (1622, true)]
theorem step9624 (p : Nat → Bool) (h : Constraints p) : clause p c9624 = true :=
  Snake9.LocalRup.prove_clause [c8368, c1454] c9624 (by decide) p (sat_cons (step8368 p h) (sat_cons (step1454 p h) (sat_nil p)))
def c9625 : List Lit := [(66, true), (63, true), (1623, true), (107, false), (109, true)]
theorem step9625 (p : Nat → Bool) (h : Constraints p) : clause p c9625 = true :=
  Snake9.LocalRup.prove_clause [c8365, c2337] c9625 (by decide) p (sat_cons (step8365 p h) (sat_cons (step2337 p h) (sat_nil p)))
def c9626 : List Lit := [(1611, false), (1623, true)]
theorem step9626 (p : Nat → Bool) (h : Constraints p) : clause p c9626 = true :=
  Snake9.LocalRup.prove_clause [c8368, c1459] c9626 (by decide) p (sat_cons (step8368 p h) (sat_cons (step1459 p h) (sat_nil p)))
def c9627 : List Lit := [(1653, true), (1643, false)]
theorem step9627 (p : Nat → Bool) (h : Constraints p) : clause p c9627 = true :=
  Snake9.LocalRup.prove_clause [c8381, c1525] c9627 (by decide) p (sat_cons (step8381 p h) (sat_cons (step1525 p h) (sat_nil p)))
def c9628 : List Lit := [(1654, true), (1644, false)]
theorem step9628 (p : Nat → Bool) (h : Constraints p) : clause p c9628 = true :=
  Snake9.LocalRup.prove_clause [c8381, c1526] c9628 (by decide) p (sat_cons (step8381 p h) (sat_cons (step1526 p h) (sat_nil p)))
def c9629 : List Lit := [(1647, false), (1657, true)]
theorem step9629 (p : Nat → Bool) (h : Constraints p) : clause p c9629 = true :=
  Snake9.LocalRup.prove_clause [c8381, c1529] c9629 (by decide) p (sat_cons (step8381 p h) (sat_cons (step1529 p h) (sat_nil p)))
def c9630 : List Lit := [(46, true), (106, false), (102, true), (118, true), (110, true)]
theorem step9630 (p : Nat → Bool) (h : Constraints p) : clause p c9630 = true :=
  Snake9.LocalRup.prove_clause [c8365, c2081] c9630 (by decide) p (sat_cons (step8365 p h) (sat_cons (step2081 p h) (sat_nil p)))
def c9631 : List Lit := [(1607, true), (63, true), (1622, true), (99, false)]
theorem step9631 (p : Nat → Bool) (h : Constraints p) : clause p c9631 = true :=
  Snake9.LocalRup.prove_clause [c8365, c2173] c9631 (by decide) p (sat_cons (step8365 p h) (sat_cons (step2173 p h) (sat_nil p)))
def c9632 : List Lit := [(1735, true), (1718, false)]
theorem step9632 (p : Nat → Bool) (h : Constraints p) : clause p c9632 = true :=
  Snake9.LocalRup.prove_clause [c8833, c1690] c9632 (by decide) p (sat_cons (step8833 p h) (sat_cons (step1690 p h) (sat_nil p)))
def c9633 : List Lit := [(1719, false), (1736, true)]
theorem step9633 (p : Nat → Bool) (h : Constraints p) : clause p c9633 = true :=
  Snake9.LocalRup.prove_clause [c8833, c1691] c9633 (by decide) p (sat_cons (step8833 p h) (sat_cons (step1691 p h) (sat_nil p)))
def c9634 : List Lit := [(71, true), (193, true), (1623, true), (63, true)]
theorem step9634 (p : Nat → Bool) (h : Constraints p) : clause p c9634 = true :=
  Snake9.LocalRup.prove_clause [c8365, c1933] c9634 (by decide) p (sat_cons (step8365 p h) (sat_cons (step1933 p h) (sat_nil p)))
def c9635 : List Lit := [(14, true), (7, true), (46, true), (12, false)]
theorem step9635 (p : Nat → Bool) (h : Constraints p) : clause p c9635 = true :=
  Snake9.LocalRup.prove_clause [c8365, c1981] c9635 (by decide) p (sat_cons (step8365 p h) (sat_cons (step1981 p h) (sat_nil p)))
def c9636 : List Lit := [(1610, false), (1644, false), (1681, false), (1705, true), (1699, false), (1736, true), (109, false), (1688, false)]
theorem step9636 (p : Nat → Bool) (h : Constraints p) : clause p c9636 = true :=
  Snake9.LocalRup.prove_clause [c8365, c2952] c9636 (by decide) p (sat_cons (step8365 p h) (sat_cons (step2952 p h) (sat_nil p)))
def c9637 : List Lit := [(116, false), (1623, true), (75, false), (1610, false), (63, true), (107, false), (109, true)]
theorem step9637 (p : Nat → Bool) (h : Constraints p) : clause p c9637 = true :=
  Snake9.LocalRup.prove_clause [c8365, c2736] c9637 (by decide) p (sat_cons (step8365 p h) (sat_cons (step2736 p h) (sat_nil p)))
def c9638 : List Lit := [(116, false), (387, true), (63, true), (1623, true), (107, false), (1610, true)]
theorem step9638 (p : Nat → Bool) (h : Constraints p) : clause p c9638 = true :=
  Snake9.LocalRup.prove_clause [c8365, c3533] c9638 (by decide) p (sat_cons (step8365 p h) (sat_cons (step3533 p h) (sat_nil p)))
def c9639 : List Lit := [(116, false), (1623, true), (387, true), (63, true), (109, true), (1686, true)]
theorem step9639 (p : Nat → Bool) (h : Constraints p) : clause p c9639 = true :=
  Snake9.LocalRup.prove_clause [c8365, c3507] c9639 (by decide) p (sat_cons (step8365 p h) (sat_cons (step3507 p h) (sat_nil p)))
def c9640 : List Lit := [(1734, true), (184, true), (212, true), (1644, false), (190, true), (1705, false)]
theorem step9640 (p : Nat → Bool) (h : Constraints p) : clause p c9640 = true :=
  Snake9.LocalRup.prove_clause [c8365, c3859] c9640 (by decide) p (sat_cons (step8365 p h) (sat_cons (step3859 p h) (sat_nil p)))
def c9641 : List Lit := [(65, false), (72, false), (66, true), (1623, true), (100, true), (99, false), (1608, true)]
theorem step9641 (p : Nat → Bool) (h : Constraints p) : clause p c9641 = true :=
  Snake9.LocalRup.prove_clause [c8365, c3666] c9641 (by decide) p (sat_cons (step8365 p h) (sat_cons (step3666 p h) (sat_nil p)))
def c9642 : List Lit := [(1617, false), (387, true), (1622, true)]
theorem step9642 (p : Nat → Bool) (h : Constraints p) : clause p c9642 = true :=
  Snake9.LocalRup.prove_clause [c8365, c3532] c9642 (by decide) p (sat_cons (step8365 p h) (sat_cons (step3532 p h) (sat_nil p)))
def c9643 : List Lit := [(417, true), (1657, true), (99, false), (107, false), (100, true), (109, true)]
theorem step9643 (p : Nat → Bool) (h : Constraints p) : clause p c9643 = true :=
  Snake9.LocalRup.prove_clause [c8365, c3933] c9643 (by decide) p (sat_cons (step8365 p h) (sat_cons (step3933 p h) (sat_nil p)))
def c9644 : List Lit := [(184, true), (1654, true), (210, true), (41, false), (63, false)]
theorem step9644 (p : Nat → Bool) (h : Constraints p) : clause p c9644 = true :=
  Snake9.LocalRup.prove_clause [c8368, c3789] c9644 (by decide) p (sat_cons (step8368 p h) (sat_cons (step3789 p h) (sat_nil p)))
def c9645 : List Lit := [(44, false), (76, true), (1657, true), (99, true), (1623, true), (109, true), (387, true), (107, true), (63, true), (1629, false), (118, true), (116, false)]
theorem step9645 (p : Nat → Bool) (h : Constraints p) : clause p c9645 = true :=
  Snake9.LocalRup.prove_clause [c8365, c3556] c9645 (by decide) p (sat_cons (step8365 p h) (sat_cons (step3556 p h) (sat_nil p)))
def c9646 : List Lit := [(1655, true), (112, false), (1627, false), (1644, false), (190, true), (210, true), (100, false)]
theorem step9646 (p : Nat → Bool) (h : Constraints p) : clause p c9646 = true :=
  Snake9.LocalRup.prove_clause [c8365, c8381, c3414] c9646 (by decide) p (sat_cons (step8365 p h) (sat_cons (step8381 p h) (sat_cons (step3414 p h) (sat_nil p))))
def c9647 : List Lit := [(116, false), (193, true), (1610, false), (1623, true), (192, true), (63, true), (107, false), (109, true)]
theorem step9647 (p : Nat → Bool) (h : Constraints p) : clause p c9647 = true :=
  Snake9.LocalRup.prove_clause [c8365, c3909] c9647 (by decide) p (sat_cons (step8365 p h) (sat_cons (step3909 p h) (sat_nil p)))
def c9648 : List Lit := [(1717, false), (1706, false), (99, true), (212, true), (210, true), (41, false), (1737, true), (100, false), (1627, false)]
theorem step9648 (p : Nat → Bool) (h : Constraints p) : clause p c9648 = true :=
  Snake9.LocalRup.prove_clause [c8381, c3757] c9648 (by decide) p (sat_cons (step8381 p h) (sat_cons (step3757 p h) (sat_nil p)))
def c9649 : List Lit := [(405, false), (41, false), (1627, false), (1655, true)]
theorem step9649 (p : Nat → Bool) (h : Constraints p) : clause p c9649 = true :=
  Snake9.LocalRup.prove_clause [c8365, c4353] c9649 (by decide) p (sat_cons (step8365 p h) (sat_cons (step4353 p h) (sat_nil p)))
def c9650 : List Lit := [(1654, true), (41, false), (184, true), (190, true), (210, true)]
theorem step9650 (p : Nat → Bool) (h : Constraints p) : clause p c9650 = true :=
  Snake9.LocalRup.prove_clause [c8365, c4664] c9650 (by decide) p (sat_cons (step8365 p h) (sat_cons (step4664 p h) (sat_nil p)))
def c9651 : List Lit := [(1673, false), (1680, false), (1705, false), (99, true), (210, true), (80, true), (1716, true), (1736, true), (1627, false)]
theorem step9651 (p : Nat → Bool) (h : Constraints p) : clause p c9651 = true :=
  Snake9.LocalRup.prove_clause [c8381, c5121] c9651 (by decide) p (sat_cons (step8381 p h) (sat_cons (step5121 p h) (sat_nil p)))
def c9652 : List Lit := [(387, true), (1622, true), (100, true)]
theorem step9652 (p : Nat → Bool) (h : Constraints p) : clause p c9652 = true :=
  Snake9.LocalRup.prove_clause [c8365, c4677] c9652 (by decide) p (sat_cons (step8365 p h) (sat_cons (step4677 p h) (sat_nil p)))
def c9653 : List Lit := [(59, false), (74, false), (371, false), (1627, true), (1622, true)]
theorem step9653 (p : Nat → Bool) (h : Constraints p) : clause p c9653 = true :=
  Snake9.LocalRup.prove_clause [c8365, c4494] c9653 (by decide) p (sat_cons (step8365 p h) (sat_cons (step4494 p h) (sat_nil p)))
def c9654 : List Lit := [(1622, true), (100, true), (99, false)]
theorem step9654 (p : Nat → Bool) (h : Constraints p) : clause p c9654 = true :=
  Snake9.LocalRup.prove_clause [c8365, c4558] c9654 (by decide) p (sat_cons (step8365 p h) (sat_cons (step4558 p h) (sat_nil p)))
def c9655 : List Lit := [(46, false), (106, true), (87, false), (86, true)]
theorem step9655 (p : Nat → Bool) (h : Constraints p) : clause p c9655 = true :=
  Snake9.LocalRup.prove_clause [c8365, c4657] c9655 (by decide) p (sat_cons (step8365 p h) (sat_cons (step4657 p h) (sat_nil p)))
def c9656 : List Lit := [(74, false), (415, false), (1627, true), (1623, true), (63, true)]
theorem step9656 (p : Nat → Bool) (h : Constraints p) : clause p c9656 = true :=
  Snake9.LocalRup.prove_clause [c8365, c4277] c9656 (by decide) p (sat_cons (step8365 p h) (sat_cons (step4277 p h) (sat_nil p)))
def c9657 : List Lit := [(65, false), (72, false), (63, true), (184, true), (66, true), (1623, true)]
theorem step9657 (p : Nat → Bool) (h : Constraints p) : clause p c9657 = true :=
  Snake9.LocalRup.prove_clause [c8365, c4278] c9657 (by decide) p (sat_cons (step8365 p h) (sat_cons (step4278 p h) (sat_nil p)))
def c9658 : List Lit := [(66, true), (65, false), (1622, true), (72, false)]
theorem step9658 (p : Nat → Bool) (h : Constraints p) : clause p c9658 = true :=
  Snake9.LocalRup.prove_clause [c8365, c4495] c9658 (by decide) p (sat_cons (step8365 p h) (sat_cons (step4495 p h) (sat_nil p)))
def c9659 : List Lit := [(69, true), (64, true), (415, false), (76, false), (74, true), (1618, true)]
theorem step9659 (p : Nat → Bool) (h : Constraints p) : clause p c9659 = true :=
  Snake9.LocalRup.prove_clause [c8365, c4405] c9659 (by decide) p (sat_cons (step8365 p h) (sat_cons (step4405 p h) (sat_nil p)))
def c9660 : List Lit := [(1705, false), (1655, true), (99, true), (1736, true), (41, false), (417, true), (100, false)]
theorem step9660 (p : Nat → Bool) (h : Constraints p) : clause p c9660 = true :=
  Snake9.LocalRup.prove_clause [c8365, c4670] c9660 (by decide) p (sat_cons (step8365 p h) (sat_cons (step4670 p h) (sat_nil p)))
def c9661 : List Lit := [(210, true), (63, true), (80, true), (190, true), (1688, true), (1655, true)]
theorem step9661 (p : Nat → Bool) (h : Constraints p) : clause p c9661 = true :=
  Snake9.LocalRup.prove_clause [c8381, c4969] c9661 (by decide) p (sat_cons (step8381 p h) (sat_cons (step4969 p h) (sat_nil p)))
def c9662 : List Lit := [(210, true), (1736, true), (1627, false), (1705, false), (99, true), (1674, false)]
theorem step9662 (p : Nat → Bool) (h : Constraints p) : clause p c9662 = true :=
  Snake9.LocalRup.prove_clause [c8381, c5125] c9662 (by decide) p (sat_cons (step8381 p h) (sat_cons (step5125 p h) (sat_nil p)))
def c9663 : List Lit := [(371, false), (1627, true), (118, false), (1622, true)]
theorem step9663 (p : Nat → Bool) (h : Constraints p) : clause p c9663 = true :=
  Snake9.LocalRup.prove_clause [c8365, c4493] c9663 (by decide) p (sat_cons (step8365 p h) (sat_cons (step4493 p h) (sat_nil p)))
def c9664 : List Lit := [(1713, true), (475, false)]
theorem step9664 (p : Nat → Bool) (h : Constraints p) : clause p c9664 = true :=
  Snake9.LocalRup.prove_clause [c8365, c5226] c9664 (by decide) p (sat_cons (step8365 p h) (sat_cons (step5226 p h) (sat_nil p)))
def c9665 : List Lit := [(58, false), (46, false), (87, false), (1640, true), (106, true)]
theorem step9665 (p : Nat → Bool) (h : Constraints p) : clause p c9665 = true :=
  Snake9.LocalRup.prove_clause [c8365, c5287] c9665 (by decide) p (sat_cons (step8365 p h) (sat_cons (step5287 p h) (sat_nil p)))
def c9666 : List Lit := [(112, false), (80, false), (190, true), (212, true), (1705, false), (1736, true), (1643, false), (100, false)]
theorem step9666 (p : Nat → Bool) (h : Constraints p) : clause p c9666 = true :=
  Snake9.LocalRup.prove_clause [c8365, c4693] c9666 (by decide) p (sat_cons (step8365 p h) (sat_cons (step4693 p h) (sat_nil p)))
def c9667 : List Lit := [(80, true), (1627, false), (109, true), (1737, true), (1674, false), (99, true), (1705, false)]
theorem step9667 (p : Nat → Bool) (h : Constraints p) : clause p c9667 = true :=
  Snake9.LocalRup.prove_clause [c8381, c5045] c9667 (by decide) p (sat_cons (step8381 p h) (sat_cons (step5045 p h) (sat_nil p)))
def c9668 : List Lit := [(415, false), (63, true), (109, true), (1645, true), (80, true), (1656, true), (118, false)]
theorem step9668 (p : Nat → Bool) (h : Constraints p) : clause p c9668 = true :=
  Snake9.LocalRup.prove_clause [c8365, c5474] c9668 (by decide) p (sat_cons (step8365 p h) (sat_cons (step5474 p h) (sat_nil p)))
def c9669 : List Lit := [(87, true), (415, true), (1736, true), (1627, false), (99, true), (1705, false), (100, true)]
theorem step9669 (p : Nat → Bool) (h : Constraints p) : clause p c9669 = true :=
  Snake9.LocalRup.prove_clause [c8381, c6251] c9669 (by decide) p (sat_cons (step8381 p h) (sat_cons (step6251 p h) (sat_nil p)))
def c9670 : List Lit := [(1654, true), (83, false), (1705, false), (1677, false), (113, false), (213, true), (1736, true), (80, false), (1627, false)]
theorem step9670 (p : Nat → Bool) (h : Constraints p) : clause p c9670 = true :=
  Snake9.LocalRup.prove_clause [c8381, c7162] c9670 (by decide) p (sat_cons (step8381 p h) (sat_cons (step7162 p h) (sat_nil p)))
def c9671 : List Lit := [(41, false), (473, true), (1490, true), (1736, true), (99, false), (1680, false), (299, true), (357, true), (192, true), (196, true), (76, false), (415, true), (63, false), (109, true), (107, false)]
theorem step9671 (p : Nat → Bool) (h : Constraints p) : clause p c9671 = true :=
  Snake9.LocalRup.prove_clause [c8365, c5756] c9671 (by decide) p (sat_cons (step8365 p h) (sat_cons (step5756 p h) (sat_nil p)))
def c9672 : List Lit := [(184, true), (1622, true), (63, false), (118, false), (99, true), (76, false), (109, true), (107, false)]
theorem step9672 (p : Nat → Bool) (h : Constraints p) : clause p c9672 = true :=
  Snake9.LocalRup.prove_clause [c8365, c5797] c9672 (by decide) p (sat_cons (step8365 p h) (sat_cons (step5797 p h) (sat_nil p)))
def c9673 : List Lit := [(1609, false), (107, false), (377, true), (109, true), (1622, true)]
theorem step9673 (p : Nat → Bool) (h : Constraints p) : clause p c9673 = true :=
  Snake9.LocalRup.prove_clause [c8365, c5714] c9673 (by decide) p (sat_cons (step8365 p h) (sat_cons (step5714 p h) (sat_nil p)))
def c9674 : List Lit := [(78, true), (63, true), (1622, true)]
theorem step9674 (p : Nat → Bool) (h : Constraints p) : clause p c9674 = true :=
  Snake9.LocalRup.prove_clause [c8365, c5455] c9674 (by decide) p (sat_cons (step8365 p h) (sat_cons (step5455 p h) (sat_nil p)))
def c9675 : List Lit := [(48, false), (210, false), (1645, true), (63, true), (112, true), (76, false), (80, true), (1656, true), (1706, true), (118, false)]
theorem step9675 (p : Nat → Bool) (h : Constraints p) : clause p c9675 = true :=
  Snake9.LocalRup.prove_clause [c8365, c5475] c9675 (by decide) p (sat_cons (step8365 p h) (sat_cons (step5475 p h) (sat_nil p)))
def c9676 : List Lit := [(62, true), (72, false), (1623, true), (109, true), (387, true), (66, true), (63, true)]
theorem step9676 (p : Nat → Bool) (h : Constraints p) : clause p c9676 = true :=
  Snake9.LocalRup.prove_clause [c8365, c5478] c9676 (by decide) p (sat_cons (step8365 p h) (sat_cons (step5478 p h) (sat_nil p)))
def c9677 : List Lit := [(1705, true), (63, true), (118, false), (385, true), (76, false), (1688, false), (1623, true)]
theorem step9677 (p : Nat → Bool) (h : Constraints p) : clause p c9677 = true :=
  Snake9.LocalRup.prove_clause [c8365, c5481] c9677 (by decide) p (sat_cons (step8365 p h) (sat_cons (step5481 p h) (sat_nil p)))
end B112E019
