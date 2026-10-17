import B112E027Inputs
namespace B112E027
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1450 : List Lit := [(61, true)]
theorem step1450 (p : Nat → Bool) (h : Constraints p) : clause p c1450 = true :=
  Snake9.LocalRup.prove_clause [c284, c283] c1450 (by decide) p (sat_cons (step284 p h) (sat_cons (step283 p h) (sat_nil p)))
def c1451 : List Lit := [(466, false)]
theorem step1451 (p : Nat → Bool) (h : Constraints p) : clause p c1451 = true :=
  Snake9.LocalRup.prove_clause [c924, c921] c1451 (by decide) p (sat_cons (step924 p h) (sat_cons (step921 p h) (sat_nil p)))
def c1452 : List Lit := [(350, false)]
theorem step1452 (p : Nat → Bool) (h : Constraints p) : clause p c1452 = true :=
  Snake9.LocalRup.prove_clause [c924, c923] c1452 (by decide) p (sat_cons (step924 p h) (sat_cons (step923 p h) (sat_nil p)))
def c1453 : List Lit := [(464, false)]
theorem step1453 (p : Nat → Bool) (h : Constraints p) : clause p c1453 = true :=
  Snake9.LocalRup.prove_clause [c1451, c917] c1453 (by decide) p (sat_cons (step1451 p h) (sat_cons (step917 p h) (sat_nil p)))
def c1454 : List Lit := [(406, false)]
theorem step1454 (p : Nat → Bool) (h : Constraints p) : clause p c1454 = true :=
  Snake9.LocalRup.prove_clause [c1451, c920] c1454 (by decide) p (sat_cons (step1451 p h) (sat_cons (step920 p h) (sat_nil p)))
def c1455 : List Lit := [(348, false)]
theorem step1455 (p : Nat → Bool) (h : Constraints p) : clause p c1455 = true :=
  Snake9.LocalRup.prove_clause [c1452, c794] c1455 (by decide) p (sat_cons (step1452 p h) (sat_cons (step794 p h) (sat_nil p)))
def c1456 : List Lit := [(292, false)]
theorem step1456 (p : Nat → Bool) (h : Constraints p) : clause p c1456 = true :=
  Snake9.LocalRup.prove_clause [c1452, c797] c1456 (by decide) p (sat_cons (step1452 p h) (sat_cons (step797 p h) (sat_nil p)))
def c1457 : List Lit := [(462, false)]
theorem step1457 (p : Nat → Bool) (h : Constraints p) : clause p c1457 = true :=
  Snake9.LocalRup.prove_clause [c1453, c912] c1457 (by decide) p (sat_cons (step1453 p h) (sat_cons (step912 p h) (sat_nil p)))
def c1458 : List Lit := [(434, false)]
theorem step1458 (p : Nat → Bool) (h : Constraints p) : clause p c1458 = true :=
  Snake9.LocalRup.prove_clause [c1453, c915] c1458 (by decide) p (sat_cons (step1453 p h) (sat_cons (step915 p h) (sat_nil p)))
def c1459 : List Lit := [(404, false)]
theorem step1459 (p : Nat → Bool) (h : Constraints p) : clause p c1459 = true :=
  Snake9.LocalRup.prove_clause [c1454, c849] c1459 (by decide) p (sat_cons (step1454 p h) (sat_cons (step849 p h) (sat_nil p)))
def c1460 : List Lit := [(376, false)]
theorem step1460 (p : Nat → Bool) (h : Constraints p) : clause p c1460 = true :=
  Snake9.LocalRup.prove_clause [c1454, c852] c1460 (by decide) p (sat_cons (step1454 p h) (sat_cons (step852 p h) (sat_nil p)))
def c1461 : List Lit := [(346, false)]
theorem step1461 (p : Nat → Bool) (h : Constraints p) : clause p c1461 = true :=
  Snake9.LocalRup.prove_clause [c1455, c789] c1461 (by decide) p (sat_cons (step1455 p h) (sat_cons (step789 p h) (sat_nil p)))
def c1462 : List Lit := [(318, false)]
theorem step1462 (p : Nat → Bool) (h : Constraints p) : clause p c1462 = true :=
  Snake9.LocalRup.prove_clause [c1455, c792] c1462 (by decide) p (sat_cons (step1455 p h) (sat_cons (step792 p h) (sat_nil p)))
def c1463 : List Lit := [(290, false)]
theorem step1463 (p : Nat → Bool) (h : Constraints p) : clause p c1463 = true :=
  Snake9.LocalRup.prove_clause [c1456, c730] c1463 (by decide) p (sat_cons (step1456 p h) (sat_cons (step730 p h) (sat_nil p)))
def c1464 : List Lit := [(262, false)]
theorem step1464 (p : Nat → Bool) (h : Constraints p) : clause p c1464 = true :=
  Snake9.LocalRup.prove_clause [c1456, c733] c1464 (by decide) p (sat_cons (step1456 p h) (sat_cons (step733 p h) (sat_nil p)))
def c1465 : List Lit := [(460, false)]
theorem step1465 (p : Nat → Bool) (h : Constraints p) : clause p c1465 = true :=
  Snake9.LocalRup.prove_clause [c1457, c907] c1465 (by decide) p (sat_cons (step1457 p h) (sat_cons (step907 p h) (sat_nil p)))
def c1466 : List Lit := [(446, false)]
theorem step1466 (p : Nat → Bool) (h : Constraints p) : clause p c1466 = true :=
  Snake9.LocalRup.prove_clause [c1457, c910] c1466 (by decide) p (sat_cons (step1457 p h) (sat_cons (step910 p h) (sat_nil p)))
def c1467 : List Lit := [(432, false)]
theorem step1467 (p : Nat → Bool) (h : Constraints p) : clause p c1467 = true :=
  Snake9.LocalRup.prove_clause [c1458, c878] c1467 (by decide) p (sat_cons (step1458 p h) (sat_cons (step878 p h) (sat_nil p)))
def c1468 : List Lit := [(418, false)]
theorem step1468 (p : Nat → Bool) (h : Constraints p) : clause p c1468 = true :=
  Snake9.LocalRup.prove_clause [c1458, c881] c1468 (by decide) p (sat_cons (step1458 p h) (sat_cons (step881 p h) (sat_nil p)))
def c1469 : List Lit := [(402, false)]
theorem step1469 (p : Nat → Bool) (h : Constraints p) : clause p c1469 = true :=
  Snake9.LocalRup.prove_clause [c1459, c844] c1469 (by decide) p (sat_cons (step1459 p h) (sat_cons (step844 p h) (sat_nil p)))
def c1470 : List Lit := [(388, false)]
theorem step1470 (p : Nat → Bool) (h : Constraints p) : clause p c1470 = true :=
  Snake9.LocalRup.prove_clause [c1459, c847] c1470 (by decide) p (sat_cons (step1459 p h) (sat_cons (step847 p h) (sat_nil p)))
def c1471 : List Lit := [(374, false)]
theorem step1471 (p : Nat → Bool) (h : Constraints p) : clause p c1471 = true :=
  Snake9.LocalRup.prove_clause [c1460, c817] c1471 (by decide) p (sat_cons (step1460 p h) (sat_cons (step817 p h) (sat_nil p)))
def c1472 : List Lit := [(362, false)]
theorem step1472 (p : Nat → Bool) (h : Constraints p) : clause p c1472 = true :=
  Snake9.LocalRup.prove_clause [c1460, c820] c1472 (by decide) p (sat_cons (step1460 p h) (sat_cons (step820 p h) (sat_nil p)))
def c1473 : List Lit := [(344, false)]
theorem step1473 (p : Nat → Bool) (h : Constraints p) : clause p c1473 = true :=
  Snake9.LocalRup.prove_clause [c1461, c784] c1473 (by decide) p (sat_cons (step1461 p h) (sat_cons (step784 p h) (sat_nil p)))
def c1474 : List Lit := [(330, false)]
theorem step1474 (p : Nat → Bool) (h : Constraints p) : clause p c1474 = true :=
  Snake9.LocalRup.prove_clause [c1461, c787] c1474 (by decide) p (sat_cons (step1461 p h) (sat_cons (step787 p h) (sat_nil p)))
def c1475 : List Lit := [(316, false)]
theorem step1475 (p : Nat → Bool) (h : Constraints p) : clause p c1475 = true :=
  Snake9.LocalRup.prove_clause [c1462, c749] c1475 (by decide) p (sat_cons (step1462 p h) (sat_cons (step749 p h) (sat_nil p)))
def c1476 : List Lit := [(288, false)]
theorem step1476 (p : Nat → Bool) (h : Constraints p) : clause p c1476 = true :=
  Snake9.LocalRup.prove_clause [c1463, c725] c1476 (by decide) p (sat_cons (step1463 p h) (sat_cons (step725 p h) (sat_nil p)))
def c1477 : List Lit := [(274, false)]
theorem step1477 (p : Nat → Bool) (h : Constraints p) : clause p c1477 = true :=
  Snake9.LocalRup.prove_clause [c1463, c728] c1477 (by decide) p (sat_cons (step1463 p h) (sat_cons (step728 p h) (sat_nil p)))
def c1478 : List Lit := [(260, false)]
theorem step1478 (p : Nat → Bool) (h : Constraints p) : clause p c1478 = true :=
  Snake9.LocalRup.prove_clause [c1464, c698] c1478 (by decide) p (sat_cons (step1464 p h) (sat_cons (step698 p h) (sat_nil p)))
def c1479 : List Lit := [(248, false)]
theorem step1479 (p : Nat → Bool) (h : Constraints p) : clause p c1479 = true :=
  Snake9.LocalRup.prove_clause [c1464, c701] c1479 (by decide) p (sat_cons (step1464 p h) (sat_cons (step701 p h) (sat_nil p)))
def c1480 : List Lit := [(458, false)]
theorem step1480 (p : Nat → Bool) (h : Constraints p) : clause p c1480 = true :=
  Snake9.LocalRup.prove_clause [c1465, c902] c1480 (by decide) p (sat_cons (step1465 p h) (sat_cons (step902 p h) (sat_nil p)))
def c1481 : List Lit := [(452, false)]
theorem step1481 (p : Nat → Bool) (h : Constraints p) : clause p c1481 = true :=
  Snake9.LocalRup.prove_clause [c1465, c905] c1481 (by decide) p (sat_cons (step1465 p h) (sat_cons (step905 p h) (sat_nil p)))
def c1482 : List Lit := [(424, false)]
theorem step1482 (p : Nat → Bool) (h : Constraints p) : clause p c1482 = true :=
  Snake9.LocalRup.prove_clause [c1467, c876] c1482 (by decide) p (sat_cons (step1467 p h) (sat_cons (step876 p h) (sat_nil p)))
def c1483 : List Lit := [(394, false)]
theorem step1483 (p : Nat → Bool) (h : Constraints p) : clause p c1483 = true :=
  Snake9.LocalRup.prove_clause [c1469, c842] c1483 (by decide) p (sat_cons (step1469 p h) (sat_cons (step842 p h) (sat_nil p)))
def c1484 : List Lit := [(380, false)]
theorem step1484 (p : Nat → Bool) (h : Constraints p) : clause p c1484 = true :=
  Snake9.LocalRup.prove_clause [c1470, c831] c1484 (by decide) p (sat_cons (step1470 p h) (sat_cons (step831 p h) (sat_nil p)))
def c1485 : List Lit := [(366, false)]
theorem step1485 (p : Nat → Bool) (h : Constraints p) : clause p c1485 = true :=
  Snake9.LocalRup.prove_clause [c1471, c815] c1485 (by decide) p (sat_cons (step1471 p h) (sat_cons (step815 p h) (sat_nil p)))
def c1486 : List Lit := [(354, false)]
theorem step1486 (p : Nat → Bool) (h : Constraints p) : clause p c1486 = true :=
  Snake9.LocalRup.prove_clause [c1472, c806] c1486 (by decide) p (sat_cons (step1472 p h) (sat_cons (step806 p h) (sat_nil p)))
def c1487 : List Lit := [(342, false)]
theorem step1487 (p : Nat → Bool) (h : Constraints p) : clause p c1487 = true :=
  Snake9.LocalRup.prove_clause [c1473, c779] c1487 (by decide) p (sat_cons (step1473 p h) (sat_cons (step779 p h) (sat_nil p)))
def c1488 : List Lit := [(336, false)]
theorem step1488 (p : Nat → Bool) (h : Constraints p) : clause p c1488 = true :=
  Snake9.LocalRup.prove_clause [c1473, c782] c1488 (by decide) p (sat_cons (step1473 p h) (sat_cons (step782 p h) (sat_nil p)))
def c1489 : List Lit := [(328, false)]
theorem step1489 (p : Nat → Bool) (h : Constraints p) : clause p c1489 = true :=
  Snake9.LocalRup.prove_clause [c1474, c763] c1489 (by decide) p (sat_cons (step1474 p h) (sat_cons (step763 p h) (sat_nil p)))
def c1490 : List Lit := [(322, false)]
theorem step1490 (p : Nat → Bool) (h : Constraints p) : clause p c1490 = true :=
  Snake9.LocalRup.prove_clause [c1474, c766] c1490 (by decide) p (sat_cons (step1474 p h) (sat_cons (step766 p h) (sat_nil p)))
def c1491 : List Lit := [(280, false)]
theorem step1491 (p : Nat → Bool) (h : Constraints p) : clause p c1491 = true :=
  Snake9.LocalRup.prove_clause [c1476, c723] c1491 (by decide) p (sat_cons (step1476 p h) (sat_cons (step723 p h) (sat_nil p)))
def c1492 : List Lit := [(240, false)]
theorem step1492 (p : Nat → Bool) (h : Constraints p) : clause p c1492 = true :=
  Snake9.LocalRup.prove_clause [c1479, c688] c1492 (by decide) p (sat_cons (step1479 p h) (sat_cons (step688 p h) (sat_nil p)))
def c1493 : List Lit := [(420, false)]
theorem step1493 (p : Nat → Bool) (h : Constraints p) : clause p c1493 = true :=
  Snake9.LocalRup.prove_clause [c1482, c870] c1493 (by decide) p (sat_cons (step1482 p h) (sat_cons (step870 p h) (sat_nil p)))
def c1494 : List Lit := [(390, false)]
theorem step1494 (p : Nat → Bool) (h : Constraints p) : clause p c1494 = true :=
  Snake9.LocalRup.prove_clause [c1483, c836] c1494 (by decide) p (sat_cons (step1483 p h) (sat_cons (step836 p h) (sat_nil p)))
def c1495 : List Lit := [(324, false)]
theorem step1495 (p : Nat → Bool) (h : Constraints p) : clause p c1495 = true :=
  Snake9.LocalRup.prove_clause [c1489, c761] c1495 (by decide) p (sat_cons (step1489 p h) (sat_cons (step761 p h) (sat_nil p)))
def c1496 : List Lit := [(320, false)]
theorem step1496 (p : Nat → Bool) (h : Constraints p) : clause p c1496 = true :=
  Snake9.LocalRup.prove_clause [c1490, c756] c1496 (by decide) p (sat_cons (step1490 p h) (sat_cons (step756 p h) (sat_nil p)))
def c1497 : List Lit := [(238, false)]
theorem step1497 (p : Nat → Bool) (h : Constraints p) : clause p c1497 = true :=
  Snake9.LocalRup.prove_clause [c1492, c682] c1497 (by decide) p (sat_cons (step1492 p h) (sat_cons (step682 p h) (sat_nil p)))
def c1498 : List Lit := [(120, true), (121, true), (125, true), (126, true), (129, true), (131, true), (133, true), (135, true), (137, true), (140, true), (141, true), (142, true), (145, true), (147, true), (150, true), (153, true), (156, true), (157, true), (159, true), (163, true), (164, true), (165, true), (166, true), (170, true), (172, true), (173, true), (174, true), (175, true), (177, true), (179, true), (182, true), (185, true), (186, true), (188, true), (192, true), (193, true), (194, true), (195, true), (199, true), (200, true), (203, true), (207, true), (208, true), (210, true), (213, true), (214, true), (215, true), (216, true), (220, true), (222, true), (223, true), (224, true), (226, true), (229, true), (232, true), (233, true), (235, true)]
theorem step1498 (p : Nat → Bool) (h : Constraints p) : clause p c1498 = true :=
  Snake9.TreeRup.prove_clause [c618, c619, c620, c621, c622, c623, c624, c625, c626, c627, c628, c629, c630, c631, c632, c633, c634, c635, c636, c637, c638, c639, c640, c641, c642, c643, c644, c645, c646, c647, c648, c649, c650, c651, c652, c653, c654, c655, c656, c657, c658, c659, c660, c661, c662, c663, c664, c665, c666, c667, c668, c669, c670, c671, c672, c673, c674, c675, c676, c677, c925] c1498 (by decide) p (sat_cons (step618 p h) (sat_cons (step619 p h) (sat_cons (step620 p h) (sat_cons (step621 p h) (sat_cons (step622 p h) (sat_cons (step623 p h) (sat_cons (step624 p h) (sat_cons (step625 p h) (sat_cons (step626 p h) (sat_cons (step627 p h) (sat_cons (step628 p h) (sat_cons (step629 p h) (sat_cons (step630 p h) (sat_cons (step631 p h) (sat_cons (step632 p h) (sat_cons (step633 p h) (sat_cons (step634 p h) (sat_cons (step635 p h) (sat_cons (step636 p h) (sat_cons (step637 p h) (sat_cons (step638 p h) (sat_cons (step639 p h) (sat_cons (step640 p h) (sat_cons (step641 p h) (sat_cons (step642 p h) (sat_cons (step643 p h) (sat_cons (step644 p h) (sat_cons (step645 p h) (sat_cons (step646 p h) (sat_cons (step647 p h) (sat_cons (step648 p h) (sat_cons (step649 p h) (sat_cons (step650 p h) (sat_cons (step651 p h) (sat_cons (step652 p h) (sat_cons (step653 p h) (sat_cons (step654 p h) (sat_cons (step655 p h) (sat_cons (step656 p h) (sat_cons (step657 p h) (sat_cons (step658 p h) (sat_cons (step659 p h) (sat_cons (step660 p h) (sat_cons (step661 p h) (sat_cons (step662 p h) (sat_cons (step663 p h) (sat_cons (step664 p h) (sat_cons (step665 p h) (sat_cons (step666 p h) (sat_cons (step667 p h) (sat_cons (step668 p h) (sat_cons (step669 p h) (sat_cons (step670 p h) (sat_cons (step671 p h) (sat_cons (step672 p h) (sat_cons (step673 p h) (sat_cons (step674 p h) (sat_cons (step675 p h) (sat_cons (step676 p h) (sat_cons (step677 p h) (sat_cons (step925 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1499 : List Lit := [(1602, true)]
theorem step1499 (p : Nat → Bool) (h : Constraints p) : clause p c1499 = true :=
  Snake9.LocalRup.prove_clause [c1221, c1228, c1206, c1170, c1184, c1186, c1163, c1181, c1182, c337, c1160, c330, c323] c1499 (by decide) p (sat_cons (step1221 p h) (sat_cons (step1228 p h) (sat_cons (step1206 p h) (sat_cons (step1170 p h) (sat_cons (step1184 p h) (sat_cons (step1186 p h) (sat_cons (step1163 p h) (sat_cons (step1181 p h) (sat_cons (step1182 p h) (sat_cons (step337 p h) (sat_cons (step1160 p h) (sat_cons (step330 p h) (sat_cons (step323 p h) (sat_nil p))))))))))))))
def c1500 : List Lit := [(75, false), (77, false), (76, false)]
theorem step1500 (p : Nat → Bool) (h : Constraints p) : clause p c1500 = true :=
  Snake9.LocalRup.prove_clause [c1470, c337, c333, c331, c826, c821, c827, c823, c830] c1500 (by decide) p (sat_cons (step1470 p h) (sat_cons (step337 p h) (sat_cons (step333 p h) (sat_cons (step331 p h) (sat_cons (step826 p h) (sat_cons (step821 p h) (sat_cons (step827 p h) (sat_cons (step823 p h) (sat_cons (step830 p h) (sat_nil p))))))))))
def c1501 : List Lit := [(1584, true)]
theorem step1501 (p : Nat → Bool) (h : Constraints p) : clause p c1501 = true :=
  Snake9.LocalRup.prove_clause [c1184, c1186, c1181, c1182, c1500] c1501 (by decide) p (sat_cons (step1184 p h) (sat_cons (step1186 p h) (sat_cons (step1181 p h) (sat_cons (step1182 p h) (sat_cons (step1500 p h) (sat_nil p))))))
def c1502 : List Lit := [(1595, true)]
theorem step1502 (p : Nat → Bool) (h : Constraints p) : clause p c1502 = true :=
  Snake9.LocalRup.prove_clause [c1501, c1206] c1502 (by decide) p (sat_cons (step1501 p h) (sat_cons (step1206 p h) (sat_nil p)))
def c1503 : List Lit := [(177, true), (59, false), (1521, true)]
theorem step1503 (p : Nat → Bool) (h : Constraints p) : clause p c1503 = true :=
  Snake9.LocalRup.prove_clause [c1450, c1075, c278, c279, c280, c1065, c1066, c1073, c236, c1067] c1503 (by decide) p (sat_cons (step1450 p h) (sat_cons (step1075 p h) (sat_cons (step278 p h) (sat_cons (step279 p h) (sat_cons (step280 p h) (sat_cons (step1065 p h) (sat_cons (step1066 p h) (sat_cons (step1073 p h) (sat_cons (step236 p h) (sat_cons (step1067 p h) (sat_nil p)))))))))))
def c1504 : List Lit := [(59, false), (1521, true)]
theorem step1504 (p : Nat → Bool) (h : Constraints p) : clause p c1504 = true :=
  Snake9.LocalRup.prove_clause [c1486, c1450, c924, c1075, c1503, c800, c801, c805, c798, c818, c282, c850, c280, c277, c918, c1065, c1066, c922, c1073, c793, c1067, c1068, c788, c269, c783, c268, c778, c774, c775] c1504 (by decide) p (sat_cons (step1486 p h) (sat_cons (step1450 p h) (sat_cons (step924 p h) (sat_cons (step1075 p h) (sat_cons (step1503 p h) (sat_cons (step800 p h) (sat_cons (step801 p h) (sat_cons (step805 p h) (sat_cons (step798 p h) (sat_cons (step818 p h) (sat_cons (step282 p h) (sat_cons (step850 p h) (sat_cons (step280 p h) (sat_cons (step277 p h) (sat_cons (step918 p h) (sat_cons (step1065 p h) (sat_cons (step1066 p h) (sat_cons (step922 p h) (sat_cons (step1073 p h) (sat_cons (step793 p h) (sat_cons (step1067 p h) (sat_cons (step1068 p h) (sat_cons (step788 p h) (sat_cons (step269 p h) (sat_cons (step783 p h) (sat_cons (step268 p h) (sat_cons (step778 p h) (sat_cons (step774 p h) (sat_cons (step775 p h) (sat_nil p))))))))))))))))))))))))))))))
def c1505 : List Lit := [(1462, true), (1684, true), (85, true), (1575, false), (1587, false), (87, false), (88, false), (57, false), (56, false)]
theorem step1505 (p : Nat → Bool) (h : Constraints p) : clause p c1505 = true :=
  Snake9.LocalRup.prove_clause [c1501, c972, c973, c455, c456, c457, c458, c436, c437, c1194, c1259, c1266, c1262, c1299, c1199, c1271, c1301, c1209, c1282, c1324, c1232, c1343, c1384] c1505 (by decide) p (sat_cons (step1501 p h) (sat_cons (step972 p h) (sat_cons (step973 p h) (sat_cons (step455 p h) (sat_cons (step456 p h) (sat_cons (step457 p h) (sat_cons (step458 p h) (sat_cons (step436 p h) (sat_cons (step437 p h) (sat_cons (step1194 p h) (sat_cons (step1259 p h) (sat_cons (step1266 p h) (sat_cons (step1262 p h) (sat_cons (step1299 p h) (sat_cons (step1199 p h) (sat_cons (step1271 p h) (sat_cons (step1301 p h) (sat_cons (step1209 p h) (sat_cons (step1282 p h) (sat_cons (step1324 p h) (sat_cons (step1232 p h) (sat_cons (step1343 p h) (sat_cons (step1384 p h) (sat_nil p))))))))))))))))))))))))
def c1506 : List Lit := [(1638, false), (107, true), (235, true), (1653, true)]
theorem step1506 (p : Nat → Bool) (h : Constraints p) : clause p c1506 = true :=
  Snake9.LocalRup.prove_clause [c1324, c1300, c1303, c1322, c1294, c1314, c1311, c1312, c616, c610] c1506 (by decide) p (sat_cons (step1324 p h) (sat_cons (step1300 p h) (sat_cons (step1303 p h) (sat_cons (step1322 p h) (sat_cons (step1294 p h) (sat_cons (step1314 p h) (sat_cons (step1311 p h) (sat_cons (step1312 p h) (sat_cons (step616 p h) (sat_cons (step610 p h) (sat_nil p)))))))))))
def c1507 : List Lit := [(1652, true), (235, true), (107, true)]
theorem step1507 (p : Nat → Bool) (h : Constraints p) : clause p c1507 = true :=
  Snake9.LocalRup.prove_clause [c1319, c1321, c1314, c1302, c1311, c1312, c1294, c616, c610] c1507 (by decide) p (sat_cons (step1319 p h) (sat_cons (step1321 p h) (sat_cons (step1314 p h) (sat_cons (step1302 p h) (sat_cons (step1311 p h) (sat_cons (step1312 p h) (sat_cons (step1294 p h) (sat_cons (step616 p h) (sat_cons (step610 p h) (sat_nil p))))))))))
def c1508 : List Lit := [(1646, true), (105, false), (235, true), (107, true)]
theorem step1508 (p : Nat → Bool) (h : Constraints p) : clause p c1508 = true :=
  Snake9.LocalRup.prove_clause [c1311, c1312, c616, c610] c1508 (by decide) p (sat_cons (step1311 p h) (sat_cons (step1312 p h) (sat_cons (step616 p h) (sat_cons (step610 p h) (sat_nil p)))))
def c1509 : List Lit := [(1636, true), (235, true), (113, true), (1649, true), (108, false), (107, true)]
theorem step1509 (p : Nat → Bool) (h : Constraints p) : clause p c1509 = true :=
  Snake9.LocalRup.prove_clause [c1481, c1294, c1295, c1508, c1317, c1308, c1309, c560, c597, c595, c605, c891, c892, c895] c1509 (by decide) p (sat_cons (step1481 p h) (sat_cons (step1294 p h) (sat_cons (step1295 p h) (sat_cons (step1508 p h) (sat_cons (step1317 p h) (sat_cons (step1308 p h) (sat_cons (step1309 p h) (sat_cons (step560 p h) (sat_cons (step597 p h) (sat_cons (step595 p h) (sat_cons (step605 p h) (sat_cons (step891 p h) (sat_cons (step892 p h) (sat_cons (step895 p h) (sat_nil p)))))))))))))))
def c1510 : List Lit := [(235, true), (113, true), (1653, true), (108, false), (107, true)]
theorem step1510 (p : Nat → Bool) (h : Constraints p) : clause p c1510 = true :=
  Snake9.LocalRup.prove_clause [c1481, c1324, c1305, c1320, c1509, c1302, c1322, c1314, c1316, c1508, c1308, c1309, c1296, c560, c597, c595, c605, c891, c892, c895] c1510 (by decide) p (sat_cons (step1481 p h) (sat_cons (step1324 p h) (sat_cons (step1305 p h) (sat_cons (step1320 p h) (sat_cons (step1509 p h) (sat_cons (step1302 p h) (sat_cons (step1322 p h) (sat_cons (step1314 p h) (sat_cons (step1316 p h) (sat_cons (step1508 p h) (sat_cons (step1308 p h) (sat_cons (step1309 p h) (sat_cons (step1296 p h) (sat_cons (step560 p h) (sat_cons (step597 p h) (sat_cons (step595 p h) (sat_cons (step605 p h) (sat_cons (step891 p h) (sat_cons (step892 p h) (sat_cons (step895 p h) (sat_nil p)))))))))))))))))))))
def c1511 : List Lit := [(1513, true), (46, false), (50, false)]
theorem step1511 (p : Nat → Bool) (h : Constraints p) : clause p c1511 = true :=
  Snake9.LocalRup.prove_clause [c1059, c1061, c1057, c214] c1511 (by decide) p (sat_cons (step1059 p h) (sat_cons (step1061 p h) (sat_cons (step1057 p h) (sat_cons (step214 p h) (sat_nil p)))))
def c1512 : List Lit := [(1459, true), (20, false), (38, false)]
theorem step1512 (p : Nat → Bool) (h : Constraints p) : clause p c1512 = true :=
  Snake9.LocalRup.prove_clause [c967, c969, c965, c103] c1512 (by decide) p (sat_cons (step967 p h) (sat_cons (step969 p h) (sat_cons (step965 p h) (sat_cons (step103 p h) (sat_nil p)))))
def c1513 : List Lit := [(1450, true)]
theorem step1513 (p : Nat → Bool) (h : Constraints p) : clause p c1513 = true :=
  Snake9.LocalRup.prove_clause [c948, c952, c942, c929, c934, c935, c926, c927, c21, c31, c39] c1513 (by decide) p (sat_cons (step948 p h) (sat_cons (step952 p h) (sat_cons (step942 p h) (sat_cons (step929 p h) (sat_cons (step934 p h) (sat_cons (step935 p h) (sat_cons (step926 p h) (sat_cons (step927 p h) (sat_cons (step21 p h) (sat_cons (step31 p h) (sat_cons (step39 p h) (sat_nil p))))))))))))
end B112E027
