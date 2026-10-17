import B112E064Inputs
namespace B112E064
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1419 : List Lit := [(98, true)]
theorem step1419 (p : Nat → Bool) (h : Constraints p) : clause p c1419 = true :=
  Snake9.LocalRup.prove_clause [c564, c563] c1419 (by decide) p (sat_cons (step564 p h) (sat_cons (step563 p h) (sat_nil p)))
def c1420 : List Lit := [(215, true), (91, true)]
theorem step1420 (p : Nat → Bool) (h : Constraints p) : clause p c1420 = true :=
  Snake9.LocalRup.prove_clause [c1419, c565] c1420 (by decide) p (sat_cons (step1419 p h) (sat_cons (step565 p h) (sat_nil p)))
def c1421 : List Lit := [(24, false)]
theorem step1421 (p : Nat → Bool) (h : Constraints p) : clause p c1421 = true :=
  Snake9.LocalRup.prove_clause [c652, c95] c1421 (by decide) p (sat_cons (step652 p h) (sat_cons (step95 p h) (sat_nil p)))
def c1422 : List Lit := [(26, false)]
theorem step1422 (p : Nat → Bool) (h : Constraints p) : clause p c1422 = true :=
  Snake9.LocalRup.prove_clause [c654, c98] c1422 (by decide) p (sat_cons (step654 p h) (sat_cons (step98 p h) (sat_nil p)))
def c1423 : List Lit := [(27, false)]
theorem step1423 (p : Nat → Bool) (h : Constraints p) : clause p c1423 = true :=
  Snake9.LocalRup.prove_clause [c655, c99] c1423 (by decide) p (sat_cons (step655 p h) (sat_cons (step99 p h) (sat_nil p)))
def c1424 : List Lit := [(462, false)]
theorem step1424 (p : Nat → Bool) (h : Constraints p) : clause p c1424 = true :=
  Snake9.LocalRup.prove_clause [c906, c903] c1424 (by decide) p (sat_cons (step906 p h) (sat_cons (step903 p h) (sat_nil p)))
def c1425 : List Lit := [(348, false)]
theorem step1425 (p : Nat → Bool) (h : Constraints p) : clause p c1425 = true :=
  Snake9.LocalRup.prove_clause [c906, c905] c1425 (by decide) p (sat_cons (step906 p h) (sat_cons (step905 p h) (sat_nil p)))
def c1426 : List Lit := [(460, false)]
theorem step1426 (p : Nat → Bool) (h : Constraints p) : clause p c1426 = true :=
  Snake9.LocalRup.prove_clause [c1424, c899] c1426 (by decide) p (sat_cons (step1424 p h) (sat_cons (step899 p h) (sat_nil p)))
def c1427 : List Lit := [(404, false)]
theorem step1427 (p : Nat → Bool) (h : Constraints p) : clause p c1427 = true :=
  Snake9.LocalRup.prove_clause [c1424, c902] c1427 (by decide) p (sat_cons (step1424 p h) (sat_cons (step902 p h) (sat_nil p)))
def c1428 : List Lit := [(346, false)]
theorem step1428 (p : Nat → Bool) (h : Constraints p) : clause p c1428 = true :=
  Snake9.LocalRup.prove_clause [c1425, c810] c1428 (by decide) p (sat_cons (step1425 p h) (sat_cons (step810 p h) (sat_nil p)))
def c1429 : List Lit := [(290, false)]
theorem step1429 (p : Nat → Bool) (h : Constraints p) : clause p c1429 = true :=
  Snake9.LocalRup.prove_clause [c1425, c813] c1429 (by decide) p (sat_cons (step1425 p h) (sat_cons (step813 p h) (sat_nil p)))
def c1430 : List Lit := [(458, false)]
theorem step1430 (p : Nat → Bool) (h : Constraints p) : clause p c1430 = true :=
  Snake9.LocalRup.prove_clause [c1426, c895] c1430 (by decide) p (sat_cons (step1426 p h) (sat_cons (step895 p h) (sat_nil p)))
def c1431 : List Lit := [(374, false)]
theorem step1431 (p : Nat → Bool) (h : Constraints p) : clause p c1431 = true :=
  Snake9.LocalRup.prove_clause [c1427, c856] c1431 (by decide) p (sat_cons (step1427 p h) (sat_cons (step856 p h) (sat_nil p)))
def c1432 : List Lit := [(344, false)]
theorem step1432 (p : Nat → Bool) (h : Constraints p) : clause p c1432 = true :=
  Snake9.LocalRup.prove_clause [c1428, c805] c1432 (by decide) p (sat_cons (step1428 p h) (sat_cons (step805 p h) (sat_nil p)))
def c1433 : List Lit := [(316, false)]
theorem step1433 (p : Nat → Bool) (h : Constraints p) : clause p c1433 = true :=
  Snake9.LocalRup.prove_clause [c1428, c808] c1433 (by decide) p (sat_cons (step1428 p h) (sat_cons (step808 p h) (sat_nil p)))
def c1434 : List Lit := [(288, false)]
theorem step1434 (p : Nat → Bool) (h : Constraints p) : clause p c1434 = true :=
  Snake9.LocalRup.prove_clause [c1429, c754] c1434 (by decide) p (sat_cons (step1429 p h) (sat_cons (step754 p h) (sat_nil p)))
def c1435 : List Lit := [(260, false)]
theorem step1435 (p : Nat → Bool) (h : Constraints p) : clause p c1435 = true :=
  Snake9.LocalRup.prove_clause [c1429, c757] c1435 (by decide) p (sat_cons (step1429 p h) (sat_cons (step757 p h) (sat_nil p)))
def c1436 : List Lit := [(360, false)]
theorem step1436 (p : Nat → Bool) (h : Constraints p) : clause p c1436 = true :=
  Snake9.LocalRup.prove_clause [c1431, c832] c1436 (by decide) p (sat_cons (step1431 p h) (sat_cons (step832 p h) (sat_nil p)))
def c1437 : List Lit := [(342, false)]
theorem step1437 (p : Nat → Bool) (h : Constraints p) : clause p c1437 = true :=
  Snake9.LocalRup.prove_clause [c1432, c801] c1437 (by decide) p (sat_cons (step1432 p h) (sat_cons (step801 p h) (sat_nil p)))
def c1438 : List Lit := [(302, false)]
theorem step1438 (p : Nat → Bool) (h : Constraints p) : clause p c1438 = true :=
  Snake9.LocalRup.prove_clause [c1433, c781] c1438 (by decide) p (sat_cons (step1433 p h) (sat_cons (step781 p h) (sat_nil p)))
def c1439 : List Lit := [(286, false)]
theorem step1439 (p : Nat → Bool) (h : Constraints p) : clause p c1439 = true :=
  Snake9.LocalRup.prove_clause [c1434, c749] c1439 (by decide) p (sat_cons (step1434 p h) (sat_cons (step749 p h) (sat_nil p)))
def c1440 : List Lit := [(272, false)]
theorem step1440 (p : Nat → Bool) (h : Constraints p) : clause p c1440 = true :=
  Snake9.LocalRup.prove_clause [c1434, c752] c1440 (by decide) p (sat_cons (step1434 p h) (sat_cons (step752 p h) (sat_nil p)))
def c1441 : List Lit := [(258, false)]
theorem step1441 (p : Nat → Bool) (h : Constraints p) : clause p c1441 = true :=
  Snake9.LocalRup.prove_clause [c1435, c727] c1441 (by decide) p (sat_cons (step1435 p h) (sat_cons (step727 p h) (sat_nil p)))
def c1442 : List Lit := [(246, false)]
theorem step1442 (p : Nat → Bool) (h : Constraints p) : clause p c1442 = true :=
  Snake9.LocalRup.prove_clause [c1435, c730] c1442 (by decide) p (sat_cons (step1435 p h) (sat_cons (step730 p h) (sat_nil p)))
def c1443 : List Lit := [(358, false)]
theorem step1443 (p : Nat → Bool) (h : Constraints p) : clause p c1443 = true :=
  Snake9.LocalRup.prove_clause [c1436, c822] c1443 (by decide) p (sat_cons (step1436 p h) (sat_cons (step822 p h) (sat_nil p)))
def c1444 : List Lit := [(300, false)]
theorem step1444 (p : Nat → Bool) (h : Constraints p) : clause p c1444 = true :=
  Snake9.LocalRup.prove_clause [c1438, c767] c1444 (by decide) p (sat_cons (step1438 p h) (sat_cons (step767 p h) (sat_nil p)))
def c1445 : List Lit := [(270, false)]
theorem step1445 (p : Nat → Bool) (h : Constraints p) : clause p c1445 = true :=
  Snake9.LocalRup.prove_clause [c1440, c739] c1445 (by decide) p (sat_cons (step1440 p h) (sat_cons (step739 p h) (sat_nil p)))
def c1446 : List Lit := [(256, false)]
theorem step1446 (p : Nat → Bool) (h : Constraints p) : clause p c1446 = true :=
  Snake9.LocalRup.prove_clause [c1441, c722] c1446 (by decide) p (sat_cons (step1441 p h) (sat_cons (step722 p h) (sat_nil p)))
def c1447 : List Lit := [(250, false)]
theorem step1447 (p : Nat → Bool) (h : Constraints p) : clause p c1447 = true :=
  Snake9.LocalRup.prove_clause [c1441, c725] c1447 (by decide) p (sat_cons (step1441 p h) (sat_cons (step725 p h) (sat_nil p)))
def c1448 : List Lit := [(244, false)]
theorem step1448 (p : Nat → Bool) (h : Constraints p) : clause p c1448 = true :=
  Snake9.LocalRup.prove_clause [c1442, c706] c1448 (by decide) p (sat_cons (step1442 p h) (sat_cons (step706 p h) (sat_nil p)))
def c1449 : List Lit := [(248, false)]
theorem step1449 (p : Nat → Bool) (h : Constraints p) : clause p c1449 = true :=
  Snake9.LocalRup.prove_clause [c1447, c713] c1449 (by decide) p (sat_cons (step1447 p h) (sat_cons (step713 p h) (sat_nil p)))
def c1450 : List Lit := [(118, true), (121, true), (124, true), (125, true), (126, true), (127, true), (128, true), (131, true), (134, true), (135, true), (138, true), (140, true), (145, true), (148, true), (149, true), (151, true), (153, true), (155, true), (156, true), (157, true), (159, true), (162, true), (164, true), (165, true), (170, true), (171, true), (172, true), (174, true), (175, true), (178, true), (180, true), (181, true), (184, true), (186, true), (188, true), (190, true), (192, true), (194, true), (196, true), (197, true), (201, true), (202, true), (204, true), (205, true), (210, true), (211, true), (212, true), (215, true), (217, true), (218, true), (219, true), (224, true), (225, true), (226, true), (228, true), (229, true), (232, true), (234, true)]
theorem step1450 (p : Nat → Bool) (h : Constraints p) : clause p c1450 = true :=
  Snake9.LocalRup.prove_clause [c641, c642, c643, c644, c645, c646, c647, c648, c649, c650, c651, c652, c653, c654, c655, c656, c657, c658, c659, c660, c661, c662, c663, c664, c665, c666, c667, c668, c669, c670, c671, c672, c673, c674, c675, c676, c677, c678, c679, c680, c681, c682, c683, c684, c685, c686, c687, c688, c689, c690, c691, c692, c693, c694, c695, c696, c697, c698, c907] c1450 (by decide) p (sat_cons (step641 p h) (sat_cons (step642 p h) (sat_cons (step643 p h) (sat_cons (step644 p h) (sat_cons (step645 p h) (sat_cons (step646 p h) (sat_cons (step647 p h) (sat_cons (step648 p h) (sat_cons (step649 p h) (sat_cons (step650 p h) (sat_cons (step651 p h) (sat_cons (step652 p h) (sat_cons (step653 p h) (sat_cons (step654 p h) (sat_cons (step655 p h) (sat_cons (step656 p h) (sat_cons (step657 p h) (sat_cons (step658 p h) (sat_cons (step659 p h) (sat_cons (step660 p h) (sat_cons (step661 p h) (sat_cons (step662 p h) (sat_cons (step663 p h) (sat_cons (step664 p h) (sat_cons (step665 p h) (sat_cons (step666 p h) (sat_cons (step667 p h) (sat_cons (step668 p h) (sat_cons (step669 p h) (sat_cons (step670 p h) (sat_cons (step671 p h) (sat_cons (step672 p h) (sat_cons (step673 p h) (sat_cons (step674 p h) (sat_cons (step675 p h) (sat_cons (step676 p h) (sat_cons (step677 p h) (sat_cons (step678 p h) (sat_cons (step679 p h) (sat_cons (step680 p h) (sat_cons (step681 p h) (sat_cons (step682 p h) (sat_cons (step683 p h) (sat_cons (step684 p h) (sat_cons (step685 p h) (sat_cons (step686 p h) (sat_cons (step687 p h) (sat_cons (step688 p h) (sat_cons (step689 p h) (sat_cons (step690 p h) (sat_cons (step691 p h) (sat_cons (step692 p h) (sat_cons (step693 p h) (sat_cons (step694 p h) (sat_cons (step695 p h) (sat_cons (step696 p h) (sat_cons (step697 p h) (sat_cons (step698 p h) (sat_cons (step907 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1451 : List Lit := [(1428, true)]
theorem step1451 (p : Nat → Bool) (h : Constraints p) : clause p c1451 = true :=
  Snake9.LocalRup.prove_clause [c1421, c951] c1451 (by decide) p (sat_cons (step1421 p h) (sat_cons (step951 p h) (sat_nil p)))
def c1452 : List Lit := [(22, true), (1429, true)]
theorem step1452 (p : Nat → Bool) (h : Constraints p) : clause p c1452 = true :=
  Snake9.LocalRup.prove_clause [c1421, c952] c1452 (by decide) p (sat_cons (step1421 p h) (sat_cons (step952 p h) (sat_nil p)))
def c1453 : List Lit := [(1430, true)]
theorem step1453 (p : Nat → Bool) (h : Constraints p) : clause p c1453 = true :=
  Snake9.LocalRup.prove_clause [c1422, c953] c1453 (by decide) p (sat_cons (step1422 p h) (sat_cons (step953 p h) (sat_nil p)))
def c1454 : List Lit := [(25, true), (1431, true)]
theorem step1454 (p : Nat → Bool) (h : Constraints p) : clause p c1454 = true :=
  Snake9.LocalRup.prove_clause [c1422, c954] c1454 (by decide) p (sat_cons (step1422 p h) (sat_cons (step954 p h) (sat_nil p)))
def c1455 : List Lit := [(1433, true)]
theorem step1455 (p : Nat → Bool) (h : Constraints p) : clause p c1455 = true :=
  Snake9.LocalRup.prove_clause [c1451, c1453, c955] c1455 (by decide) p (sat_cons (step1451 p h) (sat_cons (step1453 p h) (sat_cons (step955 p h) (sat_nil p))))
def c1456 : List Lit := [(1431, false), (1434, true)]
theorem step1456 (p : Nat → Bool) (h : Constraints p) : clause p c1456 = true :=
  Snake9.LocalRup.prove_clause [c1451, c956] c1456 (by decide) p (sat_cons (step1451 p h) (sat_cons (step956 p h) (sat_nil p)))
def c1457 : List Lit := [(1429, false), (1434, true)]
theorem step1457 (p : Nat → Bool) (h : Constraints p) : clause p c1457 = true :=
  Snake9.LocalRup.prove_clause [c1453, c957] c1457 (by decide) p (sat_cons (step1453 p h) (sat_cons (step957 p h) (sat_nil p)))
def c1458 : List Lit := [(1437, true)]
theorem step1458 (p : Nat → Bool) (h : Constraints p) : clause p c1458 = true :=
  Snake9.LocalRup.prove_clause [c1455, c959] c1458 (by decide) p (sat_cons (step1455 p h) (sat_cons (step959 p h) (sat_nil p)))
def c1459 : List Lit := [(1425, false), (1438, true)]
theorem step1459 (p : Nat → Bool) (h : Constraints p) : clause p c1459 = true :=
  Snake9.LocalRup.prove_clause [c1455, c962] c1459 (by decide) p (sat_cons (step1455 p h) (sat_cons (step962 p h) (sat_nil p)))
def c1460 : List Lit := [(1426, false), (1439, true)]
theorem step1460 (p : Nat → Bool) (h : Constraints p) : clause p c1460 = true :=
  Snake9.LocalRup.prove_clause [c1455, c965] c1460 (by decide) p (sat_cons (step1455 p h) (sat_cons (step965 p h) (sat_nil p)))
def c1461 : List Lit := [(1427, false), (1440, true)]
theorem step1461 (p : Nat → Bool) (h : Constraints p) : clause p c1461 = true :=
  Snake9.LocalRup.prove_clause [c1455, c968] c1461 (by decide) p (sat_cons (step1455 p h) (sat_cons (step968 p h) (sat_nil p)))
def c1462 : List Lit := [(1416, false), (1445, true)]
theorem step1462 (p : Nat → Bool) (h : Constraints p) : clause p c1462 = true :=
  Snake9.LocalRup.prove_clause [c1458, c971] c1462 (by decide) p (sat_cons (step1458 p h) (sat_cons (step971 p h) (sat_nil p)))
def c1463 : List Lit := [(1417, false), (1446, true)]
theorem step1463 (p : Nat → Bool) (h : Constraints p) : clause p c1463 = true :=
  Snake9.LocalRup.prove_clause [c1458, c977] c1463 (by decide) p (sat_cons (step1458 p h) (sat_cons (step977 p h) (sat_nil p)))
def c1464 : List Lit := [(1418, false), (1447, true)]
theorem step1464 (p : Nat → Bool) (h : Constraints p) : clause p c1464 = true :=
  Snake9.LocalRup.prove_clause [c1458, c982] c1464 (by decide) p (sat_cons (step1458 p h) (sat_cons (step982 p h) (sat_nil p)))
def c1465 : List Lit := [(1419, false), (1448, true)]
theorem step1465 (p : Nat → Bool) (h : Constraints p) : clause p c1465 = true :=
  Snake9.LocalRup.prove_clause [c1458, c985] c1465 (by decide) p (sat_cons (step1458 p h) (sat_cons (step985 p h) (sat_nil p)))
def c1466 : List Lit := [(1459, true)]
theorem step1466 (p : Nat → Bool) (h : Constraints p) : clause p c1466 = true :=
  Snake9.LocalRup.prove_clause [c1423, c991] c1466 (by decide) p (sat_cons (step1423 p h) (sat_cons (step991 p h) (sat_nil p)))
def c1467 : List Lit := [(1457, false), (1460, true)]
theorem step1467 (p : Nat → Bool) (h : Constraints p) : clause p c1467 = true :=
  Snake9.LocalRup.prove_clause [c1423, c992] c1467 (by decide) p (sat_cons (step1423 p h) (sat_cons (step992 p h) (sat_nil p)))
def c1468 : List Lit := [(1458, false), (1461, true)]
theorem step1468 (p : Nat → Bool) (h : Constraints p) : clause p c1468 = true :=
  Snake9.LocalRup.prove_clause [c1423, c993] c1468 (by decide) p (sat_cons (step1423 p h) (sat_cons (step993 p h) (sat_nil p)))
def c1469 : List Lit := [(1466, false), (1471, true)]
theorem step1469 (p : Nat → Bool) (h : Constraints p) : clause p c1469 = true :=
  Snake9.LocalRup.prove_clause [c1466, c1008] c1469 (by decide) p (sat_cons (step1466 p h) (sat_cons (step1008 p h) (sat_nil p)))
def c1470 : List Lit := [(1467, false), (1472, true)]
theorem step1470 (p : Nat → Bool) (h : Constraints p) : clause p c1470 = true :=
  Snake9.LocalRup.prove_clause [c1466, c1009] c1470 (by decide) p (sat_cons (step1466 p h) (sat_cons (step1009 p h) (sat_nil p)))
def c1471 : List Lit := [(1468, false), (1473, true)]
theorem step1471 (p : Nat → Bool) (h : Constraints p) : clause p c1471 = true :=
  Snake9.LocalRup.prove_clause [c1466, c1010] c1471 (by decide) p (sat_cons (step1466 p h) (sat_cons (step1010 p h) (sat_nil p)))
def c1472 : List Lit := [(1469, false), (1474, true)]
theorem step1472 (p : Nat → Bool) (h : Constraints p) : clause p c1472 = true :=
  Snake9.LocalRup.prove_clause [c1466, c1011] c1472 (by decide) p (sat_cons (step1466 p h) (sat_cons (step1011 p h) (sat_nil p)))
def c1473 : List Lit := [(1571, true)]
theorem step1473 (p : Nat → Bool) (h : Constraints p) : clause p c1473 = true :=
  Snake9.LocalRup.prove_clause [c682, c1193, c1197, c1185, c1187, c1171, c1173, c1183, c1179, c1180, c1169, c1165, c460, c484, c391] c1473 (by decide) p (sat_cons (step682 p h) (sat_cons (step1193 p h) (sat_cons (step1197 p h) (sat_cons (step1185 p h) (sat_cons (step1187 p h) (sat_cons (step1171 p h) (sat_cons (step1173 p h) (sat_cons (step1183 p h) (sat_cons (step1179 p h) (sat_cons (step1180 p h) (sat_cons (step1169 p h) (sat_cons (step1165 p h) (sat_cons (step460 p h) (sat_cons (step484 p h) (sat_cons (step391 p h) (sat_nil p))))))))))))))))
def c1474 : List Lit := [(1580, true)]
theorem step1474 (p : Nat → Bool) (h : Constraints p) : clause p c1474 = true :=
  Snake9.LocalRup.prove_clause [c1473, c673, c1214, c1219, c1202, c1147, c1176, c1139, c1141, c1136, c1137, c1133, c1134, c302, c293, c291, c289, c334, c1167] c1474 (by decide) p (sat_cons (step1473 p h) (sat_cons (step673 p h) (sat_cons (step1214 p h) (sat_cons (step1219 p h) (sat_cons (step1202 p h) (sat_cons (step1147 p h) (sat_cons (step1176 p h) (sat_cons (step1139 p h) (sat_cons (step1141 p h) (sat_cons (step1136 p h) (sat_cons (step1137 p h) (sat_cons (step1133 p h) (sat_cons (step1134 p h) (sat_cons (step302 p h) (sat_cons (step293 p h) (sat_cons (step291 p h) (sat_cons (step289 p h) (sat_cons (step334 p h) (sat_cons (step1167 p h) (sat_nil p))))))))))))))))))))
def c1475 : List Lit := [(1567, true)]
theorem step1475 (p : Nat → Bool) (h : Constraints p) : clause p c1475 = true :=
  Snake9.LocalRup.prove_clause [c682, c1185, c1187, c1182, c1183, c1179, c1180, c535, c465, c482] c1475 (by decide) p (sat_cons (step682 p h) (sat_cons (step1185 p h) (sat_cons (step1187 p h) (sat_cons (step1182 p h) (sat_cons (step1183 p h) (sat_cons (step1179 p h) (sat_cons (step1180 p h) (sat_cons (step535 p h) (sat_cons (step465 p h) (sat_cons (step482 p h) (sat_nil p)))))))))))
def c1476 : List Lit := [(1565, true), (1559, true)]
theorem step1476 (p : Nat → Bool) (h : Constraints p) : clause p c1476 = true :=
  Snake9.LocalRup.prove_clause [c680, c1173, c1165, c1171, c1169, c1168, c1182, c1183, c434, c532, c399, c402] c1476 (by decide) p (sat_cons (step680 p h) (sat_cons (step1173 p h) (sat_cons (step1165 p h) (sat_cons (step1171 p h) (sat_cons (step1169 p h) (sat_cons (step1168 p h) (sat_cons (step1182 p h) (sat_cons (step1183 p h) (sat_cons (step434 p h) (sat_cons (step532 p h) (sat_cons (step399 p h) (sat_cons (step402 p h) (sat_nil p)))))))))))))
def c1477 : List Lit := [(1572, true)]
theorem step1477 (p : Nat → Bool) (h : Constraints p) : clause p c1477 = true :=
  Snake9.LocalRup.prove_clause [c1475, c682, c1194, c1198, c1171, c1173, c1168, c1169, c1165, c390, c1476, c1188, c1179, c1180, c459, c484] c1477 (by decide) p (sat_cons (step1475 p h) (sat_cons (step682 p h) (sat_cons (step1194 p h) (sat_cons (step1198 p h) (sat_cons (step1171 p h) (sat_cons (step1173 p h) (sat_cons (step1168 p h) (sat_cons (step1169 p h) (sat_cons (step1165 p h) (sat_cons (step390 p h) (sat_cons (step1476 p h) (sat_cons (step1188 p h) (sat_cons (step1179 p h) (sat_cons (step1180 p h) (sat_cons (step459 p h) (sat_cons (step484 p h) (sat_nil p)))))))))))))))))
def c1478 : List Lit := [(1581, true)]
theorem step1478 (p : Nat → Bool) (h : Constraints p) : clause p c1478 = true :=
  Snake9.LocalRup.prove_clause [c1475, c1477, c673, c1215, c1203, c1176, c1220, c1147, c1139, c1141, c1136, c1137, c1133, c1134, c302, c293, c291, c289, c334, c1167] c1478 (by decide) p (sat_cons (step1475 p h) (sat_cons (step1477 p h) (sat_cons (step673 p h) (sat_cons (step1215 p h) (sat_cons (step1203 p h) (sat_cons (step1176 p h) (sat_cons (step1220 p h) (sat_cons (step1147 p h) (sat_cons (step1139 p h) (sat_cons (step1141 p h) (sat_cons (step1136 p h) (sat_cons (step1137 p h) (sat_cons (step1133 p h) (sat_cons (step1134 p h) (sat_cons (step302 p h) (sat_cons (step293 p h) (sat_cons (step291 p h) (sat_cons (step289 p h) (sat_cons (step334 p h) (sat_cons (step1167 p h) (sat_nil p)))))))))))))))))))))
def c1479 : List Lit := [(12, true), (1446, true)]
theorem step1479 (p : Nat → Bool) (h : Constraints p) : clause p c1479 = true :=
  Snake9.LocalRup.prove_clause [c642, c1463, c931, c927, c916, c918, c924, c930, c935, c972, c911, c1459, c909, c948, c10, c30] c1479 (by decide) p (sat_cons (step642 p h) (sat_cons (step1463 p h) (sat_cons (step931 p h) (sat_cons (step927 p h) (sat_cons (step916 p h) (sat_cons (step918 p h) (sat_cons (step924 p h) (sat_cons (step930 p h) (sat_cons (step935 p h) (sat_cons (step972 p h) (sat_cons (step911 p h) (sat_cons (step1459 p h) (sat_cons (step909 p h) (sat_cons (step948 p h) (sat_cons (step10 p h) (sat_cons (step30 p h) (sat_nil p)))))))))))))))))
def c1480 : List Lit := [(1416, true), (11, false), (12, false)]
theorem step1480 (p : Nat → Bool) (h : Constraints p) : clause p c1480 = true :=
  Snake9.LocalRup.prove_clause [c930, c934, c922, c913, c919, c46] c1480 (by decide) p (sat_cons (step930 p h) (sat_cons (step934 p h) (sat_cons (step922 p h) (sat_cons (step913 p h) (sat_cons (step919 p h) (sat_cons (step46 p h) (sat_nil p)))))))
def c1481 : List Lit := [(1416, true), (12, false)]
theorem step1481 (p : Nat → Bool) (h : Constraints p) : clause p c1481 = true :=
  Snake9.LocalRup.prove_clause [c647, c930, c934, c1480, c922, c911, c919, c920, c908, c70, c61] c1481 (by decide) p (sat_cons (step647 p h) (sat_cons (step930 p h) (sat_cons (step934 p h) (sat_cons (step1480 p h) (sat_cons (step922 p h) (sat_cons (step911 p h) (sat_cons (step919 p h) (sat_cons (step920 p h) (sat_cons (step908 p h) (sat_cons (step70 p h) (sat_cons (step61 p h) (sat_nil p))))))))))))
def c1482 : List Lit := [(1412, true), (11, true), (1446, true)]
theorem step1482 (p : Nat → Bool) (h : Constraints p) : clause p c1482 = true :=
  Snake9.LocalRup.prove_clause [c647, c642, c1479, c1481, c972, c1459, c948, c1463, c938, c912, c922, c924, c919, c920, c917, c70, c61, c910, c10, c30] c1482 (by decide) p (sat_cons (step647 p h) (sat_cons (step642 p h) (sat_cons (step1479 p h) (sat_cons (step1481 p h) (sat_cons (step972 p h) (sat_cons (step1459 p h) (sat_cons (step948 p h) (sat_cons (step1463 p h) (sat_cons (step938 p h) (sat_cons (step912 p h) (sat_cons (step922 p h) (sat_cons (step924 p h) (sat_cons (step919 p h) (sat_cons (step920 p h) (sat_cons (step917 p h) (sat_cons (step70 p h) (sat_cons (step61 p h) (sat_cons (step910 p h) (sat_cons (step10 p h) (sat_cons (step30 p h) (sat_nil p)))))))))))))))))))))
end B112E064
