import B112E254Inputs
namespace B112E254
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1415 : List Lit := [(5, false)]
theorem step1415 (p : Nat → Bool) (h : Constraints p) : clause p c1415 = true :=
  Snake9.LocalRup.prove_clause [c610, c8] c1415 (by decide) p (sat_cons (step610 p h) (sat_cons (step8 p h) (sat_nil p)))
def c1416 : List Lit := [(482, false)]
theorem step1416 (p : Nat → Bool) (h : Constraints p) : clause p c1416 = true :=
  Snake9.LocalRup.prove_clause [c886, c883] c1416 (by decide) p (sat_cons (step886 p h) (sat_cons (step883 p h) (sat_nil p)))
def c1417 : List Lit := [(362, false)]
theorem step1417 (p : Nat → Bool) (h : Constraints p) : clause p c1417 = true :=
  Snake9.LocalRup.prove_clause [c886, c885] c1417 (by decide) p (sat_cons (step886 p h) (sat_cons (step885 p h) (sat_nil p)))
def c1418 : List Lit := [(480, false)]
theorem step1418 (p : Nat → Bool) (h : Constraints p) : clause p c1418 = true :=
  Snake9.LocalRup.prove_clause [c1416, c879] c1418 (by decide) p (sat_cons (step1416 p h) (sat_cons (step879 p h) (sat_nil p)))
def c1419 : List Lit := [(420, false)]
theorem step1419 (p : Nat → Bool) (h : Constraints p) : clause p c1419 = true :=
  Snake9.LocalRup.prove_clause [c1416, c882] c1419 (by decide) p (sat_cons (step1416 p h) (sat_cons (step882 p h) (sat_nil p)))
def c1420 : List Lit := [(360, false)]
theorem step1420 (p : Nat → Bool) (h : Constraints p) : clause p c1420 = true :=
  Snake9.LocalRup.prove_clause [c1417, c775] c1420 (by decide) p (sat_cons (step1417 p h) (sat_cons (step775 p h) (sat_nil p)))
def c1421 : List Lit := [(302, false)]
theorem step1421 (p : Nat → Bool) (h : Constraints p) : clause p c1421 = true :=
  Snake9.LocalRup.prove_clause [c1417, c778] c1421 (by decide) p (sat_cons (step1417 p h) (sat_cons (step778 p h) (sat_nil p)))
def c1422 : List Lit := [(448, false)]
theorem step1422 (p : Nat → Bool) (h : Constraints p) : clause p c1422 = true :=
  Snake9.LocalRup.prove_clause [c1418, c877] c1422 (by decide) p (sat_cons (step1418 p h) (sat_cons (step877 p h) (sat_nil p)))
def c1423 : List Lit := [(418, false)]
theorem step1423 (p : Nat → Bool) (h : Constraints p) : clause p c1423 = true :=
  Snake9.LocalRup.prove_clause [c1419, c827] c1423 (by decide) p (sat_cons (step1419 p h) (sat_cons (step827 p h) (sat_nil p)))
def c1424 : List Lit := [(390, false)]
theorem step1424 (p : Nat → Bool) (h : Constraints p) : clause p c1424 = true :=
  Snake9.LocalRup.prove_clause [c1419, c830] c1424 (by decide) p (sat_cons (step1419 p h) (sat_cons (step830 p h) (sat_nil p)))
def c1425 : List Lit := [(330, false)]
theorem step1425 (p : Nat → Bool) (h : Constraints p) : clause p c1425 = true :=
  Snake9.LocalRup.prove_clause [c1420, c773] c1425 (by decide) p (sat_cons (step1420 p h) (sat_cons (step773 p h) (sat_nil p)))
def c1426 : List Lit := [(300, false)]
theorem step1426 (p : Nat → Bool) (h : Constraints p) : clause p c1426 = true :=
  Snake9.LocalRup.prove_clause [c1421, c723] c1426 (by decide) p (sat_cons (step1421 p h) (sat_cons (step723 p h) (sat_nil p)))
def c1427 : List Lit := [(272, false)]
theorem step1427 (p : Nat → Bool) (h : Constraints p) : clause p c1427 = true :=
  Snake9.LocalRup.prove_clause [c1421, c726] c1427 (by decide) p (sat_cons (step1421 p h) (sat_cons (step726 p h) (sat_nil p)))
def c1428 : List Lit := [(446, false)]
theorem step1428 (p : Nat → Bool) (h : Constraints p) : clause p c1428 = true :=
  Snake9.LocalRup.prove_clause [c1422, c849] c1428 (by decide) p (sat_cons (step1422 p h) (sat_cons (step849 p h) (sat_nil p)))
def c1429 : List Lit := [(432, false)]
theorem step1429 (p : Nat → Bool) (h : Constraints p) : clause p c1429 = true :=
  Snake9.LocalRup.prove_clause [c1422, c851] c1429 (by decide) p (sat_cons (step1422 p h) (sat_cons (step851 p h) (sat_nil p)))
def c1430 : List Lit := [(416, false)]
theorem step1430 (p : Nat → Bool) (h : Constraints p) : clause p c1430 = true :=
  Snake9.LocalRup.prove_clause [c1423, c824] c1430 (by decide) p (sat_cons (step1423 p h) (sat_cons (step824 p h) (sat_nil p)))
def c1431 : List Lit := [(388, false)]
theorem step1431 (p : Nat → Bool) (h : Constraints p) : clause p c1431 = true :=
  Snake9.LocalRup.prove_clause [c1424, c802] c1431 (by decide) p (sat_cons (step1424 p h) (sat_cons (step802 p h) (sat_nil p)))
def c1432 : List Lit := [(328, false)]
theorem step1432 (p : Nat → Bool) (h : Constraints p) : clause p c1432 = true :=
  Snake9.LocalRup.prove_clause [c1425, c749] c1432 (by decide) p (sat_cons (step1425 p h) (sat_cons (step749 p h) (sat_nil p)))
def c1433 : List Lit := [(298, false)]
theorem step1433 (p : Nat → Bool) (h : Constraints p) : clause p c1433 = true :=
  Snake9.LocalRup.prove_clause [c1426, c718] c1433 (by decide) p (sat_cons (step1426 p h) (sat_cons (step718 p h) (sat_nil p)))
def c1434 : List Lit := [(284, false)]
theorem step1434 (p : Nat → Bool) (h : Constraints p) : clause p c1434 = true :=
  Snake9.LocalRup.prove_clause [c1426, c721] c1434 (by decide) p (sat_cons (step1426 p h) (sat_cons (step721 p h) (sat_nil p)))
def c1435 : List Lit := [(270, false)]
theorem step1435 (p : Nat → Bool) (h : Constraints p) : clause p c1435 = true :=
  Snake9.LocalRup.prove_clause [c1427, c690] c1435 (by decide) p (sat_cons (step1427 p h) (sat_cons (step690 p h) (sat_nil p)))
def c1436 : List Lit := [(256, false)]
theorem step1436 (p : Nat → Bool) (h : Constraints p) : clause p c1436 = true :=
  Snake9.LocalRup.prove_clause [c1427, c693] c1436 (by decide) p (sat_cons (step1427 p h) (sat_cons (step693 p h) (sat_nil p)))
def c1437 : List Lit := [(444, false)]
theorem step1437 (p : Nat → Bool) (h : Constraints p) : clause p c1437 = true :=
  Snake9.LocalRup.prove_clause [c1428, c847] c1437 (by decide) p (sat_cons (step1428 p h) (sat_cons (step847 p h) (sat_nil p)))
def c1438 : List Lit := [(408, false)]
theorem step1438 (p : Nat → Bool) (h : Constraints p) : clause p c1438 = true :=
  Snake9.LocalRup.prove_clause [c1430, c822] c1438 (by decide) p (sat_cons (step1430 p h) (sat_cons (step822 p h) (sat_nil p)))
def c1439 : List Lit := [(386, false)]
theorem step1439 (p : Nat → Bool) (h : Constraints p) : clause p c1439 = true :=
  Snake9.LocalRup.prove_clause [c1431, c799] c1439 (by decide) p (sat_cons (step1431 p h) (sat_cons (step799 p h) (sat_nil p)))
def c1440 : List Lit := [(326, false)]
theorem step1440 (p : Nat → Bool) (h : Constraints p) : clause p c1440 = true :=
  Snake9.LocalRup.prove_clause [c1432, c745] c1440 (by decide) p (sat_cons (step1432 p h) (sat_cons (step745 p h) (sat_nil p)))
def c1441 : List Lit := [(296, false)]
theorem step1441 (p : Nat → Bool) (h : Constraints p) : clause p c1441 = true :=
  Snake9.LocalRup.prove_clause [c1433, c713] c1441 (by decide) p (sat_cons (step1433 p h) (sat_cons (step713 p h) (sat_nil p)))
def c1442 : List Lit := [(290, false)]
theorem step1442 (p : Nat → Bool) (h : Constraints p) : clause p c1442 = true :=
  Snake9.LocalRup.prove_clause [c1433, c716] c1442 (by decide) p (sat_cons (step1433 p h) (sat_cons (step716 p h) (sat_nil p)))
def c1443 : List Lit := [(254, false)]
theorem step1443 (p : Nat → Bool) (h : Constraints p) : clause p c1443 = true :=
  Snake9.LocalRup.prove_clause [c1436, c678] c1443 (by decide) p (sat_cons (step1436 p h) (sat_cons (step678 p h) (sat_nil p)))
def c1444 : List Lit := [(404, false)]
theorem step1444 (p : Nat → Bool) (h : Constraints p) : clause p c1444 = true :=
  Snake9.LocalRup.prove_clause [c1438, c812] c1444 (by decide) p (sat_cons (step1438 p h) (sat_cons (step812 p h) (sat_nil p)))
def c1445 : List Lit := [(382, false)]
theorem step1445 (p : Nat → Bool) (h : Constraints p) : clause p c1445 = true :=
  Snake9.LocalRup.prove_clause [c1439, c797] c1445 (by decide) p (sat_cons (step1439 p h) (sat_cons (step797 p h) (sat_nil p)))
def c1446 : List Lit := [(322, false)]
theorem step1446 (p : Nat → Bool) (h : Constraints p) : clause p c1446 = true :=
  Snake9.LocalRup.prove_clause [c1440, c743] c1446 (by decide) p (sat_cons (step1440 p h) (sat_cons (step743 p h) (sat_nil p)))
def c1447 : List Lit := [(252, false)]
theorem step1447 (p : Nat → Bool) (h : Constraints p) : clause p c1447 = true :=
  Snake9.LocalRup.prove_clause [c1443, c674] c1447 (by decide) p (sat_cons (step1443 p h) (sat_cons (step674 p h) (sat_nil p)))
def c1448 : List Lit := [(123, true), (125, true), (126, true), (128, true), (129, true), (132, true), (133, true), (135, true), (138, true), (139, true), (142, true), (143, true), (145, true), (146, true), (148, true), (150, true), (152, true), (155, true), (157, true), (159, true), (161, true), (162, true), (164, true), (165, true), (168, true), (171, true), (172, true), (174, true), (176, true), (178, true), (179, true), (182, true), (183, true), (185, true), (186, true), (190, true), (193, true), (194, true), (195, true), (196, true), (197, true), (198, true), (202, true), (206, true), (207, true), (210, true), (211, true), (212, true), (213, true), (215, true), (217, true), (218, true), (220, true), (226, true), (228, true), (229, true), (231, true), (234, true), (235, true), (237, true), (238, true), (240, true), (241, true), (242, true)]
theorem step1448 (p : Nat → Bool) (h : Constraints p) : clause p c1448 = true :=
  Snake9.LocalRup.prove_clause [c609, c610, c611, c612, c613, c614, c615, c616, c617, c618, c619, c620, c621, c622, c623, c624, c625, c626, c627, c628, c629, c630, c631, c632, c633, c634, c635, c636, c637, c638, c639, c640, c641, c642, c643, c644, c645, c646, c647, c648, c649, c650, c651, c652, c653, c654, c655, c656, c657, c658, c659, c660, c661, c662, c663, c664, c665, c887] c1448 (by decide) p (sat_cons (step609 p h) (sat_cons (step610 p h) (sat_cons (step611 p h) (sat_cons (step612 p h) (sat_cons (step613 p h) (sat_cons (step614 p h) (sat_cons (step615 p h) (sat_cons (step616 p h) (sat_cons (step617 p h) (sat_cons (step618 p h) (sat_cons (step619 p h) (sat_cons (step620 p h) (sat_cons (step621 p h) (sat_cons (step622 p h) (sat_cons (step623 p h) (sat_cons (step624 p h) (sat_cons (step625 p h) (sat_cons (step626 p h) (sat_cons (step627 p h) (sat_cons (step628 p h) (sat_cons (step629 p h) (sat_cons (step630 p h) (sat_cons (step631 p h) (sat_cons (step632 p h) (sat_cons (step633 p h) (sat_cons (step634 p h) (sat_cons (step635 p h) (sat_cons (step636 p h) (sat_cons (step637 p h) (sat_cons (step638 p h) (sat_cons (step639 p h) (sat_cons (step640 p h) (sat_cons (step641 p h) (sat_cons (step642 p h) (sat_cons (step643 p h) (sat_cons (step644 p h) (sat_cons (step645 p h) (sat_cons (step646 p h) (sat_cons (step647 p h) (sat_cons (step648 p h) (sat_cons (step649 p h) (sat_cons (step650 p h) (sat_cons (step651 p h) (sat_cons (step652 p h) (sat_cons (step653 p h) (sat_cons (step654 p h) (sat_cons (step655 p h) (sat_cons (step656 p h) (sat_cons (step657 p h) (sat_cons (step658 p h) (sat_cons (step659 p h) (sat_cons (step660 p h) (sat_cons (step661 p h) (sat_cons (step662 p h) (sat_cons (step663 p h) (sat_cons (step664 p h) (sat_cons (step665 p h) (sat_cons (step887 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1449 : List Lit := [(1501, true)]
theorem step1449 (p : Nat → Bool) (h : Constraints p) : clause p c1449 = true :=
  Snake9.LocalRup.prove_clause [c1415, c888] c1449 (by decide) p (sat_cons (step1415 p h) (sat_cons (step888 p h) (sat_nil p)))
def c1450 : List Lit := [(8, true), (1502, true)]
theorem step1450 (p : Nat → Bool) (h : Constraints p) : clause p c1450 = true :=
  Snake9.LocalRup.prove_clause [c1415, c889] c1450 (by decide) p (sat_cons (step1415 p h) (sat_cons (step889 p h) (sat_nil p)))
def c1451 : List Lit := [(1503, true)]
theorem step1451 (p : Nat → Bool) (h : Constraints p) : clause p c1451 = true :=
  Snake9.LocalRup.prove_clause [c1449, c890] c1451 (by decide) p (sat_cons (step1449 p h) (sat_cons (step890 p h) (sat_nil p)))
def c1452 : List Lit := [(2, true), (1504, true)]
theorem step1452 (p : Nat → Bool) (h : Constraints p) : clause p c1452 = true :=
  Snake9.LocalRup.prove_clause [c1449, c892] c1452 (by decide) p (sat_cons (step1449 p h) (sat_cons (step892 p h) (sat_nil p)))
def c1453 : List Lit := [(1514, true)]
theorem step1453 (p : Nat → Bool) (h : Constraints p) : clause p c1453 = true :=
  Snake9.LocalRup.prove_clause [c1451, c908] c1453 (by decide) p (sat_cons (step1451 p h) (sat_cons (step908 p h) (sat_nil p)))
def c1454 : List Lit := [(1510, false), (1515, true)]
theorem step1454 (p : Nat → Bool) (h : Constraints p) : clause p c1454 = true :=
  Snake9.LocalRup.prove_clause [c1451, c909] c1454 (by decide) p (sat_cons (step1451 p h) (sat_cons (step909 p h) (sat_nil p)))
def c1455 : List Lit := [(1511, false), (1516, true)]
theorem step1455 (p : Nat → Bool) (h : Constraints p) : clause p c1455 = true :=
  Snake9.LocalRup.prove_clause [c1451, c910] c1455 (by decide) p (sat_cons (step1451 p h) (sat_cons (step910 p h) (sat_nil p)))
def c1456 : List Lit := [(1512, false), (1517, true)]
theorem step1456 (p : Nat → Bool) (h : Constraints p) : clause p c1456 = true :=
  Snake9.LocalRup.prove_clause [c1451, c911] c1456 (by decide) p (sat_cons (step1451 p h) (sat_cons (step911 p h) (sat_nil p)))
def c1457 : List Lit := [(1513, false), (1518, true)]
theorem step1457 (p : Nat → Bool) (h : Constraints p) : clause p c1457 = true :=
  Snake9.LocalRup.prove_clause [c1451, c912] c1457 (by decide) p (sat_cons (step1451 p h) (sat_cons (step912 p h) (sat_nil p)))
def c1458 : List Lit := [(1541, true)]
theorem step1458 (p : Nat → Bool) (h : Constraints p) : clause p c1458 = true :=
  Snake9.LocalRup.prove_clause [c1453, c961] c1458 (by decide) p (sat_cons (step1453 p h) (sat_cons (step961 p h) (sat_nil p)))
def c1459 : List Lit := [(1534, false), (1542, true)]
theorem step1459 (p : Nat → Bool) (h : Constraints p) : clause p c1459 = true :=
  Snake9.LocalRup.prove_clause [c1453, c962] c1459 (by decide) p (sat_cons (step1453 p h) (sat_cons (step962 p h) (sat_nil p)))
def c1460 : List Lit := [(1535, false), (1543, true)]
theorem step1460 (p : Nat → Bool) (h : Constraints p) : clause p c1460 = true :=
  Snake9.LocalRup.prove_clause [c1453, c963] c1460 (by decide) p (sat_cons (step1453 p h) (sat_cons (step963 p h) (sat_nil p)))
def c1461 : List Lit := [(1536, false), (1544, true)]
theorem step1461 (p : Nat → Bool) (h : Constraints p) : clause p c1461 = true :=
  Snake9.LocalRup.prove_clause [c1453, c964] c1461 (by decide) p (sat_cons (step1453 p h) (sat_cons (step964 p h) (sat_nil p)))
def c1462 : List Lit := [(1537, false), (1545, true)]
theorem step1462 (p : Nat → Bool) (h : Constraints p) : clause p c1462 = true :=
  Snake9.LocalRup.prove_clause [c1453, c965] c1462 (by decide) p (sat_cons (step1453 p h) (sat_cons (step965 p h) (sat_nil p)))
def c1463 : List Lit := [(1538, false), (1546, true)]
theorem step1463 (p : Nat → Bool) (h : Constraints p) : clause p c1463 = true :=
  Snake9.LocalRup.prove_clause [c1453, c966] c1463 (by decide) p (sat_cons (step1453 p h) (sat_cons (step966 p h) (sat_nil p)))
def c1464 : List Lit := [(1603, false), (1619, true)]
theorem step1464 (p : Nat → Bool) (h : Constraints p) : clause p c1464 = true :=
  Snake9.LocalRup.prove_clause [c1458, c1074] c1464 (by decide) p (sat_cons (step1458 p h) (sat_cons (step1074 p h) (sat_nil p)))
def c1465 : List Lit := [(1585, true)]
theorem step1465 (p : Nat → Bool) (h : Constraints p) : clause p c1465 = true :=
  Snake9.LocalRup.prove_clause [c636, c1038, c1039, c280, c281, c1403] c1465 (by decide) p (sat_cons (step636 p h) (sat_cons (step1038 p h) (sat_cons (step1039 p h) (sat_cons (step280 p h) (sat_cons (step281 p h) (sat_cons (step1403 p h) (sat_nil p)))))))
def c1466 : List Lit := [(1587, true)]
theorem step1466 (p : Nat → Bool) (h : Constraints p) : clause p c1466 = true :=
  Snake9.LocalRup.prove_clause [c1465, c1041] c1466 (by decide) p (sat_cons (step1465 p h) (sat_cons (step1041 p h) (sat_nil p)))
def c1467 : List Lit := [(1591, true)]
theorem step1467 (p : Nat → Bool) (h : Constraints p) : clause p c1467 = true :=
  Snake9.LocalRup.prove_clause [c1466, c1047] c1467 (by decide) p (sat_cons (step1466 p h) (sat_cons (step1047 p h) (sat_nil p)))
def c1468 : List Lit := [(1599, true)]
theorem step1468 (p : Nat → Bool) (h : Constraints p) : clause p c1468 = true :=
  Snake9.LocalRup.prove_clause [c1467, c1056] c1468 (by decide) p (sat_cons (step1467 p h) (sat_cons (step1056 p h) (sat_nil p)))
def c1469 : List Lit := [(1645, true)]
theorem step1469 (p : Nat → Bool) (h : Constraints p) : clause p c1469 = true :=
  Snake9.LocalRup.prove_clause [c637, c1127, c1130, c1119, c1121, c1108, c1110, c1117, c1113, c1105, c1106, c283, c358, c305] c1469 (by decide) p (sat_cons (step637 p h) (sat_cons (step1127 p h) (sat_cons (step1130 p h) (sat_cons (step1119 p h) (sat_cons (step1121 p h) (sat_cons (step1108 p h) (sat_cons (step1110 p h) (sat_cons (step1117 p h) (sat_cons (step1113 p h) (sat_cons (step1105 p h) (sat_cons (step1106 p h) (sat_cons (step283 p h) (sat_cons (step358 p h) (sat_cons (step305 p h) (sat_nil p)))))))))))))))
def c1470 : List Lit := [(1672, true)]
theorem step1470 (p : Nat → Bool) (h : Constraints p) : clause p c1470 = true :=
  Snake9.LocalRup.prove_clause [c1469, c1185] c1470 (by decide) p (sat_cons (step1469 p h) (sat_cons (step1185 p h) (sat_nil p)))
def c1471 : List Lit := [(1542, true)]
theorem step1471 (p : Nat → Bool) (h : Constraints p) : clause p c1471 = true :=
  Snake9.LocalRup.prove_clause [c615, c1459, c967, c944, c948, c1454, c913, c936, c938, c925, c900, c902, c891, c934, c930, c922, c923, c897, c894, c895, c1450, c29, c126, c83, c96] c1471 (by decide) p (sat_cons (step615 p h) (sat_cons (step1459 p h) (sat_cons (step967 p h) (sat_cons (step944 p h) (sat_cons (step948 p h) (sat_cons (step1454 p h) (sat_cons (step913 p h) (sat_cons (step936 p h) (sat_cons (step938 p h) (sat_cons (step925 p h) (sat_cons (step900 p h) (sat_cons (step902 p h) (sat_cons (step891 p h) (sat_cons (step934 p h) (sat_cons (step930 p h) (sat_cons (step922 p h) (sat_cons (step923 p h) (sat_cons (step897 p h) (sat_cons (step894 p h) (sat_cons (step895 p h) (sat_cons (step1450 p h) (sat_cons (step29 p h) (sat_cons (step126 p h) (sat_cons (step83 p h) (sat_cons (step96 p h) (sat_nil p))))))))))))))))))))))))))
def c1472 : List Lit := [(1617, true)]
theorem step1472 (p : Nat → Bool) (h : Constraints p) : clause p c1472 = true :=
  Snake9.LocalRup.prove_clause [c1468, c1471, c1467, c625, c627, c1080, c1460, c953, c1075, c1059, c1015, c1018, c1010, c997, c999, c1002, c1003, c994, c214, c193, c219, c218, c184, c1390, c928, c922] c1472 (by decide) p (sat_cons (step1468 p h) (sat_cons (step1471 p h) (sat_cons (step1467 p h) (sat_cons (step625 p h) (sat_cons (step627 p h) (sat_cons (step1080 p h) (sat_cons (step1460 p h) (sat_cons (step953 p h) (sat_cons (step1075 p h) (sat_cons (step1059 p h) (sat_cons (step1015 p h) (sat_cons (step1018 p h) (sat_cons (step1010 p h) (sat_cons (step997 p h) (sat_cons (step999 p h) (sat_cons (step1002 p h) (sat_cons (step1003 p h) (sat_cons (step994 p h) (sat_cons (step214 p h) (sat_cons (step193 p h) (sat_cons (step219 p h) (sat_cons (step218 p h) (sat_cons (step184 p h) (sat_cons (step1390 p h) (sat_cons (step928 p h) (sat_cons (step922 p h) (sat_nil p)))))))))))))))))))))))))))
def c1473 : List Lit := [(1758, false)]
theorem step1473 (p : Nat → Bool) (h : Constraints p) : clause p c1473 = true :=
  Snake9.LocalRup.prove_clause [c1472, c1372, c1365] c1473 (by decide) p (sat_cons (step1472 p h) (sat_cons (step1372 p h) (sat_cons (step1365 p h) (sat_nil p))))
def c1474 : List Lit := [(1544, true), (1568, true)]
theorem step1474 (p : Nat → Bool) (h : Constraints p) : clause p c1474 = true :=
  Snake9.LocalRup.prove_clause [c627, c625, c1018, c997, c994, c999, c1015, c1010, c1002, c1003, c214, c193, c184, c219, c218, c1390, c922, c928, c953, c1461, c969, c957, c1454, c929, c900, c924, c897, c127] c1474 (by decide) p (sat_cons (step627 p h) (sat_cons (step625 p h) (sat_cons (step1018 p h) (sat_cons (step997 p h) (sat_cons (step994 p h) (sat_cons (step999 p h) (sat_cons (step1015 p h) (sat_cons (step1010 p h) (sat_cons (step1002 p h) (sat_cons (step1003 p h) (sat_cons (step214 p h) (sat_cons (step193 p h) (sat_cons (step184 p h) (sat_cons (step219 p h) (sat_cons (step218 p h) (sat_cons (step1390 p h) (sat_cons (step922 p h) (sat_cons (step928 p h) (sat_cons (step953 p h) (sat_cons (step1461 p h) (sat_cons (step969 p h) (sat_cons (step957 p h) (sat_cons (step1454 p h) (sat_cons (step929 p h) (sat_cons (step900 p h) (sat_cons (step924 p h) (sat_cons (step897 p h) (sat_cons (step127 p h) (sat_nil p)))))))))))))))))))))))))))))
def c1475 : List Lit := [(1516, true), (1508, false), (104, false), (85, false), (10, true), (113, false)]
theorem step1475 (p : Nat → Bool) (h : Constraints p) : clause p c1475 = true :=
  Snake9.LocalRup.prove_clause [c609, c612, c1415, c886, c900, c1455, c914, c903, c1452, c895, c3, c23, c7, c341, c542, c669, c549, c675, c841, c677, c844, c691, c846, c724, c848, c776, c875, c884, c878] c1475 (by decide) p (sat_cons (step609 p h) (sat_cons (step612 p h) (sat_cons (step1415 p h) (sat_cons (step886 p h) (sat_cons (step900 p h) (sat_cons (step1455 p h) (sat_cons (step914 p h) (sat_cons (step903 p h) (sat_cons (step1452 p h) (sat_cons (step895 p h) (sat_cons (step3 p h) (sat_cons (step23 p h) (sat_cons (step7 p h) (sat_cons (step341 p h) (sat_cons (step542 p h) (sat_cons (step669 p h) (sat_cons (step549 p h) (sat_cons (step675 p h) (sat_cons (step841 p h) (sat_cons (step677 p h) (sat_cons (step844 p h) (sat_cons (step691 p h) (sat_cons (step846 p h) (sat_cons (step724 p h) (sat_cons (step848 p h) (sat_cons (step776 p h) (sat_cons (step875 p h) (sat_cons (step884 p h) (sat_cons (step878 p h) (sat_nil p))))))))))))))))))))))))))))))
def c1476 : List Lit := [(68, false), (104, false), (85, false), (83, true), (113, false)]
theorem step1476 (p : Nat → Bool) (h : Constraints p) : clause p c1476 = true :=
  Snake9.LocalRup.prove_clause [c1416, c341, c542, c549, c435, c841, c808, c844, c811, c846, c820, c848, c823, c875, c826, c881] c1476 (by decide) p (sat_cons (step1416 p h) (sat_cons (step341 p h) (sat_cons (step542 p h) (sat_cons (step549 p h) (sat_cons (step435 p h) (sat_cons (step841 p h) (sat_cons (step808 p h) (sat_cons (step844 p h) (sat_cons (step811 p h) (sat_cons (step846 p h) (sat_cons (step820 p h) (sat_cons (step848 p h) (sat_cons (step823 p h) (sat_cons (step875 p h) (sat_cons (step826 p h) (sat_cons (step881 p h) (sat_nil p)))))))))))))))))
def c1477 : List Lit := [(459, true), (1755, true), (1702, false), (110, false), (103, true), (1655, false), (83, true), (1583, true)]
theorem step1477 (p : Nat → Bool) (h : Constraints p) : clause p c1477 = true :=
  Snake9.LocalRup.prove_clause [c633, c661, c660, c1469, c1154, c1161, c1177, c1188, c1338, c1320, c1288, c1036, c262, c1035, c858, c859, c857, c856, c570, c568, c566, c564, c579, c580, c1272, c1276, c1281, c1284, c1287, c1274, c1319, c573, c1342, c1155, c1189, c1164, c1178] c1477 (by decide) p (sat_cons (step633 p h) (sat_cons (step661 p h) (sat_cons (step660 p h) (sat_cons (step1469 p h) (sat_cons (step1154 p h) (sat_cons (step1161 p h) (sat_cons (step1177 p h) (sat_cons (step1188 p h) (sat_cons (step1338 p h) (sat_cons (step1320 p h) (sat_cons (step1288 p h) (sat_cons (step1036 p h) (sat_cons (step262 p h) (sat_cons (step1035 p h) (sat_cons (step858 p h) (sat_cons (step859 p h) (sat_cons (step857 p h) (sat_cons (step856 p h) (sat_cons (step570 p h) (sat_cons (step568 p h) (sat_cons (step566 p h) (sat_cons (step564 p h) (sat_cons (step579 p h) (sat_cons (step580 p h) (sat_cons (step1272 p h) (sat_cons (step1276 p h) (sat_cons (step1281 p h) (sat_cons (step1284 p h) (sat_cons (step1287 p h) (sat_cons (step1274 p h) (sat_cons (step1319 p h) (sat_cons (step573 p h) (sat_cons (step1342 p h) (sat_cons (step1155 p h) (sat_cons (step1189 p h) (sat_cons (step1164 p h) (sat_cons (step1178 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))
def c1478 : List Lit := [(61, false), (1600, true)]
theorem step1478 (p : Nat → Bool) (h : Constraints p) : clause p c1478 = true :=
  Snake9.LocalRup.prove_clause [c1465, c1467, c1059, c1015, c1010, c1003, c1057, c1048, c1043, c1035, c1042, c276, c277, c1040] c1478 (by decide) p (sat_cons (step1465 p h) (sat_cons (step1467 p h) (sat_cons (step1059 p h) (sat_cons (step1015 p h) (sat_cons (step1010 p h) (sat_cons (step1003 p h) (sat_cons (step1057 p h) (sat_cons (step1048 p h) (sat_cons (step1043 p h) (sat_cons (step1035 p h) (sat_cons (step1042 p h) (sat_cons (step276 p h) (sat_cons (step277 p h) (sat_cons (step1040 p h) (sat_nil p)))))))))))))))
end B112E254
