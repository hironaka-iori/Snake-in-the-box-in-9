import B112E036Part0000
namespace B112E036
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1709 : List Lit := [(1720, true), (111, false), (88, false), (98, false), (72, true)]
theorem step1709 (p : Nat → Bool) (h : Constraints p) : clause p c1709 = true :=
  Snake9.LocalRup.prove_clause [c1295, c1305, c1303, c1296, c1297, c1298, c1706, c370] c1709 (by decide) p (sat_cons (step1295 p h) (sat_cons (step1305 p h) (sat_cons (step1303 p h) (sat_cons (step1296 p h) (sat_cons (step1297 p h) (sat_cons (step1298 p h) (sat_cons (step1706 p h) (sat_cons (step370 p h) (sat_nil p)))))))))
def c1710 : List Lit := [(1711, true), (66, false), (125, false)]
theorem step1710 (p : Nat → Bool) (h : Constraints p) : clause p c1710 = true :=
  Snake9.LocalRup.prove_clause [c1286, c1288, c1284, c1280, c327] c1710 (by decide) p (sat_cons (step1286 p h) (sat_cons (step1288 p h) (sat_cons (step1284 p h) (sat_cons (step1280 p h) (sat_cons (step327 p h) (sat_nil p))))))
def c1711 : List Lit := [(1623, true), (31, true), (101, false)]
theorem step1711 (p : Nat → Bool) (h : Constraints p) : clause p c1711 = true :=
  Snake9.LocalRup.prove_clause [c787, c1124, c1126, c1121, c1122, c1118, c197, c190, c186] c1711 (by decide) p (sat_cons (step787 p h) (sat_cons (step1124 p h) (sat_cons (step1126 p h) (sat_cons (step1121 p h) (sat_cons (step1122 p h) (sat_cons (step1118 p h) (sat_cons (step197 p h) (sat_cons (step190 p h) (sat_cons (step186 p h) (sat_nil p))))))))))
def c1712 : List Lit := [(1624, true), (42, true), (39, true), (31, true)]
theorem step1712 (p : Nat → Bool) (h : Constraints p) : clause p c1712 = true :=
  Snake9.LocalRup.prove_clause [c787, c1119, c1129, c1127, c1120, c1121, c1122, c186, c197] c1712 (by decide) p (sat_cons (step787 p h) (sat_cons (step1119 p h) (sat_cons (step1129 p h) (sat_cons (step1127 p h) (sat_cons (step1120 p h) (sat_cons (step1121 p h) (sat_cons (step1122 p h) (sat_cons (step186 p h) (sat_cons (step197 p h) (sat_nil p))))))))))
def c1713 : List Lit := [(1575, true)]
theorem step1713 (p : Nat → Bool) (h : Constraints p) : clause p c1713 = true :=
  Snake9.LocalRup.prove_clause [c406, c1645, c1049, c1050, c1047, c1043, c70] c1713 (by decide) p (sat_cons (step406 p h) (sat_cons (step1645 p h) (sat_cons (step1049 p h) (sat_cons (step1050 p h) (sat_cons (step1047 p h) (sat_cons (step1043 p h) (sat_cons (step70 p h) (sat_nil p))))))))
def c1714 : List Lit := [(1590, true)]
theorem step1714 (p : Nat → Bool) (h : Constraints p) : clause p c1714 = true :=
  Snake9.LocalRup.prove_clause [c1713, c782, c1676, c1064, c1694, c1673, c1057, c1058, c90, c94] c1714 (by decide) p (sat_cons (step1713 p h) (sat_cons (step782 p h) (sat_cons (step1676 p h) (sat_cons (step1064 p h) (sat_cons (step1694 p h) (sat_cons (step1673 p h) (sat_cons (step1057 p h) (sat_cons (step1058 p h) (sat_cons (step90 p h) (sat_cons (step94 p h) (sat_nil p)))))))))))
def c1715 : List Lit := [(7, false), (74, false), (70, false), (1718, true)]
theorem step1715 (p : Nat → Bool) (h : Constraints p) : clause p c1715 = true :=
  Snake9.LocalRup.prove_clause [c362, c363, c1299] c1715 (by decide) p (sat_cons (step362 p h) (sat_cons (step363 p h) (sat_cons (step1299 p h) (sat_nil p))))
def c1716 : List Lit := [(1591, true), (2, false)]
theorem step1716 (p : Nat → Bool) (h : Constraints p) : clause p c1716 = true :=
  Snake9.LocalRup.prove_clause [c1645, c406, c782, c67, c1043, c68, c1047, c1051, c1677, c1067, c1054, c1673, c1045, c1057, c1058, c90, c94] c1716 (by decide) p (sat_cons (step1645 p h) (sat_cons (step406 p h) (sat_cons (step782 p h) (sat_cons (step67 p h) (sat_cons (step1043 p h) (sat_cons (step68 p h) (sat_cons (step1047 p h) (sat_cons (step1051 p h) (sat_cons (step1677 p h) (sat_cons (step1067 p h) (sat_cons (step1054 p h) (sat_cons (step1673 p h) (sat_cons (step1045 p h) (sat_cons (step1057 p h) (sat_cons (step1058 p h) (sat_cons (step90 p h) (sat_cons (step94 p h) (sat_nil p))))))))))))))))))
def c1717 : List Lit := [(1581, true), (17, false)]
theorem step1717 (p : Nat → Bool) (h : Constraints p) : clause p c1717 = true :=
  Snake9.LocalRup.prove_clause [c782, c1057, c1058, c90, c94] c1717 (by decide) p (sat_cons (step782 p h) (sat_cons (step1057 p h) (sat_cons (step1058 p h) (sat_cons (step90 p h) (sat_cons (step94 p h) (sat_nil p))))))
def c1718 : List Lit := [(1557, true), (15, true), (17, false)]
theorem step1718 (p : Nat → Bool) (h : Constraints p) : clause p c1718 = true :=
  Snake9.LocalRup.prove_clause [c775, c1013, c1014, c59, c63] c1718 (by decide) p (sat_cons (step775 p h) (sat_cons (step1013 p h) (sat_cons (step1014 p h) (sat_cons (step59 p h) (sat_cons (step63 p h) (sat_nil p))))))
def c1719 : List Lit := [(1720, true), (73, true), (7, false)]
theorem step1719 (p : Nat → Bool) (h : Constraints p) : clause p c1719 = true :=
  Snake9.LocalRup.prove_clause [c804, c1294, c1305, c1303, c1296, c1297, c1298, c376, c366, c373] c1719 (by decide) p (sat_cons (step804 p h) (sat_cons (step1294 p h) (sat_cons (step1305 p h) (sat_cons (step1303 p h) (sat_cons (step1296 p h) (sat_cons (step1297 p h) (sat_cons (step1298 p h) (sat_cons (step376 p h) (sat_cons (step366 p h) (sat_cons (step373 p h) (sat_nil p)))))))))))
def c1720 : List Lit := [(311, true), (28, true), (23, false), (21, true)]
theorem step1720 (p : Nat → Bool) (h : Constraints p) : clause p c1720 = true :=
  Snake9.LocalRup.prove_clause [c778, c854, c855, c853, c848, c849, c847, c92, c85, c81] c1720 (by decide) p (sat_cons (step778 p h) (sat_cons (step854 p h) (sat_cons (step855 p h) (sat_cons (step853 p h) (sat_cons (step848 p h) (sat_cons (step849 p h) (sat_cons (step847 p h) (sat_cons (step92 p h) (sat_cons (step85 p h) (sat_cons (step81 p h) (sat_nil p)))))))))))
def c1721 : List Lit := [(1735, true), (86, true), (15, true)]
theorem step1721 (p : Nat → Bool) (h : Constraints p) : clause p c1721 = true :=
  Snake9.LocalRup.prove_clause [c808, c1328, c1330, c1326, c1322, c1323, c398, c385] c1721 (by decide) p (sat_cons (step808 p h) (sat_cons (step1328 p h) (sat_cons (step1330 p h) (sat_cons (step1326 p h) (sat_cons (step1322 p h) (sat_cons (step1323 p h) (sat_cons (step398 p h) (sat_cons (step385 p h) (sat_nil p)))))))))
def c1722 : List Lit := [(1711, true), (66, false), (27, false)]
theorem step1722 (p : Nat → Bool) (h : Constraints p) : clause p c1722 = true :=
  Snake9.LocalRup.prove_clause [c1286, c1288, c1284, c1280, c321] c1722 (by decide) p (sat_cons (step1286 p h) (sat_cons (step1288 p h) (sat_cons (step1284 p h) (sat_cons (step1280 p h) (sat_cons (step321 p h) (sat_nil p))))))
def c1723 : List Lit := [(1815, true), (100, false)]
theorem step1723 (p : Nat → Bool) (h : Constraints p) : clause p c1723 = true :=
  Snake9.LocalRup.prove_clause [c822, c1473, c1476, c1466, c1444, c1446, c1453, c1441, c1439, c712, c726, c729] c1723 (by decide) p (sat_cons (step822 p h) (sat_cons (step1473 p h) (sat_cons (step1476 p h) (sat_cons (step1466 p h) (sat_cons (step1444 p h) (sat_cons (step1446 p h) (sat_cons (step1453 p h) (sat_cons (step1441 p h) (sat_cons (step1439 p h) (sat_cons (step712 p h) (sat_cons (step726 p h) (sat_cons (step729 p h) (sat_nil p)))))))))))))
def c1724 : List Lit := [(1810, true), (101, false)]
theorem step1724 (p : Nat → Bool) (h : Constraints p) : clause p c1724 = true :=
  Snake9.LocalRup.prove_clause [c823, c1463, c1466, c1458, c1460, c1452, c1456, c738, c742, c741, c1639] c1724 (by decide) p (sat_cons (step823 p h) (sat_cons (step1463 p h) (sat_cons (step1466 p h) (sat_cons (step1458 p h) (sat_cons (step1460 p h) (sat_cons (step1452 p h) (sat_cons (step1456 p h) (sat_cons (step738 p h) (sat_cons (step742 p h) (sat_cons (step741 p h) (sat_cons (step1639 p h) (sat_nil p))))))))))))
def c1725 : List Lit := [(121, true), (122, false), (101, false)]
theorem step1725 (p : Nat → Bool) (h : Constraints p) : clause p c1725 = true :=
  Snake9.LocalRup.prove_clause [c823, c742, c741, c1639] c1725 (by decide) p (sat_cons (step823 p h) (sat_cons (step742 p h) (sat_cons (step741 p h) (sat_cons (step1639 p h) (sat_nil p)))))
def c1726 : List Lit := [(102, false), (122, false), (1784, true), (101, false)]
theorem step1726 (p : Nat → Bool) (h : Constraints p) : clause p c1726 = true :=
  Snake9.LocalRup.prove_clause [c626, c625, c1403, c1400, c1409] c1726 (by decide) p (sat_cons (step626 p h) (sat_cons (step625 p h) (sat_cons (step1403 p h) (sat_cons (step1400 p h) (sat_cons (step1409 p h) (sat_nil p))))))
def c1727 : List Lit := [(122, false), (1803, false), (1784, true), (1817, true), (101, false)]
theorem step1727 (p : Nat → Bool) (h : Constraints p) : clause p c1727 = true :=
  Snake9.LocalRup.prove_clause [c823, c1725, c1726, c743, c733, c1439, c1446, c1478, c1467, c1458, c1460, c1456, c738] c1727 (by decide) p (sat_cons (step823 p h) (sat_cons (step1725 p h) (sat_cons (step1726 p h) (sat_cons (step743 p h) (sat_cons (step733 p h) (sat_cons (step1439 p h) (sat_cons (step1446 p h) (sat_cons (step1478 p h) (sat_cons (step1467 p h) (sat_cons (step1458 p h) (sat_cons (step1460 p h) (sat_cons (step1456 p h) (sat_cons (step738 p h) (sat_nil p))))))))))))))
def c1728 : List Lit := [(118, false), (1797, true), (100, false)]
theorem step1728 (p : Nat → Bool) (h : Constraints p) : clause p c1728 = true :=
  Snake9.LocalRup.prove_clause [c822, c1442, c1441, c729, c713, c726] c1728 (by decide) p (sat_cons (step822 p h) (sat_cons (step1442 p h) (sat_cons (step1441 p h) (sat_cons (step729 p h) (sat_cons (step713 p h) (sat_cons (step726 p h) (sat_nil p)))))))
def c1729 : List Lit := [(1771, true), (115, false), (100, false)]
theorem step1729 (p : Nat → Bool) (h : Constraints p) : clause p c1729 = true :=
  Snake9.LocalRup.prove_clause [c813, c1386, c1387, c534, c571, c565] c1729 (by decide) p (sat_cons (step813 p h) (sat_cons (step1386 p h) (sat_cons (step1387 p h) (sat_cons (step534 p h) (sat_cons (step571 p h) (sat_cons (step565 p h) (sat_nil p)))))))
def c1730 : List Lit := [(114, false), (119, true), (1742, true), (100, false)]
theorem step1730 (p : Nat → Bool) (h : Constraints p) : clause p c1730 = true :=
  Snake9.LocalRup.prove_clause [c819, c698, c499, c496, c1336] c1730 (by decide) p (sat_cons (step819 p h) (sat_cons (step698 p h) (sat_cons (step499 p h) (sat_cons (step496 p h) (sat_cons (step1336 p h) (sat_nil p))))))
def c1731 : List Lit := [(119, true), (1742, true), (118, false), (1796, true), (1801, true), (117, true), (100, false)]
theorem step1731 (p : Nat → Bool) (h : Constraints p) : clause p c1731 = true :=
  Snake9.LocalRup.prove_clause [c822, c726, c1730, c1438, c1440, c1448, c711, c1443] c1731 (by decide) p (sat_cons (step822 p h) (sat_cons (step726 p h) (sat_cons (step1730 p h) (sat_cons (step1438 p h) (sat_cons (step1440 p h) (sat_cons (step1448 p h) (sat_cons (step711 p h) (sat_cons (step1443 p h) (sat_nil p)))))))))
def c1732 : List Lit := [(1783, true), (1773, true)]
theorem step1732 (p : Nat → Bool) (h : Constraints p) : clause p c1732 = true :=
  Snake9.LocalRup.prove_clause [c815, c1390, c1389, c1406, c1408, c1403, c1400, c1401, c636, c624, c678, c640] c1732 (by decide) p (sat_cons (step815 p h) (sat_cons (step1390 p h) (sat_cons (step1389 p h) (sat_cons (step1406 p h) (sat_cons (step1408 p h) (sat_cons (step1403 p h) (sat_cons (step1400 p h) (sat_cons (step1401 p h) (sat_cons (step636 p h) (sat_cons (step624 p h) (sat_cons (step678 p h) (sat_cons (step640 p h) (sat_nil p)))))))))))))
def c1733 : List Lit := [(1788, true), (122, false), (1783, false), (100, false), (101, false)]
theorem step1733 (p : Nat → Bool) (h : Constraints p) : clause p c1733 = true :=
  Snake9.LocalRup.prove_clause [c813, c815, c1415, c1419, c1407, c1726, c1394, c1386, c1387, c571, c565, c533, c1404, c1405, c1409, c1400, c1401, c636, c678, c640] c1733 (by decide) p (sat_cons (step813 p h) (sat_cons (step815 p h) (sat_cons (step1415 p h) (sat_cons (step1419 p h) (sat_cons (step1407 p h) (sat_cons (step1726 p h) (sat_cons (step1394 p h) (sat_cons (step1386 p h) (sat_cons (step1387 p h) (sat_cons (step571 p h) (sat_cons (step565 p h) (sat_cons (step533 p h) (sat_cons (step1404 p h) (sat_cons (step1405 p h) (sat_cons (step1409 p h) (sat_cons (step1400 p h) (sat_cons (step1401 p h) (sat_cons (step636 p h) (sat_cons (step678 p h) (sat_cons (step640 p h) (sat_nil p)))))))))))))))))))))
def c1734 : List Lit := [(9, false), (17, false), (1549, true)]
theorem step1734 (p : Nat → Bool) (h : Constraints p) : clause p c1734 = true :=
  Snake9.LocalRup.prove_clause [c772, c1000, c999, c17, c38, c35] c1734 (by decide) p (sat_cons (step772 p h) (sat_cons (step1000 p h) (sat_cons (step999 p h) (sat_cons (step17 p h) (sat_cons (step38 p h) (sat_cons (step35 p h) (sat_nil p)))))))
def c1735 : List Lit := [(114, false), (117, false), (1742, true), (100, false)]
theorem step1735 (p : Nat → Bool) (h : Constraints p) : clause p c1735 = true :=
  Snake9.LocalRup.prove_clause [c727, c1730] c1735 (by decide) p (sat_cons (step727 p h) (sat_cons (step1730 p h) (sat_nil p)))
def c1736 : List Lit := [(1807, true), (1790, true), (122, false), (1773, false)]
theorem step1736 (p : Nat → Bool) (h : Constraints p) : clause p c1736 = true :=
  Snake9.LocalRup.prove_clause [c826, c825, c1458, c1460, c1455, c1456, c767, c738, c761, c755, c747, c1705, c1401] c1736 (by decide) p (sat_cons (step826 p h) (sat_cons (step825 p h) (sat_cons (step1458 p h) (sat_cons (step1460 p h) (sat_cons (step1455 p h) (sat_cons (step1456 p h) (sat_cons (step767 p h) (sat_cons (step738 p h) (sat_cons (step761 p h) (sat_cons (step755 p h) (sat_cons (step747 p h) (sat_cons (step1705 p h) (sat_cons (step1401 p h) (sat_nil p))))))))))))))
def c1737 : List Lit := [(1735, true), (15, true), (17, false)]
theorem step1737 (p : Nat → Bool) (h : Constraints p) : clause p c1737 = true :=
  Snake9.LocalRup.prove_clause [c1328, c1330, c1721, c1326, c1322, c403] c1737 (by decide) p (sat_cons (step1328 p h) (sat_cons (step1330 p h) (sat_cons (step1721 p h) (sat_cons (step1326 p h) (sat_cons (step1322 p h) (sat_cons (step403 p h) (sat_nil p)))))))
def c1738 : List Lit := [(1781, true), (108, false), (83, false)]
theorem step1738 (p : Nat → Bool) (h : Constraints p) : clause p c1738 = true :=
  Snake9.LocalRup.prove_clause [c1403, c1404, c658] c1738 (by decide) p (sat_cons (step1403 p h) (sat_cons (step1404 p h) (sat_cons (step658 p h) (sat_nil p))))
def c1739 : List Lit := [(1779, true), (91, true), (89, true), (92, false), (93, false)]
theorem step1739 (p : Nat → Bool) (h : Constraints p) : clause p c1739 = true :=
  Snake9.LocalRup.prove_clause [c810, c1400, c1401, c493, c635, c467] c1739 (by decide) p (sat_cons (step810 p h) (sat_cons (step1400 p h) (sat_cons (step1401 p h) (sat_cons (step493 p h) (sat_cons (step635 p h) (sat_cons (step467 p h) (sat_nil p)))))))
def c1740 : List Lit := [(1771, true), (1743, true)]
theorem step1740 (p : Nat → Bool) (h : Constraints p) : clause p c1740 = true :=
  Snake9.LocalRup.prove_clause [c813, c1339, c1333, c1337, c1334, c1335, c450, c1386, c1387, c527, c567] c1740 (by decide) p (sat_cons (step813 p h) (sat_cons (step1339 p h) (sat_cons (step1333 p h) (sat_cons (step1337 p h) (sat_cons (step1334 p h) (sat_cons (step1335 p h) (sat_cons (step450 p h) (sat_cons (step1386 p h) (sat_cons (step1387 p h) (sat_cons (step527 p h) (sat_cons (step567 p h) (sat_nil p))))))))))))
def c1741 : List Lit := [(1827, true), (1783, false), (1771, false), (1807, false)]
theorem step1741 (p : Nat → Bool) (h : Constraints p) : clause p c1741 = true :=
  Snake9.LocalRup.prove_clause [c1394, c1419, c1463, c1473, c1504, c1424, c1395, c1497, c1390, c1474, c1477, c1467, c1444, c1453, c1728] c1741 (by decide) p (sat_cons (step1394 p h) (sat_cons (step1419 p h) (sat_cons (step1463 p h) (sat_cons (step1473 p h) (sat_cons (step1504 p h) (sat_cons (step1424 p h) (sat_cons (step1395 p h) (sat_cons (step1497 p h) (sat_cons (step1390 p h) (sat_cons (step1474 p h) (sat_cons (step1477 p h) (sat_cons (step1467 p h) (sat_cons (step1444 p h) (sat_cons (step1453 p h) (sat_cons (step1728 p h) (sat_nil p))))))))))))))))
def c1742 : List Lit := [(59, false), (55, false)]
theorem step1742 (p : Nat → Bool) (h : Constraints p) : clause p c1742 = true :=
  Snake9.LocalRup.prove_clause [c796, c293, c294, c1608] c1742 (by decide) p (sat_cons (step796 p h) (sat_cons (step293 p h) (sat_cons (step294 p h) (sat_cons (step1608 p h) (sat_nil p)))))
def c1743 : List Lit := [(59, false), (57, true), (188, true)]
theorem step1743 (p : Nat → Bool) (h : Constraints p) : clause p c1743 = true :=
  Snake9.LocalRup.prove_clause [c796, c293, c1742, c297] c1743 (by decide) p (sat_cons (step796 p h) (sat_cons (step293 p h) (sat_cons (step1742 p h) (sat_cons (step297 p h) (sat_nil p)))))
def c1744 : List Lit := [(74, false), (1720, true), (7, false)]
theorem step1744 (p : Nat → Bool) (h : Constraints p) : clause p c1744 = true :=
  Snake9.LocalRup.prove_clause [c1719, c1301, c364, c365, c1299] c1744 (by decide) p (sat_cons (step1719 p h) (sat_cons (step1301 p h) (sat_cons (step364 p h) (sat_cons (step365 p h) (sat_cons (step1299 p h) (sat_nil p))))))
def c1745 : List Lit := [(1549, false), (6, true), (1558, false), (1566, true)]
theorem step1745 (p : Nat → Bool) (h : Constraints p) : clause p c1745 = true :=
  Snake9.LocalRup.prove_clause [c772, c1017, c1035, c1002, c1005, c1031, c996, c1020, c1010, c1011, c5, c37] c1745 (by decide) p (sat_cons (step772 p h) (sat_cons (step1017 p h) (sat_cons (step1035 p h) (sat_cons (step1002 p h) (sat_cons (step1005 p h) (sat_cons (step1031 p h) (sat_cons (step996 p h) (sat_cons (step1020 p h) (sat_cons (step1010 p h) (sat_cons (step1011 p h) (sat_cons (step5 p h) (sat_cons (step37 p h) (sat_nil p)))))))))))))
def c1746 : List Lit := [(1624, true), (39, true), (49, true)]
theorem step1746 (p : Nat → Bool) (h : Constraints p) : clause p c1746 = true :=
  Snake9.LocalRup.prove_clause [c789, c1119, c1129, c1127, c1120, c1121, c1122, c197, c205] c1746 (by decide) p (sat_cons (step789 p h) (sat_cons (step1119 p h) (sat_cons (step1129 p h) (sat_cons (step1127 p h) (sat_cons (step1120 p h) (sat_cons (step1121 p h) (sat_cons (step1122 p h) (sat_cons (step197 p h) (sat_cons (step205 p h) (sat_nil p))))))))))
def c1747 : List Lit := [(35, true), (4, false), (11, false), (5, true)]
theorem step1747 (p : Nat → Bool) (h : Constraints p) : clause p c1747 = true :=
  Snake9.LocalRup.prove_clause [c769, c11, c10, c1587] c1747 (by decide) p (sat_cons (step769 p h) (sat_cons (step11 p h) (sat_cons (step10 p h) (sat_cons (step1587 p h) (sat_nil p)))))
def c1748 : List Lit := [(95, false), (73, false), (1772, true), (37, false)]
theorem step1748 (p : Nat → Bool) (h : Constraints p) : clause p c1748 = true :=
  Snake9.LocalRup.prove_clause [c504, c503, c1388] c1748 (by decide) p (sat_cons (step504 p h) (sat_cons (step503 p h) (sat_cons (step1388 p h) (sat_nil p))))
def c1749 : List Lit := [(73, false), (1726, true), (1772, true), (1707, false), (6, true), (37, false), (7, false)]
theorem step1749 (p : Nat → Bool) (h : Constraints p) : clause p c1749 = true :=
  Snake9.LocalRup.prove_clause [c803, c1748, c358, c361, c1744, c1283, c1315, c1289] c1749 (by decide) p (sat_cons (step803 p h) (sat_cons (step1748 p h) (sat_cons (step358 p h) (sat_cons (step361 p h) (sat_cons (step1744 p h) (sat_cons (step1283 p h) (sat_cons (step1315 p h) (sat_cons (step1289 p h) (sat_nil p)))))))))
def c1750 : List Lit := [(1712, true), (64, true), (50, false)]
theorem step1750 (p : Nat → Bool) (h : Constraints p) : clause p c1750 = true :=
  Snake9.LocalRup.prove_clause [c798, c1280, c1291, c1289, c1282, c1284, c306, c337] c1750 (by decide) p (sat_cons (step798 p h) (sat_cons (step1280 p h) (sat_cons (step1291 p h) (sat_cons (step1289 p h) (sat_cons (step1282 p h) (sat_cons (step1284 p h) (sat_cons (step306 p h) (sat_cons (step337 p h) (sat_nil p)))))))))
def c1751 : List Lit := [(1735, false), (1760, true), (1712, false), (1741, false), (6, true), (37, false), (7, false)]
theorem step1751 (p : Nat → Bool) (h : Constraints p) : clause p c1751 = true :=
  Snake9.LocalRup.prove_clause [c1679, c803, c1314, c1368, c1337, c1346, c1373, c1315, c1347, c1719, c1744, c1340, c1689, c358, c1333, c1615] c1751 (by decide) p (sat_cons (step1679 p h) (sat_cons (step803 p h) (sat_cons (step1314 p h) (sat_cons (step1368 p h) (sat_cons (step1337 p h) (sat_cons (step1346 p h) (sat_cons (step1373 p h) (sat_cons (step1315 p h) (sat_cons (step1347 p h) (sat_cons (step1719 p h) (sat_cons (step1744 p h) (sat_cons (step1340 p h) (sat_cons (step1689 p h) (sat_cons (step358 p h) (sat_cons (step1333 p h) (sat_cons (step1615 p h) (sat_nil p)))))))))))))))))
def c1752 : List Lit := [(1735, true), (8, false), (17, false)]
theorem step1752 (p : Nat → Bool) (h : Constraints p) : clause p c1752 = true :=
  Snake9.LocalRup.prove_clause [c1328, c1737, c1326, c53] c1752 (by decide) p (sat_cons (step1328 p h) (sat_cons (step1737 p h) (sat_cons (step1326 p h) (sat_cons (step53 p h) (sat_nil p)))))
def c1753 : List Lit := [(1720, true), (1772, true), (6, true), (37, false), (7, false)]
theorem step1753 (p : Nat → Bool) (h : Constraints p) : clause p c1753 = true :=
  Snake9.LocalRup.prove_clause [c803, c1719, c1744, c1748, c358] c1753 (by decide) p (sat_cons (step803 p h) (sat_cons (step1719 p h) (sat_cons (step1744 p h) (sat_cons (step1748 p h) (sat_cons (step358 p h) (sat_nil p))))))
def c1754 : List Lit := [(1736, true), (83, true), (81, false), (11, false)]
theorem step1754 (p : Nat → Bool) (h : Constraints p) : clause p c1754 = true :=
  Snake9.LocalRup.prove_clause [c1326, c1329, c1331, c1327, c1322, c389] c1754 (by decide) p (sat_cons (step1326 p h) (sat_cons (step1329 p h) (sat_cons (step1331 p h) (sat_cons (step1327 p h) (sat_cons (step1322 p h) (sat_cons (step389 p h) (sat_nil p)))))))
def c1755 : List Lit := [(74, false), (1725, true), (7, false)]
theorem step1755 (p : Nat → Bool) (h : Constraints p) : clause p c1755 = true :=
  Snake9.LocalRup.prove_clause [c1309, c1744, c1311, c1286, c1283, c361, c1715, c1294, c1304] c1755 (by decide) p (sat_cons (step1309 p h) (sat_cons (step1744 p h) (sat_cons (step1311 p h) (sat_cons (step1286 p h) (sat_cons (step1283 p h) (sat_cons (step361 p h) (sat_cons (step1715 p h) (sat_cons (step1294 p h) (sat_cons (step1304 p h) (sat_nil p))))))))))
def c1756 : List Lit := [(1773, true), (1826, true), (1783, false)]
theorem step1756 (p : Nat → Bool) (h : Constraints p) : clause p c1756 = true :=
  Snake9.LocalRup.prove_clause [c1414, c1493, c1474, c1470, c1389, c1390, c1724, c1723, c1477, c1496, c1444, c1733, c1728, c1454] c1756 (by decide) p (sat_cons (step1414 p h) (sat_cons (step1493 p h) (sat_cons (step1474 p h) (sat_cons (step1470 p h) (sat_cons (step1389 p h) (sat_cons (step1390 p h) (sat_cons (step1724 p h) (sat_cons (step1723 p h) (sat_cons (step1477 p h) (sat_cons (step1496 p h) (sat_cons (step1444 p h) (sat_cons (step1733 p h) (sat_cons (step1728 p h) (sat_cons (step1454 p h) (sat_nil p)))))))))))))))
def c1757 : List Lit := [(1826, true), (1783, false)]
theorem step1757 (p : Nat → Bool) (h : Constraints p) : clause p c1757 = true :=
  Snake9.LocalRup.prove_clause [c1503, c1424, c1393, c1756, c1392, c1419, c1496, c1473, c1723, c1724, c1391] c1757 (by decide) p (sat_cons (step1503 p h) (sat_cons (step1424 p h) (sat_cons (step1393 p h) (sat_cons (step1756 p h) (sat_cons (step1392 p h) (sat_cons (step1419 p h) (sat_cons (step1496 p h) (sat_cons (step1473 p h) (sat_cons (step1723 p h) (sat_cons (step1724 p h) (sat_cons (step1391 p h) (sat_nil p))))))))))))
def c1758 : List Lit := [(1810, true), (1711, true)]
theorem step1758 (p : Nat → Bool) (h : Constraints p) : clause p c1758 = true :=
  Snake9.LocalRup.prove_clause [c825, c1463, c1466, c1458, c1460, c1452, c1455, c1456, c767, c738, c1710, c756] c1758 (by decide) p (sat_cons (step825 p h) (sat_cons (step1463 p h) (sat_cons (step1466 p h) (sat_cons (step1458 p h) (sat_cons (step1460 p h) (sat_cons (step1452 p h) (sat_cons (step1455 p h) (sat_cons (step1456 p h) (sat_cons (step767 p h) (sat_cons (step738 p h) (sat_cons (step1710 p h) (sat_cons (step756 p h) (sat_nil p)))))))))))))
def c1759 : List Lit := [(1807, true), (122, false), (1711, true)]
theorem step1759 (p : Nat → Bool) (h : Constraints p) : clause p c1759 = true :=
  Snake9.LocalRup.prove_clause [c825, c1458, c1460, c1455, c1456, c767, c738, c1710, c756] c1759 (by decide) p (sat_cons (step825 p h) (sat_cons (step1458 p h) (sat_cons (step1460 p h) (sat_cons (step1455 p h) (sat_cons (step1456 p h) (sat_cons (step767 p h) (sat_cons (step738 p h) (sat_cons (step1710 p h) (sat_cons (step756 p h) (sat_nil p))))))))))
def c1760 : List Lit := [(1731, true), (79, false), (83, false)]
theorem step1760 (p : Nat → Bool) (h : Constraints p) : clause p c1760 = true :=
  Snake9.LocalRup.prove_clause [c1322, c1323, c385] c1760 (by decide) p (sat_cons (step1322 p h) (sat_cons (step1323 p h) (sat_cons (step385 p h) (sat_nil p))))
def c1761 : List Lit := [(100, false), (77, false), (76, false), (1721, true), (73, true)]
theorem step1761 (p : Nat → Bool) (h : Constraints p) : clause p c1761 = true :=
  Snake9.LocalRup.prove_clause [c379, c378, c1298, c1296, c1306] c1761 (by decide) p (sat_cons (step379 p h) (sat_cons (step378 p h) (sat_cons (step1298 p h) (sat_cons (step1296 p h) (sat_cons (step1306 p h) (sat_nil p))))))
def c1762 : List Lit := [(101, false), (122, false), (80, false), (70, false)]
theorem step1762 (p : Nat → Bool) (h : Constraints p) : clause p c1762 = true :=
  Snake9.LocalRup.prove_clause [c806, c382, c620, c387] c1762 (by decide) p (sat_cons (step806 p h) (sat_cons (step382 p h) (sat_cons (step620 p h) (sat_cons (step387 p h) (sat_nil p)))))
def c1763 : List Lit := [(101, false), (80, false), (1744, true), (70, false), (74, true)]
theorem step1763 (p : Nat → Bool) (h : Constraints p) : clause p c1763 = true :=
  Snake9.LocalRup.prove_clause [c801, c382, c347, c438, c436, c1335, c1333, c1340] c1763 (by decide) p (sat_cons (step801 p h) (sat_cons (step382 p h) (sat_cons (step347 p h) (sat_cons (step438 p h) (sat_cons (step436 p h) (sat_cons (step1335 p h) (sat_cons (step1333 p h) (sat_cons (step1340 p h) (sat_nil p)))))))))
def c1764 : List Lit := [(98, false), (96, false), (1741, true)]
theorem step1764 (p : Nat → Bool) (h : Constraints p) : clause p c1764 = true :=
  Snake9.LocalRup.prove_clause [c813, c1335, c1334, c456, c568, c566] c1764 (by decide) p (sat_cons (step813 p h) (sat_cons (step1335 p h) (sat_cons (step1334 p h) (sat_cons (step456 p h) (sat_cons (step568 p h) (sat_cons (step566 p h) (sat_nil p)))))))
def c1765 : List Lit := [(127, false), (1801, true), (116, false), (115, false), (94, true), (255, true), (112, true)]
theorem step1765 (p : Nat → Bool) (h : Constraints p) : clause p c1765 = true :=
  Snake9.LocalRup.prove_clause [c819, c766, c724, c713, c698, c1441, c1440, c1450] c1765 (by decide) p (sat_cons (step819 p h) (sat_cons (step766 p h) (sat_cons (step724 p h) (sat_cons (step713 p h) (sat_cons (step698 p h) (sat_cons (step1441 p h) (sat_cons (step1440 p h) (sat_cons (step1450 p h) (sat_nil p)))))))))
def c1766 : List Lit := [(126, false), (124, false), (127, true)]
theorem step1766 (p : Nat → Bool) (h : Constraints p) : clause p c1766 = true :=
  Snake9.LocalRup.prove_clause [c826, c760, c762, c1644] c1766 (by decide) p (sat_cons (step826 p h) (sat_cons (step760 p h) (sat_cons (step762 p h) (sat_cons (step1644 p h) (sat_nil p)))))
def c1767 : List Lit := [(114, false), (124, false), (94, true), (93, false)]
theorem step1767 (p : Nat → Bool) (h : Constraints p) : clause p c1767 = true :=
  Snake9.LocalRup.prove_clause [c819, c693, c699] c1767 (by decide) p (sat_cons (step819 p h) (sat_cons (step693 p h) (sat_cons (step699 p h) (sat_nil p))))
def c1768 : List Lit := [(1601, true), (1560, false)]
theorem step1768 (p : Nat → Bool) (h : Constraints p) : clause p c1768 = true :=
  Snake9.LocalRup.prove_clause [c1714, c1025, c1086, c1083, c1030, c1716, c1004, c997] c1768 (by decide) p (sat_cons (step1714 p h) (sat_cons (step1025 p h) (sat_cons (step1086 p h) (sat_cons (step1083 p h) (sat_cons (step1030 p h) (sat_cons (step1716 p h) (sat_cons (step1004 p h) (sat_cons (step997 p h) (sat_nil p)))))))))
def c1769 : List Lit := [(1629, true), (32, true), (93, false), (1613, false)]
theorem step1769 (p : Nat → Bool) (h : Constraints p) : clause p c1769 = true :=
  Snake9.LocalRup.prove_clause [c789, c1105, c1113, c1145, c1142, c1116, c1124, c1126, c1106, c1121, c1122, c1118, c153, c197, c207] c1769 (by decide) p (sat_cons (step789 p h) (sat_cons (step1105 p h) (sat_cons (step1113 p h) (sat_cons (step1145 p h) (sat_cons (step1142 p h) (sat_cons (step1116 p h) (sat_cons (step1124 p h) (sat_cons (step1126 p h) (sat_cons (step1106 p h) (sat_cons (step1121 p h) (sat_cons (step1122 p h) (sat_cons (step1118 p h) (sat_cons (step153 p h) (sat_cons (step197 p h) (sat_cons (step207 p h) (sat_nil p))))))))))))))))
def c1770 : List Lit := [(1797, true), (118, false), (111, true)]
theorem step1770 (p : Nat → Bool) (h : Constraints p) : clause p c1770 = true :=
  Snake9.LocalRup.prove_clause [c820, c1441, c1442, c713, c701] c1770 (by decide) p (sat_cons (step820 p h) (sat_cons (step1441 p h) (sat_cons (step1442 p h) (sat_cons (step713 p h) (sat_cons (step701 p h) (sat_nil p))))))
def c1771 : List Lit := [(1771, true), (1741, true)]
theorem step1771 (p : Nat → Bool) (h : Constraints p) : clause p c1771 = true :=
  Snake9.LocalRup.prove_clause [c1386, c1387, c1764] c1771 (by decide) p (sat_cons (step1386 p h) (sat_cons (step1387 p h) (sat_cons (step1764 p h) (sat_nil p))))
def c1772 : List Lit := [(1629, true), (35, false), (88, false), (1741, true), (1613, false)]
theorem step1772 (p : Nat → Bool) (h : Constraints p) : clause p c1772 = true :=
  Snake9.LocalRup.prove_clause [c1335, c1334, c1110, c1138, c1769, c1129, c149, c1119, c1120, c1127, c104, c1122, c1712, c187] c1772 (by decide) p (sat_cons (step1335 p h) (sat_cons (step1334 p h) (sat_cons (step1110 p h) (sat_cons (step1138 p h) (sat_cons (step1769 p h) (sat_cons (step1129 p h) (sat_cons (step149 p h) (sat_cons (step1119 p h) (sat_cons (step1120 p h) (sat_cons (step1127 p h) (sat_cons (step104 p h) (sat_cons (step1122 p h) (sat_cons (step1712 p h) (sat_cons (step187 p h) (sat_nil p)))))))))))))))
end B112E036
