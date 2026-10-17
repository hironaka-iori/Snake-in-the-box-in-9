import B112E121Part0000
namespace B112E121
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1788 : List Lit := [(1119, true)]
theorem step1788 (p : Nat → Bool) (h : Constraints p) : clause p c1788 = true :=
  Snake9.LocalRup.prove_clause [c934, c1565, c1568, c1558, c1545, c1556, c1542, c1543, c878, c860] c1788 (by decide) p (sat_cons (step934 p h) (sat_cons (step1565 p h) (sat_cons (step1568 p h) (sat_cons (step1558 p h) (sat_cons (step1545 p h) (sat_cons (step1556 p h) (sat_cons (step1542 p h) (sat_cons (step1543 p h) (sat_cons (step878 p h) (sat_cons (step860 p h) (sat_nil p)))))))))))
def c1789 : List Lit := [(5, false), (3, true), (6, true), (133, true), (21, false)]
theorem step1789 (p : Nat → Bool) (h : Constraints p) : clause p c1789 = true :=
  Snake9.LocalRup.prove_clause [c883, c18, c26, c1656] c1789 (by decide) p (sat_cons (step883 p h) (sat_cons (step18 p h) (sat_cons (step26 p h) (sat_cons (step1656 p h) (sat_nil p)))))
def c1790 : List Lit := [(897, false), (906, true), (13, true), (887, false), (14, false), (9, false), (22, true)]
theorem step1790 (p : Nat → Bool) (h : Constraints p) : clause p c1790 = true :=
  Snake9.LocalRup.prove_clause [c887, c1142, c1147, c1177, c1158, c1161, c1181, c1153, c1148, c1143, c328, c84, c179] c1790 (by decide) p (sat_cons (step887 p h) (sat_cons (step1142 p h) (sat_cons (step1147 p h) (sat_cons (step1177 p h) (sat_cons (step1158 p h) (sat_cons (step1161 p h) (sat_cons (step1181 p h) (sat_cons (step1153 p h) (sat_cons (step1148 p h) (sat_cons (step1143 p h) (sat_cons (step328 p h) (sat_cons (step84 p h) (sat_cons (step179 p h) (sat_nil p))))))))))))))
def c1791 : List Lit := [(895, true), (897, true), (14, false)]
theorem step1791 (p : Nat → Bool) (h : Constraints p) : clause p c1791 = true :=
  Snake9.LocalRup.prove_clause [c892, c1156, c1155, c1152, c1153, c348, c363, c330, c379] c1791 (by decide) p (sat_cons (step892 p h) (sat_cons (step1156 p h) (sat_cons (step1155 p h) (sat_cons (step1152 p h) (sat_cons (step1153 p h) (sat_cons (step348 p h) (sat_cons (step363 p h) (sat_cons (step330 p h) (sat_cons (step379 p h) (sat_nil p))))))))))
def c1792 : List Lit := [(19, false), (10, false), (30, true), (13, true), (28, false)]
theorem step1792 (p : Nat → Bool) (h : Constraints p) : clause p c1792 = true :=
  Snake9.LocalRup.prove_clause [c888, c196, c205] c1792 (by decide) p (sat_cons (step888 p h) (sat_cons (step196 p h) (sat_cons (step205 p h) (sat_nil p))))
def c1793 : List Lit := [(1095, true)]
theorem step1793 (p : Nat → Bool) (h : Constraints p) : clause p c1793 = true :=
  Snake9.LocalRup.prove_clause [c926, c1518, c1522, c1510, c1512, c1498, c1507, c1508, c1504, c1490, c1491, c836, c822, c821] c1793 (by decide) p (sat_cons (step926 p h) (sat_cons (step1518 p h) (sat_cons (step1522 p h) (sat_cons (step1510 p h) (sat_cons (step1512 p h) (sat_cons (step1498 p h) (sat_cons (step1507 p h) (sat_cons (step1508 p h) (sat_cons (step1504 p h) (sat_cons (step1490 p h) (sat_cons (step1491 p h) (sat_cons (step836 p h) (sat_cons (step822 p h) (sat_cons (step821 p h) (sat_nil p)))))))))))))))
def c1794 : List Lit := [(1091, true), (1026, true), (1085, true), (61, true)]
theorem step1794 (p : Nat → Bool) (h : Constraints p) : clause p c1794 = true :=
  Snake9.LocalRup.prove_clause [c928, c926, c1510, c1512, c1507, c1508, c1504, c1505, c840, c823, c843, c822, c787, c796, c821, c1401, c1493, c753, c1502, c1492] c1794 (by decide) p (sat_cons (step928 p h) (sat_cons (step926 p h) (sat_cons (step1510 p h) (sat_cons (step1512 p h) (sat_cons (step1507 p h) (sat_cons (step1508 p h) (sat_cons (step1504 p h) (sat_cons (step1505 p h) (sat_cons (step840 p h) (sat_cons (step823 p h) (sat_cons (step843 p h) (sat_cons (step822 p h) (sat_cons (step787 p h) (sat_cons (step796 p h) (sat_cons (step821 p h) (sat_cons (step1401 p h) (sat_cons (step1493 p h) (sat_cons (step753 p h) (sat_cons (step1502 p h) (sat_cons (step1492 p h) (sat_nil p)))))))))))))))))))))
def c1795 : List Lit := [(101, true), (1089, true), (1084, true), (61, true)]
theorem step1795 (p : Nat → Bool) (h : Constraints p) : clause p c1795 = true :=
  Snake9.LocalRup.prove_clause [c928, c1508, c1507, c1497, c1493, c1495, c1499, c1490, c761, c836, c843] c1795 (by decide) p (sat_cons (step928 p h) (sat_cons (step1508 p h) (sat_cons (step1507 p h) (sat_cons (step1497 p h) (sat_cons (step1493 p h) (sat_cons (step1495 p h) (sat_cons (step1499 p h) (sat_cons (step1490 p h) (sat_cons (step761 p h) (sat_cons (step836 p h) (sat_cons (step843 p h) (sat_nil p))))))))))))
def c1796 : List Lit := [(78, false), (101, false), (70, true), (20, true)]
theorem step1796 (p : Nat → Bool) (h : Constraints p) : clause p c1796 = true :=
  Snake9.LocalRup.prove_clause [c915, c564, c565, c1706] c1796 (by decide) p (sat_cons (step915 p h) (sat_cons (step564 p h) (sat_cons (step565 p h) (sat_cons (step1706 p h) (sat_nil p)))))
def c1797 : List Lit := [(1089, true), (1084, true), (1026, true), (70, true), (20, true), (61, true)]
theorem step1797 (p : Nat → Bool) (h : Constraints p) : clause p c1797 = true :=
  Snake9.LocalRup.prove_clause [c928, c1507, c1508, c1795, c839, c843, c1796, c1401, c753, c755, c1490, c1494, c1499] c1797 (by decide) p (sat_cons (step928 p h) (sat_cons (step1507 p h) (sat_cons (step1508 p h) (sat_cons (step1795 p h) (sat_cons (step839 p h) (sat_cons (step843 p h) (sat_cons (step1796 p h) (sat_cons (step1401 p h) (sat_cons (step753 p h) (sat_cons (step755 p h) (sat_cons (step1490 p h) (sat_cons (step1494 p h) (sat_cons (step1499 p h) (sat_nil p))))))))))))))
def c1798 : List Lit := [(99, false), (109, false), (77, false), (1084, true)]
theorem step1798 (p : Nat → Bool) (h : Constraints p) : clause p c1798 = true :=
  Snake9.LocalRup.prove_clause [c753, c755, c1490, c1494, c1499] c1798 (by decide) p (sat_cons (step753 p h) (sat_cons (step755 p h) (sat_cons (step1490 p h) (sat_cons (step1494 p h) (sat_cons (step1499 p h) (sat_nil p))))))
def c1799 : List Lit := [(109, false), (77, false), (1084, true), (101, false), (61, true)]
theorem step1799 (p : Nat → Bool) (h : Constraints p) : clause p c1799 = true :=
  Snake9.LocalRup.prove_clause [c928, c1798, c843, c844, c1721] c1799 (by decide) p (sat_cons (step928 p h) (sat_cons (step1798 p h) (sat_cons (step843 p h) (sat_cons (step844 p h) (sat_cons (step1721 p h) (sat_nil p))))))
def c1800 : List Lit := [(1092, true), (108, false), (109, true), (101, false), (1089, false)]
theorem step1800 (p : Nat → Bool) (h : Constraints p) : clause p c1800 = true :=
  Snake9.LocalRup.prove_clause [c1511, c1513, c1509, c1504, c837] c1800 (by decide) p (sat_cons (step1511 p h) (sat_cons (step1513 p h) (sat_cons (step1509 p h) (sat_cons (step1504 p h) (sat_cons (step837 p h) (sat_nil p))))))
def c1801 : List Lit := [(73, true), (74, false), (16, true), (70, true), (77, false)]
theorem step1801 (p : Nat → Bool) (h : Constraints p) : clause p c1801 = true :=
  Snake9.LocalRup.prove_clause [c913, c551, c552, c1705] c1801 (by decide) p (sat_cons (step913 p h) (sat_cons (step551 p h) (sat_cons (step552 p h) (sat_cons (step1705 p h) (sat_nil p)))))
def c1802 : List Lit := [(86, false), (82, true), (79, false), (30, true), (107, false)]
theorem step1802 (p : Nat → Bool) (h : Constraints p) : clause p c1802 = true :=
  Snake9.LocalRup.prove_clause [c918, c589, c593] c1802 (by decide) p (sat_cons (step918 p h) (sat_cons (step589 p h) (sat_cons (step593 p h) (sat_nil p))))
def c1803 : List Lit := [(1115, true), (123, false), (107, false)]
theorem step1803 (p : Nat → Bool) (h : Constraints p) : clause p c1803 = true :=
  Snake9.LocalRup.prove_clause [c1558, c1560, c1555, c1552, c876] c1803 (by decide) p (sat_cons (step1558 p h) (sat_cons (step1560 p h) (sat_cons (step1555 p h) (sat_cons (step1552 p h) (sat_cons (step876 p h) (sat_nil p))))))
def c1804 : List Lit := [(1041, true), (81, false)]
theorem step1804 (p : Nat → Bool) (h : Constraints p) : clause p c1804 = true :=
  Snake9.LocalRup.prove_clause [c917, c1427, c1428, c591, c590] c1804 (by decide) p (sat_cons (step917 p h) (sat_cons (step1427 p h) (sat_cons (step1428 p h) (sat_cons (step591 p h) (sat_cons (step590 p h) (sat_nil p))))))
def c1805 : List Lit := [(109, false), (99, true), (61, true), (103, false), (93, false)]
theorem step1805 (p : Nat → Bool) (h : Constraints p) : clause p c1805 = true :=
  Snake9.LocalRup.prove_clause [c928, c844, c815] c1805 (by decide) p (sat_cons (step928 p h) (sat_cons (step844 p h) (sat_cons (step815 p h) (sat_nil p))))
def c1806 : List Lit := [(77, false), (202, true), (99, true), (71, false), (85, true), (93, false)]
theorem step1806 (p : Nat → Bool) (h : Constraints p) : clause p c1806 = true :=
  Snake9.LocalRup.prove_clause [c914, c542, c558, c559, c556, c1705] c1806 (by decide) p (sat_cons (step914 p h) (sat_cons (step542 p h) (sat_cons (step558 p h) (sat_cons (step559 p h) (sat_cons (step556 p h) (sat_cons (step1705 p h) (sat_nil p)))))))
def c1807 : List Lit := [(327, false), (3, true), (35, false), (43, true), (25, true)]
theorem step1807 (p : Nat → Bool) (h : Constraints p) : clause p c1807 = true :=
  Snake9.LocalRup.prove_clause [c1749, c1739, c895, c1728, c1727, c986, c988, c989, c984, c994, c392, c982, c384, c978, c382, c977] c1807 (by decide) p (sat_cons (step1749 p h) (sat_cons (step1739 p h) (sat_cons (step895 p h) (sat_cons (step1728 p h) (sat_cons (step1727 p h) (sat_cons (step986 p h) (sat_cons (step988 p h) (sat_cons (step989 p h) (sat_cons (step984 p h) (sat_cons (step994 p h) (sat_cons (step392 p h) (sat_cons (step982 p h) (sat_cons (step384 p h) (sat_cons (step978 p h) (sat_cons (step382 p h) (sat_cons (step977 p h) (sat_nil p)))))))))))))))))
def c1808 : List Lit := [(61, false), (60, false), (68, false), (969, true), (951, false)]
theorem step1808 (p : Nat → Bool) (h : Constraints p) : clause p c1808 = true :=
  Snake9.LocalRup.prove_clause [c494, c497, c1272, c1286, c1277, c1288, c1303] c1808 (by decide) p (sat_cons (step494 p h) (sat_cons (step497 p h) (sat_cons (step1272 p h) (sat_cons (step1286 p h) (sat_cons (step1277 p h) (sat_cons (step1288 p h) (sat_cons (step1303 p h) (sat_nil p))))))))
def c1809 : List Lit := [(963, true), (61, true), (60, false)]
theorem step1809 (p : Nat → Bool) (h : Constraints p) : clause p c1809 = true :=
  Snake9.LocalRup.prove_clause [c907, c1288, c1290, c1286, c1282, c479, c477] c1809 (by decide) p (sat_cons (step907 p h) (sat_cons (step1288 p h) (sat_cons (step1290 p h) (sat_cons (step1286 p h) (sat_cons (step1282 p h) (sat_cons (step479 p h) (sat_cons (step477 p h) (sat_nil p))))))))
def c1810 : List Lit := [(947, true), (43, true), (25, true), (13, false), (71, false)]
theorem step1810 (p : Nat → Bool) (h : Constraints p) : clause p c1810 = true :=
  Snake9.LocalRup.prove_clause [c898, c1249, c1763, c1769, c1263, c1255, c1758, c1761, c1240, c397, c119, c395, c1807, c985] c1810 (by decide) p (sat_cons (step898 p h) (sat_cons (step1249 p h) (sat_cons (step1763 p h) (sat_cons (step1769 p h) (sat_cons (step1263 p h) (sat_cons (step1255 p h) (sat_cons (step1758 p h) (sat_cons (step1761 p h) (sat_cons (step1240 p h) (sat_cons (step397 p h) (sat_cons (step119 p h) (sat_cons (step395 p h) (sat_cons (step1807 p h) (sat_cons (step985 p h) (sat_nil p)))))))))))))))
def c1811 : List Lit := [(1084, true), (92, true), (101, true), (51, false)]
theorem step1811 (p : Nat → Bool) (h : Constraints p) : clause p c1811 = true :=
  Snake9.LocalRup.prove_clause [c924, c1493, c1497, c1499, c1495, c1490, c1491, c743, c721, c736] c1811 (by decide) p (sat_cons (step924 p h) (sat_cons (step1493 p h) (sat_cons (step1497 p h) (sat_cons (step1499 p h) (sat_cons (step1495 p h) (sat_cons (step1490 p h) (sat_cons (step1491 p h) (sat_cons (step743 p h) (sat_cons (step721 p h) (sat_cons (step736 p h) (sat_nil p)))))))))))
def c1812 : List Lit := [(1089, true), (96, false), (99, true), (61, true)]
theorem step1812 (p : Nat → Bool) (h : Constraints p) : clause p c1812 = true :=
  Snake9.LocalRup.prove_clause [c928, c1507, c1508, c843, c836] c1812 (by decide) p (sat_cons (step928 p h) (sat_cons (step1507 p h) (sat_cons (step1508 p h) (sat_cons (step843 p h) (sat_cons (step836 p h) (sat_nil p))))))
def c1813 : List Lit := [(47, false), (56, true), (71, false)]
theorem step1813 (p : Nat → Bool) (h : Constraints p) : clause p c1813 = true :=
  Snake9.LocalRup.prove_clause [c902, c426, c1681, c424] c1813 (by decide) p (sat_cons (step902 p h) (sat_cons (step426 p h) (sat_cons (step1681 p h) (sat_cons (step424 p h) (sat_nil p)))))
def c1814 : List Lit := [(4, false), (9, false), (6, true), (53, false)]
theorem step1814 (p : Nat → Bool) (h : Constraints p) : clause p c1814 = true :=
  Snake9.LocalRup.prove_clause [c882, c210, c12] c1814 (by decide) p (sat_cons (step882 p h) (sat_cons (step210 p h) (sat_cons (step12 p h) (sat_nil p))))
def c1815 : List Lit := [(1091, true), (1026, true), (1085, true), (68, false), (51, false)]
theorem step1815 (p : Nat → Bool) (h : Constraints p) : clause p c1815 = true :=
  Snake9.LocalRup.prove_clause [c1510, c1794, c1507, c496] c1815 (by decide) p (sat_cons (step1510 p h) (sat_cons (step1794 p h) (sat_cons (step1507 p h) (sat_cons (step496 p h) (sat_nil p)))))
def c1816 : List Lit := [(1043, true)]
theorem step1816 (p : Nat → Bool) (h : Constraints p) : clause p c1816 = true :=
  Snake9.LocalRup.prove_clause [c1430, c1432, c1804, c1424] c1816 (by decide) p (sat_cons (step1430 p h) (sat_cons (step1432 p h) (sat_cons (step1804 p h) (sat_cons (step1424 p h) (sat_nil p)))))
def c1817 : List Lit := [(1056, true)]
theorem step1817 (p : Nat → Bool) (h : Constraints p) : clause p c1817 = true :=
  Snake9.LocalRup.prove_clause [c1816, c1784, c1454] c1817 (by decide) p (sat_cons (step1816 p h) (sat_cons (step1784 p h) (sat_cons (step1454 p h) (sat_nil p))))
def c1818 : List Lit := [(1064, true)]
theorem step1818 (p : Nat → Bool) (h : Constraints p) : clause p c1818 = true :=
  Snake9.LocalRup.prove_clause [c1817, c1466] c1818 (by decide) p (sat_cons (step1817 p h) (sat_cons (step1466 p h) (sat_nil p)))
def c1819 : List Lit := [(1027, true), (101, false), (9, false), (53, false)]
theorem step1819 (p : Nat → Bool) (h : Constraints p) : clause p c1819 = true :=
  Snake9.LocalRup.prove_clause [c1402, c1404, c1399, c1396, c524, c229, c1796] c1819 (by decide) p (sat_cons (step1402 p h) (sat_cons (step1404 p h) (sat_cons (step1399 p h) (sat_cons (step1396 p h) (sat_cons (step524 p h) (sat_cons (step229 p h) (sat_cons (step1796 p h) (sat_nil p))))))))
def c1820 : List Lit := [(78, false), (20, true), (9, false), (1067, true), (101, false), (53, false)]
theorem step1820 (p : Nat → Bool) (h : Constraints p) : clause p c1820 = true :=
  Snake9.LocalRup.prove_clause [c915, c1784, c1819, c766, c1796, c563, c522, c575, c1388, c1425, c1391, c1415, c1478, c1458, c1435, c1433, c1426, c1804] c1820 (by decide) p (sat_cons (step915 p h) (sat_cons (step1784 p h) (sat_cons (step1819 p h) (sat_cons (step766 p h) (sat_cons (step1796 p h) (sat_cons (step563 p h) (sat_cons (step522 p h) (sat_cons (step575 p h) (sat_cons (step1388 p h) (sat_cons (step1425 p h) (sat_cons (step1391 p h) (sat_cons (step1415 p h) (sat_cons (step1478 p h) (sat_cons (step1458 p h) (sat_cons (step1435 p h) (sat_cons (step1433 p h) (sat_cons (step1426 p h) (sat_cons (step1804 p h) (sat_nil p)))))))))))))))))))
def c1821 : List Lit := [(1019, false), (70, false), (1025, false), (1027, false), (9, false), (1067, true), (92, false), (71, false)]
theorem step1821 (p : Nat → Bool) (h : Constraints p) : clause p c1821 = true :=
  Snake9.LocalRup.prove_clause [c1817, c1816, c1482, c1416, c1415, c1405, c1478, c1396, c1455, c525, c1448, c1438, c1439, c1446, c675, c1441] c1821 (by decide) p (sat_cons (step1817 p h) (sat_cons (step1816 p h) (sat_cons (step1482 p h) (sat_cons (step1416 p h) (sat_cons (step1415 p h) (sat_cons (step1405 p h) (sat_cons (step1478 p h) (sat_cons (step1396 p h) (sat_cons (step1455 p h) (sat_cons (step525 p h) (sat_cons (step1448 p h) (sat_cons (step1438 p h) (sat_cons (step1439 p h) (sat_cons (step1446 p h) (sat_cons (step675 p h) (sat_cons (step1441 p h) (sat_nil p)))))))))))))))))
def c1822 : List Lit := [(70, false), (1025, false), (71, false), (1027, false), (9, false), (1067, true), (92, false)]
theorem step1822 (p : Nat → Bool) (h : Constraints p) : clause p c1822 = true :=
  Snake9.LocalRup.prove_clause [c1816, c1821, c1391, c1388, c523, c521, c1438, c1396, c1405, c1411, c1478, c1455, c1448, c1446, c1439, c1441, c675] c1822 (by decide) p (sat_cons (step1816 p h) (sat_cons (step1821 p h) (sat_cons (step1391 p h) (sat_cons (step1388 p h) (sat_cons (step523 p h) (sat_cons (step521 p h) (sat_cons (step1438 p h) (sat_cons (step1396 p h) (sat_cons (step1405 p h) (sat_cons (step1411 p h) (sat_cons (step1478 p h) (sat_cons (step1455 p h) (sat_cons (step1448 p h) (sat_cons (step1446 p h) (sat_cons (step1439 p h) (sat_cons (step1441 p h) (sat_cons (step675 p h) (sat_nil p))))))))))))))))))
def c1823 : List Lit := [(90, false), (92, false), (71, false), (1052, true)]
theorem step1823 (p : Nat → Bool) (h : Constraints p) : clause p c1823 = true :=
  Snake9.LocalRup.prove_clause [c679, c675, c1440, c1437, c1446] c1823 (by decide) p (sat_cons (step679 p h) (sat_cons (step675 p h) (sat_cons (step1440 p h) (sat_cons (step1437 p h) (sat_cons (step1446 p h) (sat_nil p))))))
def c1824 : List Lit := [(92, false), (71, false), (1052, true)]
theorem step1824 (p : Nat → Bool) (h : Constraints p) : clause p c1824 = true :=
  Snake9.LocalRup.prove_clause [c1444, c1823, c1441, c1442, c1446, c676, c1437] c1824 (by decide) p (sat_cons (step1444 p h) (sat_cons (step1823 p h) (sat_cons (step1441 p h) (sat_cons (step1442 p h) (sat_cons (step1446 p h) (sat_cons (step676 p h) (sat_cons (step1437 p h) (sat_nil p))))))))
def c1825 : List Lit := [(1047, true), (92, true), (69, false)]
theorem step1825 (p : Nat → Bool) (h : Constraints p) : clause p c1825 = true :=
  Snake9.LocalRup.prove_clause [c920, c1437, c1438, c642, c607] c1825 (by decide) p (sat_cons (step920 p h) (sat_cons (step1437 p h) (sat_cons (step1438 p h) (sat_cons (step642 p h) (sat_cons (step607 p h) (sat_nil p))))))
def c1826 : List Lit := [(1111, true), (122, true), (101, false)]
theorem step1826 (p : Nat → Bool) (h : Constraints p) : clause p c1826 = true :=
  Snake9.LocalRup.prove_clause [c933, c1552, c1553, c870, c873] c1826 (by decide) p (sat_cons (step933 p h) (sat_cons (step1552 p h) (sat_cons (step1553 p h) (sat_cons (step870 p h) (sat_cons (step873 p h) (sat_nil p))))))
def c1827 : List Lit := [(1084, true), (94, true), (95, false), (89, false)]
theorem step1827 (p : Nat → Bool) (h : Constraints p) : clause p c1827 = true :=
  Snake9.LocalRup.prove_clause [c1491, c1501, c1499, c1492, c1494, c718] c1827 (by decide) p (sat_cons (step1491 p h) (sat_cons (step1501 p h) (sat_cons (step1499 p h) (sat_cons (step1492 p h) (sat_cons (step1494 p h) (sat_cons (step718 p h) (sat_nil p)))))))
def c1828 : List Lit := [(79, true), (1044, true)]
theorem step1828 (p : Nat → Bool) (h : Constraints p) : clause p c1828 = true :=
  Snake9.LocalRup.prove_clause [c1435, c1425, c1426, c1433, c1804] c1828 (by decide) p (sat_cons (step1435 p h) (sat_cons (step1425 p h) (sat_cons (step1426 p h) (sat_cons (step1433 p h) (sat_cons (step1804 p h) (sat_nil p))))))
def c1829 : List Lit := [(82, false), (1044, true), (71, false)]
theorem step1829 (p : Nat → Bool) (h : Constraints p) : clause p c1829 = true :=
  Snake9.LocalRup.prove_clause [c1828, c584, c583, c1427, c1424, c1433] c1829 (by decide) p (sat_cons (step1828 p h) (sat_cons (step584 p h) (sat_cons (step583 p h) (sat_cons (step1427 p h) (sat_cons (step1424 p h) (sat_cons (step1433 p h) (sat_nil p)))))))
def c1830 : List Lit := [(889, false), (905, true), (897, false), (13, false), (71, false)]
theorem step1830 (p : Nat → Bool) (h : Constraints p) : clause p c1830 = true :=
  Snake9.LocalRup.prove_clause [c1158, c1176, c1144, c1147, c1172, c1138, c1161, c169, c1153] c1830 (by decide) p (sat_cons (step1158 p h) (sat_cons (step1176 p h) (sat_cons (step1144 p h) (sat_cons (step1147 p h) (sat_cons (step1172 p h) (sat_cons (step1138 p h) (sat_cons (step1161 p h) (sat_cons (step169 p h) (sat_cons (step1153 p h) (sat_nil p))))))))))
def c1831 : List Lit := [(27, false), (20, true), (74, false), (9, false)]
theorem step1831 (p : Nat → Bool) (h : Constraints p) : clause p c1831 = true :=
  Snake9.LocalRup.prove_clause [c890, c339, c188] c1831 (by decide) p (sat_cons (step890 p h) (sat_cons (step339 p h) (sat_cons (step188 p h) (sat_nil p))))
def c1832 : List Lit := [(980, true), (953, false), (13, false), (940, false), (71, false)]
theorem step1832 (p : Nat → Bool) (h : Constraints p) : clause p c1832 = true :=
  Snake9.LocalRup.prove_clause [c1274, c1298, c1768, c1328, c1322, c1263, c1302, c1758, c1277, c1240, c1268, c176] c1832 (by decide) p (sat_cons (step1274 p h) (sat_cons (step1298 p h) (sat_cons (step1768 p h) (sat_cons (step1328 p h) (sat_cons (step1322 p h) (sat_cons (step1263 p h) (sat_cons (step1302 p h) (sat_cons (step1758 p h) (sat_cons (step1277 p h) (sat_cons (step1240 p h) (sat_cons (step1268 p h) (sat_cons (step176 p h) (sat_nil p)))))))))))))
def c1833 : List Lit := [(109, false), (108, true), (99, true), (101, false), (93, false)]
theorem step1833 (p : Nat → Bool) (h : Constraints p) : clause p c1833 = true :=
  Snake9.LocalRup.prove_clause [c928, c814, c841] c1833 (by decide) p (sat_cons (step928 p h) (sat_cons (step814 p h) (sat_cons (step841 p h) (sat_nil p))))
def c1834 : List Lit := [(35, false), (882, true), (14, true), (13, false), (71, false)]
theorem step1834 (p : Nat → Bool) (h : Constraints p) : clause p c1834 = true :=
  Snake9.LocalRup.prove_clause [c140, c119, c155, c1100, c1086, c1105, c1094, c1110, c1121] c1834 (by decide) p (sat_cons (step140 p h) (sat_cons (step119 p h) (sat_cons (step155 p h) (sat_cons (step1100 p h) (sat_cons (step1086 p h) (sat_cons (step1105 p h) (sat_cons (step1094 p h) (sat_cons (step1110 p h) (sat_cons (step1121 p h) (sat_nil p))))))))))
def c1835 : List Lit := [(874, false), (881, true), (13, false), (71, false)]
theorem step1835 (p : Nat → Bool) (h : Constraints p) : clause p c1835 = true :=
  Snake9.LocalRup.prove_clause [c1116, c1107, c1110, c1120, c1100, c1094, c99, c1086] c1835 (by decide) p (sat_cons (step1116 p h) (sat_cons (step1107 p h) (sat_cons (step1110 p h) (sat_cons (step1120 p h) (sat_cons (step1100 p h) (sat_cons (step1094 p h) (sat_cons (step99 p h) (sat_cons (step1086 p h) (sat_nil p)))))))))
def c1836 : List Lit := [(1, false), (9, false)]
theorem step1836 (p : Nat → Bool) (h : Constraints p) : clause p c1836 = true :=
  Snake9.LocalRup.prove_clause [c880, c1, c2, c1650] c1836 (by decide) p (sat_cons (step880 p h) (sat_cons (step1 p h) (sat_cons (step2 p h) (sat_cons (step1650 p h) (sat_nil p)))))
def c1837 : List Lit := [(27, true), (904, true), (13, false), (71, false)]
theorem step1837 (p : Nat → Bool) (h : Constraints p) : clause p c1837 = true :=
  Snake9.LocalRup.prove_clause [c1167, c1163, c1152, c1154, c1160, c169, c1171, c1138, c1146] c1837 (by decide) p (sat_cons (step1167 p h) (sat_cons (step1163 p h) (sat_cons (step1152 p h) (sat_cons (step1154 p h) (sat_cons (step1160 p h) (sat_cons (step169 p h) (sat_cons (step1171 p h) (sat_cons (step1138 p h) (sat_cons (step1146 p h) (sat_nil p))))))))))
def c1838 : List Lit := [(25, false), (877, true), (14, true), (13, false), (71, false)]
theorem step1838 (p : Nat → Bool) (h : Constraints p) : clause p c1838 = true :=
  Snake9.LocalRup.prove_clause [c153, c138, c1105, c1100, c1110] c1838 (by decide) p (sat_cons (step153 p h) (sat_cons (step138 p h) (sat_cons (step1105 p h) (sat_cons (step1100 p h) (sat_cons (step1110 p h) (sat_nil p))))))
def c1839 : List Lit := [(868, false), (915, true), (14, true), (13, false), (71, false)]
theorem step1839 (p : Nat → Bool) (h : Constraints p) : clause p c1839 = true :=
  Snake9.LocalRup.prove_clause [c890, c1214, c1103, c1106, c1126, c1124, c1201, c1167, c1837, c1838, c1153, c1160, c1161, c1171, c1155, c1156, c1144, c348, c1141, c1142, c337, c230] c1839 (by decide) p (sat_cons (step890 p h) (sat_cons (step1214 p h) (sat_cons (step1103 p h) (sat_cons (step1106 p h) (sat_cons (step1126 p h) (sat_cons (step1124 p h) (sat_cons (step1201 p h) (sat_cons (step1167 p h) (sat_cons (step1837 p h) (sat_cons (step1838 p h) (sat_cons (step1153 p h) (sat_cons (step1160 p h) (sat_cons (step1161 p h) (sat_cons (step1171 p h) (sat_cons (step1155 p h) (sat_cons (step1156 p h) (sat_cons (step1144 p h) (sat_cons (step348 p h) (sat_cons (step1141 p h) (sat_cons (step1142 p h) (sat_cons (step337 p h) (sat_cons (step230 p h) (sat_nil p)))))))))))))))))))))))
def c1840 : List Lit := [(915, true), (1, true), (14, true), (13, false), (71, false)]
theorem step1840 (p : Nat → Bool) (h : Constraints p) : clause p c1840 = true :=
  Snake9.LocalRup.prove_clause [c1839, c1097, c1088, c114, c105, c117, c1138, c1105, c1153, c1146, c1835, c1160, c1201, c1171] c1840 (by decide) p (sat_cons (step1839 p h) (sat_cons (step1097 p h) (sat_cons (step1088 p h) (sat_cons (step114 p h) (sat_cons (step105 p h) (sat_cons (step117 p h) (sat_cons (step1138 p h) (sat_cons (step1105 p h) (sat_cons (step1153 p h) (sat_cons (step1146 p h) (sat_cons (step1835 p h) (sat_cons (step1160 p h) (sat_cons (step1201 p h) (sat_cons (step1171 p h) (sat_nil p)))))))))))))))
def c1841 : List Lit := [(968, true), (59, true), (92, true)]
theorem step1841 (p : Nat → Bool) (h : Constraints p) : clause p c1841 = true :=
  Snake9.LocalRup.prove_clause [c902, c1286, c1288, c1296, c1299, c1289, c1291, c1276, c1287, c1283, c1268, c424, c469] c1841 (by decide) p (sat_cons (step902 p h) (sat_cons (step1286 p h) (sat_cons (step1288 p h) (sat_cons (step1296 p h) (sat_cons (step1299 p h) (sat_cons (step1289 p h) (sat_cons (step1291 p h) (sat_cons (step1276 p h) (sat_cons (step1287 p h) (sat_cons (step1283 p h) (sat_cons (step1268 p h) (sat_cons (step424 p h) (sat_cons (step469 p h) (sat_nil p))))))))))))))
def c1842 : List Lit := [(867, false), (874, false), (9, true), (915, true), (13, false), (71, false)]
theorem step1842 (p : Nat → Bool) (h : Constraints p) : clause p c1842 = true :=
  Snake9.LocalRup.prove_clause [c1101, c1110, c1214, c1122, c1121, c1113, c1207, c1102, c1166, c138, c1160, c1153] c1842 (by decide) p (sat_cons (step1101 p h) (sat_cons (step1110 p h) (sat_cons (step1214 p h) (sat_cons (step1122 p h) (sat_cons (step1121 p h) (sat_cons (step1113 p h) (sat_cons (step1207 p h) (sat_cons (step1102 p h) (sat_cons (step1166 p h) (sat_cons (step138 p h) (sat_cons (step1160 p h) (sat_cons (step1153 p h) (sat_nil p)))))))))))))
def c1843 : List Lit := [(11, false), (905, true), (1, false), (13, false), (71, false)]
theorem step1843 (p : Nat → Bool) (h : Constraints p) : clause p c1843 = true :=
  Snake9.LocalRup.prove_clause [c880, c1, c150, c153, c31, c1153, c1140, c1160, c1149, c1176] c1843 (by decide) p (sat_cons (step880 p h) (sat_cons (step1 p h) (sat_cons (step150 p h) (sat_cons (step153 p h) (sat_cons (step31 p h) (sat_cons (step1153 p h) (sat_cons (step1140 p h) (sat_cons (step1160 p h) (sat_cons (step1149 p h) (sat_cons (step1176 p h) (sat_nil p)))))))))))
def c1844 : List Lit := [(915, true), (14, true), (13, false), (71, false)]
theorem step1844 (p : Nat → Bool) (h : Constraints p) : clause p c1844 = true :=
  Snake9.LocalRup.prove_clause [c1103, c1840, c1836, c1101, c1109, c1115, c1195, c1843, c1105, c1835, c1842, c1201, c1094, c1086, c114, c117, c1138, c1153, c1146, c1160, c1171] c1844 (by decide) p (sat_cons (step1103 p h) (sat_cons (step1840 p h) (sat_cons (step1836 p h) (sat_cons (step1101 p h) (sat_cons (step1109 p h) (sat_cons (step1115 p h) (sat_cons (step1195 p h) (sat_cons (step1843 p h) (sat_cons (step1105 p h) (sat_cons (step1835 p h) (sat_cons (step1842 p h) (sat_cons (step1201 p h) (sat_cons (step1094 p h) (sat_cons (step1086 p h) (sat_cons (step114 p h) (sat_cons (step117 p h) (sat_cons (step1138 p h) (sat_cons (step1153 p h) (sat_cons (step1146 p h) (sat_cons (step1160 p h) (sat_cons (step1171 p h) (sat_nil p))))))))))))))))))))))
def c1845 : List Lit := [(46, true), (980, true), (13, false), (940, false), (71, false)]
theorem step1845 (p : Nat → Bool) (h : Constraints p) : clause p c1845 = true :=
  Snake9.LocalRup.prove_clause [c1768, c1322, c1302, c1279, c1269, c1270, c1276, c176, c1298, c1240, c1328, c1758, c1263] c1845 (by decide) p (sat_cons (step1768 p h) (sat_cons (step1322 p h) (sat_cons (step1302 p h) (sat_cons (step1279 p h) (sat_cons (step1269 p h) (sat_cons (step1270 p h) (sat_cons (step1276 p h) (sat_cons (step176 p h) (sat_cons (step1298 p h) (sat_cons (step1240 p h) (sat_cons (step1328 p h) (sat_cons (step1758 p h) (sat_cons (step1263 p h) (sat_nil p))))))))))))))
def c1846 : List Lit := [(940, false), (980, true), (13, false), (92, true), (71, false)]
theorem step1846 (p : Nat → Bool) (h : Constraints p) : clause p c1846 = true :=
  Snake9.LocalRup.prove_clause [c907, c1768, c1832, c1845, c1322, c1272, c1841, c433, c480, c491, c1285, c1288, c1295, c1299, c1328, c1276, c1263, c1268, c1758, c176, c1240] c1846 (by decide) p (sat_cons (step907 p h) (sat_cons (step1768 p h) (sat_cons (step1832 p h) (sat_cons (step1845 p h) (sat_cons (step1322 p h) (sat_cons (step1272 p h) (sat_cons (step1841 p h) (sat_cons (step433 p h) (sat_cons (step480 p h) (sat_cons (step491 p h) (sat_cons (step1285 p h) (sat_cons (step1288 p h) (sat_cons (step1295 p h) (sat_cons (step1299 p h) (sat_cons (step1328 p h) (sat_cons (step1276 p h) (sat_cons (step1263 p h) (sat_cons (step1268 p h) (sat_cons (step1758 p h) (sat_cons (step176 p h) (sat_cons (step1240 p h) (sat_nil p))))))))))))))))))))))
def c1847 : List Lit := [(968, false), (1001, true), (14, true), (13, false), (71, false)]
theorem step1847 (p : Nat → Bool) (h : Constraints p) : clause p c1847 = true :=
  Snake9.LocalRup.prove_clause [c1844, c1345, c1777, c1322, c1350, c1770, c1758, c1240, c174, c171, c1834, c1153, c1138, c1208, c1160, c1146, c1171] c1847 (by decide) p (sat_cons (step1844 p h) (sat_cons (step1345 p h) (sat_cons (step1777 p h) (sat_cons (step1322 p h) (sat_cons (step1350 p h) (sat_cons (step1770 p h) (sat_cons (step1758 p h) (sat_cons (step1240 p h) (sat_cons (step174 p h) (sat_cons (step171 p h) (sat_cons (step1834 p h) (sat_cons (step1153 p h) (sat_cons (step1138 p h) (sat_cons (step1208 p h) (sat_cons (step1160 p h) (sat_cons (step1146 p h) (sat_cons (step1171 p h) (sat_nil p))))))))))))))))))
def c1848 : List Lit := [(51, false), (46, false), (59, false), (968, true), (44, false), (91, true)]
theorem step1848 (p : Nat → Bool) (h : Constraints p) : clause p c1848 = true :=
  Snake9.LocalRup.prove_clause [c907, c901, c433, c480, c419, c491, c414, c1285, c1271, c1288, c1274, c1299] c1848 (by decide) p (sat_cons (step907 p h) (sat_cons (step901 p h) (sat_cons (step433 p h) (sat_cons (step480 p h) (sat_cons (step419 p h) (sat_cons (step491 p h) (sat_cons (step414 p h) (sat_cons (step1285 p h) (sat_cons (step1271 p h) (sat_cons (step1288 p h) (sat_cons (step1274 p h) (sat_cons (step1299 p h) (sat_nil p)))))))))))))
def c1849 : List Lit := [(953, false), (968, true), (92, true)]
theorem step1849 (p : Nat → Bool) (h : Constraints p) : clause p c1849 = true :=
  Snake9.LocalRup.prove_clause [c902, c1302, c1274, c1277, c1299, c1268, c1288, c1290, c424, c1285, c1283, c469] c1849 (by decide) p (sat_cons (step902 p h) (sat_cons (step1302 p h) (sat_cons (step1274 p h) (sat_cons (step1277 p h) (sat_cons (step1299 p h) (sat_cons (step1268 p h) (sat_cons (step1288 p h) (sat_cons (step1290 p h) (sat_cons (step424 p h) (sat_cons (step1285 p h) (sat_cons (step1283 p h) (sat_cons (step469 p h) (sat_nil p)))))))))))))
def c1850 : List Lit := [(51, false), (59, false), (91, true), (968, true), (44, false)]
theorem step1850 (p : Nat → Bool) (h : Constraints p) : clause p c1850 = true :=
  Snake9.LocalRup.prove_clause [c1848, c1269, c1276, c1299, c1288, c1285, c491, c1809] c1850 (by decide) p (sat_cons (step1848 p h) (sat_cons (step1269 p h) (sat_cons (step1276 p h) (sat_cons (step1299 p h) (sat_cons (step1288 p h) (sat_cons (step1285 p h) (sat_cons (step491 p h) (sat_cons (step1809 p h) (sat_nil p)))))))))
def c1851 : List Lit := [(1001, true), (91, true), (82, true), (92, true), (71, false)]
theorem step1851 (p : Nat → Bool) (h : Constraints p) : clause p c1851 = true :=
  Snake9.LocalRup.prove_clause [c912, c536, c535, c1677, c1844, c1345, c1846, c1763, c1248, c1847, c1841, c1849, c1272, c1850] c1851 (by decide) p (sat_cons (step912 p h) (sat_cons (step536 p h) (sat_cons (step535 p h) (sat_cons (step1677 p h) (sat_cons (step1844 p h) (sat_cons (step1345 p h) (sat_cons (step1846 p h) (sat_cons (step1763 p h) (sat_cons (step1248 p h) (sat_cons (step1847 p h) (sat_cons (step1841 p h) (sat_cons (step1849 p h) (sat_cons (step1272 p h) (sat_cons (step1850 p h) (sat_nil p)))))))))))))))
end B112E121
