import B112E097Part0002
namespace B112E097
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1787 : List Lit := [(101, true), (86, false), (1063, true), (1057, true)]
theorem step1787 (p : Nat → Bool) (h : Constraints p) : clause p c1787 = true :=
  Snake9.LocalRup.prove_clause [c740, c1465, c736, c1779, c1321, c1311, c1322, c1310, c621, c631, c662, c1762, c1457, c1663, c632, c627, c678, c685, c672, c1172, c684, c1326, c1328, c1757, c1745, c1173, c1026, c1033, c1262, c1259, c1268, c1277, c1783, c1343, c1318, c1784, c1781, c1438, c1786, c1601, c560, c558, c486, c593, c1275, c1308, c1285, c1315, c1299, c1339, c1392] c1787 (by decide) p (sat_cons (step740 p h) (sat_cons (step1465 p h) (sat_cons (step736 p h) (sat_cons (step1779 p h) (sat_cons (step1321 p h) (sat_cons (step1311 p h) (sat_cons (step1322 p h) (sat_cons (step1310 p h) (sat_cons (step621 p h) (sat_cons (step631 p h) (sat_cons (step662 p h) (sat_cons (step1762 p h) (sat_cons (step1457 p h) (sat_cons (step1663 p h) (sat_cons (step632 p h) (sat_cons (step627 p h) (sat_cons (step678 p h) (sat_cons (step685 p h) (sat_cons (step672 p h) (sat_cons (step1172 p h) (sat_cons (step684 p h) (sat_cons (step1326 p h) (sat_cons (step1328 p h) (sat_cons (step1757 p h) (sat_cons (step1745 p h) (sat_cons (step1173 p h) (sat_cons (step1026 p h) (sat_cons (step1033 p h) (sat_cons (step1262 p h) (sat_cons (step1259 p h) (sat_cons (step1268 p h) (sat_cons (step1277 p h) (sat_cons (step1783 p h) (sat_cons (step1343 p h) (sat_cons (step1318 p h) (sat_cons (step1784 p h) (sat_cons (step1781 p h) (sat_cons (step1438 p h) (sat_cons (step1786 p h) (sat_cons (step1601 p h) (sat_cons (step560 p h) (sat_cons (step558 p h) (sat_cons (step486 p h) (sat_cons (step593 p h) (sat_cons (step1275 p h) (sat_cons (step1308 p h) (sat_cons (step1285 p h) (sat_cons (step1315 p h) (sat_cons (step1299 p h) (sat_cons (step1339 p h) (sat_cons (step1392 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1788 : List Lit := [(111, false), (88, true), (101, false), (107, true), (115, false)]
theorem step1788 (p : Nat → Bool) (h : Constraints p) : clause p c1788 = true :=
  Snake9.LocalRup.prove_clause [c736, c483, c560] c1788 (by decide) p (sat_cons (step736 p h) (sat_cons (step483 p h) (sat_cons (step560 p h) (sat_nil p))))
def c1789 : List Lit := [(102, false), (1045, true), (101, false), (106, true), (114, false)]
theorem step1789 (p : Nat → Bool) (h : Constraints p) : clause p c1789 = true :=
  Snake9.LocalRup.prove_clause [c473, c474, c1273, c1278, c1283] c1789 (by decide) p (sat_cons (step473 p h) (sat_cons (step474 p h) (sat_cons (step1273 p h) (sat_cons (step1278 p h) (sat_cons (step1283 p h) (sat_nil p))))))
def c1790 : List Lit := [(109, true), (111, true), (101, false), (86, false), (107, true), (1107, true), (1044, false), (995, false), (1068, false), (100, true), (95, true), (106, true), (116, true), (115, false), (114, false)]
theorem step1790 (p : Nat → Bool) (h : Constraints p) : clause p c1790 = true :=
  Snake9.LocalRup.prove_clause [c738, c734, c1615, c729, c1750, c1421, c1262, c1259, c1268, c1298, c1309, c1318, c1343, c1385, c1399, c1775, c1438, c1306, c1781, c1188, c1185, c1789, c611, c446, c403, c477, c1261, c884, c1272, c885, c1264, c889, c418, c892, c381, c882, c405, c873] c1790 (by decide) p (sat_cons (step738 p h) (sat_cons (step734 p h) (sat_cons (step1615 p h) (sat_cons (step729 p h) (sat_cons (step1750 p h) (sat_cons (step1421 p h) (sat_cons (step1262 p h) (sat_cons (step1259 p h) (sat_cons (step1268 p h) (sat_cons (step1298 p h) (sat_cons (step1309 p h) (sat_cons (step1318 p h) (sat_cons (step1343 p h) (sat_cons (step1385 p h) (sat_cons (step1399 p h) (sat_cons (step1775 p h) (sat_cons (step1438 p h) (sat_cons (step1306 p h) (sat_cons (step1781 p h) (sat_cons (step1188 p h) (sat_cons (step1185 p h) (sat_cons (step1789 p h) (sat_cons (step611 p h) (sat_cons (step446 p h) (sat_cons (step403 p h) (sat_cons (step477 p h) (sat_cons (step1261 p h) (sat_cons (step884 p h) (sat_cons (step1272 p h) (sat_cons (step885 p h) (sat_cons (step1264 p h) (sat_cons (step889 p h) (sat_cons (step418 p h) (sat_cons (step892 p h) (sat_cons (step381 p h) (sat_cons (step882 p h) (sat_cons (step405 p h) (sat_cons (step873 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))
def c1791 : List Lit := [(1002, true), (92, false), (109, false), (88, true), (1063, true), (1057, true)]
theorem step1791 (p : Nat → Bool) (h : Constraints p) : clause p c1791 = true :=
  Snake9.LocalRup.prove_clause [c740, c1465, c1666, c712, c1755, c1459, c1321, c1311, c1322, c1310, c621, c631, c662, c1026, c1033, c1185, c1186, c398, c392, c589, c1043, c945, c1735, c1717, c1016, c1643, c1115, c1082, c1058, c1702, c1048, c1027, c1039, c1040, c1718, c225, c216] c1791 (by decide) p (sat_cons (step740 p h) (sat_cons (step1465 p h) (sat_cons (step1666 p h) (sat_cons (step712 p h) (sat_cons (step1755 p h) (sat_cons (step1459 p h) (sat_cons (step1321 p h) (sat_cons (step1311 p h) (sat_cons (step1322 p h) (sat_cons (step1310 p h) (sat_cons (step621 p h) (sat_cons (step631 p h) (sat_cons (step662 p h) (sat_cons (step1026 p h) (sat_cons (step1033 p h) (sat_cons (step1185 p h) (sat_cons (step1186 p h) (sat_cons (step398 p h) (sat_cons (step392 p h) (sat_cons (step589 p h) (sat_cons (step1043 p h) (sat_cons (step945 p h) (sat_cons (step1735 p h) (sat_cons (step1717 p h) (sat_cons (step1016 p h) (sat_cons (step1643 p h) (sat_cons (step1115 p h) (sat_cons (step1082 p h) (sat_cons (step1058 p h) (sat_cons (step1702 p h) (sat_cons (step1048 p h) (sat_cons (step1027 p h) (sat_cons (step1039 p h) (sat_cons (step1040 p h) (sat_cons (step1718 p h) (sat_cons (step225 p h) (sat_cons (step216 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))
def c1792 : List Lit := [(894, true), (109, false), (113, false)]
theorem step1792 (p : Nat → Bool) (h : Constraints p) : clause p c1792 = true :=
  Snake9.LocalRup.prove_clause [c995, c1735, c992, c574] c1792 (by decide) p (sat_cons (step995 p h) (sat_cons (step1735 p h) (sat_cons (step992 p h) (sat_cons (step574 p h) (sat_nil p)))))
def c1793 : List Lit := [(1020, false), (906, false), (1073, false), (101, false), (1085, false), (1044, false), (1033, false), (46, true), (95, true), (106, true), (116, true), (114, false)]
theorem step1793 (p : Nat → Bool) (h : Constraints p) : clause p c1793 = true :=
  Snake9.LocalRup.prove_clause [c1465, c1699, c738, c709, c1762, c1457, c1026, c1033, c1259, c1268, c1438, c1437, c1392, c1458, c1303, c1299, c1106, c1271, c1789, c1082, c1261, c611, c1058, c1702, c399, c1027, c1043, c1728, c1048, c155, c1718] c1793 (by decide) p (sat_cons (step1465 p h) (sat_cons (step1699 p h) (sat_cons (step738 p h) (sat_cons (step709 p h) (sat_cons (step1762 p h) (sat_cons (step1457 p h) (sat_cons (step1026 p h) (sat_cons (step1033 p h) (sat_cons (step1259 p h) (sat_cons (step1268 p h) (sat_cons (step1438 p h) (sat_cons (step1437 p h) (sat_cons (step1392 p h) (sat_cons (step1458 p h) (sat_cons (step1303 p h) (sat_cons (step1299 p h) (sat_cons (step1106 p h) (sat_cons (step1271 p h) (sat_cons (step1789 p h) (sat_cons (step1082 p h) (sat_cons (step1261 p h) (sat_cons (step611 p h) (sat_cons (step1058 p h) (sat_cons (step1702 p h) (sat_cons (step399 p h) (sat_cons (step1027 p h) (sat_cons (step1043 p h) (sat_cons (step1728 p h) (sat_cons (step1048 p h) (sat_cons (step155 p h) (sat_cons (step1718 p h) (sat_nil p))))))))))))))))))))))))))))))))
def c1794 : List Lit := [(88, true), (86, false), (1063, true), (1057, true)]
theorem step1794 (p : Nat → Bool) (h : Constraints p) : clause p c1794 = true :=
  Snake9.TreeRup.prove_clause [c740, c1465, c1666, c738, c1787, c1779, c1321, c1311, c1322, c1310, c621, c631, c662, c1762, c1457, c1663, c1277, c678, c632, c627, c1259, c684, c685, c1326, c1328, c672, c1172, c1757, c1747, c1745, c1173, c1175, c1205, c1262, c1788, c1790, c1307, c1315, c1339, c1792, c1016, c1793, c1781, c1188, c1749, c1791, c611, c463, c1789, c1133, c1304, c1136, c1398, c1157, c1429, c1231, c1238, c1210, c1158, c1178, c1752, c1168] c1794 (by decide) p (sat_cons (step740 p h) (sat_cons (step1465 p h) (sat_cons (step1666 p h) (sat_cons (step738 p h) (sat_cons (step1787 p h) (sat_cons (step1779 p h) (sat_cons (step1321 p h) (sat_cons (step1311 p h) (sat_cons (step1322 p h) (sat_cons (step1310 p h) (sat_cons (step621 p h) (sat_cons (step631 p h) (sat_cons (step662 p h) (sat_cons (step1762 p h) (sat_cons (step1457 p h) (sat_cons (step1663 p h) (sat_cons (step1277 p h) (sat_cons (step678 p h) (sat_cons (step632 p h) (sat_cons (step627 p h) (sat_cons (step1259 p h) (sat_cons (step684 p h) (sat_cons (step685 p h) (sat_cons (step1326 p h) (sat_cons (step1328 p h) (sat_cons (step672 p h) (sat_cons (step1172 p h) (sat_cons (step1757 p h) (sat_cons (step1747 p h) (sat_cons (step1745 p h) (sat_cons (step1173 p h) (sat_cons (step1175 p h) (sat_cons (step1205 p h) (sat_cons (step1262 p h) (sat_cons (step1788 p h) (sat_cons (step1790 p h) (sat_cons (step1307 p h) (sat_cons (step1315 p h) (sat_cons (step1339 p h) (sat_cons (step1792 p h) (sat_cons (step1016 p h) (sat_cons (step1793 p h) (sat_cons (step1781 p h) (sat_cons (step1188 p h) (sat_cons (step1749 p h) (sat_cons (step1791 p h) (sat_cons (step611 p h) (sat_cons (step463 p h) (sat_cons (step1789 p h) (sat_cons (step1133 p h) (sat_cons (step1304 p h) (sat_cons (step1136 p h) (sat_cons (step1398 p h) (sat_cons (step1157 p h) (sat_cons (step1429 p h) (sat_cons (step1231 p h) (sat_cons (step1238 p h) (sat_cons (step1210 p h) (sat_cons (step1158 p h) (sat_cons (step1178 p h) (sat_cons (step1752 p h) (sat_cons (step1168 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1795 : List Lit := [(86, false), (1063, true), (1057, true)]
theorem step1795 (p : Nat → Bool) (h : Constraints p) : clause p c1795 = true :=
  Snake9.LocalRup.prove_clause [c740, c1465, c1666, c1779, c1321, c1311, c1322, c1310, c621, c631, c662, c1762, c1457, c1663, c1277, c678, c632, c627, c1259, c684, c685, c1326, c1328, c672, c1172, c1757, c1747, c1745, c1173, c1262, c1787, c1794, c1601, c1599, c1307, c1790, c1186, c1315, c1792, c1188, c1339, c1016, c1781, c1793] c1795 (by decide) p (sat_cons (step740 p h) (sat_cons (step1465 p h) (sat_cons (step1666 p h) (sat_cons (step1779 p h) (sat_cons (step1321 p h) (sat_cons (step1311 p h) (sat_cons (step1322 p h) (sat_cons (step1310 p h) (sat_cons (step621 p h) (sat_cons (step631 p h) (sat_cons (step662 p h) (sat_cons (step1762 p h) (sat_cons (step1457 p h) (sat_cons (step1663 p h) (sat_cons (step1277 p h) (sat_cons (step678 p h) (sat_cons (step632 p h) (sat_cons (step627 p h) (sat_cons (step1259 p h) (sat_cons (step684 p h) (sat_cons (step685 p h) (sat_cons (step1326 p h) (sat_cons (step1328 p h) (sat_cons (step672 p h) (sat_cons (step1172 p h) (sat_cons (step1757 p h) (sat_cons (step1747 p h) (sat_cons (step1745 p h) (sat_cons (step1173 p h) (sat_cons (step1262 p h) (sat_cons (step1787 p h) (sat_cons (step1794 p h) (sat_cons (step1601 p h) (sat_cons (step1599 p h) (sat_cons (step1307 p h) (sat_cons (step1790 p h) (sat_cons (step1186 p h) (sat_cons (step1315 p h) (sat_cons (step1792 p h) (sat_cons (step1188 p h) (sat_cons (step1339 p h) (sat_cons (step1016 p h) (sat_cons (step1781 p h) (sat_cons (step1793 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))
def c1796 : List Lit := [(894, true), (1056, true), (113, false)]
theorem step1796 (p : Nat → Bool) (h : Constraints p) : clause p c1796 = true :=
  Snake9.LocalRup.prove_clause [c995, c1735, c1792, c992, c1309, c575] c1796 (by decide) p (sat_cons (step995 p h) (sat_cons (step1735 p h) (sat_cons (step1792 p h) (sat_cons (step992 p h) (sat_cons (step1309 p h) (sat_cons (step575 p h) (sat_nil p)))))))
def c1797 : List Lit := [(1063, true), (1057, true)]
theorem step1797 (p : Nat → Bool) (h : Constraints p) : clause p c1797 = true :=
  Snake9.TreeRup.prove_clause [c740, c1465, c1699, c1666, c1695, c1311, c1310, c1321, c1322, c621, c1663, c632, c631, c1277, c627, c678, c672, c684, c662, c685, c1259, c1262, c1172, c1026, c1326, c1268, c1033, c1328, c1745, c1173, c1757, c1298, c1747, c1762, c1457, c1795, c1183, c1190, c1781, c1438, c1437, c1385, c1458, c1343, c1106, c1318, c1796, c1016, c1082, c1702, c1027, c1706, c1057, c1062, c1081, c1034, c1114, c1028, c1029, c984, c1709, c1638, c172, c932, c924] c1797 (by decide) p (sat_cons (step740 p h) (sat_cons (step1465 p h) (sat_cons (step1699 p h) (sat_cons (step1666 p h) (sat_cons (step1695 p h) (sat_cons (step1311 p h) (sat_cons (step1310 p h) (sat_cons (step1321 p h) (sat_cons (step1322 p h) (sat_cons (step621 p h) (sat_cons (step1663 p h) (sat_cons (step632 p h) (sat_cons (step631 p h) (sat_cons (step1277 p h) (sat_cons (step627 p h) (sat_cons (step678 p h) (sat_cons (step672 p h) (sat_cons (step684 p h) (sat_cons (step662 p h) (sat_cons (step685 p h) (sat_cons (step1259 p h) (sat_cons (step1262 p h) (sat_cons (step1172 p h) (sat_cons (step1026 p h) (sat_cons (step1326 p h) (sat_cons (step1268 p h) (sat_cons (step1033 p h) (sat_cons (step1328 p h) (sat_cons (step1745 p h) (sat_cons (step1173 p h) (sat_cons (step1757 p h) (sat_cons (step1298 p h) (sat_cons (step1747 p h) (sat_cons (step1762 p h) (sat_cons (step1457 p h) (sat_cons (step1795 p h) (sat_cons (step1183 p h) (sat_cons (step1190 p h) (sat_cons (step1781 p h) (sat_cons (step1438 p h) (sat_cons (step1437 p h) (sat_cons (step1385 p h) (sat_cons (step1458 p h) (sat_cons (step1343 p h) (sat_cons (step1106 p h) (sat_cons (step1318 p h) (sat_cons (step1796 p h) (sat_cons (step1016 p h) (sat_cons (step1082 p h) (sat_cons (step1702 p h) (sat_cons (step1027 p h) (sat_cons (step1706 p h) (sat_cons (step1057 p h) (sat_cons (step1062 p h) (sat_cons (step1081 p h) (sat_cons (step1034 p h) (sat_cons (step1114 p h) (sat_cons (step1028 p h) (sat_cons (step1029 p h) (sat_cons (step984 p h) (sat_cons (step1709 p h) (sat_cons (step1638 p h) (sat_cons (step172 p h) (sat_cons (step932 p h) (sat_cons (step924 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1798 : List Lit := [(46, true), (959, true), (906, false)]
theorem step1798 (p : Nat → Bool) (h : Constraints p) : clause p c1798 = true :=
  Snake9.LocalRup.prove_clause [c1699, c1695, c1106, c1082, c1702, c1026, c1027, c1033, c1706, c1057, c1062, c1081, c1034, c1114, c1028, c1029, c984, c1709, c1638, c172, c932, c924] c1798 (by decide) p (sat_cons (step1699 p h) (sat_cons (step1695 p h) (sat_cons (step1106 p h) (sat_cons (step1082 p h) (sat_cons (step1702 p h) (sat_cons (step1026 p h) (sat_cons (step1027 p h) (sat_cons (step1033 p h) (sat_cons (step1706 p h) (sat_cons (step1057 p h) (sat_cons (step1062 p h) (sat_cons (step1081 p h) (sat_cons (step1034 p h) (sat_cons (step1114 p h) (sat_cons (step1028 p h) (sat_cons (step1029 p h) (sat_cons (step984 p h) (sat_cons (step1709 p h) (sat_cons (step1638 p h) (sat_cons (step172 p h) (sat_cons (step932 p h) (sat_cons (step924 p h) (sat_nil p)))))))))))))))))))))))
def c1799 : List Lit := [(52, false), (7, false), (47, false), (921, true)]
theorem step1799 (p : Nat → Bool) (h : Constraints p) : clause p c1799 = true :=
  Snake9.LocalRup.prove_clause [c174, c173, c1041] c1799 (by decide) p (sat_cons (step174 p h) (sat_cons (step173 p h) (sat_cons (step1041 p h) (sat_nil p))))
def c1800 : List Lit := [(54, true), (49, false), (47, false), (925, true)]
theorem step1800 (p : Nat → Bool) (h : Constraints p) : clause p c1800 = true :=
  Snake9.LocalRup.prove_clause [c1050, c1040, c1041, c1048, c162, c1042] c1800 (by decide) p (sat_cons (step1050 p h) (sat_cons (step1040 p h) (sat_cons (step1041 p h) (sat_cons (step1048 p h) (sat_cons (step162 p h) (sat_cons (step1042 p h) (sat_nil p)))))))
def c1801 : List Lit := [(37, false), (895, true), (46, false), (113, false)]
theorem step1801 (p : Nat → Bool) (h : Constraints p) : clause p c1801 = true :=
  Snake9.LocalRup.prove_clause [c117, c118, c998, c992] c1801 (by decide) p (sat_cons (step117 p h) (sat_cons (step118 p h) (sat_cons (step998 p h) (sat_cons (step992 p h) (sat_nil p)))))
def c1802 : List Lit := [(1045, true), (1042, false), (102, false), (106, true), (114, false)]
theorem step1802 (p : Nat → Bool) (h : Constraints p) : clause p c1802 = true :=
  Snake9.LocalRup.prove_clause [c1789, c1283, c1274] c1802 (by decide) p (sat_cons (step1789 p h) (sat_cons (step1283 p h) (sat_cons (step1274 p h) (sat_nil p))))
def c1803 : List Lit := [(94, false), (916, false), (92, false), (959, true), (906, false), (114, false)]
theorem step1803 (p : Nat → Bool) (h : Constraints p) : clause p c1803 = true :=
  Snake9.LocalRup.prove_clause [c399, c393, c1043, c945, c1045, c1717, c1057, c1643, c1081, c1114] c1803 (by decide) p (sat_cons (step399 p h) (sat_cons (step393 p h) (sat_cons (step1043 p h) (sat_cons (step945 p h) (sat_cons (step1045 p h) (sat_cons (step1717 p h) (sat_cons (step1057 p h) (sat_cons (step1643 p h) (sat_cons (step1081 p h) (sat_cons (step1114 p h) (sat_nil p)))))))))))
def c1804 : List Lit := [(1044, true), (106, true), (115, false), (1056, true), (114, false)]
theorem step1804 (p : Nat → Bool) (h : Constraints p) : clause p c1804 = true :=
  Snake9.LocalRup.prove_clause [c734, c1277, c1280, c1282, c1278, c1273, c1274, c481, c475, c445, c529, c530, c1309] c1804 (by decide) p (sat_cons (step734 p h) (sat_cons (step1277 p h) (sat_cons (step1280 p h) (sat_cons (step1282 p h) (sat_cons (step1278 p h) (sat_cons (step1273 p h) (sat_cons (step1274 p h) (sat_cons (step481 p h) (sat_cons (step475 p h) (sat_cons (step445 p h) (sat_cons (step529 p h) (sat_cons (step530 p h) (sat_cons (step1309 p h) (sat_nil p))))))))))))))
def c1805 : List Lit := [(959, true), (881, false), (123, true), (906, false), (113, false)]
theorem step1805 (p : Nat → Bool) (h : Constraints p) : clause p c1805 = true :=
  Snake9.LocalRup.prove_clause [c708, c1677, c1666, c1798, c1114, c153, c1086, c1801, c1020] c1805 (by decide) p (sat_cons (step708 p h) (sat_cons (step1677 p h) (sat_cons (step1666 p h) (sat_cons (step1798 p h) (sat_cons (step1114 p h) (sat_cons (step153 p h) (sat_cons (step1086 p h) (sat_cons (step1801 p h) (sat_cons (step1020 p h) (sat_nil p))))))))))
def c1806 : List Lit := [(44, true), (902, true)]
theorem step1806 (p : Nat → Bool) (h : Constraints p) : clause p c1806 = true :=
  Snake9.LocalRup.prove_clause [c705, c1007, c1003, c1005, c1009, c1000, c1001, c129, c126] c1806 (by decide) p (sat_cons (step705 p h) (sat_cons (step1007 p h) (sat_cons (step1003 p h) (sat_cons (step1005 p h) (sat_cons (step1009 p h) (sat_cons (step1000 p h) (sat_cons (step1001 p h) (sat_cons (step129 p h) (sat_cons (step126 p h) (sat_nil p))))))))))
def c1807 : List Lit := [(922, false), (7, false), (929, true)]
theorem step1807 (p : Nat → Bool) (h : Constraints p) : clause p c1807 = true :=
  Snake9.LocalRup.prove_clause [c1054, c1045, c1048, c1057, c1039, c1040, c1031, c1033, c181, c1029, c1025, c1709] c1807 (by decide) p (sat_cons (step1054 p h) (sat_cons (step1045 p h) (sat_cons (step1048 p h) (sat_cons (step1057 p h) (sat_cons (step1039 p h) (sat_cons (step1040 p h) (sat_cons (step1031 p h) (sat_cons (step1033 p h) (sat_cons (step181 p h) (sat_cons (step1029 p h) (sat_cons (step1025 p h) (sat_cons (step1709 p h) (sat_nil p)))))))))))))
def c1808 : List Lit := [(916, true), (7, false)]
theorem step1808 (p : Nat → Bool) (h : Constraints p) : clause p c1808 = true :=
  Snake9.LocalRup.prove_clause [c1031, c1033, c1028, c1029, c1025, c172, c1709] c1808 (by decide) p (sat_cons (step1031 p h) (sat_cons (step1033 p h) (sat_cons (step1028 p h) (sat_cons (step1029 p h) (sat_cons (step1025 p h) (sat_cons (step172 p h) (sat_cons (step1709 p h) (sat_nil p))))))))
def c1809 : List Lit := [(959, true), (100, false), (906, false), (113, false)]
theorem step1809 (p : Nat → Bool) (h : Constraints p) : clause p c1809 = true :=
  Snake9.LocalRup.prove_clause [c1699, c708, c1695, c1666, c1106, c1798, c658, c153, c1805, c1801, c984, c1020, c1638, c1087, c932, c1061, c924, c1808, c1057, c1047, c1706, c1039, c1040, c1025, c181, c1034, c1673, c1029] c1809 (by decide) p (sat_cons (step1699 p h) (sat_cons (step708 p h) (sat_cons (step1695 p h) (sat_cons (step1666 p h) (sat_cons (step1106 p h) (sat_cons (step1798 p h) (sat_cons (step658 p h) (sat_cons (step153 p h) (sat_cons (step1805 p h) (sat_cons (step1801 p h) (sat_cons (step984 p h) (sat_cons (step1020 p h) (sat_cons (step1638 p h) (sat_cons (step1087 p h) (sat_cons (step932 p h) (sat_cons (step1061 p h) (sat_cons (step924 p h) (sat_cons (step1808 p h) (sat_cons (step1057 p h) (sat_cons (step1047 p h) (sat_cons (step1706 p h) (sat_cons (step1039 p h) (sat_cons (step1040 p h) (sat_cons (step1025 p h) (sat_cons (step181 p h) (sat_cons (step1034 p h) (sat_cons (step1673 p h) (sat_cons (step1029 p h) (sat_nil p)))))))))))))))))))))))))))))
def c1810 : List Lit := [(1084, true), (1044, false), (1068, false), (1031, false), (34, false), (113, false)]
theorem step1810 (p : Nat → Bool) (h : Constraints p) : clause p c1810 = true :=
  Snake9.LocalRup.prove_clause [c736, c1267, c1293, c1336, c1377, c1383, c1339, c1298, c1315, c1268, c1307, c1308, c1263, c1604, c593, c512, c558] c1810 (by decide) p (sat_cons (step736 p h) (sat_cons (step1267 p h) (sat_cons (step1293 p h) (sat_cons (step1336 p h) (sat_cons (step1377 p h) (sat_cons (step1383 p h) (sat_cons (step1339 p h) (sat_cons (step1298 p h) (sat_cons (step1315 p h) (sat_cons (step1268 p h) (sat_cons (step1307 p h) (sat_cons (step1308 p h) (sat_cons (step1263 p h) (sat_cons (step1604 p h) (sat_cons (step593 p h) (sat_cons (step512 p h) (sat_cons (step558 p h) (sat_nil p))))))))))))))))))
def c1811 : List Lit := [(46, false), (100, false), (37, true), (113, false)]
theorem step1811 (p : Nat → Bool) (h : Constraints p) : clause p c1811 = true :=
  Snake9.LocalRup.prove_clause [c708, c153, c658] c1811 (by decide) p (sat_cons (step708 p h) (sat_cons (step153 p h) (sat_cons (step658 p h) (sat_nil p))))
def c1812 : List Lit := [(123, false), (100, false), (1066, true), (113, false)]
theorem step1812 (p : Nat → Bool) (h : Constraints p) : clause p c1812 = true :=
  Snake9.LocalRup.prove_clause [c679, c680, c1326] c1812 (by decide) p (sat_cons (step679 p h) (sat_cons (step680 p h) (sat_cons (step1326 p h) (sat_nil p))))
def c1813 : List Lit := [(1006, true), (92, true), (87, true), (89, true), (97, false)]
theorem step1813 (p : Nat → Bool) (h : Constraints p) : clause p c1813 = true :=
  Snake9.LocalRup.prove_clause [c729, c1182, c1186, c1192, c1194, c1187, c1184, c382, c418] c1813 (by decide) p (sat_cons (step729 p h) (sat_cons (step1182 p h) (sat_cons (step1186 p h) (sat_cons (step1192 p h) (sat_cons (step1194 p h) (sat_cons (step1187 p h) (sat_cons (step1184 p h) (sat_cons (step382 p h) (sat_cons (step418 p h) (sat_nil p))))))))))
def c1814 : List Lit := [(1006, false), (994, false), (1021, true), (979, false)]
theorem step1814 (p : Nat → Bool) (h : Constraints p) : clause p c1814 = true :=
  Snake9.LocalRup.prove_clause [c1174, c1147, c1154, c1233, c1203, c1208, c1240, c1177, c1155, c1158, c1169, c1150, c1751, c1142] c1814 (by decide) p (sat_cons (step1174 p h) (sat_cons (step1147 p h) (sat_cons (step1154 p h) (sat_cons (step1233 p h) (sat_cons (step1203 p h) (sat_cons (step1208 p h) (sat_cons (step1240 p h) (sat_cons (step1177 p h) (sat_cons (step1155 p h) (sat_cons (step1158 p h) (sat_cons (step1169 p h) (sat_cons (step1150 p h) (sat_cons (step1751 p h) (sat_cons (step1142 p h) (sat_nil p)))))))))))))))
def c1815 : List Lit := [(2, false), (7, true)]
theorem step1815 (p : Nat → Bool) (h : Constraints p) : clause p c1815 = true :=
  Snake9.LocalRup.prove_clause [c1605, c1606, c2] c1815 (by decide) p (sat_cons (step1605 p h) (sat_cons (step1606 p h) (sat_cons (step2 p h) (sat_nil p))))
def c1816 : List Lit := [(2, false), (125, true)]
theorem step1816 (p : Nat → Bool) (h : Constraints p) : clause p c1816 = true :=
  Snake9.LocalRup.prove_clause [c1605, c1606, c3] c1816 (by decide) p (sat_cons (step1605 p h) (sat_cons (step1606 p h) (sat_cons (step3 p h) (sat_nil p))))
def c1817 : List Lit := [(5, false), (10, true), (128, true)]
theorem step1817 (p : Nat → Bool) (h : Constraints p) : clause p c1817 = true :=
  Snake9.LocalRup.prove_clause [c1607, c6] c1817 (by decide) p (sat_cons (step1607 p h) (sat_cons (step6 p h) (sat_nil p)))
def c1818 : List Lit := [(5, false), (6, true), (128, true)]
theorem step1818 (p : Nat → Bool) (h : Constraints p) : clause p c1818 = true :=
  Snake9.LocalRup.prove_clause [c1607, c7] c1818 (by decide) p (sat_cons (step1607 p h) (sat_cons (step7 p h) (sat_nil p)))
def c1819 : List Lit := [(16, true), (51, true), (6, false)]
theorem step1819 (p : Nat → Bool) (h : Constraints p) : clause p c1819 = true :=
  Snake9.LocalRup.prove_clause [c691, c9] c1819 (by decide) p (sat_cons (step691 p h) (sat_cons (step9 p h) (sat_nil p)))
def c1820 : List Lit := [(5, true), (51, true), (6, false)]
theorem step1820 (p : Nat → Bool) (h : Constraints p) : clause p c1820 = true :=
  Snake9.LocalRup.prove_clause [c691, c10] c1820 (by decide) p (sat_cons (step691 p h) (sat_cons (step10 p h) (sat_nil p)))
def c1821 : List Lit := [(5, true), (16, true), (6, false)]
theorem step1821 (p : Nat → Bool) (h : Constraints p) : clause p c1821 = true :=
  Snake9.LocalRup.prove_clause [c691, c11] c1821 (by decide) p (sat_cons (step691 p h) (sat_cons (step11 p h) (sat_nil p)))
def c1822 : List Lit := [(12, true), (52, true), (7, false), (17, true)]
theorem step1822 (p : Nat → Bool) (h : Constraints p) : clause p c1822 = true :=
  Snake9.LocalRup.prove_clause [c692, c13] c1822 (by decide) p (sat_cons (step692 p h) (sat_cons (step13 p h) (sat_nil p)))
def c1823 : List Lit := [(52, true), (17, true), (2, true), (7, false)]
theorem step1823 (p : Nat → Bool) (h : Constraints p) : clause p c1823 = true :=
  Snake9.LocalRup.prove_clause [c692, c14] c1823 (by decide) p (sat_cons (step692 p h) (sat_cons (step14 p h) (sat_nil p)))
def c1824 : List Lit := [(12, true), (17, true), (2, true), (7, false)]
theorem step1824 (p : Nat → Bool) (h : Constraints p) : clause p c1824 = true :=
  Snake9.LocalRup.prove_clause [c692, c15] c1824 (by decide) p (sat_cons (step692 p h) (sat_cons (step15 p h) (sat_nil p)))
def c1825 : List Lit := [(12, true), (11, true), (8, false)]
theorem step1825 (p : Nat → Bool) (h : Constraints p) : clause p c1825 = true :=
  Snake9.LocalRup.prove_clause [c693, c17] c1825 (by decide) p (sat_cons (step693 p h) (sat_cons (step17 p h) (sat_nil p)))
def c1826 : List Lit := [(12, true), (9, true), (8, false)]
theorem step1826 (p : Nat → Bool) (h : Constraints p) : clause p c1826 = true :=
  Snake9.LocalRup.prove_clause [c693, c18] c1826 (by decide) p (sat_cons (step693 p h) (sat_cons (step18 p h) (sat_nil p)))
def c1827 : List Lit := [(11, true), (9, true), (8, false)]
theorem step1827 (p : Nat → Bool) (h : Constraints p) : clause p c1827 = true :=
  Snake9.LocalRup.prove_clause [c693, c19] c1827 (by decide) p (sat_cons (step693 p h) (sat_cons (step19 p h) (sat_nil p)))
def c1828 : List Lit := [(9, true), (58, true), (10, false)]
theorem step1828 (p : Nat → Bool) (h : Constraints p) : clause p c1828 = true :=
  Snake9.LocalRup.prove_clause [c694, c24] c1828 (by decide) p (sat_cons (step694 p h) (sat_cons (step24 p h) (sat_nil p)))
def c1829 : List Lit := [(5, true), (58, true), (10, false)]
theorem step1829 (p : Nat → Bool) (h : Constraints p) : clause p c1829 = true :=
  Snake9.LocalRup.prove_clause [c694, c25] c1829 (by decide) p (sat_cons (step694 p h) (sat_cons (step25 p h) (sat_nil p)))
def c1830 : List Lit := [(15, true), (13, false), (17, true)]
theorem step1830 (p : Nat → Bool) (h : Constraints p) : clause p c1830 = true :=
  Snake9.LocalRup.prove_clause [c695, c29] c1830 (by decide) p (sat_cons (step695 p h) (sat_cons (step29 p h) (sat_nil p)))
def c1831 : List Lit := [(14, true), (13, false), (17, true)]
theorem step1831 (p : Nat → Bool) (h : Constraints p) : clause p c1831 = true :=
  Snake9.LocalRup.prove_clause [c695, c30] c1831 (by decide) p (sat_cons (step695 p h) (sat_cons (step30 p h) (sat_nil p)))
def c1832 : List Lit := [(15, false), (22, false), (13, false)]
theorem step1832 (p : Nat → Bool) (h : Constraints p) : clause p c1832 = true :=
  Snake9.LocalRup.prove_clause [c57, c34] c1832 (by decide) p (sat_cons (step57 p h) (sat_cons (step34 p h) (sat_nil p)))
def c1833 : List Lit := [(13, false), (17, false), (7, false)]
theorem step1833 (p : Nat → Bool) (h : Constraints p) : clause p c1833 = true :=
  Snake9.LocalRup.prove_clause [c57, c38] c1833 (by decide) p (sat_cons (step57 p h) (sat_cons (step38 p h) (sat_nil p)))
def c1834 : List Lit := [(18, false), (17, false), (7, false)]
theorem step1834 (p : Nat → Bool) (h : Constraints p) : clause p c1834 = true :=
  Snake9.LocalRup.prove_clause [c57, c39] c1834 (by decide) p (sat_cons (step57 p h) (sat_cons (step39 p h) (sat_nil p)))
def c1835 : List Lit := [(17, false), (7, false), (34, false)]
theorem step1835 (p : Nat → Bool) (h : Constraints p) : clause p c1835 = true :=
  Snake9.LocalRup.prove_clause [c57, c40] c1835 (by decide) p (sat_cons (step57 p h) (sat_cons (step40 p h) (sat_nil p)))
def c1836 : List Lit := [(17, false), (86, false), (7, false)]
theorem step1836 (p : Nat → Bool) (h : Constraints p) : clause p c1836 = true :=
  Snake9.LocalRup.prove_clause [c57, c41] c1836 (by decide) p (sat_cons (step57 p h) (sat_cons (step41 p h) (sat_nil p)))
def c1837 : List Lit := [(13, false), (18, false), (17, false)]
theorem step1837 (p : Nat → Bool) (h : Constraints p) : clause p c1837 = true :=
  Snake9.LocalRup.prove_clause [c57, c42] c1837 (by decide) p (sat_cons (step57 p h) (sat_cons (step42 p h) (sat_nil p)))
def c1838 : List Lit := [(13, false), (17, false), (34, false)]
theorem step1838 (p : Nat → Bool) (h : Constraints p) : clause p c1838 = true :=
  Snake9.LocalRup.prove_clause [c57, c43] c1838 (by decide) p (sat_cons (step57 p h) (sat_cons (step43 p h) (sat_nil p)))
def c1839 : List Lit := [(13, false), (17, false), (86, false)]
theorem step1839 (p : Nat → Bool) (h : Constraints p) : clause p c1839 = true :=
  Snake9.LocalRup.prove_clause [c57, c44] c1839 (by decide) p (sat_cons (step57 p h) (sat_cons (step44 p h) (sat_nil p)))
def c1840 : List Lit := [(18, false), (17, false), (34, false)]
theorem step1840 (p : Nat → Bool) (h : Constraints p) : clause p c1840 = true :=
  Snake9.LocalRup.prove_clause [c57, c45] c1840 (by decide) p (sat_cons (step57 p h) (sat_cons (step45 p h) (sat_nil p)))
def c1841 : List Lit := [(17, false), (18, false), (86, false)]
theorem step1841 (p : Nat → Bool) (h : Constraints p) : clause p c1841 = true :=
  Snake9.LocalRup.prove_clause [c57, c46] c1841 (by decide) p (sat_cons (step57 p h) (sat_cons (step46 p h) (sat_nil p)))
def c1842 : List Lit := [(17, false), (86, false), (34, false)]
theorem step1842 (p : Nat → Bool) (h : Constraints p) : clause p c1842 = true :=
  Snake9.LocalRup.prove_clause [c57, c47] c1842 (by decide) p (sat_cons (step57 p h) (sat_cons (step47 p h) (sat_nil p)))
def c1843 : List Lit := [(19, true), (27, true), (17, true), (18, false)]
theorem step1843 (p : Nat → Bool) (h : Constraints p) : clause p c1843 = true :=
  Snake9.LocalRup.prove_clause [c696, c49] c1843 (by decide) p (sat_cons (step696 p h) (sat_cons (step49 p h) (sat_nil p)))
def c1844 : List Lit := [(15, true), (88, true), (17, true)]
theorem step1844 (p : Nat → Bool) (h : Constraints p) : clause p c1844 = true :=
  Snake9.LocalRup.prove_clause [c57, c54] c1844 (by decide) p (sat_cons (step57 p h) (sat_cons (step54 p h) (sat_nil p)))
def c1845 : List Lit := [(15, false), (88, false)]
theorem step1845 (p : Nat → Bool) (h : Constraints p) : clause p c1845 = true :=
  Snake9.LocalRup.prove_clause [c58, c55] c1845 (by decide) p (sat_cons (step58 p h) (sat_cons (step55 p h) (sat_nil p)))
def c1846 : List Lit := [(17, false), (88, false)]
theorem step1846 (p : Nat → Bool) (h : Constraints p) : clause p c1846 = true :=
  Snake9.LocalRup.prove_clause [c58, c56] c1846 (by decide) p (sat_cons (step58 p h) (sat_cons (step56 p h) (sat_nil p)))
def c1847 : List Lit := [(26, true), (92, true), (21, false)]
theorem step1847 (p : Nat → Bool) (h : Constraints p) : clause p c1847 = true :=
  Snake9.LocalRup.prove_clause [c697, c60] c1847 (by decide) p (sat_cons (step697 p h) (sat_cons (step60 p h) (sat_nil p)))
def c1848 : List Lit := [(23, true), (92, true), (21, false)]
theorem step1848 (p : Nat → Bool) (h : Constraints p) : clause p c1848 = true :=
  Snake9.LocalRup.prove_clause [c697, c61] c1848 (by decide) p (sat_cons (step697 p h) (sat_cons (step61 p h) (sat_nil p)))
def c1849 : List Lit := [(26, true), (23, true), (21, false)]
theorem step1849 (p : Nat → Bool) (h : Constraints p) : clause p c1849 = true :=
  Snake9.LocalRup.prove_clause [c697, c62] c1849 (by decide) p (sat_cons (step697 p h) (sat_cons (step62 p h) (sat_nil p)))
def c1850 : List Lit := [(11, true), (23, true), (41, true), (15, true), (22, false)]
theorem step1850 (p : Nat → Bool) (h : Constraints p) : clause p c1850 = true :=
  Snake9.LocalRup.prove_clause [c698, c67] c1850 (by decide) p (sat_cons (step698 p h) (sat_cons (step67 p h) (sat_nil p)))
end B112E097
