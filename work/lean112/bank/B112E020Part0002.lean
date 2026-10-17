import B112E020Part0001
namespace B112E020
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1740 : List Lit := [(69, false), (84, false), (1739, false), (65, false), (1732, false), (66, false), (68, false), (1752, true)]
theorem step1740 (p : Nat → Bool) (h : Constraints p) : clause p c1740 = true :=
  Snake9.LocalRup.prove_clause [c802, c407, c424, c419, c1739] c1740 (by decide) p (sat_cons (step802 p h) (sat_cons (step407 p h) (sat_cons (step424 p h) (sat_cons (step419 p h) (sat_cons (step1739 p h) (sat_nil p))))))
def c1741 : List Lit := [(60, false), (1652, true), (1584, true)]
theorem step1741 (p : Nat → Bool) (h : Constraints p) : clause p c1741 = true :=
  Snake9.LocalRup.prove_clause [c1158, c1155, c1160, c1153, c1156, c232, c1725, c1734] c1741 (by decide) p (sat_cons (step1158 p h) (sat_cons (step1155 p h) (sat_cons (step1160 p h) (sat_cons (step1153 p h) (sat_cons (step1156 p h) (sat_cons (step232 p h) (sat_cons (step1725 p h) (sat_cons (step1734 p h) (sat_nil p)))))))))
def c1742 : List Lit := [(31, false), (7, false), (1525, true)]
theorem step1742 (p : Nat → Bool) (h : Constraints p) : clause p c1742 = true :=
  Snake9.LocalRup.prove_clause [c783, c778, c1059, c1058, c80, c177, c88, c94] c1742 (by decide) p (sat_cons (step783 p h) (sat_cons (step778 p h) (sat_cons (step1059 p h) (sat_cons (step1058 p h) (sat_cons (step80 p h) (sat_cons (step177 p h) (sat_cons (step88 p h) (sat_cons (step94 p h) (sat_nil p)))))))))
def c1743 : List Lit := [(60, false), (42, false), (47, false), (46, true), (69, false)]
theorem step1743 (p : Nat → Bool) (h : Constraints p) : clause p c1743 = true :=
  Snake9.LocalRup.prove_clause [c1725, c400] c1743 (by decide) p (sat_cons (step1725 p h) (sat_cons (step400 p h) (sat_nil p)))
def c1744 : List Lit := [(67, false), (1652, true), (47, false), (69, false)]
theorem step1744 (p : Nat → Bool) (h : Constraints p) : clause p c1744 = true :=
  Snake9.LocalRup.prove_clause [c403, c402, c1278] c1744 (by decide) p (sat_cons (step403 p h) (sat_cons (step402 p h) (sat_cons (step1278 p h) (sat_nil p))))
def c1745 : List Lit := [(1546, true), (8, true), (10, false), (47, false)]
theorem step1745 (p : Nat → Bool) (h : Constraints p) : clause p c1745 = true :=
  Snake9.LocalRup.prove_clause [c1651, c1612, c5, c1021, c1029, c1095, c1728, c1043, c1, c1020, c1017, c1018, c1019, c31, c1039, c1024, c1030] c1745 (by decide) p (sat_cons (step1651 p h) (sat_cons (step1612 p h) (sat_cons (step5 p h) (sat_cons (step1021 p h) (sat_cons (step1029 p h) (sat_cons (step1095 p h) (sat_cons (step1728 p h) (sat_cons (step1043 p h) (sat_cons (step1 p h) (sat_cons (step1020 p h) (sat_cons (step1017 p h) (sat_cons (step1018 p h) (sat_cons (step1019 p h) (sat_cons (step31 p h) (sat_cons (step1039 p h) (sat_cons (step1024 p h) (sat_cons (step1030 p h) (sat_nil p))))))))))))))))))
def c1746 : List Lit := [(77, false), (1525, true), (7, false)]
theorem step1746 (p : Nat → Bool) (h : Constraints p) : clause p c1746 = true :=
  Snake9.LocalRup.prove_clause [c778, c1059, c1058, c95, c93, c88] c1746 (by decide) p (sat_cons (step778 p h) (sat_cons (step1059 p h) (sat_cons (step1058 p h) (sat_cons (step95 p h) (sat_cons (step93 p h) (sat_cons (step88 p h) (sat_nil p)))))))
def c1747 : List Lit := [(1684, true), (77, true), (75, true)]
theorem step1747 (p : Nat → Bool) (h : Constraints p) : clause p c1747 = true :=
  Snake9.LocalRup.prove_clause [c1313, c1320, c1345, c1342, c1323, c1321, c1333, c1314, c1316, c1326, c1714] c1747 (by decide) p (sat_cons (step1313 p h) (sat_cons (step1320 p h) (sat_cons (step1345 p h) (sat_cons (step1342 p h) (sat_cons (step1323 p h) (sat_cons (step1321 p h) (sat_cons (step1333 p h) (sat_cons (step1314 p h) (sat_cons (step1316 p h) (sat_cons (step1326 p h) (sat_cons (step1714 p h) (sat_nil p))))))))))))
def c1748 : List Lit := [(58, true), (1661, true), (73, true), (67, true)]
theorem step1748 (p : Nat → Bool) (h : Constraints p) : clause p c1748 = true :=
  Snake9.LocalRup.prove_clause [c1279, c1282, c1300, c1273, c1263, c1264, c1270, c1271, c1296, c1265, c1283, c1285, c1281, c1276, c1710] c1748 (by decide) p (sat_cons (step1279 p h) (sat_cons (step1282 p h) (sat_cons (step1300 p h) (sat_cons (step1273 p h) (sat_cons (step1263 p h) (sat_cons (step1264 p h) (sat_cons (step1270 p h) (sat_cons (step1271 p h) (sat_cons (step1296 p h) (sat_cons (step1265 p h) (sat_cons (step1283 p h) (sat_cons (step1285 p h) (sat_cons (step1281 p h) (sat_cons (step1276 p h) (sat_cons (step1710 p h) (sat_nil p))))))))))))))))
def c1749 : List Lit := [(1759, true), (1749, false), (1731, false), (118, true)]
theorem step1749 (p : Nat → Bool) (h : Constraints p) : clause p c1749 = true :=
  Snake9.LocalRup.prove_clause [c812, c1689, c1487, c1663, c1412, c1386, c1388, c1383, c1380, c1381, c498, c513] c1749 (by decide) p (sat_cons (step812 p h) (sat_cons (step1689 p h) (sat_cons (step1487 p h) (sat_cons (step1663 p h) (sat_cons (step1412 p h) (sat_cons (step1386 p h) (sat_cons (step1388 p h) (sat_cons (step1383 p h) (sat_cons (step1380 p h) (sat_cons (step1381 p h) (sat_cons (step498 p h) (sat_cons (step513 p h) (sat_nil p)))))))))))))
def c1750 : List Lit := [(26, false), (1528, true), (78, false), (61, false)]
theorem step1750 (p : Nat → Bool) (h : Constraints p) : clause p c1750 = true :=
  Snake9.LocalRup.prove_clause [c152, c149, c1063] c1750 (by decide) p (sat_cons (step152 p h) (sat_cons (step149 p h) (sat_cons (step1063 p h) (sat_nil p))))
def c1751 : List Lit := [(1511, true)]
theorem step1751 (p : Nat → Bool) (h : Constraints p) : clause p c1751 = true :=
  Snake9.LocalRup.prove_clause [c1612, c5, c774, c1720, c1727, c1, c1021, c1025, c1035, c1027, c1028, c1038, c1026, c1019, c48, c27, c1016] c1751 (by decide) p (sat_cons (step1612 p h) (sat_cons (step5 p h) (sat_cons (step774 p h) (sat_cons (step1720 p h) (sat_cons (step1727 p h) (sat_cons (step1 p h) (sat_cons (step1021 p h) (sat_cons (step1025 p h) (sat_cons (step1035 p h) (sat_cons (step1027 p h) (sat_cons (step1028 p h) (sat_cons (step1038 p h) (sat_cons (step1026 p h) (sat_cons (step1019 p h) (sat_cons (step48 p h) (sat_cons (step27 p h) (sat_cons (step1016 p h) (sat_nil p))))))))))))))))))
def c1752 : List Lit := [(1545, true)]
theorem step1752 (p : Nat → Bool) (h : Constraints p) : clause p c1752 = true :=
  Snake9.LocalRup.prove_clause [c1751, c1651, c1089] c1752 (by decide) p (sat_cons (step1751 p h) (sat_cons (step1651 p h) (sat_cons (step1089 p h) (sat_nil p))))
def c1753 : List Lit := [(1712, false), (99, false), (1737, false), (1763, true), (1717, false), (1740, false)]
theorem step1753 (p : Nat → Bool) (h : Constraints p) : clause p c1753 = true :=
  Snake9.LocalRup.prove_clause [c1448, c1467, c1502, c1399, c1417, c1418, c1497, c1402, c1468, c1394, c1449, c1440, c1441, c1700] c1753 (by decide) p (sat_cons (step1448 p h) (sat_cons (step1467 p h) (sat_cons (step1502 p h) (sat_cons (step1399 p h) (sat_cons (step1417 p h) (sat_cons (step1418 p h) (sat_cons (step1497 p h) (sat_cons (step1402 p h) (sat_cons (step1468 p h) (sat_cons (step1394 p h) (sat_cons (step1449 p h) (sat_cons (step1440 p h) (sat_cons (step1441 p h) (sat_cons (step1700 p h) (sat_nil p)))))))))))))))
def c1754 : List Lit := [(1752, true), (1740, false), (1732, false), (1737, false), (1720, true), (99, false)]
theorem step1754 (p : Nat → Bool) (h : Constraints p) : clause p c1754 = true :=
  Snake9.LocalRup.prove_clause [c817, c816, c1448, c1404, c1472, c1468, c1436, c1449, c1440, c1441, c1700, c1394, c1395, c1402, c1396, c1397, c1681, c540, c552, c539, c611, c1599, c1428] c1754 (by decide) p (sat_cons (step817 p h) (sat_cons (step816 p h) (sat_cons (step1448 p h) (sat_cons (step1404 p h) (sat_cons (step1472 p h) (sat_cons (step1468 p h) (sat_cons (step1436 p h) (sat_cons (step1449 p h) (sat_cons (step1440 p h) (sat_cons (step1441 p h) (sat_cons (step1700 p h) (sat_cons (step1394 p h) (sat_cons (step1395 p h) (sat_cons (step1402 p h) (sat_cons (step1396 p h) (sat_cons (step1397 p h) (sat_cons (step1681 p h) (sat_cons (step540 p h) (sat_cons (step552 p h) (sat_cons (step539 p h) (sat_cons (step611 p h) (sat_cons (step1599 p h) (sat_cons (step1428 p h) (sat_nil p))))))))))))))))))))))))
def c1755 : List Lit := [(1655, true), (70, true), (122, true), (47, false)]
theorem step1755 (p : Nat → Bool) (h : Constraints p) : clause p c1755 = true :=
  Snake9.LocalRup.prove_clause [c802, c1282, c1284, c1280, c1276, c403, c419] c1755 (by decide) p (sat_cons (step802 p h) (sat_cons (step1282 p h) (sat_cons (step1284 p h) (sat_cons (step1280 p h) (sat_cons (step1276 p h) (sat_cons (step403 p h) (sat_cons (step419 p h) (sat_nil p))))))))
def c1756 : List Lit := [(66, true), (1656, true), (70, true), (47, false), (122, true)]
theorem step1756 (p : Nat → Bool) (h : Constraints p) : clause p c1756 = true :=
  Snake9.LocalRup.prove_clause [c802, c1287, c1277, c1278, c1285, c1280, c403, c419] c1756 (by decide) p (sat_cons (step802 p h) (sat_cons (step1287 p h) (sat_cons (step1277 p h) (sat_cons (step1278 p h) (sat_cons (step1285 p h) (sat_cons (step1280 p h) (sat_cons (step403 p h) (sat_cons (step419 p h) (sat_nil p)))))))))
def c1757 : List Lit := [(1724, true), (1709, false), (61, false)]
theorem step1757 (p : Nat → Bool) (h : Constraints p) : clause p c1757 = true :=
  Snake9.LocalRup.prove_clause [c1386, c1416, c1412, c1389, c1399, c1663, c1380, c1397, c631] c1757 (by decide) p (sat_cons (step1386 p h) (sat_cons (step1416 p h) (sat_cons (step1412 p h) (sat_cons (step1389 p h) (sat_cons (step1399 p h) (sat_cons (step1663 p h) (sat_cons (step1380 p h) (sat_cons (step1397 p h) (sat_cons (step631 p h) (sat_nil p))))))))))
def c1758 : List Lit := [(1751, true), (1740, false), (124, true), (109, true), (91, false), (84, false), (1731, false)]
theorem step1758 (p : Nat → Bool) (h : Constraints p) : clause p c1758 = true :=
  Snake9.LocalRup.prove_clause [c819, c1440, c1449, c1431, c1459, c1463, c1450, c1434, c1432, c1442, c1425, c1427, c739, c601, c585, c607] c1758 (by decide) p (sat_cons (step819 p h) (sat_cons (step1440 p h) (sat_cons (step1449 p h) (sat_cons (step1431 p h) (sat_cons (step1459 p h) (sat_cons (step1463 p h) (sat_cons (step1450 p h) (sat_cons (step1434 p h) (sat_cons (step1432 p h) (sat_cons (step1442 p h) (sat_cons (step1425 p h) (sat_cons (step1427 p h) (sat_cons (step739 p h) (sat_cons (step601 p h) (sat_cons (step585 p h) (sat_cons (step607 p h) (sat_nil p)))))))))))))))))
def c1759 : List Lit := [(111, false), (107, false), (122, true), (66, false), (67, true), (91, false)]
theorem step1759 (p : Nat → Bool) (h : Constraints p) : clause p c1759 = true :=
  Snake9.LocalRup.prove_clause [c819, c810, c800, c585, c607, c491, c567, c557, c384] c1759 (by decide) p (sat_cons (step819 p h) (sat_cons (step810 p h) (sat_cons (step800 p h) (sat_cons (step585 p h) (sat_cons (step607 p h) (sat_cons (step491 p h) (sat_cons (step567 p h) (sat_cons (step557 p h) (sat_cons (step384 p h) (sat_nil p))))))))))
def c1760 : List Lit := [(90, false), (110, false), (107, false), (66, false), (67, true)]
theorem step1760 (p : Nat → Bool) (h : Constraints p) : clause p c1760 = true :=
  Snake9.LocalRup.prove_clause [c800, c557, c567, c384] c1760 (by decide) p (sat_cons (step800 p h) (sat_cons (step557 p h) (sat_cons (step567 p h) (sat_cons (step384 p h) (sat_nil p)))))
def c1761 : List Lit := [(110, false), (107, false), (66, false), (67, true), (91, false)]
theorem step1761 (p : Nat → Bool) (h : Constraints p) : clause p c1761 = true :=
  Snake9.LocalRup.prove_clause [c810, c800, c1760, c491, c561, c570, c384] c1761 (by decide) p (sat_cons (step810 p h) (sat_cons (step800 p h) (sat_cons (step1760 p h) (sat_cons (step491 p h) (sat_cons (step561 p h) (sat_cons (step570 p h) (sat_cons (step384 p h) (sat_nil p))))))))
def c1762 : List Lit := [(49, false), (1583, true), (46, false), (66, false)]
theorem step1762 (p : Nat → Bool) (h : Constraints p) : clause p c1762 = true :=
  Snake9.LocalRup.prove_clause [c240, c241, c1157] c1762 (by decide) p (sat_cons (step240 p h) (sat_cons (step241 p h) (sat_cons (step1157 p h) (sat_nil p))))
def c1763 : List Lit := [(45, true), (34, false), (1585, true), (46, true), (67, true)]
theorem step1763 (p : Nat → Bool) (h : Constraints p) : clause p c1763 = true :=
  Snake9.LocalRup.prove_clause [c791, c1163, c1152, c1154, c1161, c1156, c246, c214] c1763 (by decide) p (sat_cons (step791 p h) (sat_cons (step1163 p h) (sat_cons (step1152 p h) (sat_cons (step1154 p h) (sat_cons (step1161 p h) (sat_cons (step1156 p h) (sat_cons (step246 p h) (sat_cons (step214 p h) (sat_nil p)))))))))
def c1764 : List Lit := [(1584, true), (1607, true), (1590, false)]
theorem step1764 (p : Nat → Bool) (h : Constraints p) : clause p c1764 = true :=
  Snake9.LocalRup.prove_clause [c1653, c1655, c1658, c1140, c1167, c1201, c1175, c1181] c1764 (by decide) p (sat_cons (step1653 p h) (sat_cons (step1655 p h) (sat_cons (step1658 p h) (sat_cons (step1140 p h) (sat_cons (step1167 p h) (sat_cons (step1201 p h) (sat_cons (step1175 p h) (sat_cons (step1181 p h) (sat_nil p)))))))))
def c1765 : List Lit := [(64, true), (45, false), (49, false)]
theorem step1765 (p : Nat → Bool) (h : Constraints p) : clause p c1765 = true :=
  Snake9.LocalRup.prove_clause [c790, c230, c229, c1576] c1765 (by decide) p (sat_cons (step790 p h) (sat_cons (step230 p h) (sat_cons (step229 p h) (sat_cons (step1576 p h) (sat_nil p)))))
def c1766 : List Lit := [(36, true), (1569, true)]
theorem step1766 (p : Nat → Bool) (h : Constraints p) : clause p c1766 = true :=
  Snake9.LocalRup.prove_clause [c785, c786, c1134, c186, c1124, c1125, c1132, c194, c1126, c1127, c201] c1766 (by decide) p (sat_cons (step785 p h) (sat_cons (step786 p h) (sat_cons (step1134 p h) (sat_cons (step186 p h) (sat_cons (step1124 p h) (sat_cons (step1125 p h) (sat_cons (step1132 p h) (sat_cons (step194 p h) (sat_cons (step1126 p h) (sat_cons (step1127 p h) (sat_cons (step201 p h) (sat_nil p))))))))))))
def c1767 : List Lit := [(35, true), (1573, true)]
theorem step1767 (p : Nat → Bool) (h : Constraints p) : clause p c1767 = true :=
  Snake9.LocalRup.prove_clause [c1653, c1137, c1766, c1140, c1115, c1112, c1134, c1124, c1125, c1132, c189, c1127] c1767 (by decide) p (sat_cons (step1653 p h) (sat_cons (step1137 p h) (sat_cons (step1766 p h) (sat_cons (step1140 p h) (sat_cons (step1115 p h) (sat_cons (step1112 p h) (sat_cons (step1134 p h) (sat_cons (step1124 p h) (sat_cons (step1125 p h) (sat_cons (step1132 p h) (sat_cons (step189 p h) (sat_cons (step1127 p h) (sat_nil p)))))))))))))
def c1768 : List Lit := [(1573, true)]
theorem step1768 (p : Nat → Bool) (h : Constraints p) : clause p c1768 = true :=
  Snake9.LocalRup.prove_clause [c1653, c785, c1137, c1140, c1115, c1112, c1766, c1767, c187, c1570] c1768 (by decide) p (sat_cons (step1653 p h) (sat_cons (step785 p h) (sat_cons (step1137 p h) (sat_cons (step1140 p h) (sat_cons (step1115 p h) (sat_cons (step1112 p h) (sat_cons (step1766 p h) (sat_cons (step1767 p h) (sat_cons (step187 p h) (sat_cons (step1570 p h) (sat_nil p)))))))))))
def c1769 : List Lit := [(1606, true)]
theorem step1769 (p : Nat → Bool) (h : Constraints p) : clause p c1769 = true :=
  Snake9.LocalRup.prove_clause [c1768, c1654, c1200] c1769 (by decide) p (sat_cons (step1768 p h) (sat_cons (step1654 p h) (sat_cons (step1200 p h) (sat_nil p))))
def c1770 : List Lit := [(1569, true), (1566, true), (34, false)]
theorem step1770 (p : Nat → Bool) (h : Constraints p) : clause p c1770 = true :=
  Snake9.LocalRup.prove_clause [c788, c1126, c1127, c199, c201, c1134, c1766, c1125, c188] c1770 (by decide) p (sat_cons (step788 p h) (sat_cons (step1126 p h) (sat_cons (step1127 p h) (sat_cons (step199 p h) (sat_cons (step201 p h) (sat_cons (step1134 p h) (sat_cons (step1766 p h) (sat_cons (step1125 p h) (sat_cons (step188 p h) (sat_nil p))))))))))
def c1771 : List Lit := [(35, false), (34, false)]
theorem step1771 (p : Nat → Bool) (h : Constraints p) : clause p c1771 = true :=
  Snake9.LocalRup.prove_clause [c785, c186, c187, c1570] c1771 (by decide) p (sat_cons (step785 p h) (sat_cons (step186 p h) (sat_cons (step187 p h) (sat_cons (step1570 p h) (sat_nil p)))))
def c1772 : List Lit := [(1607, true), (1590, false)]
theorem step1772 (p : Nat → Bool) (h : Constraints p) : clause p c1772 = true :=
  Snake9.LocalRup.prove_clause [c1768, c1172, c1764, c1201, c1185] c1772 (by decide) p (sat_cons (step1768 p h) (sat_cons (step1172 p h) (sat_cons (step1764 p h) (sat_cons (step1201 p h) (sat_cons (step1185 p h) (sat_nil p))))))
def c1773 : List Lit := [(1597, true), (1590, false)]
theorem step1773 (p : Nat → Bool) (h : Constraints p) : clause p c1773 = true :=
  Snake9.LocalRup.prove_clause [c1172, c1181, c1185, c1175, c1658, c1167] c1773 (by decide) p (sat_cons (step1172 p h) (sat_cons (step1181 p h) (sat_cons (step1185 p h) (sat_cons (step1175 p h) (sat_cons (step1658 p h) (sat_cons (step1167 p h) (sat_nil p)))))))
def c1774 : List Lit := [(1584, true), (43, true), (67, true)]
theorem step1774 (p : Nat → Bool) (h : Constraints p) : clause p c1774 = true :=
  Snake9.LocalRup.prove_clause [c791, c1158, c1160, c1155, c1156, c1153, c246, c232] c1774 (by decide) p (sat_cons (step791 p h) (sat_cons (step1158 p h) (sat_cons (step1160 p h) (sat_cons (step1155 p h) (sat_cons (step1156 p h) (sat_cons (step1153 p h) (sat_cons (step246 p h) (sat_cons (step232 p h) (sat_nil p)))))))))
def c1775 : List Lit := [(53, false), (54, false), (58, false), (51, true)]
theorem step1775 (p : Nat → Bool) (h : Constraints p) : clause p c1775 = true :=
  Snake9.LocalRup.prove_clause [c794, c276, c270] c1775 (by decide) p (sat_cons (step794 p h) (sat_cons (step276 p h) (sat_cons (step270 p h) (sat_nil p))))
def c1776 : List Lit := [(91, false), (107, true), (75, false), (1760, true), (1739, false), (86, true)]
theorem step1776 (p : Nat → Bool) (h : Constraints p) : clause p c1776 = true :=
  Snake9.LocalRup.prove_clause [c810, c1445, c492, c574, c571, c573, c1427, c1393, c1425, c1435, c1401, c1466, c1407, c1488, c1482, c1408, c1412, c1467, c1404, c1386, c1446, c1395, c1383, c1440, c1441, c1700] c1776 (by decide) p (sat_cons (step810 p h) (sat_cons (step1445 p h) (sat_cons (step492 p h) (sat_cons (step574 p h) (sat_cons (step571 p h) (sat_cons (step573 p h) (sat_cons (step1427 p h) (sat_cons (step1393 p h) (sat_cons (step1425 p h) (sat_cons (step1435 p h) (sat_cons (step1401 p h) (sat_cons (step1466 p h) (sat_cons (step1407 p h) (sat_cons (step1488 p h) (sat_cons (step1482 p h) (sat_cons (step1408 p h) (sat_cons (step1412 p h) (sat_cons (step1467 p h) (sat_cons (step1404 p h) (sat_cons (step1386 p h) (sat_cons (step1446 p h) (sat_cons (step1395 p h) (sat_cons (step1383 p h) (sat_cons (step1440 p h) (sat_cons (step1441 p h) (sat_cons (step1700 p h) (sat_nil p)))))))))))))))))))))))))))
def c1777 : List Lit := [(1677, false), (107, false), (75, false), (1684, true)]
theorem step1777 (p : Nat → Bool) (h : Constraints p) : clause p c1777 = true :=
  Snake9.LocalRup.prove_clause [c805, c1339, c1331, c1334, c1342, c1326, c1318, c1320, c1316, c1312, c464, c435, c443] c1777 (by decide) p (sat_cons (step805 p h) (sat_cons (step1339 p h) (sat_cons (step1331 p h) (sat_cons (step1334 p h) (sat_cons (step1342 p h) (sat_cons (step1326 p h) (sat_cons (step1318 p h) (sat_cons (step1320 p h) (sat_cons (step1316 p h) (sat_cons (step1312 p h) (sat_cons (step464 p h) (sat_cons (step435 p h) (sat_cons (step443 p h) (sat_nil p))))))))))))))
def c1778 : List Lit := [(1525, true), (77, false), (31, false), (58, false)]
theorem step1778 (p : Nat → Bool) (h : Constraints p) : clause p c1778 = true :=
  Snake9.LocalRup.prove_clause [c778, c783, c1058, c1059, c83, c88, c177, c104] c1778 (by decide) p (sat_cons (step778 p h) (sat_cons (step783 p h) (sat_cons (step1058 p h) (sat_cons (step1059 p h) (sat_cons (step83 p h) (sat_cons (step88 p h) (sat_cons (step177 p h) (sat_cons (step104 p h) (sat_nil p)))))))))
def c1779 : List Lit := [(22, false), (80, false), (77, false), (31, false), (58, false), (125, true)]
theorem step1779 (p : Nat → Bool) (h : Constraints p) : clause p c1779 = true :=
  Snake9.LocalRup.prove_clause [c783, c769, c1612, c83, c177, c178, c97, c158, c6, c3] c1779 (by decide) p (sat_cons (step783 p h) (sat_cons (step769 p h) (sat_cons (step1612 p h) (sat_cons (step83 p h) (sat_cons (step177 p h) (sat_cons (step178 p h) (sat_cons (step97 p h) (sat_cons (step158 p h) (sat_cons (step6 p h) (sat_cons (step3 p h) (sat_nil p)))))))))))
def c1780 : List Lit := [(107, false), (75, false), (1684, true), (86, true)]
theorem step1780 (p : Nat → Bool) (h : Constraints p) : clause p c1780 = true :=
  Snake9.LocalRup.prove_clause [c810, c1777, c1328, c492, c572] c1780 (by decide) p (sat_cons (step810 p h) (sat_cons (step1777 p h) (sat_cons (step1328 p h) (sat_cons (step492 p h) (sat_cons (step572 p h) (sat_nil p))))))
def c1781 : List Lit := [(84, false), (1760, true), (1731, false), (81, true), (69, false), (1739, false)]
theorem step1781 (p : Nat → Bool) (h : Constraints p) : clause p c1781 = true :=
  Snake9.LocalRup.prove_clause [c808, c474, c729, c726, c727, c728, c1394, c1427, c1442, c1401, c1432, c1447, c1407, c1463, c1482] c1781 (by decide) p (sat_cons (step808 p h) (sat_cons (step474 p h) (sat_cons (step729 p h) (sat_cons (step726 p h) (sat_cons (step727 p h) (sat_cons (step728 p h) (sat_cons (step1394 p h) (sat_cons (step1427 p h) (sat_cons (step1442 p h) (sat_cons (step1401 p h) (sat_cons (step1432 p h) (sat_cons (step1447 p h) (sat_cons (step1407 p h) (sat_cons (step1463 p h) (sat_cons (step1482 p h) (sat_nil p))))))))))))))))
def c1782 : List Lit := [(11, true), (1508, true), (6, false), (9, true), (128, true), (10, false), (47, false)]
theorem step1782 (p : Nat → Bool) (h : Constraints p) : clause p c1782 = true :=
  Snake9.LocalRup.prove_clause [c774, c771, c47, c15, c1026, c8, c1031, c29, c1021] c1782 (by decide) p (sat_cons (step774 p h) (sat_cons (step771 p h) (sat_cons (step47 p h) (sat_cons (step15 p h) (sat_cons (step1026 p h) (sat_cons (step8 p h) (sat_cons (step1031 p h) (sat_cons (step29 p h) (sat_cons (step1021 p h) (sat_nil p))))))))))
def c1783 : List Lit := [(5, true), (1512, true), (1502, false)]
theorem step1783 (p : Nat → Bool) (h : Constraints p) : clause p c1783 = true :=
  Snake9.LocalRup.prove_clause [c1612, c5, c1029, c1043, c1020, c1016, c1018, c1019, c1, c1039, c1025, c1030] c1783 (by decide) p (sat_cons (step1612 p h) (sat_cons (step5 p h) (sat_cons (step1029 p h) (sat_cons (step1043 p h) (sat_cons (step1020 p h) (sat_cons (step1016 p h) (sat_cons (step1018 p h) (sat_cons (step1019 p h) (sat_cons (step1 p h) (sat_cons (step1039 p h) (sat_cons (step1025 p h) (sat_cons (step1030 p h) (sat_nil p)))))))))))))
def c1784 : List Lit := [(1683, true), (1760, true), (1739, false), (86, true)]
theorem step1784 (p : Nat → Bool) (h : Constraints p) : clause p c1784 = true :=
  Snake9.LocalRup.prove_clause [c810, c1338, c1341, c1331, c1320, c1328, c1313, c492, c1776, c572] c1784 (by decide) p (sat_cons (step810 p h) (sat_cons (step1338 p h) (sat_cons (step1341 p h) (sat_cons (step1331 p h) (sat_cons (step1320 p h) (sat_cons (step1328 p h) (sat_cons (step1313 p h) (sat_cons (step492 p h) (sat_cons (step1776 p h) (sat_cons (step572 p h) (sat_nil p)))))))))))
def c1785 : List Lit := [(3, false), (9, false)]
theorem step1785 (p : Nat → Bool) (h : Constraints p) : clause p c1785 = true :=
  Snake9.LocalRup.prove_clause [c5, c1612, c1] c1785 (by decide) p (sat_cons (step5 p h) (sat_cons (step1612 p h) (sat_cons (step1 p h) (sat_nil p))))
def c1786 : List Lit := [(125, false), (9, false)]
theorem step1786 (p : Nat → Bool) (h : Constraints p) : clause p c1786 = true :=
  Snake9.LocalRup.prove_clause [c5, c2] c1786 (by decide) p (sat_cons (step5 p h) (sat_cons (step2 p h) (sat_nil p)))
def c1787 : List Lit := [(9, true), (3, true), (125, true)]
theorem step1787 (p : Nat → Bool) (h : Constraints p) : clause p c1787 = true :=
  Snake9.LocalRup.prove_clause [c1612, c3] c1787 (by decide) p (sat_cons (step1612 p h) (sat_cons (step3 p h) (sat_nil p)))
def c1788 : List Lit := [(3, false), (7, true)]
theorem step1788 (p : Nat → Bool) (h : Constraints p) : clause p c1788 = true :=
  Snake9.LocalRup.prove_clause [c769, c6] c1788 (by decide) p (sat_cons (step769 p h) (sat_cons (step6 p h) (sat_nil p)))
def c1789 : List Lit := [(10, true), (19, true), (5, false)]
theorem step1789 (p : Nat → Bool) (h : Constraints p) : clause p c1789 = true :=
  Snake9.LocalRup.prove_clause [c770, c10] c1789 (by decide) p (sat_cons (step770 p h) (sat_cons (step10 p h) (sat_nil p)))
def c1790 : List Lit := [(19, true), (4, true), (5, false)]
theorem step1790 (p : Nat → Bool) (h : Constraints p) : clause p c1790 = true :=
  Snake9.LocalRup.prove_clause [c770, c11] c1790 (by decide) p (sat_cons (step770 p h) (sat_cons (step11 p h) (sat_nil p)))
def c1791 : List Lit := [(4, true), (5, false), (10, true)]
theorem step1791 (p : Nat → Bool) (h : Constraints p) : clause p c1791 = true :=
  Snake9.LocalRup.prove_clause [c770, c12] c1791 (by decide) p (sat_cons (step770 p h) (sat_cons (step12 p h) (sat_nil p)))
def c1792 : List Lit := [(6, false), (11, true), (7, true)]
theorem step1792 (p : Nat → Bool) (h : Constraints p) : clause p c1792 = true :=
  Snake9.LocalRup.prove_clause [c771, c14] c1792 (by decide) p (sat_cons (step771 p h) (sat_cons (step14 p h) (sat_nil p)))
def c1793 : List Lit := [(11, true), (6, false), (4, true)]
theorem step1793 (p : Nat → Bool) (h : Constraints p) : clause p c1793 = true :=
  Snake9.LocalRup.prove_clause [c771, c15] c1793 (by decide) p (sat_cons (step771 p h) (sat_cons (step15 p h) (sat_nil p)))
def c1794 : List Lit := [(6, false), (7, true), (4, true)]
theorem step1794 (p : Nat → Bool) (h : Constraints p) : clause p c1794 = true :=
  Snake9.LocalRup.prove_clause [c771, c16] c1794 (by decide) p (sat_cons (step771 p h) (sat_cons (step16 p h) (sat_nil p)))
def c1795 : List Lit := [(25, true), (8, false), (43, true)]
theorem step1795 (p : Nat → Bool) (h : Constraints p) : clause p c1795 = true :=
  Snake9.LocalRup.prove_clause [c772, c21] c1795 (by decide) p (sat_cons (step772 p h) (sat_cons (step21 p h) (sat_nil p)))
def c1796 : List Lit := [(10, true), (8, false), (43, true)]
theorem step1796 (p : Nat → Bool) (h : Constraints p) : clause p c1796 = true :=
  Snake9.LocalRup.prove_clause [c772, c22] c1796 (by decide) p (sat_cons (step772 p h) (sat_cons (step22 p h) (sat_nil p)))
def c1797 : List Lit := [(10, true), (25, true), (8, false)]
theorem step1797 (p : Nat → Bool) (h : Constraints p) : clause p c1797 = true :=
  Snake9.LocalRup.prove_clause [c772, c23] c1797 (by decide) p (sat_cons (step772 p h) (sat_cons (step23 p h) (sat_nil p)))
def c1798 : List Lit := [(9, false), (28, true), (44, true)]
theorem step1798 (p : Nat → Bool) (h : Constraints p) : clause p c1798 = true :=
  Snake9.LocalRup.prove_clause [c773, c25] c1798 (by decide) p (sat_cons (step773 p h) (sat_cons (step25 p h) (sat_nil p)))
def c1799 : List Lit := [(12, true), (5, true), (47, true), (10, false), (8, true), (29, true)]
theorem step1799 (p : Nat → Bool) (h : Constraints p) : clause p c1799 = true :=
  Snake9.LocalRup.prove_clause [c1614, c26] c1799 (by decide) p (sat_cons (step1614 p h) (sat_cons (step26 p h) (sat_nil p)))
def c1800 : List Lit := [(12, true), (10, false), (29, true), (134, true), (47, true), (8, true)]
theorem step1800 (p : Nat → Bool) (h : Constraints p) : clause p c1800 = true :=
  Snake9.LocalRup.prove_clause [c1614, c37] c1800 (by decide) p (sat_cons (step1614 p h) (sat_cons (step37 p h) (sat_nil p)))
def c1801 : List Lit := [(5, true), (47, true), (29, true), (134, true), (10, false), (8, true)]
theorem step1801 (p : Nat → Bool) (h : Constraints p) : clause p c1801 = true :=
  Snake9.LocalRup.prove_clause [c1614, c38] c1801 (by decide) p (sat_cons (step1614 p h) (sat_cons (step38 p h) (sat_nil p)))
def c1802 : List Lit := [(12, true), (5, true), (10, false), (8, true), (134, true), (47, true)]
theorem step1802 (p : Nat → Bool) (h : Constraints p) : clause p c1802 = true :=
  Snake9.LocalRup.prove_clause [c1614, c39] c1802 (by decide) p (sat_cons (step1614 p h) (sat_cons (step39 p h) (sat_nil p)))
def c1803 : List Lit := [(12, true), (8, true), (134, true), (29, true), (5, true), (10, false)]
theorem step1803 (p : Nat → Bool) (h : Constraints p) : clause p c1803 = true :=
  Snake9.LocalRup.prove_clause [c1614, c40] c1803 (by decide) p (sat_cons (step1614 p h) (sat_cons (step40 p h) (sat_nil p)))
end B112E020
