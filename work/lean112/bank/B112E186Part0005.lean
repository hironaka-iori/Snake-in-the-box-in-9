import B112E186Part0004
namespace B112E186
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1720 : List Lit := [(1609, false), (1628, true)]
theorem step1720 (p : Nat → Bool) (h : Constraints p) : clause p c1720 = true :=
  Snake9.LocalRup.prove_clause [c1516, c1017] c1720 (by decide) p (sat_cons (step1516 p h) (sat_cons (step1017 p h) (sat_nil p)))
def c1721 : List Lit := [(1610, false), (1629, true)]
theorem step1721 (p : Nat → Bool) (h : Constraints p) : clause p c1721 = true :=
  Snake9.LocalRup.prove_clause [c1516, c1018] c1721 (by decide) p (sat_cons (step1516 p h) (sat_cons (step1018 p h) (sat_nil p)))
def c1722 : List Lit := [(1611, false), (1630, true)]
theorem step1722 (p : Nat → Bool) (h : Constraints p) : clause p c1722 = true :=
  Snake9.LocalRup.prove_clause [c1516, c1019] c1722 (by decide) p (sat_cons (step1516 p h) (sat_cons (step1019 p h) (sat_nil p)))
def c1723 : List Lit := [(1612, false), (1631, true)]
theorem step1723 (p : Nat → Bool) (h : Constraints p) : clause p c1723 = true :=
  Snake9.LocalRup.prove_clause [c1516, c1020] c1723 (by decide) p (sat_cons (step1516 p h) (sat_cons (step1020 p h) (sat_nil p)))
def c1724 : List Lit := [(1684, true), (1679, false)]
theorem step1724 (p : Nat → Bool) (h : Constraints p) : clause p c1724 = true :=
  Snake9.LocalRup.prove_clause [c1473, c1127] c1724 (by decide) p (sat_cons (step1473 p h) (sat_cons (step1127 p h) (sat_nil p)))
def c1725 : List Lit := [(1685, true), (1680, false)]
theorem step1725 (p : Nat → Bool) (h : Constraints p) : clause p c1725 = true :=
  Snake9.LocalRup.prove_clause [c1473, c1128] c1725 (by decide) p (sat_cons (step1473 p h) (sat_cons (step1128 p h) (sat_nil p)))
def c1726 : List Lit := [(1686, true), (1681, false)]
theorem step1726 (p : Nat → Bool) (h : Constraints p) : clause p c1726 = true :=
  Snake9.LocalRup.prove_clause [c1473, c1129] c1726 (by decide) p (sat_cons (step1473 p h) (sat_cons (step1129 p h) (sat_nil p)))
def c1727 : List Lit := [(1682, false), (1687, true)]
theorem step1727 (p : Nat → Bool) (h : Constraints p) : clause p c1727 = true :=
  Snake9.LocalRup.prove_clause [c1473, c1130] c1727 (by decide) p (sat_cons (step1473 p h) (sat_cons (step1130 p h) (sat_nil p)))
def c1728 : List Lit := [(1693, true), (1660, false)]
theorem step1728 (p : Nat → Bool) (h : Constraints p) : clause p c1728 = true :=
  Snake9.LocalRup.prove_clause [c1491, c1158] c1728 (by decide) p (sat_cons (step1491 p h) (sat_cons (step1158 p h) (sat_nil p)))
def c1729 : List Lit := [(1661, false), (1694, true)]
theorem step1729 (p : Nat → Bool) (h : Constraints p) : clause p c1729 = true :=
  Snake9.LocalRup.prove_clause [c1491, c1165] c1729 (by decide) p (sat_cons (step1491 p h) (sat_cons (step1165 p h) (sat_nil p)))
def c1730 : List Lit := [(1662, false), (1695, true)]
theorem step1730 (p : Nat → Bool) (h : Constraints p) : clause p c1730 = true :=
  Snake9.LocalRup.prove_clause [c1491, c1172] c1730 (by decide) p (sat_cons (step1491 p h) (sat_cons (step1172 p h) (sat_nil p)))
def c1731 : List Lit := [(1724, true), (1719, false)]
theorem step1731 (p : Nat → Bool) (h : Constraints p) : clause p c1731 = true :=
  Snake9.LocalRup.prove_clause [c1440, c1211] c1731 (by decide) p (sat_cons (step1440 p h) (sat_cons (step1211 p h) (sat_nil p)))
def c1732 : List Lit := [(1725, true), (1720, false)]
theorem step1732 (p : Nat → Bool) (h : Constraints p) : clause p c1732 = true :=
  Snake9.LocalRup.prove_clause [c1440, c1212] c1732 (by decide) p (sat_cons (step1440 p h) (sat_cons (step1212 p h) (sat_nil p)))
def c1733 : List Lit := [(1721, false), (1726, true)]
theorem step1733 (p : Nat → Bool) (h : Constraints p) : clause p c1733 = true :=
  Snake9.LocalRup.prove_clause [c1440, c1213] c1733 (by decide) p (sat_cons (step1440 p h) (sat_cons (step1213 p h) (sat_nil p)))
def c1734 : List Lit := [(1722, false), (1727, true)]
theorem step1734 (p : Nat → Bool) (h : Constraints p) : clause p c1734 = true :=
  Snake9.LocalRup.prove_clause [c1440, c1214] c1734 (by decide) p (sat_cons (step1440 p h) (sat_cons (step1214 p h) (sat_nil p)))
def c1735 : List Lit := [(1748, true), (1735, false)]
theorem step1735 (p : Nat → Bool) (h : Constraints p) : clause p c1735 = true :=
  Snake9.LocalRup.prove_clause [c1534, c1261] c1735 (by decide) p (sat_cons (step1534 p h) (sat_cons (step1261 p h) (sat_nil p)))
def c1736 : List Lit := [(1736, false), (1749, true)]
theorem step1736 (p : Nat → Bool) (h : Constraints p) : clause p c1736 = true :=
  Snake9.LocalRup.prove_clause [c1534, c1265] c1736 (by decide) p (sat_cons (step1534 p h) (sat_cons (step1265 p h) (sat_nil p)))
def c1737 : List Lit := [(1737, false), (1750, true)]
theorem step1737 (p : Nat → Bool) (h : Constraints p) : clause p c1737 = true :=
  Snake9.LocalRup.prove_clause [c1534, c1268] c1737 (by decide) p (sat_cons (step1534 p h) (sat_cons (step1268 p h) (sat_nil p)))
def c1738 : List Lit := [(1738, false), (1751, true)]
theorem step1738 (p : Nat → Bool) (h : Constraints p) : clause p c1738 = true :=
  Snake9.LocalRup.prove_clause [c1534, c1271] c1738 (by decide) p (sat_cons (step1534 p h) (sat_cons (step1271 p h) (sat_nil p)))
def c1739 : List Lit := [(1750, false), (1759, true)]
theorem step1739 (p : Nat → Bool) (h : Constraints p) : clause p c1739 = true :=
  Snake9.LocalRup.prove_clause [c1441, c1272] c1739 (by decide) p (sat_cons (step1441 p h) (sat_cons (step1272 p h) (sat_nil p)))
def c1740 : List Lit := [(1757, true), (1724, false)]
theorem step1740 (p : Nat → Bool) (h : Constraints p) : clause p c1740 = true :=
  Snake9.LocalRup.prove_clause [c1525, c1273] c1740 (by decide) p (sat_cons (step1525 p h) (sat_cons (step1273 p h) (sat_nil p)))
def c1741 : List Lit := [(1759, true), (1726, false)]
theorem step1741 (p : Nat → Bool) (h : Constraints p) : clause p c1741 = true :=
  Snake9.LocalRup.prove_clause [c1525, c1282] c1741 (by decide) p (sat_cons (step1525 p h) (sat_cons (step1282 p h) (sat_nil p)))
def c1742 : List Lit := [(1760, true), (1727, false)]
theorem step1742 (p : Nat → Bool) (h : Constraints p) : clause p c1742 = true :=
  Snake9.LocalRup.prove_clause [c1525, c1287] c1742 (by decide) p (sat_cons (step1525 p h) (sat_cons (step1287 p h) (sat_nil p)))
def c1743 : List Lit := [(1761, true), (1728, false)]
theorem step1743 (p : Nat → Bool) (h : Constraints p) : clause p c1743 = true :=
  Snake9.LocalRup.prove_clause [c1525, c1292] c1743 (by decide) p (sat_cons (step1525 p h) (sat_cons (step1292 p h) (sat_nil p)))
def c1744 : List Lit := [(1729, false), (1762, true)]
theorem step1744 (p : Nat → Bool) (h : Constraints p) : clause p c1744 = true :=
  Snake9.LocalRup.prove_clause [c1525, c1295] c1744 (by decide) p (sat_cons (step1525 p h) (sat_cons (step1295 p h) (sat_nil p)))
def c1745 : List Lit := [(1762, false), (1779, true)]
theorem step1745 (p : Nat → Bool) (h : Constraints p) : clause p c1745 = true :=
  Snake9.LocalRup.prove_clause [c1492, c1296] c1745 (by decide) p (sat_cons (step1492 p h) (sat_cons (step1296 p h) (sat_nil p)))
def c1746 : List Lit := [(1626, false), (1786, false)]
theorem step1746 (p : Nat → Bool) (h : Constraints p) : clause p c1746 = true :=
  Snake9.LocalRup.prove_clause [c1350, c1341] c1746 (by decide) p (sat_cons (step1350 p h) (sat_cons (step1341 p h) (sat_nil p)))
def c1747 : List Lit := [(1627, false), (1785, false)]
theorem step1747 (p : Nat → Bool) (h : Constraints p) : clause p c1747 = true :=
  Snake9.LocalRup.prove_clause [c1350, c1342] c1747 (by decide) p (sat_cons (step1350 p h) (sat_cons (step1342 p h) (sat_nil p)))
def c1748 : List Lit := [(1628, false), (1784, false)]
theorem step1748 (p : Nat → Bool) (h : Constraints p) : clause p c1748 = true :=
  Snake9.LocalRup.prove_clause [c1350, c1343] c1748 (by decide) p (sat_cons (step1350 p h) (sat_cons (step1343 p h) (sat_nil p)))
def c1749 : List Lit := [(1629, false), (1783, false)]
theorem step1749 (p : Nat → Bool) (h : Constraints p) : clause p c1749 = true :=
  Snake9.LocalRup.prove_clause [c1350, c1344] c1749 (by decide) p (sat_cons (step1350 p h) (sat_cons (step1344 p h) (sat_nil p)))
def c1750 : List Lit := [(1630, false), (1782, false)]
theorem step1750 (p : Nat → Bool) (h : Constraints p) : clause p c1750 = true :=
  Snake9.LocalRup.prove_clause [c1350, c1345] c1750 (by decide) p (sat_cons (step1350 p h) (sat_cons (step1345 p h) (sat_nil p)))
def c1751 : List Lit := [(1631, false), (1781, false)]
theorem step1751 (p : Nat → Bool) (h : Constraints p) : clause p c1751 = true :=
  Snake9.LocalRup.prove_clause [c1350, c1346] c1751 (by decide) p (sat_cons (step1350 p h) (sat_cons (step1346 p h) (sat_nil p)))
def c1752 : List Lit := [(1632, false), (1780, false)]
theorem step1752 (p : Nat → Bool) (h : Constraints p) : clause p c1752 = true :=
  Snake9.LocalRup.prove_clause [c1350, c1347] c1752 (by decide) p (sat_cons (step1350 p h) (sat_cons (step1347 p h) (sat_nil p)))
def c1753 : List Lit := [(1633, false), (1779, false)]
theorem step1753 (p : Nat → Bool) (h : Constraints p) : clause p c1753 = true :=
  Snake9.LocalRup.prove_clause [c1350, c1348] c1753 (by decide) p (sat_cons (step1350 p h) (sat_cons (step1348 p h) (sat_nil p)))
def c1754 : List Lit := [(1634, false), (1778, false)]
theorem step1754 (p : Nat → Bool) (h : Constraints p) : clause p c1754 = true :=
  Snake9.LocalRup.prove_clause [c1350, c1349] c1754 (by decide) p (sat_cons (step1350 p h) (sat_cons (step1349 p h) (sat_nil p)))
def c1755 : List Lit := [(1759, true), (1712, false), (1717, false)]
theorem step1755 (p : Nat → Bool) (h : Constraints p) : clause p c1755 = true :=
  Snake9.LocalRup.prove_clause [c1525, c1534, c1466] c1755 (by decide) p (sat_cons (step1525 p h) (sat_cons (step1534 p h) (sat_cons (step1466 p h) (sat_nil p))))
def c1756 : List Lit := [(1748, true), (107, false), (101, false)]
theorem step1756 (p : Nat → Bool) (h : Constraints p) : clause p c1756 = true :=
  Snake9.LocalRup.prove_clause [c1534, c1467] c1756 (by decide) p (sat_cons (step1534 p h) (sat_cons (step1467 p h) (sat_nil p)))
def c1757 : List Lit := [(97, false), (85, true), (84, false), (101, false)]
theorem step1757 (p : Nat → Bool) (h : Constraints p) : clause p c1757 = true :=
  Snake9.LocalRup.prove_clause [c1652, c456] c1757 (by decide) p (sat_cons (step1652 p h) (sat_cons (step456 p h) (sat_nil p)))
def c1758 : List Lit := [(19, true), (1535, true), (15, true)]
theorem step1758 (p : Nat → Bool) (h : Constraints p) : clause p c1758 = true :=
  Snake9.LocalRup.prove_clause [c849, c884, c858, c851, c853, c857, c860, c881, c850, c868, c1502] c1758 (by decide) p (sat_cons (step849 p h) (sat_cons (step884 p h) (sat_cons (step858 p h) (sat_cons (step851 p h) (sat_cons (step853 p h) (sat_cons (step857 p h) (sat_cons (step860 p h) (sat_cons (step881 p h) (sat_cons (step850 p h) (sat_cons (step868 p h) (sat_cons (step1502 p h) (sat_nil p))))))))))))
def c1759 : List Lit := [(1737, true), (88, true), (120, true), (113, true), (109, true), (105, false)]
theorem step1759 (p : Nat → Bool) (h : Constraints p) : clause p c1759 = true :=
  Snake9.LocalRup.prove_clause [c1232, c1229, c1238, c1240, c1233, c1230, c1673, c598] c1759 (by decide) p (sat_cons (step1232 p h) (sat_cons (step1229 p h) (sat_cons (step1238 p h) (sat_cons (step1240 p h) (sat_cons (step1233 p h) (sat_cons (step1230 p h) (sat_cons (step1673 p h) (sat_cons (step598 p h) (sat_nil p)))))))))
def c1760 : List Lit := [(117, false), (118, true), (105, false), (94, false)]
theorem step1760 (p : Nat → Bool) (h : Constraints p) : clause p c1760 = true :=
  Snake9.LocalRup.prove_clause [c625, c1684] c1760 (by decide) p (sat_cons (step625 p h) (sat_cons (step1684 p h) (sat_nil p)))
def c1761 : List Lit := [(1534, true), (83, false), (87, false)]
theorem step1761 (p : Nat → Bool) (h : Constraints p) : clause p c1761 = true :=
  Snake9.LocalRup.prove_clause [c1520, c1523] c1761 (by decide) p (sat_cons (step1520 p h) (sat_cons (step1523 p h) (sat_nil p)))
def c1762 : List Lit := [(1597, true), (47, false), (84, false)]
theorem step1762 (p : Nat → Bool) (h : Constraints p) : clause p c1762 = true :=
  Snake9.LocalRup.prove_clause [c1431, c1482, c948, c963, c157] c1762 (by decide) p (sat_cons (step1431 p h) (sat_cons (step1482 p h) (sat_cons (step948 p h) (sat_cons (step963 p h) (sat_cons (step157 p h) (sat_nil p))))))
def c1763 : List Lit := [(98, false), (96, true), (1715, true)]
theorem step1763 (p : Nat → Bool) (h : Constraints p) : clause p c1763 = true :=
  Snake9.LocalRup.prove_clause [c1197, c1196, c524, c1654] c1763 (by decide) p (sat_cons (step1197 p h) (sat_cons (step1196 p h) (sat_cons (step524 p h) (sat_cons (step1654 p h) (sat_nil p)))))
def c1764 : List Lit := [(1645, false), (1660, true), (53, false), (48, false)]
theorem step1764 (p : Nat → Bool) (h : Constraints p) : clause p c1764 = true :=
  Snake9.LocalRup.prove_clause [c1089, c1059, c1062, c1086, c1053, c1075, c186, c1067] c1764 (by decide) p (sat_cons (step1089 p h) (sat_cons (step1059 p h) (sat_cons (step1062 p h) (sat_cons (step1086 p h) (sat_cons (step1053 p h) (sat_cons (step1075 p h) (sat_cons (step186 p h) (sat_cons (step1067 p h) (sat_nil p)))))))))
def c1765 : List Lit := [(1599, true), (1589, false), (51, true)]
theorem step1765 (p : Nat → Bool) (h : Constraints p) : clause p c1765 = true :=
  Snake9.LocalRup.prove_clause [c973, c951, c954, c981, c974, c984, c1470, c955, c953] c1765 (by decide) p (sat_cons (step973 p h) (sat_cons (step951 p h) (sat_cons (step954 p h) (sat_cons (step981 p h) (sat_cons (step974 p h) (sat_cons (step984 p h) (sat_cons (step1470 p h) (sat_cons (step955 p h) (sat_cons (step953 p h) (sat_nil p))))))))))
def c1766 : List Lit := [(1660, true), (53, false), (47, false), (106, false), (67, true), (48, false)]
theorem step1766 (p : Nat → Bool) (h : Constraints p) : clause p c1766 = true :=
  Snake9.LocalRup.prove_clause [c1082, c1764, c1056, c226, c1629, c1070, c1073, c1076, c1086, c1067, c1061, c186, c1053] c1766 (by decide) p (sat_cons (step1082 p h) (sat_cons (step1764 p h) (sat_cons (step1056 p h) (sat_cons (step226 p h) (sat_cons (step1629 p h) (sat_cons (step1070 p h) (sat_cons (step1073 p h) (sat_cons (step1076 p h) (sat_cons (step1086 p h) (sat_cons (step1067 p h) (sat_cons (step1061 p h) (sat_cons (step186 p h) (sat_cons (step1053 p h) (sat_nil p))))))))))))))
def c1767 : List Lit := [(1717, false), (1725, true)]
theorem step1767 (p : Nat → Bool) (h : Constraints p) : clause p c1767 = true :=
  Snake9.LocalRup.prove_clause [c1732, c1202, c1205, c1216, c1487] c1767 (by decide) p (sat_cons (step1732 p h) (sat_cons (step1202 p h) (sat_cons (step1205 p h) (sat_cons (step1216 p h) (sat_cons (step1487 p h) (sat_nil p))))))
def c1768 : List Lit := [(1724, true)]
theorem step1768 (p : Nat → Bool) (h : Constraints p) : clause p c1768 = true :=
  Snake9.LocalRup.prove_clause [c1215, c1731, c1487, c1204] c1768 (by decide) p (sat_cons (step1215 p h) (sat_cons (step1731 p h) (sat_cons (step1487 p h) (sat_cons (step1204 p h) (sat_nil p)))))
def c1769 : List Lit := [(1569, true), (37, true)]
theorem step1769 (p : Nat → Bool) (h : Constraints p) : clause p c1769 = true :=
  Snake9.LocalRup.prove_clause [c921, c931, c929, c922, c923, c924, c1428] c1769 (by decide) p (sat_cons (step921 p h) (sat_cons (step931 p h) (sat_cons (step929 p h) (sat_cons (step922 p h) (sat_cons (step923 p h) (sat_cons (step924 p h) (sat_cons (step1428 p h) (sat_nil p))))))))
def c1770 : List Lit := [(1566, true), (44, false)]
theorem step1770 (p : Nat → Bool) (h : Constraints p) : clause p c1770 = true :=
  Snake9.LocalRup.prove_clause [c1587, c923, c924, c154] c1770 (by decide) p (sat_cons (step1587 p h) (sat_cons (step923 p h) (sat_cons (step924 p h) (sat_cons (step154 p h) (sat_nil p)))))
def c1771 : List Lit := [(114, true), (1737, true), (33, false), (85, true), (112, true), (107, false)]
theorem step1771 (p : Nat → Bool) (h : Constraints p) : clause p c1771 = true :=
  Snake9.LocalRup.prove_clause [c1228, c1238, c1231, c1233, c1240, c1230, c574, c551, c1665] c1771 (by decide) p (sat_cons (step1228 p h) (sat_cons (step1238 p h) (sat_cons (step1231 p h) (sat_cons (step1233 p h) (sat_cons (step1240 p h) (sat_cons (step1230 p h) (sat_cons (step574 p h) (sat_cons (step551 p h) (sat_cons (step1665 p h) (sat_nil p))))))))))
def c1772 : List Lit := [(1757, true)]
theorem step1772 (p : Nat → Bool) (h : Constraints p) : clause p c1772 = true :=
  Snake9.LocalRup.prove_clause [c1768, c1740] c1772 (by decide) p (sat_cons (step1768 p h) (sat_cons (step1740 p h) (sat_nil p)))
def c1773 : List Lit := [(13, false), (17, false), (36, false), (85, true)]
theorem step1773 (p : Nat → Bool) (h : Constraints p) : clause p c1773 = true :=
  Snake9.LocalRup.prove_clause [c1547, c48] c1773 (by decide) p (sat_cons (step1547 p h) (sat_cons (step48 p h) (sat_nil p)))
def c1774 : List Lit := [(1527, false), (1535, true), (19, false), (16, true), (1556, true)]
theorem step1774 (p : Nat → Bool) (h : Constraints p) : clause p c1774 = true :=
  Snake9.LocalRup.prove_clause [c848, c856, c879, c868, c871, c881, c862, c863, c859, c850, c1452, c69, c28, c1553] c1774 (by decide) p (sat_cons (step848 p h) (sat_cons (step856 p h) (sat_cons (step879 p h) (sat_cons (step868 p h) (sat_cons (step871 p h) (sat_cons (step881 p h) (sat_cons (step862 p h) (sat_cons (step863 p h) (sat_cons (step859 p h) (sat_cons (step850 p h) (sat_cons (step1452 p h) (sat_cons (step69 p h) (sat_cons (step28 p h) (sat_cons (step1553 p h) (sat_nil p)))))))))))))))
def c1775 : List Lit := [(1597, true), (51, true)]
theorem step1775 (p : Nat → Bool) (h : Constraints p) : clause p c1775 = true :=
  Snake9.LocalRup.prove_clause [c951, c954, c982, c979, c955, c968, c953, c1470] c1775 (by decide) p (sat_cons (step951 p h) (sat_cons (step954 p h) (sat_cons (step982 p h) (sat_cons (step979 p h) (sat_cons (step955 p h) (sat_cons (step968 p h) (sat_cons (step953 p h) (sat_cons (step1470 p h) (sat_nil p)))))))))
def c1776 : List Lit := [(105, false), (1737, true), (106, false), (112, true), (107, false)]
theorem step1776 (p : Nat → Bool) (h : Constraints p) : clause p c1776 = true :=
  Snake9.LocalRup.prove_clause [c549, c548, c1232, c1230, c1240] c1776 (by decide) p (sat_cons (step549 p h) (sat_cons (step548 p h) (sat_cons (step1232 p h) (sat_cons (step1230 p h) (sat_cons (step1240 p h) (sat_nil p))))))
def c1777 : List Lit := [(1598, true), (1662, true), (85, true), (51, true), (107, false)]
theorem step1777 (p : Nat → Bool) (h : Constraints p) : clause p c1777 = true :=
  Snake9.LocalRup.prove_clause [c1509, c1476, c948, c963, c1481, c1590, c1589, c1362] c1777 (by decide) p (sat_cons (step1509 p h) (sat_cons (step1476 p h) (sat_cons (step948 p h) (sat_cons (step963 p h) (sat_cons (step1481 p h) (sat_cons (step1590 p h) (sat_cons (step1589 p h) (sat_cons (step1362 p h) (sat_nil p)))))))))
def c1778 : List Lit := [(66, true), (105, false), (111, true), (1648, true), (1672, true), (71, false), (69, false), (100, false)]
theorem step1778 (p : Nat → Bool) (h : Constraints p) : clause p c1778 = true :=
  Snake9.LocalRup.prove_clause [c1060, c1109, c1056, c1058, c1062, c219, c1053, c1054, c1619, c211, c276, c1611, c1098, c1100, c1107, c1631, c1102, c289, c288, c1625] c1778 (by decide) p (sat_cons (step1060 p h) (sat_cons (step1109 p h) (sat_cons (step1056 p h) (sat_cons (step1058 p h) (sat_cons (step1062 p h) (sat_cons (step219 p h) (sat_cons (step1053 p h) (sat_cons (step1054 p h) (sat_cons (step1619 p h) (sat_cons (step211 p h) (sat_cons (step276 p h) (sat_cons (step1611 p h) (sat_cons (step1098 p h) (sat_cons (step1100 p h) (sat_cons (step1107 p h) (sat_cons (step1631 p h) (sat_cons (step1102 p h) (sat_cons (step289 p h) (sat_cons (step288 p h) (sat_cons (step1625 p h) (sat_nil p)))))))))))))))))))))
def c1779 : List Lit := [(78, true), (63, false), (1672, true), (1654, true), (66, false)]
theorem step1779 (p : Nat → Bool) (h : Constraints p) : clause p c1779 = true :=
  Snake9.LocalRup.prove_clause [c1109, c1098, c1100, c1107, c1631, c1632, c1102, c289, c288, c269, c1625, c1072] c1779 (by decide) p (sat_cons (step1109 p h) (sat_cons (step1098 p h) (sat_cons (step1100 p h) (sat_cons (step1107 p h) (sat_cons (step1631 p h) (sat_cons (step1632 p h) (sat_cons (step1102 p h) (sat_cons (step289 p h) (sat_cons (step288 p h) (sat_cons (step269 p h) (sat_cons (step1625 p h) (sat_cons (step1072 p h) (sat_nil p)))))))))))))
def c1780 : List Lit := [(1715, true), (99, false), (60, false)]
theorem step1780 (p : Nat → Bool) (h : Constraints p) : clause p c1780 = true :=
  Snake9.LocalRup.prove_clause [c1196, c1197, c480] c1780 (by decide) p (sat_cons (step1196 p h) (sat_cons (step1197 p h) (sat_cons (step480 p h) (sat_nil p))))
def c1781 : List Lit := [(119, true), (242, true), (1740, true), (105, false), (123, true), (109, false)]
theorem step1781 (p : Nat → Bool) (h : Constraints p) : clause p c1781 = true :=
  Snake9.LocalRup.prove_clause [c1244, c630, c561, c1685] c1781 (by decide) p (sat_cons (step1244 p h) (sat_cons (step630 p h) (sat_cons (step561 p h) (sat_cons (step1685 p h) (sat_nil p)))))
def c1782 : List Lit := [(1695, true), (1670, false), (1686, false), (1680, false)]
theorem step1782 (p : Nat → Bool) (h : Constraints p) : clause p c1782 = true :=
  Snake9.LocalRup.prove_clause [c1149, c1154, c1138, c1081, c1085, c1108, c1073, c1059, c1099, c1070, c1056, c1632, c269] c1782 (by decide) p (sat_cons (step1149 p h) (sat_cons (step1154 p h) (sat_cons (step1138 p h) (sat_cons (step1081 p h) (sat_cons (step1085 p h) (sat_cons (step1108 p h) (sat_cons (step1073 p h) (sat_cons (step1059 p h) (sat_cons (step1099 p h) (sat_cons (step1070 p h) (sat_cons (step1056 p h) (sat_cons (step1632 p h) (sat_cons (step269 p h) (sat_nil p))))))))))))))
def c1783 : List Lit := [(1733, true), (105, false), (109, false), (121, true)]
theorem step1783 (p : Nat → Bool) (h : Constraints p) : clause p c1783 = true :=
  Snake9.LocalRup.prove_clause [c1231, c1232, c550, c599, c1677, c624] c1783 (by decide) p (sat_cons (step1231 p h) (sat_cons (step1232 p h) (sat_cons (step550 p h) (sat_cons (step599 p h) (sat_cons (step1677 p h) (sat_cons (step624 p h) (sat_nil p)))))))
end B112E186
