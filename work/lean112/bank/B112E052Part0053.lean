import B112E052Part0052
namespace B112E052
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c5382 : List Lit := [(1712, true), (122, false)]
theorem step5382 (p : Nat → Bool) (h : Constraints p) : clause p c5382 = true :=
  Snake9.LocalRup.prove_clause [c1561, c2078, c2601, c2158, c1535] c5382 (by decide) p (sat_cons (step1561 p h) (sat_cons (step2078 p h) (sat_cons (step2601 p h) (sat_cons (step2158 p h) (sat_cons (step1535 p h) (sat_nil p))))))
def c5383 : List Lit := [(79, false), (1740, false), (69, false), (1620, false), (80, true), (46, true), (121, false), (101, true), (122, false), (1810, false), (99, false), (112, false)]
theorem step5383 (p : Nat → Bool) (h : Constraints p) : clause p c5383 = true :=
  Snake9.LocalRup.prove_clause [c4955, c912, c4952, c5336, c4325, c1654, c1347, c1875, c1349, c2470, c1374, c5346] c5383 (by decide) p (sat_cons (step4955 p h) (sat_cons (step912 p h) (sat_cons (step4952 p h) (sat_cons (step5336 p h) (sat_cons (step4325 p h) (sat_cons (step1654 p h) (sat_cons (step1347 p h) (sat_cons (step1875 p h) (sat_cons (step1349 p h) (sat_cons (step2470 p h) (sat_cons (step1374 p h) (sat_cons (step5346 p h) (sat_nil p)))))))))))))
def c5384 : List Lit := [(1625, true), (44, false), (1620, false), (39, true), (122, false)]
theorem step5384 (p : Nat → Bool) (h : Constraints p) : clause p c5384 = true :=
  Snake9.LocalRup.prove_clause [c1371, c1374, c2538, c1349, c1347] c5384 (by decide) p (sat_cons (step1371 p h) (sat_cons (step1374 p h) (sat_cons (step2538 p h) (sat_cons (step1349 p h) (sat_cons (step1347 p h) (sat_nil p))))))
def c5385 : List Lit := [(1795, true), (118, false), (126, false), (1764, true), (112, false), (116, true)]
theorem step5385 (p : Nat → Bool) (h : Constraints p) : clause p c5385 = true :=
  Snake9.LocalRup.prove_clause [c1756, c1758, c2094, c1753, c1751, c5199, c887, c5344] c5385 (by decide) p (sat_cons (step1756 p h) (sat_cons (step1758 p h) (sat_cons (step2094 p h) (sat_cons (step1753 p h) (sat_cons (step1751 p h) (sat_cons (step5199 p h) (sat_cons (step887 p h) (sat_cons (step5344 p h) (sat_nil p)))))))))
def c5386 : List Lit := [(126, false), (1770, false), (107, true), (112, false), (1811, true), (100, false), (1796, true), (116, true)]
theorem step5386 (p : Nat → Bool) (h : Constraints p) : clause p c5386 = true :=
  Snake9.LocalRup.prove_clause [c1817, c1699, c1709, c1725, c5377, c1742, c1739, c1740, c5385, c1764, c1811, c1716, c1720, c1712, c1693, c5379, c1701, c1685, c1686, c2093, c756, c691, c5344, c2339, c887, c623, c1753, c2347, c1759, c949, c1750] c5386 (by decide) p (sat_cons (step1817 p h) (sat_cons (step1699 p h) (sat_cons (step1709 p h) (sat_cons (step1725 p h) (sat_cons (step5377 p h) (sat_cons (step1742 p h) (sat_cons (step1739 p h) (sat_cons (step1740 p h) (sat_cons (step5385 p h) (sat_cons (step1764 p h) (sat_cons (step1811 p h) (sat_cons (step1716 p h) (sat_cons (step1720 p h) (sat_cons (step1712 p h) (sat_cons (step1693 p h) (sat_cons (step5379 p h) (sat_cons (step1701 p h) (sat_cons (step1685 p h) (sat_cons (step1686 p h) (sat_cons (step2093 p h) (sat_cons (step756 p h) (sat_cons (step691 p h) (sat_cons (step5344 p h) (sat_cons (step2339 p h) (sat_cons (step887 p h) (sat_cons (step623 p h) (sat_cons (step1753 p h) (sat_cons (step2347 p h) (sat_cons (step1759 p h) (sat_cons (step949 p h) (sat_cons (step1750 p h) (sat_nil p))))))))))))))))))))))))))))))))
def c5387 : List Lit := [(1770, false), (107, true), (112, false), (1811, true), (100, false), (1796, true), (116, true)]
theorem step5387 (p : Nat → Bool) (h : Constraints p) : clause p c5387 = true :=
  Snake9.LocalRup.prove_clause [c1699, c1757, c1709, c1715, c1805, c5386, c1754, c1755, c1756, c1759, c1764, c1769, c1750, c1811, c1742, c1716, c1720, c1739, c1740, c1712, c1693, c952, c2134, c1686, c2391, c887] c5387 (by decide) p (sat_cons (step1699 p h) (sat_cons (step1757 p h) (sat_cons (step1709 p h) (sat_cons (step1715 p h) (sat_cons (step1805 p h) (sat_cons (step5386 p h) (sat_cons (step1754 p h) (sat_cons (step1755 p h) (sat_cons (step1756 p h) (sat_cons (step1759 p h) (sat_cons (step1764 p h) (sat_cons (step1769 p h) (sat_cons (step1750 p h) (sat_cons (step1811 p h) (sat_cons (step1742 p h) (sat_cons (step1716 p h) (sat_cons (step1720 p h) (sat_cons (step1739 p h) (sat_cons (step1740 p h) (sat_cons (step1712 p h) (sat_cons (step1693 p h) (sat_cons (step952 p h) (sat_cons (step2134 p h) (sat_cons (step1686 p h) (sat_cons (step2391 p h) (sat_cons (step887 p h) (sat_nil p)))))))))))))))))))))))))))
def c5388 : List Lit := [(1788, true), (108, false), (114, true), (1767, false), (112, false), (1811, true), (100, false), (92, true), (1796, true)]
theorem step5388 (p : Nat → Bool) (h : Constraints p) : clause p c5388 = true :=
  Snake9.LocalRup.prove_clause [c1736, c5378, c1745, c5235, c1739] c5388 (by decide) p (sat_cons (step1736 p h) (sat_cons (step5378 p h) (sat_cons (step1745 p h) (sat_cons (step5235 p h) (sat_cons (step1739 p h) (sat_nil p))))))
def c5389 : List Lit := [(62, false), (1733, false), (1722, false), (1585, false), (1658, false), (79, false), (1810, false), (122, false)]
theorem step5389 (p : Nat → Bool) (h : Constraints p) : clause p c5389 = true :=
  Snake9.LocalRup.prove_clause [c371, c391, c388, c390, c385, c1248, c1582, c1546, c1550, c1535, c1251, c1592, c1555, c1538, c2037, c1627, c1566, c1325, c1654, c1500, c1875, c2470] c5389 (by decide) p (sat_cons (step371 p h) (sat_cons (step391 p h) (sat_cons (step388 p h) (sat_cons (step390 p h) (sat_cons (step385 p h) (sat_cons (step1248 p h) (sat_cons (step1582 p h) (sat_cons (step1546 p h) (sat_cons (step1550 p h) (sat_cons (step1535 p h) (sat_cons (step1251 p h) (sat_cons (step1592 p h) (sat_cons (step1555 p h) (sat_cons (step1538 p h) (sat_cons (step2037 p h) (sat_cons (step1627 p h) (sat_cons (step1566 p h) (sat_cons (step1325 p h) (sat_cons (step1654 p h) (sat_cons (step1500 p h) (sat_cons (step1875 p h) (sat_cons (step2470 p h) (sat_nil p)))))))))))))))))))))))
def c5390 : List Lit := [(1597, true), (21, false), (1569, false), (95, false), (44, true), (88, true), (101, true), (122, false)]
theorem step5390 (p : Nat → Bool) (h : Constraints p) : clause p c5390 = true :=
  Snake9.LocalRup.prove_clause [c2603, c2046, c2485, c2424, c1309, c5086, c71, c2547, c1276, c1272, c1281] c5390 (by decide) p (sat_cons (step2603 p h) (sat_cons (step2046 p h) (sat_cons (step2485 p h) (sat_cons (step2424 p h) (sat_cons (step1309 p h) (sat_cons (step5086 p h) (sat_cons (step71 p h) (sat_cons (step2547 p h) (sat_cons (step1276 p h) (sat_cons (step1272 p h) (sat_cons (step1281 p h) (sat_nil p))))))))))))
def c5391 : List Lit := [(95, false), (44, true), (1625, false), (88, true), (101, true), (1682, true), (122, false), (105, true), (92, true), (116, true)]
theorem step5391 (p : Nat → Bool) (h : Constraints p) : clause p c5391 = true :=
  Snake9.LocalRup.prove_clause [c2171, c2329, c2330, c5390, c1501, c1452, c5310, c260, c261, c1390, c1402, c1393, c1409, c1419] c5391 (by decide) p (sat_cons (step2171 p h) (sat_cons (step2329 p h) (sat_cons (step2330 p h) (sat_cons (step5390 p h) (sat_cons (step1501 p h) (sat_cons (step1452 p h) (sat_cons (step5310 p h) (sat_cons (step260 p h) (sat_cons (step261 p h) (sat_cons (step1390 p h) (sat_cons (step1402 p h) (sat_cons (step1393 p h) (sat_cons (step1409 p h) (sat_cons (step1419 p h) (sat_nil p)))))))))))))))
def c5392 : List Lit := [(1763, false), (1769, false), (89, true), (112, true), (101, true), (1811, true)]
theorem step5392 (p : Nat → Bool) (h : Constraints p) : clause p c5392 = true :=
  Snake9.LocalRup.prove_clause [c1705, c1737, c1744, c1768, c1811, c1718, c1720, c1799, c2971, c1770, c1805, c3472, c1719, c1692, c1706, c1708, c1699, c1700, c2544, c3066, c1774, c1745, c1739, c5218, c906, c1704, c5320, c1750, c1759, c1753, c2107, c950, c2339, c2346, c1690, c714] c5392 (by decide) p (sat_cons (step1705 p h) (sat_cons (step1737 p h) (sat_cons (step1744 p h) (sat_cons (step1768 p h) (sat_cons (step1811 p h) (sat_cons (step1718 p h) (sat_cons (step1720 p h) (sat_cons (step1799 p h) (sat_cons (step2971 p h) (sat_cons (step1770 p h) (sat_cons (step1805 p h) (sat_cons (step3472 p h) (sat_cons (step1719 p h) (sat_cons (step1692 p h) (sat_cons (step1706 p h) (sat_cons (step1708 p h) (sat_cons (step1699 p h) (sat_cons (step1700 p h) (sat_cons (step2544 p h) (sat_cons (step3066 p h) (sat_cons (step1774 p h) (sat_cons (step1745 p h) (sat_cons (step1739 p h) (sat_cons (step5218 p h) (sat_cons (step906 p h) (sat_cons (step1704 p h) (sat_cons (step5320 p h) (sat_cons (step1750 p h) (sat_cons (step1759 p h) (sat_cons (step1753 p h) (sat_cons (step2107 p h) (sat_cons (step950 p h) (sat_cons (step2339 p h) (sat_cons (step2346 p h) (sat_cons (step1690 p h) (sat_cons (step714 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))
def c5393 : List Lit := [(1769, false), (89, true), (112, true), (101, true), (1811, true)]
theorem step5393 (p : Nat → Bool) (h : Constraints p) : clause p c5393 = true :=
  Snake9.LocalRup.prove_clause [c1737, c1744, c1768, c1811, c5392, c1691, c1693, c1689, c1686, c2339, c5200, c5186, c1753, c1711, c1756, c1715, c1769, c1805] c5393 (by decide) p (sat_cons (step1737 p h) (sat_cons (step1744 p h) (sat_cons (step1768 p h) (sat_cons (step1811 p h) (sat_cons (step5392 p h) (sat_cons (step1691 p h) (sat_cons (step1693 p h) (sat_cons (step1689 p h) (sat_cons (step1686 p h) (sat_cons (step2339 p h) (sat_cons (step5200 p h) (sat_cons (step5186 p h) (sat_cons (step1753 p h) (sat_cons (step1711 p h) (sat_cons (step1756 p h) (sat_cons (step1715 p h) (sat_cons (step1769 p h) (sat_cons (step1805 p h) (sat_nil p)))))))))))))))))))
def c5394 : List Lit := [(1763, true), (89, true), (112, true), (101, true), (1811, true)]
theorem step5394 (p : Nat → Bool) (h : Constraints p) : clause p c5394 = true :=
  Snake9.LocalRup.prove_clause [c5393, c1691, c1693, c1689, c1686, c2339, c758, c5186, c1753, c1710, c5093, c1756, c1714, c2998, c1799, c1774] c5394 (by decide) p (sat_cons (step5393 p h) (sat_cons (step1691 p h) (sat_cons (step1693 p h) (sat_cons (step1689 p h) (sat_cons (step1686 p h) (sat_cons (step2339 p h) (sat_cons (step758 p h) (sat_cons (step5186 p h) (sat_cons (step1753 p h) (sat_cons (step1710 p h) (sat_cons (step5093 p h) (sat_cons (step1756 p h) (sat_cons (step1714 p h) (sat_cons (step2998 p h) (sat_cons (step1799 p h) (sat_cons (step1774 p h) (sat_nil p)))))))))))))))))
def c5395 : List Lit := [(100, false), (89, true), (112, true), (101, true), (1811, true)]
theorem step5395 (p : Nat → Bool) (h : Constraints p) : clause p c5395 = true :=
  Snake9.LocalRup.prove_clause [c5394, c1737, c1744, c1768, c1811, c1720, c2971, c1805, c1719, c1710, c5393, c2339, c5094, c2134, c1707, c2941, c1753, c1718, c2998, c1756, c1799, c1774] c5395 (by decide) p (sat_cons (step5394 p h) (sat_cons (step1737 p h) (sat_cons (step1744 p h) (sat_cons (step1768 p h) (sat_cons (step1811 p h) (sat_cons (step1720 p h) (sat_cons (step2971 p h) (sat_cons (step1805 p h) (sat_cons (step1719 p h) (sat_cons (step1710 p h) (sat_cons (step5393 p h) (sat_cons (step2339 p h) (sat_cons (step5094 p h) (sat_cons (step2134 p h) (sat_cons (step1707 p h) (sat_cons (step2941 p h) (sat_cons (step1753 p h) (sat_cons (step1718 p h) (sat_cons (step2998 p h) (sat_cons (step1756 p h) (sat_cons (step1799 p h) (sat_cons (step1774 p h) (sat_nil p)))))))))))))))))))))))
def c5396 : List Lit := [(1801, true), (1761, false), (1773, true), (1769, true), (112, true), (1811, true)]
theorem step5396 (p : Nat → Bool) (h : Constraints p) : clause p c5396 = true :=
  Snake9.LocalRup.prove_clause [c1703, c1702, c1737, c1744, c3154, c1770, c1738, c2998, c1774, c2639, c1756, c1753, c1754, c2112, c5325, c856] c5396 (by decide) p (sat_cons (step1703 p h) (sat_cons (step1702 p h) (sat_cons (step1737 p h) (sat_cons (step1744 p h) (sat_cons (step3154 p h) (sat_cons (step1770 p h) (sat_cons (step1738 p h) (sat_cons (step2998 p h) (sat_cons (step1774 p h) (sat_cons (step2639 p h) (sat_cons (step1756 p h) (sat_cons (step1753 p h) (sat_cons (step1754 p h) (sat_cons (step2112 p h) (sat_cons (step5325 p h) (sat_cons (step856 p h) (sat_nil p)))))))))))))))))
def c5397 : List Lit := [(1793, true), (122, false), (124, false), (1789, true), (103, false), (110, false), (112, true)]
theorem step5397 (p : Nat → Bool) (h : Constraints p) : clause p c5397 = true :=
  Snake9.LocalRup.prove_clause [c1737, c1746, c1753, c1754, c950, c1739, c1741, c1748, c856, c1738, c5325] c5397 (by decide) p (sat_cons (step1737 p h) (sat_cons (step1746 p h) (sat_cons (step1753 p h) (sat_cons (step1754 p h) (sat_cons (step950 p h) (sat_cons (step1739 p h) (sat_cons (step1741 p h) (sat_cons (step1748 p h) (sat_cons (step856 p h) (sat_cons (step1738 p h) (sat_cons (step5325 p h) (sat_nil p))))))))))))
def c5398 : List Lit := [(92, true), (1680, true), (101, true), (46, true), (113, true), (122, false)]
theorem step5398 (p : Nat → Bool) (h : Constraints p) : clause p c5398 = true :=
  Snake9.LocalRup.prove_clause [c5307, c2773, c2422, c4650, c2044, c2778, c1304, c1485, c2172, c1452, c2563] c5398 (by decide) p (sat_cons (step5307 p h) (sat_cons (step2773 p h) (sat_cons (step2422 p h) (sat_cons (step4650 p h) (sat_cons (step2044 p h) (sat_cons (step2778 p h) (sat_cons (step1304 p h) (sat_cons (step1485 p h) (sat_cons (step2172 p h) (sat_cons (step1452 p h) (sat_cons (step2563 p h) (sat_nil p))))))))))))
def c5399 : List Lit := [(1571, false), (1585, true), (1680, true), (1648, false), (44, false), (122, false)]
theorem step5399 (p : Nat → Bool) (h : Constraints p) : clause p c5399 = true :=
  Snake9.LocalRup.prove_clause [c2422, c1304, c2044, c2172, c1485, c2563, c1452] c5399 (by decide) p (sat_cons (step2422 p h) (sat_cons (step1304 p h) (sat_cons (step2044 p h) (sat_cons (step2172 p h) (sat_cons (step1485 p h) (sat_cons (step2563 p h) (sat_cons (step1452 p h) (sat_nil p))))))))
def c5400 : List Lit := [(1571, true), (1751, true), (86, true), (90, true), (92, false), (114, false)]
theorem step5400 (p : Nat → Bool) (h : Constraints p) : clause p c5400 = true :=
  Snake9.LocalRup.prove_clause [c1277, c1279, c2619, c1274, c1275, c1271, c70, c5358, c2218, c5091, c1922, c1587] c5400 (by decide) p (sat_cons (step1277 p h) (sat_cons (step1279 p h) (sat_cons (step2619 p h) (sat_cons (step1274 p h) (sat_cons (step1275 p h) (sat_cons (step1271 p h) (sat_cons (step70 p h) (sat_cons (step5358 p h) (sat_cons (step2218 p h) (sat_cons (step5091 p h) (sat_cons (step1922 p h) (sat_cons (step1587 p h) (sat_nil p)))))))))))))
def c5401 : List Lit := [(106, false), (96, false), (1769, false), (114, false), (1810, true), (112, false), (1811, true), (102, true)]
theorem step5401 (p : Nat → Bool) (h : Constraints p) : clause p c5401 = true :=
  Snake9.LocalRup.prove_clause [c1688, c1691, c1810, c1720, c1711, c4627, c5200, c5186, c1753, c1690, c1759, c1692, c1751, c5356, c4118] c5401 (by decide) p (sat_cons (step1688 p h) (sat_cons (step1691 p h) (sat_cons (step1810 p h) (sat_cons (step1720 p h) (sat_cons (step1711 p h) (sat_cons (step4627 p h) (sat_cons (step5200 p h) (sat_cons (step5186 p h) (sat_cons (step1753 p h) (sat_cons (step1690 p h) (sat_cons (step1759 p h) (sat_cons (step1692 p h) (sat_cons (step1751 p h) (sat_cons (step5356 p h) (sat_cons (step4118 p h) (sat_nil p))))))))))))))))
def c5402 : List Lit := [(1764, false), (1771, false), (1810, true)]
theorem step5402 (p : Nat → Bool) (h : Constraints p) : clause p c5402 = true :=
  Snake9.LocalRup.prove_clause [c4118, c1723] c5402 (by decide) p (sat_cons (step4118 p h) (sat_cons (step1723 p h) (sat_nil p)))
def c5403 : List Lit := [(1769, false), (114, false), (1810, true), (112, false), (87, false), (1811, true), (102, true), (99, false)]
theorem step5403 (p : Nat → Bool) (h : Constraints p) : clause p c5403 = true :=
  Snake9.LocalRup.prove_clause [c1688, c1705, c5402, c1692, c1694, c1690, c1686, c522, c634, c5401, c2340] c5403 (by decide) p (sat_cons (step1688 p h) (sat_cons (step1705 p h) (sat_cons (step5402 p h) (sat_cons (step1692 p h) (sat_cons (step1694 p h) (sat_cons (step1690 p h) (sat_cons (step1686 p h) (sat_cons (step522 p h) (sat_cons (step634 p h) (sat_cons (step5401 p h) (sat_cons (step2340 p h) (sat_nil p))))))))))))
def c5404 : List Lit := [(1800, true), (1810, true), (112, false), (87, false), (1811, true), (102, true), (99, false)]
theorem step5404 (p : Nat → Bool) (h : Constraints p) : clause p c5404 = true :=
  Snake9.LocalRup.prove_clause [c1688, c1691, c1810, c1720, c1773, c2971, c1736, c5403, c1702, c1703, c2917, c790, c1769, c1756, c1758, c1754, c5324, c879, c5275, c2364] c5404 (by decide) p (sat_cons (step1688 p h) (sat_cons (step1691 p h) (sat_cons (step1810 p h) (sat_cons (step1720 p h) (sat_cons (step1773 p h) (sat_cons (step2971 p h) (sat_cons (step1736 p h) (sat_cons (step5403 p h) (sat_cons (step1702 p h) (sat_cons (step1703 p h) (sat_cons (step2917 p h) (sat_cons (step790 p h) (sat_cons (step1769 p h) (sat_cons (step1756 p h) (sat_cons (step1758 p h) (sat_cons (step1754 p h) (sat_cons (step5324 p h) (sat_cons (step879 p h) (sat_cons (step5275 p h) (sat_cons (step2364 p h) (sat_nil p)))))))))))))))))))))
def c5405 : List Lit := [(1810, true), (112, false), (87, false), (1811, true), (102, true), (99, false)]
theorem step5405 (p : Nat → Bool) (h : Constraints p) : clause p c5405 = true :=
  Snake9.LocalRup.prove_clause [c1688, c1691, c4627, c5404, c1798, c1722, c1718, c1692, c1694, c1707, c1690, c2965, c2583] c5405 (by decide) p (sat_cons (step1688 p h) (sat_cons (step1691 p h) (sat_cons (step4627 p h) (sat_cons (step5404 p h) (sat_cons (step1798 p h) (sat_cons (step1722 p h) (sat_cons (step1718 p h) (sat_cons (step1692 p h) (sat_cons (step1694 p h) (sat_cons (step1707 p h) (sat_cons (step1690 p h) (sat_cons (step2965 p h) (sat_cons (step2583 p h) (sat_nil p))))))))))))))
def c5406 : List Lit := [(1776, true), (87, false), (102, true), (99, false)]
theorem step5406 (p : Nat → Bool) (h : Constraints p) : clause p c5406 = true :=
  Snake9.LocalRup.prove_clause [c1688, c1691, c1722, c1718, c1692, c1694, c1707, c1690, c1699, c2583, c690] c5406 (by decide) p (sat_cons (step1688 p h) (sat_cons (step1691 p h) (sat_cons (step1722 p h) (sat_cons (step1718 p h) (sat_cons (step1692 p h) (sat_cons (step1694 p h) (sat_cons (step1707 p h) (sat_cons (step1690 p h) (sat_cons (step1699 p h) (sat_cons (step2583 p h) (sat_cons (step690 p h) (sat_nil p))))))))))))
def c5407 : List Lit := [(1764, true), (87, false), (1811, true), (102, true), (99, false)]
theorem step5407 (p : Nat → Bool) (h : Constraints p) : clause p c5407 = true :=
  Snake9.LocalRup.prove_clause [c1688, c1692, c1694, c1690, c1686, c522, c634, c2583, c2340, c691, c5186, c5092, c5093] c5407 (by decide) p (sat_cons (step1688 p h) (sat_cons (step1692 p h) (sat_cons (step1694 p h) (sat_cons (step1690 p h) (sat_cons (step1686 p h) (sat_cons (step522 p h) (sat_cons (step634 p h) (sat_cons (step2583 p h) (sat_cons (step2340 p h) (sat_cons (step691 p h) (sat_cons (step5186 p h) (sat_cons (step5092 p h) (sat_cons (step5093 p h) (sat_nil p))))))))))))))
def c5408 : List Lit := [(1768, false), (1811, true), (1764, false)]
theorem step5408 (p : Nat → Bool) (h : Constraints p) : clause p c5408 = true :=
  Snake9.LocalRup.prove_clause [c1817, c1725, c1710, c1711, c1724, c1702, c1811, c2917, c1768] c5408 (by decide) p (sat_cons (step1817 p h) (sat_cons (step1725 p h) (sat_cons (step1710 p h) (sat_cons (step1711 p h) (sat_cons (step1724 p h) (sat_cons (step1702 p h) (sat_cons (step1811 p h) (sat_cons (step2917 p h) (sat_cons (step1768 p h) (sat_nil p))))))))))
def c5409 : List Lit := [(1795, false), (1767, false), (1800, true), (1811, true), (1764, false)]
theorem step5409 (p : Nat → Bool) (h : Constraints p) : clause p c5409 = true :=
  Snake9.LocalRup.prove_clause [c1764, c1769, c1811, c2917, c1724, c1702, c1708] c5409 (by decide) p (sat_cons (step1764 p h) (sat_cons (step1769 p h) (sat_cons (step1811 p h) (sat_cons (step2917 p h) (sat_cons (step1724 p h) (sat_cons (step1702 p h) (sat_cons (step1708 p h) (sat_nil p))))))))
def c5410 : List Lit := [(103, false), (1795, true), (96, false)]
theorem step5410 (p : Nat → Bool) (h : Constraints p) : clause p c5410 = true :=
  Snake9.LocalRup.prove_clause [c1756, c1753, c2200, c760] c5410 (by decide) p (sat_cons (step1756 p h) (sat_cons (step1753 p h) (sat_cons (step2200 p h) (sat_cons (step760 p h) (sat_nil p)))))
def c5411 : List Lit := [(117, true), (1788, true), (1795, true)]
theorem step5411 (p : Nat → Bool) (h : Constraints p) : clause p c5411 = true :=
  Snake9.LocalRup.prove_clause [c1743, c1758, c1750, c1756, c1754, c1753, c953, c1751, c2388, c952, c1739, c5272, c1741, c1745, c857, c1737] c5411 (by decide) p (sat_cons (step1743 p h) (sat_cons (step1758 p h) (sat_cons (step1750 p h) (sat_cons (step1756 p h) (sat_cons (step1754 p h) (sat_cons (step1753 p h) (sat_cons (step953 p h) (sat_cons (step1751 p h) (sat_cons (step2388 p h) (sat_cons (step952 p h) (sat_cons (step1739 p h) (sat_cons (step5272 p h) (sat_cons (step1741 p h) (sat_cons (step1745 p h) (sat_cons (step857 p h) (sat_cons (step1737 p h) (sat_nil p)))))))))))))))))
def c5412 : List Lit := [(1788, true), (1795, true), (96, false)]
theorem step5412 (p : Nat → Bool) (h : Constraints p) : clause p c5412 = true :=
  Snake9.LocalRup.prove_clause [c1758, c1750, c1756, c1754, c1753, c953, c1743, c5411, c887, c1972, c1741, c2389, c952] c5412 (by decide) p (sat_cons (step1758 p h) (sat_cons (step1750 p h) (sat_cons (step1756 p h) (sat_cons (step1754 p h) (sat_cons (step1753 p h) (sat_cons (step953 p h) (sat_cons (step1743 p h) (sat_cons (step5411 p h) (sat_cons (step887 p h) (sat_cons (step1972 p h) (sat_cons (step1741 p h) (sat_cons (step2389 p h) (sat_cons (step952 p h) (sat_nil p))))))))))))))
def c5413 : List Lit := [(1571, true), (87, false), (99, false)]
theorem step5413 (p : Nat → Bool) (h : Constraints p) : clause p c5413 = true :=
  Snake9.LocalRup.prove_clause [c1279, c2619, c1271, c482] c5413 (by decide) p (sat_cons (step1279 p h) (sat_cons (step2619 p h) (sat_cons (step1271 p h) (sat_cons (step482 p h) (sat_nil p)))))
def c5414 : List Lit := [(1649, true), (88, true), (46, true), (1641, false), (87, false)]
theorem step5414 (p : Nat → Bool) (h : Constraints p) : clause p c5414 = true :=
  Snake9.LocalRup.prove_clause [c1388, c1395, c1407, c1420, c1424, c2628, c1410, c1396, c1402, c1391, c230] c5414 (by decide) p (sat_cons (step1388 p h) (sat_cons (step1395 p h) (sat_cons (step1407 p h) (sat_cons (step1420 p h) (sat_cons (step1424 p h) (sat_cons (step2628 p h) (sat_cons (step1410 p h) (sat_cons (step1396 p h) (sat_cons (step1402 p h) (sat_cons (step1391 p h) (sat_cons (step230 p h) (sat_nil p))))))))))))
def c5415 : List Lit := [(56, false), (49, true), (1633, true), (88, true), (87, false)]
theorem step5415 (p : Nat → Bool) (h : Constraints p) : clause p c5415 = true :=
  Snake9.LocalRup.prove_clause [c1391, c1390, c259, c230, c2266] c5415 (by decide) p (sat_cons (step1391 p h) (sat_cons (step1390 p h) (sat_cons (step259 p h) (sat_cons (step230 p h) (sat_cons (step2266 p h) (sat_nil p))))))
def c5416 : List Lit := [(1730, false), (1734, true), (1749, true), (90, true), (96, false)]
theorem step5416 (p : Nat → Bool) (h : Constraints p) : clause p c5416 = true :=
  Snake9.LocalRup.prove_clause [c1597, c1606, c1609, c5362, c1598, c5108] c5416 (by decide) p (sat_cons (step1597 p h) (sat_cons (step1606 p h) (sat_cons (step1609 p h) (sat_cons (step5362 p h) (sat_cons (step1598 p h) (sat_cons (step5108 p h) (sat_nil p)))))))
def c5417 : List Lit := [(95, false), (112, false), (1795, true), (99, false)]
theorem step5417 (p : Nat → Bool) (h : Constraints p) : clause p c5417 = true :=
  Snake9.LocalRup.prove_clause [c1756, c1754, c874, c721, c2094] c5417 (by decide) p (sat_cons (step1756 p h) (sat_cons (step1754 p h) (sat_cons (step874 p h) (sat_cons (step721 p h) (sat_cons (step2094 p h) (sat_nil p))))))
def c5418 : List Lit := [(1748, true), (94, false), (1729, false), (90, true), (1712, false)]
theorem step5418 (p : Nat → Bool) (h : Constraints p) : clause p c5418 = true :=
  Snake9.LocalRup.prove_clause [c1597, c1605, c5106, c3196, c1608, c4685, c1598] c5418 (by decide) p (sat_cons (step1597 p h) (sat_cons (step1605 p h) (sat_cons (step5106 p h) (sat_cons (step3196 p h) (sat_cons (step1608 p h) (sat_cons (step4685 p h) (sat_cons (step1598 p h) (sat_nil p))))))))
def c5419 : List Lit := [(1783, true), (1769, true), (94, false), (126, false)]
theorem step5419 (p : Nat → Bool) (h : Constraints p) : clause p c5419 = true :=
  Snake9.LocalRup.prove_clause [c1703, c1702, c1736, c5317, c864, c791, c2364] c5419 (by decide) p (sat_cons (step1703 p h) (sat_cons (step1702 p h) (sat_cons (step1736 p h) (sat_cons (step5317 p h) (sat_cons (step864 p h) (sat_cons (step791 p h) (sat_cons (step2364 p h) (sat_nil p))))))))
def c5420 : List Lit := [(1681, true), (1658, false), (1648, false), (30, true), (1585, false)]
theorem step5420 (p : Nat → Bool) (h : Constraints p) : clause p c5420 = true :=
  Snake9.LocalRup.prove_clause [c2045, c1500, c1493, c1325, c1452, c2037, c5294, c1251, c1248] c5420 (by decide) p (sat_cons (step2045 p h) (sat_cons (step1500 p h) (sat_cons (step1493 p h) (sat_cons (step1325 p h) (sat_cons (step1452 p h) (sat_cons (step2037 p h) (sat_cons (step5294 p h) (sat_cons (step1251 p h) (sat_cons (step1248 p h) (sat_nil p))))))))))
def c5421 : List Lit := [(1748, true), (1737, false), (65, true), (122, false)]
theorem step5421 (p : Nat → Bool) (h : Constraints p) : clause p c5421 = true :=
  Snake9.LocalRup.prove_clause [c1651, c2166] c5421 (by decide) p (sat_cons (step1651 p h) (sat_cons (step2166 p h) (sat_nil p)))
def c5422 : List Lit := [(120, true), (1788, true), (122, false), (117, true)]
theorem step5422 (p : Nat → Bool) (h : Constraints p) : clause p c5422 = true :=
  Snake9.LocalRup.prove_clause [c1743, c1739, c5272, c1741, c1745, c857, c1737] c5422 (by decide) p (sat_cons (step1743 p h) (sat_cons (step1739 p h) (sat_cons (step5272 p h) (sat_cons (step1741 p h) (sat_cons (step1745 p h) (sat_cons (step857 p h) (sat_cons (step1737 p h) (sat_nil p))))))))
def c5423 : List Lit := [(1791, true), (120, false), (1770, true), (127, false)]
theorem step5423 (p : Nat → Bool) (h : Constraints p) : clause p c5423 = true :=
  Snake9.LocalRup.prove_clause [c1750, c5324, c952, c1704, c2373, c897] c5423 (by decide) p (sat_cons (step1750 p h) (sat_cons (step5324 p h) (sat_cons (step952 p h) (sat_cons (step1704 p h) (sat_cons (step2373 p h) (sat_cons (step897 p h) (sat_nil p)))))))
def c5424 : List Lit := [(1787, true), (126, false), (122, false), (117, true)]
theorem step5424 (p : Nat → Bool) (h : Constraints p) : clause p c5424 = true :=
  Snake9.LocalRup.prove_clause [c1742, c1744, c1740, c1737, c5344] c5424 (by decide) p (sat_cons (step1742 p h) (sat_cons (step1744 p h) (sat_cons (step1740 p h) (sat_cons (step1737 p h) (sat_cons (step5344 p h) (sat_nil p))))))
def c5425 : List Lit := [(1649, true), (1641, false), (46, true), (87, false), (99, false)]
theorem step5425 (p : Nat → Bool) (h : Constraints p) : clause p c5425 = true :=
  Snake9.LocalRup.prove_clause [c1407, c1388, c1424, c5414, c1396, c492, c1391] c5425 (by decide) p (sat_cons (step1407 p h) (sat_cons (step1388 p h) (sat_cons (step1424 p h) (sat_cons (step5414 p h) (sat_cons (step1396 p h) (sat_cons (step492 p h) (sat_cons (step1391 p h) (sat_nil p))))))))
def c5426 : List Lit := [(1649, false), (1585, false), (1682, true), (30, true)]
theorem step5426 (p : Nat → Bool) (h : Constraints p) : clause p c5426 = true :=
  Snake9.LocalRup.prove_clause [c2045, c1494, c1344, c2612, c1446, c1453, c1501, c5294, c1325, c1248, c2037, c1251] c5426 (by decide) p (sat_cons (step2045 p h) (sat_cons (step1494 p h) (sat_cons (step1344 p h) (sat_cons (step2612 p h) (sat_cons (step1446 p h) (sat_cons (step1453 p h) (sat_cons (step1501 p h) (sat_cons (step5294 p h) (sat_cons (step1325 p h) (sat_cons (step1248 p h) (sat_cons (step2037 p h) (sat_cons (step1251 p h) (sat_nil p)))))))))))))
def c5427 : List Lit := [(114, true), (1792, false), (1768, false), (117, true), (1814, true), (1764, false)]
theorem step5427 (p : Nat → Bool) (h : Constraints p) : clause p c5427 = true :=
  Snake9.LocalRup.prove_clause [c1710, c1724, c1814, c1761, c1775, c1747, c1736, c1738, c1744, c1745, c1771, c1770, c1740, c1762, c1820, c1754, c1725, c1711, c880, c1702, c2369, c854] c5427 (by decide) p (sat_cons (step1710 p h) (sat_cons (step1724 p h) (sat_cons (step1814 p h) (sat_cons (step1761 p h) (sat_cons (step1775 p h) (sat_cons (step1747 p h) (sat_cons (step1736 p h) (sat_cons (step1738 p h) (sat_cons (step1744 p h) (sat_cons (step1745 p h) (sat_cons (step1771 p h) (sat_cons (step1770 p h) (sat_cons (step1740 p h) (sat_cons (step1762 p h) (sat_cons (step1820 p h) (sat_cons (step1754 p h) (sat_cons (step1725 p h) (sat_cons (step1711 p h) (sat_cons (step880 p h) (sat_cons (step1702 p h) (sat_cons (step2369 p h) (sat_cons (step854 p h) (sat_nil p)))))))))))))))))))))))
def c5428 : List Lit := [(1788, true), (113, false), (90, false), (120, true)]
theorem step5428 (p : Nat → Bool) (h : Constraints p) : clause p c5428 = true :=
  Snake9.LocalRup.prove_clause [c1739, c1743, c1745, c1741, c1737, c851] c5428 (by decide) p (sat_cons (step1739 p h) (sat_cons (step1743 p h) (sat_cons (step1745 p h) (sat_cons (step1741 p h) (sat_cons (step1737 p h) (sat_cons (step851 p h) (sat_nil p)))))))
def c5429 : List Lit := [(114, false), (1712, false), (1719, false), (1769, true), (1748, true), (90, true)]
theorem step5429 (p : Nat → Bool) (h : Constraints p) : clause p c5429 = true :=
  Snake9.LocalRup.prove_clause [c1644, c2478, c2482, c5418, c2081] c5429 (by decide) p (sat_cons (step1644 p h) (sat_cons (step2478 p h) (sat_cons (step2482 p h) (sat_cons (step5418 p h) (sat_cons (step2081 p h) (sat_nil p))))))
def c5430 : List Lit := [(120, true), (1796, false), (1768, false), (117, true), (1814, true), (1764, false)]
theorem step5430 (p : Nat → Bool) (h : Constraints p) : clause p c5430 = true :=
  Snake9.LocalRup.prove_clause [c1710, c1724, c1814, c1775, c1743, c1739, c5272, c1741, c1742, c1745, c1770, c1737, c1820, c854, c1725, c1702, c1711] c5430 (by decide) p (sat_cons (step1710 p h) (sat_cons (step1724 p h) (sat_cons (step1814 p h) (sat_cons (step1775 p h) (sat_cons (step1743 p h) (sat_cons (step1739 p h) (sat_cons (step5272 p h) (sat_cons (step1741 p h) (sat_cons (step1742 p h) (sat_cons (step1745 p h) (sat_cons (step1770 p h) (sat_cons (step1737 p h) (sat_cons (step1820 p h) (sat_cons (step854 p h) (sat_cons (step1725 p h) (sat_cons (step1702 p h) (sat_cons (step1711 p h) (sat_nil p))))))))))))))))))
def c5431 : List Lit := [(1748, true), (71, true), (90, true), (65, true), (122, false)]
theorem step5431 (p : Nat → Bool) (h : Constraints p) : clause p c5431 = true :=
  Snake9.LocalRup.prove_clause [c2536, c1658, c5421, c2551, c2168] c5431 (by decide) p (sat_cons (step2536 p h) (sat_cons (step1658 p h) (sat_cons (step5421 p h) (sat_cons (step2551 p h) (sat_cons (step2168 p h) (sat_nil p))))))
def c5432 : List Lit := [(1800, true), (1787, false), (117, true)]
theorem step5432 (p : Nat → Bool) (h : Constraints p) : clause p c5432 = true :=
  Snake9.LocalRup.prove_clause [c1773, c1769, c5411] c5432 (by decide) p (sat_cons (step1773 p h) (sat_cons (step1769 p h) (sat_cons (step5411 p h) (sat_nil p))))
def c5433 : List Lit := [(1719, true), (71, false), (1714, true), (113, true), (112, false), (122, false)]
theorem step5433 (p : Nat → Bool) (h : Constraints p) : clause p c5433 = true :=
  Snake9.LocalRup.prove_clause [c1582, c1583, c397, c2104, c2296, c2314, c1538, c326, c431, c1567, c1546, c5009, c1556, c1571, c1551, c1541, c2150, c1532] c5433 (by decide) p (sat_cons (step1582 p h) (sat_cons (step1583 p h) (sat_cons (step397 p h) (sat_cons (step2104 p h) (sat_cons (step2296 p h) (sat_cons (step2314 p h) (sat_cons (step1538 p h) (sat_cons (step326 p h) (sat_cons (step431 p h) (sat_cons (step1567 p h) (sat_cons (step1546 p h) (sat_cons (step5009 p h) (sat_cons (step1556 p h) (sat_cons (step1571 p h) (sat_cons (step1551 p h) (sat_cons (step1541 p h) (sat_cons (step2150 p h) (sat_cons (step1532 p h) (sat_nil p)))))))))))))))))))
def c5434 : List Lit := [(1697, false), (1713, true), (71, false), (113, true), (112, false), (122, false)]
theorem step5434 (p : Nat → Bool) (h : Constraints p) : clause p c5434 = true :=
  Snake9.LocalRup.prove_clause [c1538, c1566, c2158, c2296, c4773, c326, c1546] c5434 (by decide) p (sat_cons (step1538 p h) (sat_cons (step1566 p h) (sat_cons (step2158 p h) (sat_cons (step2296 p h) (sat_cons (step4773 p h) (sat_cons (step326 p h) (sat_cons (step1546 p h) (sat_nil p))))))))
def c5435 : List Lit := [(1713, true), (71, false), (122, false), (113, true), (112, false)]
theorem step5435 (p : Nat → Bool) (h : Constraints p) : clause p c5435 = true :=
  Snake9.LocalRup.prove_clause [c5434, c1536, c2104, c4955, c2158, c2297, c1566, c327, c1540, c1532] c5435 (by decide) p (sat_cons (step5434 p h) (sat_cons (step1536 p h) (sat_cons (step2104 p h) (sat_cons (step4955 p h) (sat_cons (step2158 p h) (sat_cons (step2297 p h) (sat_cons (step1566 p h) (sat_cons (step327 p h) (sat_cons (step1540 p h) (sat_cons (step1532 p h) (sat_nil p)))))))))))
def c5436 : List Lit := [(1720, false), (90, true), (1738, true)]
theorem step5436 (p : Nat → Bool) (h : Constraints p) : clause p c5436 = true :=
  Snake9.LocalRup.prove_clause [c1597, c1604, c1625, c1593, c1594, c1621, c2138] c5436 (by decide) p (sat_cons (step1597 p h) (sat_cons (step1604 p h) (sat_cons (step1625 p h) (sat_cons (step1593 p h) (sat_cons (step1594 p h) (sat_cons (step1621 p h) (sat_cons (step2138 p h) (sat_nil p))))))))
def c5437 : List Lit := [(79, false), (1720, true), (1713, true), (1697, false), (122, false)]
theorem step5437 (p : Nat → Bool) (h : Constraints p) : clause p c5437 = true :=
  Snake9.LocalRup.prove_clause [c1538, c1566, c4726, c2683, c2159, c1570, c1541, c1532, c2122, c1584, c400, c401, c1546, c1550, c1555] c5437 (by decide) p (sat_cons (step1538 p h) (sat_cons (step1566 p h) (sat_cons (step4726 p h) (sat_cons (step2683 p h) (sat_cons (step2159 p h) (sat_cons (step1570 p h) (sat_cons (step1541 p h) (sat_cons (step1532 p h) (sat_cons (step2122 p h) (sat_cons (step1584 p h) (sat_cons (step400 p h) (sat_cons (step401 p h) (sat_cons (step1546 p h) (sat_cons (step1550 p h) (sat_cons (step1555 p h) (sat_nil p))))))))))))))))
def c5438 : List Lit := [(1633, true), (88, true), (95, false), (52, true), (69, true)]
theorem step5438 (p : Nat → Bool) (h : Constraints p) : clause p c5438 = true :=
  Snake9.LocalRup.prove_clause [c1390, c1391, c260, c2263] c5438 (by decide) p (sat_cons (step1390 p h) (sat_cons (step1391 p h) (sat_cons (step260 p h) (sat_cons (step2263 p h) (sat_nil p)))))
def c5439 : List Lit := [(1784, false), (1770, true), (1802, true), (118, true), (127, false)]
theorem step5439 (p : Nat → Bool) (h : Constraints p) : clause p c5439 = true :=
  Snake9.LocalRup.prove_clause [c1782, c1740, c1749, c1748, c1741, c1779, c5423, c1758] c5439 (by decide) p (sat_cons (step1782 p h) (sat_cons (step1740 p h) (sat_cons (step1749 p h) (sat_cons (step1748 p h) (sat_cons (step1741 p h) (sat_cons (step1779 p h) (sat_cons (step5423 p h) (sat_cons (step1758 p h) (sat_nil p)))))))))
def c5440 : List Lit := [(1763, true), (122, false), (87, false)]
theorem step5440 (p : Nat → Bool) (h : Constraints p) : clause p c5440 = true :=
  Snake9.LocalRup.prove_clause [c1691, c1693, c2621, c1689, c1685, c691] c5440 (by decide) p (sat_cons (step1691 p h) (sat_cons (step1693 p h) (sat_cons (step2621 p h) (sat_cons (step1689 p h) (sat_cons (step1685 p h) (sat_cons (step691 p h) (sat_nil p)))))))
def c5441 : List Lit := [(1800, true), (1787, false), (96, false)]
theorem step5441 (p : Nat → Bool) (h : Constraints p) : clause p c5441 = true :=
  Snake9.LocalRup.prove_clause [c1773, c1769, c5412] c5441 (by decide) p (sat_cons (step1773 p h) (sat_cons (step1769 p h) (sat_cons (step5412 p h) (sat_nil p))))
def c5442 : List Lit := [(1769, true), (122, false), (112, false), (114, false), (120, false)]
theorem step5442 (p : Nat → Bool) (h : Constraints p) : clause p c5442 = true :=
  Snake9.LocalRup.prove_clause [c1702, c1703, c855, c791, c906, c2356] c5442 (by decide) p (sat_cons (step1702 p h) (sat_cons (step1703 p h) (sat_cons (step855 p h) (sat_cons (step791 p h) (sat_cons (step906 p h) (sat_cons (step2356 p h) (sat_nil p)))))))
def c5443 : List Lit := [(110, false), (113, true), (109, true), (122, false), (120, false)]
theorem step5443 (p : Nat → Bool) (h : Constraints p) : clause p c5443 = true :=
  Snake9.LocalRup.prove_clause [c906, c2356] c5443 (by decide) p (sat_cons (step906 p h) (sat_cons (step2356 p h) (sat_nil p)))
def c5444 : List Lit := [(1734, false), (1585, false), (1813, false), (1633, false), (113, true), (1712, false)]
theorem step5444 (p : Nat → Bool) (h : Constraints p) : clause p c5444 = true :=
  Snake9.LocalRup.prove_clause [c2729, c2468, c1870, c5100, c3143, c1861, c1586, c2469, c2192, c4650] c5444 (by decide) p (sat_cons (step2729 p h) (sat_cons (step2468 p h) (sat_cons (step1870 p h) (sat_cons (step5100 p h) (sat_cons (step3143 p h) (sat_cons (step1861 p h) (sat_cons (step1586 p h) (sat_cons (step2469 p h) (sat_cons (step2192 p h) (sat_cons (step4650 p h) (sat_nil p)))))))))))
def c5445 : List Lit := [(1813, false), (1734, false), (1634, false), (1595, false), (122, false)]
theorem step5445 (p : Nat → Bool) (h : Constraints p) : clause p c5445 = true :=
  Snake9.LocalRup.prove_clause [c5382, c5100, c2620, c1394, c1423, c1445, c1484, c2468, c1870, c1861, c3143, c2469, c1586, c1485, c3291, c1446] c5445 (by decide) p (sat_cons (step5382 p h) (sat_cons (step5100 p h) (sat_cons (step2620 p h) (sat_cons (step1394 p h) (sat_cons (step1423 p h) (sat_cons (step1445 p h) (sat_cons (step1484 p h) (sat_cons (step2468 p h) (sat_cons (step1870 p h) (sat_cons (step1861 p h) (sat_cons (step3143 p h) (sat_cons (step2469 p h) (sat_cons (step1586 p h) (sat_cons (step1485 p h) (sat_cons (step3291 p h) (sat_cons (step1446 p h) (sat_nil p)))))))))))))))))
end B112E052
