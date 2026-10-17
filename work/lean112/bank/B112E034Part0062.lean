import B112E034Part0061
namespace B112E034
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c5747 : List Lit := [(74, false), (70, false), (1646, true), (1803, false), (1820, true), (1805, false), (93, false), (117, true), (109, false)]
theorem step5747 (p : Nat → Bool) (h : Constraints p) : clause p c5747 = true :=
  Snake9.LocalRup.prove_clause [c3748, c2319, c689, c688, c1559, c3248] c5747 (by decide) p (sat_cons (step3748 p h) (sat_cons (step2319 p h) (sat_cons (step689 p h) (sat_cons (step688 p h) (sat_cons (step1559 p h) (sat_cons (step3248 p h) (sat_nil p)))))))
def c5748 : List Lit := [(1757, true), (74, true), (1718, false)]
theorem step5748 (p : Nat → Bool) (h : Constraints p) : clause p c5748 = true :=
  Snake9.LocalRup.prove_clause [c3190, c1479, c2163, c2637, c5642, c1418] c5748 (by decide) p (sat_cons (step3190 p h) (sat_cons (step1479 p h) (sat_cons (step2163 p h) (sat_cons (step2637 p h) (sat_cons (step5642 p h) (sat_cons (step1418 p h) (sat_nil p)))))))
def c5749 : List Lit := [(1757, true), (70, true)]
theorem step5749 (p : Nat → Bool) (h : Constraints p) : clause p c5749 = true :=
  Snake9.LocalRup.prove_clause [c1386, c3190, c5741, c2163, c1387, c1396] c5749 (by decide) p (sat_cons (step1386 p h) (sat_cons (step3190 p h) (sat_cons (step5741 p h) (sat_cons (step2163 p h) (sat_cons (step1387 p h) (sat_cons (step1396 p h) (sat_nil p)))))))
def c5750 : List Lit := [(1791, true), (89, false), (112, false), (1776, false), (104, true), (98, true), (86, false), (1775, false), (107, true)]
theorem step5750 (p : Nat → Bool) (h : Constraints p) : clause p c5750 = true :=
  Snake9.LocalRup.prove_clause [c1518, c4823, c2487, c1520, c1936, c445] c5750 (by decide) p (sat_cons (step1518 p h) (sat_cons (step4823 p h) (sat_cons (step2487 p h) (sat_cons (step1520 p h) (sat_cons (step1936 p h) (sat_cons (step445 p h) (sat_nil p)))))))
def c5751 : List Lit := [(1833, false), (1757, false), (1633, false), (86, false), (1621, false), (1856, true), (1594, false)]
theorem step5751 (p : Nat → Bool) (h : Constraints p) : clause p c5751 = true :=
  Snake9.LocalRup.prove_clause [c1686, c1670, c5689, c2176, c1285, c1337, c1300] c5751 (by decide) p (sat_cons (step1686 p h) (sat_cons (step1670 p h) (sat_cons (step5689 p h) (sat_cons (step2176 p h) (sat_cons (step1285 p h) (sat_cons (step1337 p h) (sat_cons (step1300 p h) (sat_nil p))))))))
def c5752 : List Lit := [(1832, false), (1644, false), (44, true), (1737, false), (92, false), (1633, false), (1621, false), (1604, true), (1630, false)]
theorem step5752 (p : Nat → Bool) (h : Constraints p) : clause p c5752 = true :=
  Snake9.LocalRup.prove_clause [c4462, c1285, c1300, c1337, c2176, c2486, c2206, c1192, c1191, c1677, c1669, c1485, c2177, c1338, c1345, c1301, c2145, c1286, c1290, c4807, c1250, c1240, c96, c5735, c1406, c1407, c1480, c2194, c2438, c1418] c5752 (by decide) p (sat_cons (step4462 p h) (sat_cons (step1285 p h) (sat_cons (step1300 p h) (sat_cons (step1337 p h) (sat_cons (step2176 p h) (sat_cons (step2486 p h) (sat_cons (step2206 p h) (sat_cons (step1192 p h) (sat_cons (step1191 p h) (sat_cons (step1677 p h) (sat_cons (step1669 p h) (sat_cons (step1485 p h) (sat_cons (step2177 p h) (sat_cons (step1338 p h) (sat_cons (step1345 p h) (sat_cons (step1301 p h) (sat_cons (step2145 p h) (sat_cons (step1286 p h) (sat_cons (step1290 p h) (sat_cons (step4807 p h) (sat_cons (step1250 p h) (sat_cons (step1240 p h) (sat_cons (step96 p h) (sat_cons (step5735 p h) (sat_cons (step1406 p h) (sat_cons (step1407 p h) (sat_cons (step1480 p h) (sat_cons (step2194 p h) (sat_cons (step2438 p h) (sat_cons (step1418 p h) (sat_nil p)))))))))))))))))))))))))))))))
def c5753 : List Lit := [(1811, true), (112, false), (1803, false), (111, true)]
theorem step5753 (p : Nat → Bool) (h : Constraints p) : clause p c5753 = true :=
  Snake9.LocalRup.prove_clause [c1586, c1583, c1576, c2105, c1947] c5753 (by decide) p (sat_cons (step1586 p h) (sat_cons (step1583 p h) (sat_cons (step1576 p h) (sat_cons (step2105 p h) (sat_cons (step1947 p h) (sat_nil p))))))
def c5754 : List Lit := [(1818, true), (1811, false), (112, false), (117, true), (111, true), (109, false)]
theorem step5754 (p : Nat → Bool) (h : Constraints p) : clause p c5754 = true :=
  Snake9.LocalRup.prove_clause [c1558, c1560, c1596, c1601, c5746, c5729] c5754 (by decide) p (sat_cons (step1558 p h) (sat_cons (step1560 p h) (sat_cons (step1596 p h) (sat_cons (step1601 p h) (sat_cons (step5746 p h) (sat_cons (step5729 p h) (sat_nil p)))))))
def c5755 : List Lit := [(1831, false), (1738, false), (92, false), (1633, false), (86, false), (1604, true), (1621, false)]
theorem step5755 (p : Nat → Bool) (h : Constraints p) : clause p c5755 = true :=
  Snake9.LocalRup.prove_clause [c2468, c4462, c2154, c1299, c1336, c2175, c1192, c1191, c1693, c5547, c1676, c5374, c4807, c2177, c1285, c1338, c1300, c1301, c1337, c1345, c1286, c2176, c1684, c4539, c5635, c5735, c1176, c1920, c94, c5392, c1820, c4346, c1895, c1106, c1182, c1818, c1113] c5755 (by decide) p (sat_cons (step2468 p h) (sat_cons (step4462 p h) (sat_cons (step2154 p h) (sat_cons (step1299 p h) (sat_cons (step1336 p h) (sat_cons (step2175 p h) (sat_cons (step1192 p h) (sat_cons (step1191 p h) (sat_cons (step1693 p h) (sat_cons (step5547 p h) (sat_cons (step1676 p h) (sat_cons (step5374 p h) (sat_cons (step4807 p h) (sat_cons (step2177 p h) (sat_cons (step1285 p h) (sat_cons (step1338 p h) (sat_cons (step1300 p h) (sat_cons (step1301 p h) (sat_cons (step1337 p h) (sat_cons (step1345 p h) (sat_cons (step1286 p h) (sat_cons (step2176 p h) (sat_cons (step1684 p h) (sat_cons (step4539 p h) (sat_cons (step5635 p h) (sat_cons (step5735 p h) (sat_cons (step1176 p h) (sat_cons (step1920 p h) (sat_cons (step94 p h) (sat_cons (step5392 p h) (sat_cons (step1820 p h) (sat_cons (step4346 p h) (sat_cons (step1895 p h) (sat_cons (step1106 p h) (sat_cons (step1182 p h) (sat_cons (step1818 p h) (sat_cons (step1113 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))
def c5756 : List Lit := [(1790, true), (92, false), (107, true), (86, false), (1803, true)]
theorem step5756 (p : Nat → Bool) (h : Constraints p) : clause p c5756 = true :=
  Snake9.LocalRup.prove_clause [c4693, c5057, c402] c5756 (by decide) p (sat_cons (step4693 p h) (sat_cons (step5057 p h) (sat_cons (step402 p h) (sat_nil p))))
def c5757 : List Lit := [(1584, false), (1713, false), (1688, true), (1746, false), (1662, false), (1831, false), (1633, false), (1604, true), (1621, false)]
theorem step5757 (p : Nat → Bool) (h : Constraints p) : clause p c5757 = true :=
  Snake9.LocalRup.prove_clause [c1353, c2145, c1177, c1345, c1346, c2177, c1301, c1676, c1286, c1485, c5635, c1407] c5757 (by decide) p (sat_cons (step1353 p h) (sat_cons (step2145 p h) (sat_cons (step1177 p h) (sat_cons (step1345 p h) (sat_cons (step1346 p h) (sat_cons (step2177 p h) (sat_cons (step1301 p h) (sat_cons (step1676 p h) (sat_cons (step1286 p h) (sat_cons (step1485 p h) (sat_cons (step5635 p h) (sat_cons (step1407 p h) (sat_nil p)))))))))))))
def c5758 : List Lit := [(1737, false), (1706, false), (1758, true), (1803, true)]
theorem step5758 (p : Nat → Bool) (h : Constraints p) : clause p c5758 = true :=
  Snake9.LocalRup.prove_clause [c3192, c1408, c1396, c1406, c1480, c5645, c2502, c2438, c2762, c4540, c1387] c5758 (by decide) p (sat_cons (step3192 p h) (sat_cons (step1408 p h) (sat_cons (step1396 p h) (sat_cons (step1406 p h) (sat_cons (step1480 p h) (sat_cons (step5645 p h) (sat_cons (step2502 p h) (sat_cons (step2438 p h) (sat_cons (step2762 p h) (sat_cons (step4540 p h) (sat_cons (step1387 p h) (sat_nil p))))))))))))
def c5759 : List Lit := [(107, false), (74, false), (93, false), (1747, true), (1646, true)]
theorem step5759 (p : Nat → Bool) (h : Constraints p) : clause p c5759 = true :=
  Snake9.LocalRup.prove_clause [c4775, c687] c5759 (by decide) p (sat_cons (step4775 p h) (sat_cons (step687 p h) (sat_nil p)))
def c5760 : List Lit := [(1713, true), (1803, true), (1726, true)]
theorem step5760 (p : Nat → Bool) (h : Constraints p) : clause p c5760 = true :=
  Snake9.LocalRup.prove_clause [c1393, c2194, c1386, c1419, c2762] c5760 (by decide) p (sat_cons (step1393 p h) (sat_cons (step2194 p h) (sat_cons (step1386 p h) (sat_cons (step1419 p h) (sat_cons (step2762 p h) (sat_nil p))))))
def c5761 : List Lit := [(70, true), (77, false), (1714, true)]
theorem step5761 (p : Nat → Bool) (h : Constraints p) : clause p c5761 = true :=
  Snake9.LocalRup.prove_clause [c5642, c1396, c1386, c1387, c1394, c1919, c1389] c5761 (by decide) p (sat_cons (step5642 p h) (sat_cons (step1396 p h) (sat_cons (step1386 p h) (sat_cons (step1387 p h) (sat_cons (step1394 p h) (sat_cons (step1919 p h) (sat_cons (step1389 p h) (sat_nil p))))))))
def c5762 : List Lit := [(1725, true), (1714, true), (1803, true)]
theorem step5762 (p : Nat → Bool) (h : Constraints p) : clause p c5762 = true :=
  Snake9.LocalRup.prove_clause [c1417, c1418, c2762, c5761] c5762 (by decide) p (sat_cons (step1417 p h) (sat_cons (step1418 p h) (sat_cons (step2762 p h) (sat_cons (step5761 p h) (sat_nil p)))))
def c5763 : List Lit := [(122, false), (1622, false), (110, false), (1798, false), (1810, false), (1790, false), (91, false), (1646, false), (1757, false), (1803, true)]
theorem step5763 (p : Nat → Bool) (h : Constraints p) : clause p c5763 = true :=
  Snake9.LocalRup.prove_clause [c2958, c2313, c633, c2178, c1555, c1668, c1564, c1637, c1606] c5763 (by decide) p (sat_cons (step2958 p h) (sat_cons (step2313 p h) (sat_cons (step633 p h) (sat_cons (step2178 p h) (sat_cons (step1555 p h) (sat_cons (step1668 p h) (sat_cons (step1564 p h) (sat_cons (step1637 p h) (sat_cons (step1606 p h) (sat_nil p))))))))))
def c5764 : List Lit := [(74, false), (1646, true), (113, false), (88, true), (93, false)]
theorem step5764 (p : Nat → Bool) (h : Constraints p) : clause p c5764 = true :=
  Snake9.LocalRup.prove_clause [c688, c3748, c2067] c5764 (by decide) p (sat_cons (step688 p h) (sat_cons (step3748 p h) (sat_cons (step2067 p h) (sat_nil p))))
def c5765 : List Lit := [(1622, false), (1746, false), (1632, false), (1714, false), (1663, true), (1832, false), (1644, false)]
theorem step5765 (p : Nat → Bool) (h : Constraints p) : clause p c5765 = true :=
  Snake9.LocalRup.prove_clause [c2163, c1485, c1677, c2176, c1280, c2430, c1307, c1306, c4483, c2175, c1281, c1337, c1238, c1685, c2452, c4065, c4370, c1491, c1815, c5443, c1408] c5765 (by decide) p (sat_cons (step2163 p h) (sat_cons (step1485 p h) (sat_cons (step1677 p h) (sat_cons (step2176 p h) (sat_cons (step1280 p h) (sat_cons (step2430 p h) (sat_cons (step1307 p h) (sat_cons (step1306 p h) (sat_cons (step4483 p h) (sat_cons (step2175 p h) (sat_cons (step1281 p h) (sat_cons (step1337 p h) (sat_cons (step1238 p h) (sat_cons (step1685 p h) (sat_cons (step2452 p h) (sat_cons (step4065 p h) (sat_cons (step4370 p h) (sat_cons (step1491 p h) (sat_cons (step1815 p h) (sat_cons (step5443 p h) (sat_cons (step1408 p h) (sat_nil p))))))))))))))))))))))
def c5766 : List Lit := [(1805, false), (122, false), (1818, true), (1791, true), (1623, true), (1811, true), (1710, true), (89, false), (79, false), (92, false), (93, false), (86, false)]
theorem step5766 (p : Nat → Bool) (h : Constraints p) : clause p c5766 = true :=
  Snake9.LocalRup.prove_clause [c415, c400, c1574, c1579, c1583, c1606, c1568, c1569, c2762, c4806, c1945, c5247, c756, c1387, c1504, c2104, c607, c605, c596, c1555, c2820, c1564, c2065, c2192, c4665, c1191, c1523, c497, c4780] c5766 (by decide) p (sat_cons (step415 p h) (sat_cons (step400 p h) (sat_cons (step1574 p h) (sat_cons (step1579 p h) (sat_cons (step1583 p h) (sat_cons (step1606 p h) (sat_cons (step1568 p h) (sat_cons (step1569 p h) (sat_cons (step2762 p h) (sat_cons (step4806 p h) (sat_cons (step1945 p h) (sat_cons (step5247 p h) (sat_cons (step756 p h) (sat_cons (step1387 p h) (sat_cons (step1504 p h) (sat_cons (step2104 p h) (sat_cons (step607 p h) (sat_cons (step605 p h) (sat_cons (step596 p h) (sat_cons (step1555 p h) (sat_cons (step2820 p h) (sat_cons (step1564 p h) (sat_cons (step2065 p h) (sat_cons (step2192 p h) (sat_cons (step4665 p h) (sat_cons (step1191 p h) (sat_cons (step1523 p h) (sat_cons (step497 p h) (sat_cons (step4780 p h) (sat_nil p))))))))))))))))))))))))))))))
def c5767 : List Lit := [(1803, true), (1612, false), (119, true), (1604, false), (122, false), (1623, true), (1710, true), (79, false)]
theorem step5767 (p : Nat → Bool) (h : Constraints p) : clause p c5767 = true :=
  Snake9.LocalRup.prove_clause [c1568, c1569, c2762, c1945, c4519, c1387, c2104, c596] c5767 (by decide) p (sat_cons (step1568 p h) (sat_cons (step1569 p h) (sat_cons (step2762 p h) (sat_cons (step1945 p h) (sat_cons (step4519 p h) (sat_cons (step1387 p h) (sat_cons (step2104 p h) (sat_cons (step596 p h) (sat_nil p)))))))))
def c5768 : List Lit := [(117, false), (121, false), (1811, true), (92, false), (125, false), (119, true)]
theorem step5768 (p : Nat → Bool) (h : Constraints p) : clause p c5768 = true :=
  Snake9.LocalRup.prove_clause [c669, c840, c2472] c5768 (by decide) p (sat_cons (step669 p h) (sat_cons (step840 p h) (sat_cons (step2472 p h) (sat_nil p))))
def c5769 : List Lit := [(88, true), (103, true), (115, true), (107, true), (1791, true), (126, false), (1775, false), (93, false), (86, false)]
theorem step5769 (p : Nat → Bool) (h : Constraints p) : clause p c5769 = true :=
  Snake9.LocalRup.prove_clause [c2065, c4787, c505, c4823, c1520] c5769 (by decide) p (sat_cons (step2065 p h) (sat_cons (step4787 p h) (sat_cons (step505 p h) (sat_cons (step4823 p h) (sat_cons (step1520 p h) (sat_nil p))))))
def c5770 : List Lit := [(1831, false), (1622, false), (1709, false), (1853, true), (113, false), (114, true), (115, true), (1718, false), (122, false), (93, false)]
theorem step5770 (p : Nat → Bool) (h : Constraints p) : clause p c5770 = true :=
  Snake9.LocalRup.prove_clause [c2662, c1676, c1668, c1480, c2638, c2490, c2178, c1438, c2313, c3748, c5764, c2319, c415, c2200, c2439, c1485, c1418, c2163, c5761] c5770 (by decide) p (sat_cons (step2662 p h) (sat_cons (step1676 p h) (sat_cons (step1668 p h) (sat_cons (step1480 p h) (sat_cons (step2638 p h) (sat_cons (step2490 p h) (sat_cons (step2178 p h) (sat_cons (step1438 p h) (sat_cons (step2313 p h) (sat_cons (step3748 p h) (sat_cons (step5764 p h) (sat_cons (step2319 p h) (sat_cons (step415 p h) (sat_cons (step2200 p h) (sat_cons (step2439 p h) (sat_cons (step1485 p h) (sat_cons (step1418 p h) (sat_cons (step2163 p h) (sat_cons (step5761 p h) (sat_nil p))))))))))))))))))))
def c5771 : List Lit := [(1791, true), (1782, false), (121, false), (1773, false), (104, true), (114, true), (125, false), (1811, true), (92, false)]
theorem step5771 (p : Nat → Bool) (h : Constraints p) : clause p c5771 = true :=
  Snake9.LocalRup.prove_clause [c1510, c1540, c4781, c1531, c761, c1520, c2472, c839] c5771 (by decide) p (sat_cons (step1510 p h) (sat_cons (step1540 p h) (sat_cons (step4781 p h) (sat_cons (step1531 p h) (sat_cons (step761 p h) (sat_cons (step1520 p h) (sat_cons (step2472 p h) (sat_cons (step839 p h) (sat_nil p)))))))))
def c5772 : List Lit := [(1709, false), (1853, true), (1831, false), (113, false), (114, true), (115, true), (1718, false), (1604, false), (122, false), (93, false)]
theorem step5772 (p : Nat → Bool) (h : Constraints p) : clause p c5772 = true :=
  Snake9.LocalRup.prove_clause [c1676, c5770, c2638, c5188, c4698, c2619] c5772 (by decide) p (sat_cons (step1676 p h) (sat_cons (step5770 p h) (sat_cons (step2638 p h) (sat_cons (step5188 p h) (sat_cons (step4698 p h) (sat_cons (step2619 p h) (sat_nil p)))))))
def c5773 : List Lit := [(1622, true), (114, true), (115, true), (1604, false)]
theorem step5773 (p : Nat → Bool) (h : Constraints p) : clause p c5773 = true :=
  Snake9.LocalRup.prove_clause [c5188, c4698, c1996] c5773 (by decide) p (sat_cons (step5188 p h) (sat_cons (step4698 p h) (sat_cons (step1996 p h) (sat_nil p))))
def c5774 : List Lit := [(74, false), (1646, true), (70, false), (115, true), (93, false)]
theorem step5774 (p : Nat → Bool) (h : Constraints p) : clause p c5774 = true :=
  Snake9.LocalRup.prove_clause [c2319, c3748] c5774 (by decide) p (sat_cons (step2319 p h) (sat_cons (step3748 p h) (sat_nil p)))
def c5775 : List Lit := [(1800, true), (122, false), (126, false), (117, true)]
theorem step5775 (p : Nat → Bool) (h : Constraints p) : clause p c5775 = true :=
  Snake9.LocalRup.prove_clause [c1558, c1561, c1563, c5729, c1559, c1555, c625] c5775 (by decide) p (sat_cons (step1558 p h) (sat_cons (step1561 p h) (sat_cons (step1563 p h) (sat_cons (step5729 p h) (sat_cons (step1559 p h) (sat_cons (step1555 p h) (sat_cons (step625 p h) (sat_nil p))))))))
def c5776 : List Lit := [(1687, true), (1623, false), (1644, false), (86, false), (114, true), (1805, true), (92, false)]
theorem step5776 (p : Nat → Bool) (h : Constraints p) : clause p c5776 = true :=
  Snake9.LocalRup.prove_clause [c1275, c1312, c1345, c4802, c1313, c1280, c1244, c1241, c1949, c1831, c395, c1818, c2063, c1825, c4110, c1176] c5776 (by decide) p (sat_cons (step1275 p h) (sat_cons (step1312 p h) (sat_cons (step1345 p h) (sat_cons (step4802 p h) (sat_cons (step1313 p h) (sat_cons (step1280 p h) (sat_cons (step1244 p h) (sat_cons (step1241 p h) (sat_cons (step1949 p h) (sat_cons (step1831 p h) (sat_cons (step395 p h) (sat_cons (step1818 p h) (sat_cons (step2063 p h) (sat_cons (step1825 p h) (sat_cons (step4110 p h) (sat_cons (step1176 p h) (sat_nil p)))))))))))))))))
def c5777 : List Lit := [(1851, true), (94, false), (1830, false), (107, true), (86, false), (1784, false), (104, true), (98, true), (92, false)]
theorem step5777 (p : Nat → Bool) (h : Constraints p) : clause p c5777 = true :=
  Snake9.LocalRup.prove_clause [c5745, c1508, c1510, c1659, c1667, c4970, c2486, c4823, c1438, c1520, c2548, c461] c5777 (by decide) p (sat_cons (step5745 p h) (sat_cons (step1508 p h) (sat_cons (step1510 p h) (sat_cons (step1659 p h) (sat_cons (step1667 p h) (sat_cons (step4970 p h) (sat_cons (step2486 p h) (sat_cons (step4823 p h) (sat_cons (step1438 p h) (sat_cons (step1520 p h) (sat_cons (step2548 p h) (sat_cons (step461 p h) (sat_nil p)))))))))))))
def c5778 : List Lit := [(1791, true), (107, true), (1775, false), (89, false), (126, false), (94, false), (86, false), (115, true), (93, false), (92, false)]
theorem step5778 (p : Nat → Bool) (h : Constraints p) : clause p c5778 = true :=
  Snake9.LocalRup.prove_clause [c4754, c1522, c1527, c415, c4787, c2548, c5769, c461] c5778 (by decide) p (sat_cons (step4754 p h) (sat_cons (step1522 p h) (sat_cons (step1527 p h) (sat_cons (step415 p h) (sat_cons (step4787 p h) (sat_cons (step2548 p h) (sat_cons (step5769 p h) (sat_cons (step461 p h) (sat_nil p)))))))))
def c5779 : List Lit := [(54, false), (1653, true), (61, false), (1642, false), (52, true), (72, false)]
theorem step5779 (p : Nat → Bool) (h : Constraints p) : clause p c5779 = true :=
  Snake9.LocalRup.prove_clause [c227, c226, c1254, c1241, c1273, c1244, c1283] c5779 (by decide) p (sat_cons (step227 p h) (sat_cons (step226 p h) (sat_cons (step1254 p h) (sat_cons (step1241 p h) (sat_cons (step1273 p h) (sat_cons (step1244 p h) (sat_cons (step1283 p h) (sat_nil p))))))))
def c5780 : List Lit := [(1632, false), (54, true), (1806, true), (1653, true), (1665, true), (1642, false), (52, true), (1646, false), (1604, false), (113, false), (87, true), (86, false), (115, true)]
theorem step5780 (p : Nat → Bool) (h : Constraints p) : clause p c5780 = true :=
  Snake9.LocalRup.prove_clause [c1287, c1283, c1282, c1273, c1315, c1254, c4741, c5340, c2013, c208] c5780 (by decide) p (sat_cons (step1287 p h) (sat_cons (step1283 p h) (sat_cons (step1282 p h) (sat_cons (step1273 p h) (sat_cons (step1315 p h) (sat_cons (step1254 p h) (sat_cons (step4741 p h) (sat_cons (step5340 p h) (sat_cons (step2013 p h) (sat_cons (step208 p h) (sat_nil p)))))))))))
def c5781 : List Lit := [(1757, true), (126, false), (113, false), (87, true), (86, false), (114, true), (115, true), (1803, false), (93, false), (117, true), (92, false)]
theorem step5781 (p : Nat → Bool) (h : Constraints p) : clause p c5781 = true :=
  Snake9.TreeRup.prove_clause [c5745, c3501, c5773, c4754, c2063, c4708, c2061, c2984, c2162, c3190, c2486, c1479, c5748, c5749, c2662, c2163, c1407, c1438, c1927, c2637, c5774, c2319, c1385, c415, c1418, c1277, c254, c245, c255, c251, c2065, c4787, c2204, c336, c1307, c1257, c505, c5018, c2440, c2047, c1338, c1262, c4969, c1522, c4098, c2177, c1527, c1374, c1661, c5777, c1380, c2179, c1372, c1340, c1309, c5778, c1646, c5322, c5779, c5780, c1244, c1246, c1241, c1242, c1238, c1949, c1831, c807, c4110, c1818, c3669, c1825, c4741, c1176, c1314, c1347] c5781 (by decide) p (sat_cons (step5745 p h) (sat_cons (step3501 p h) (sat_cons (step5773 p h) (sat_cons (step4754 p h) (sat_cons (step2063 p h) (sat_cons (step4708 p h) (sat_cons (step2061 p h) (sat_cons (step2984 p h) (sat_cons (step2162 p h) (sat_cons (step3190 p h) (sat_cons (step2486 p h) (sat_cons (step1479 p h) (sat_cons (step5748 p h) (sat_cons (step5749 p h) (sat_cons (step2662 p h) (sat_cons (step2163 p h) (sat_cons (step1407 p h) (sat_cons (step1438 p h) (sat_cons (step1927 p h) (sat_cons (step2637 p h) (sat_cons (step5774 p h) (sat_cons (step2319 p h) (sat_cons (step1385 p h) (sat_cons (step415 p h) (sat_cons (step1418 p h) (sat_cons (step1277 p h) (sat_cons (step254 p h) (sat_cons (step245 p h) (sat_cons (step255 p h) (sat_cons (step251 p h) (sat_cons (step2065 p h) (sat_cons (step4787 p h) (sat_cons (step2204 p h) (sat_cons (step336 p h) (sat_cons (step1307 p h) (sat_cons (step1257 p h) (sat_cons (step505 p h) (sat_cons (step5018 p h) (sat_cons (step2440 p h) (sat_cons (step2047 p h) (sat_cons (step1338 p h) (sat_cons (step1262 p h) (sat_cons (step4969 p h) (sat_cons (step1522 p h) (sat_cons (step4098 p h) (sat_cons (step2177 p h) (sat_cons (step1527 p h) (sat_cons (step1374 p h) (sat_cons (step1661 p h) (sat_cons (step5777 p h) (sat_cons (step1380 p h) (sat_cons (step2179 p h) (sat_cons (step1372 p h) (sat_cons (step1340 p h) (sat_cons (step1309 p h) (sat_cons (step5778 p h) (sat_cons (step1646 p h) (sat_cons (step5322 p h) (sat_cons (step5779 p h) (sat_cons (step5780 p h) (sat_cons (step1244 p h) (sat_cons (step1246 p h) (sat_cons (step1241 p h) (sat_cons (step1242 p h) (sat_cons (step1238 p h) (sat_cons (step1949 p h) (sat_cons (step1831 p h) (sat_cons (step807 p h) (sat_cons (step4110 p h) (sat_cons (step1818 p h) (sat_cons (step3669 p h) (sat_cons (step1825 p h) (sat_cons (step4741 p h) (sat_cons (step1176 p h) (sat_cons (step1314 p h) (sat_cons (step1347 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c5782 : List Lit := [(1595, true), (27, false), (1632, true)]
theorem step5782 (p : Nat → Bool) (h : Constraints p) : clause p c5782 = true :=
  Snake9.LocalRup.prove_clause [c1244, c1241, c1831, c1818, c1825, c1949, c2268, c1246, c1238, c1182, c1176, c1113, c4066, c1106, c90, c1820] c5782 (by decide) p (sat_cons (step1244 p h) (sat_cons (step1241 p h) (sat_cons (step1831 p h) (sat_cons (step1818 p h) (sat_cons (step1825 p h) (sat_cons (step1949 p h) (sat_cons (step2268 p h) (sat_cons (step1246 p h) (sat_cons (step1238 p h) (sat_cons (step1182 p h) (sat_cons (step1176 p h) (sat_cons (step1113 p h) (sat_cons (step4066 p h) (sat_cons (step1106 p h) (sat_cons (step90 p h) (sat_cons (step1820 p h) (sat_nil p)))))))))))))))))
def c5783 : List Lit := [(117, true), (1800, true), (1812, false), (1775, false), (1831, true), (115, true), (93, false)]
theorem step5783 (p : Nat → Bool) (h : Constraints p) : clause p c5783 = true :=
  Snake9.LocalRup.prove_clause [c1561, c1558, c1559, c1560, c2100, c3122, c1596, c4667, c1523, c1637, c3789, c1539] c5783 (by decide) p (sat_cons (step1561 p h) (sat_cons (step1558 p h) (sat_cons (step1559 p h) (sat_cons (step1560 p h) (sat_cons (step2100 p h) (sat_cons (step3122 p h) (sat_cons (step1596 p h) (sat_cons (step4667 p h) (sat_cons (step1523 p h) (sat_cons (step1637 p h) (sat_cons (step3789 p h) (sat_cons (step1539 p h) (sat_nil p)))))))))))))
def c5784 : List Lit := [(118, false), (117, false), (113, false), (115, true)]
theorem step5784 (p : Nat → Bool) (h : Constraints p) : clause p c5784 = true :=
  Snake9.LocalRup.prove_clause [c714, c2098] c5784 (by decide) p (sat_cons (step714 p h) (sat_cons (step2098 p h) (sat_nil p)))
def c5785 : List Lit := [(1818, false), (1783, false), (79, true), (1771, false), (1851, true), (1788, false), (1775, false), (113, false)]
theorem step5785 (p : Nat → Bool) (h : Constraints p) : clause p c5785 = true :=
  Snake9.LocalRup.prove_clause [c1417, c2637, c1624, c1674, c5719, c2502, c2482, c1436, c1630, c1434, c1667, c2202, c1479, c2162] c5785 (by decide) p (sat_cons (step1417 p h) (sat_cons (step2637 p h) (sat_cons (step1624 p h) (sat_cons (step1674 p h) (sat_cons (step5719 p h) (sat_cons (step2502 p h) (sat_cons (step2482 p h) (sat_cons (step1436 p h) (sat_cons (step1630 p h) (sat_cons (step1434 p h) (sat_cons (step1667 p h) (sat_cons (step2202 p h) (sat_cons (step1479 p h) (sat_cons (step2162 p h) (sat_nil p)))))))))))))))
def c5786 : List Lit := [(93, true), (1725, false), (113, false), (86, true), (1759, true)]
theorem step5786 (p : Nat → Bool) (h : Constraints p) : clause p c5786 = true :=
  Snake9.LocalRup.prove_clause [c5435, c1437, c1433, c1435, c1436, c2202, c2185, c2162, c1481] c5786 (by decide) p (sat_cons (step5435 p h) (sat_cons (step1437 p h) (sat_cons (step1433 p h) (sat_cons (step1435 p h) (sat_cons (step1436 p h) (sat_cons (step2202 p h) (sat_cons (step2185 p h) (sat_cons (step2162 p h) (sat_cons (step1481 p h) (sat_nil p))))))))))
def c5787 : List Lit := [(1818, true), (115, true), (107, false), (109, false), (1803, false), (1795, true)]
theorem step5787 (p : Nat → Bool) (h : Constraints p) : clause p c5787 = true :=
  Snake9.LocalRup.prove_clause [c1555, c2953, c616, c1554, c4101, c5754, c1572, c4798, c670] c5787 (by decide) p (sat_cons (step1555 p h) (sat_cons (step2953 p h) (sat_cons (step616 p h) (sat_cons (step1554 p h) (sat_cons (step4101 p h) (sat_cons (step5754 p h) (sat_cons (step1572 p h) (sat_cons (step4798 p h) (sat_cons (step670 p h) (sat_nil p))))))))))
def c5788 : List Lit := [(1758, true), (1737, false), (73, true), (107, false), (93, false)]
theorem step5788 (p : Nat → Bool) (h : Constraints p) : clause p c5788 = true :=
  Snake9.LocalRup.prove_clause [c2206, c2219, c2162, c1485, c1480, c2163, c2438, c2440, c1418] c5788 (by decide) p (sat_cons (step2206 p h) (sat_cons (step2219 p h) (sat_cons (step2162 p h) (sat_cons (step1485 p h) (sat_cons (step1480 p h) (sat_cons (step2163 p h) (sat_cons (step2438 p h) (sat_cons (step2440 p h) (sat_cons (step1418 p h) (sat_nil p))))))))))
def c5789 : List Lit := [(1747, true), (1735, false), (117, false), (109, false), (1789, true)]
theorem step5789 (p : Nat → Bool) (h : Constraints p) : clause p c5789 = true :=
  Snake9.LocalRup.prove_clause [c1436, c2218, c1849, c1439, c2767, c2444, c2412, c1526] c5789 (by decide) p (sat_cons (step1436 p h) (sat_cons (step2218 p h) (sat_cons (step1849 p h) (sat_cons (step1439 p h) (sat_cons (step2767 p h) (sat_cons (step2444 p h) (sat_cons (step2412 p h) (sat_cons (step1526 p h) (sat_nil p)))))))))
def c5790 : List Lit := [(1779, true), (101, false), (86, false), (117, false), (93, false), (1777, true)]
theorem step5790 (p : Nat → Bool) (h : Constraints p) : clause p c5790 = true :=
  Snake9.LocalRup.prove_clause [c1518, c2412, c2203, c503, c1505, c1509, c1514] c5790 (by decide) p (sat_cons (step1518 p h) (sat_cons (step2412 p h) (sat_cons (step2203 p h) (sat_cons (step503 p h) (sat_cons (step1505 p h) (sat_cons (step1509 p h) (sat_cons (step1514 p h) (sat_nil p))))))))
def c5791 : List Lit := [(52, false), (1642, true), (57, false), (93, false)]
theorem step5791 (p : Nat → Bool) (h : Constraints p) : clause p c5791 = true :=
  Snake9.LocalRup.prove_clause [c4685, c242] c5791 (by decide) p (sat_cons (step4685 p h) (sat_cons (step242 p h) (sat_nil p)))
def c5792 : List Lit := [(1646, false), (1664, true), (1622, false), (97, false), (1688, true), (79, false), (110, true), (117, false), (115, true)]
theorem step5792 (p : Nat → Bool) (h : Constraints p) : clause p c5792 = true :=
  Snake9.LocalRup.prove_clause [c1277, c4497, c1314, c1238, c1239, c4174, c167, c743, c2002] c5792 (by decide) p (sat_cons (step1277 p h) (sat_cons (step4497 p h) (sat_cons (step1314 p h) (sat_cons (step1238 p h) (sat_cons (step1239 p h) (sat_cons (step4174 p h) (sat_cons (step167 p h) (sat_cons (step743 p h) (sat_cons (step2002 p h) (sat_nil p))))))))))
def c5793 : List Lit := [(42, false), (119, true), (1628, true)]
theorem step5793 (p : Nat → Bool) (h : Constraints p) : clause p c5793 = true :=
  Snake9.LocalRup.prove_clause [c2002, c4624] c5793 (by decide) p (sat_cons (step2002 p h) (sat_cons (step4624 p h) (sat_nil p)))
def c5794 : List Lit := [(35, false), (44, false), (110, true), (109, false)]
theorem step5794 (p : Nat → Bool) (h : Constraints p) : clause p c5794 = true :=
  Snake9.LocalRup.prove_clause [c1990, c130] c5794 (by decide) p (sat_cons (step1990 p h) (sat_cons (step130 p h) (sat_nil p)))
def c5795 : List Lit := [(48, true), (1623, false), (1687, true), (1644, false)]
theorem step5795 (p : Nat → Bool) (h : Constraints p) : clause p c5795 = true :=
  Snake9.LocalRup.prove_clause [c2427, c1314, c1285, c1245, c1242, c1243, c1244, c2195, c1280, c1338, c1313] c5795 (by decide) p (sat_cons (step2427 p h) (sat_cons (step1314 p h) (sat_cons (step1285 p h) (sat_cons (step1245 p h) (sat_cons (step1242 p h) (sat_cons (step1243 p h) (sat_cons (step1244 p h) (sat_cons (step2195 p h) (sat_cons (step1280 p h) (sat_cons (step1338 p h) (sat_cons (step1313 p h) (sat_nil p))))))))))))
def c5796 : List Lit := [(1623, false), (1760, false), (1806, false), (1687, true), (1788, false), (1799, false), (1644, false), (1803, false)]
theorem step5796 (p : Nat → Bool) (h : Constraints p) : clause p c5796 = true :=
  Snake9.LocalRup.prove_clause [c2449, c4521, c5795, c2176, c1238, c1239, c197, c2012, c1692, c188, c1625, c1578, c1597, c1585] c5796 (by decide) p (sat_cons (step2449 p h) (sat_cons (step4521 p h) (sat_cons (step5795 p h) (sat_cons (step2176 p h) (sat_cons (step1238 p h) (sat_cons (step1239 p h) (sat_cons (step197 p h) (sat_cons (step2012 p h) (sat_cons (step1692 p h) (sat_cons (step188 p h) (sat_cons (step1625 p h) (sat_cons (step1578 p h) (sat_cons (step1597 p h) (sat_cons (step1585 p h) (sat_nil p)))))))))))))))
def c5797 : List Lit := [(1628, true), (45, false), (48, false), (42, false), (1814, true), (1806, false), (79, false)]
theorem step5797 (p : Nat → Bool) (h : Constraints p) : clause p c5797 = true :=
  Snake9.LocalRup.prove_clause [c1239, c5793, c188, c4835, c1578, c1589] c5797 (by decide) p (sat_cons (step1239 p h) (sat_cons (step5793 p h) (sat_cons (step188 p h) (sat_cons (step4835 p h) (sat_cons (step1578 p h) (sat_cons (step1589 p h) (sat_nil p)))))))
def c5798 : List Lit := [(1813, true), (1806, false), (111, true), (1803, false), (112, false)]
theorem step5798 (p : Nat → Bool) (h : Constraints p) : clause p c5798 = true :=
  Snake9.LocalRup.prove_clause [c1585, c2256, c1578, c2105] c5798 (by decide) p (sat_cons (step1585 p h) (sat_cons (step2256 p h) (sat_cons (step1578 p h) (sat_cons (step2105 p h) (sat_nil p)))))
def c5799 : List Lit := [(48, false), (1628, true), (42, false), (1814, true), (1806, false), (79, false)]
theorem step5799 (p : Nat → Bool) (h : Constraints p) : clause p c5799 = true :=
  Snake9.LocalRup.prove_clause [c4624, c1239, c1238, c5797, c197, c2004] c5799 (by decide) p (sat_cons (step4624 p h) (sat_cons (step1239 p h) (sat_cons (step1238 p h) (sat_cons (step5797 p h) (sat_cons (step197 p h) (sat_cons (step2004 p h) (sat_nil p)))))))
def c5800 : List Lit := [(1622, true), (36, true), (110, true), (117, false), (115, true)]
theorem step5800 (p : Nat → Bool) (h : Constraints p) : clause p c5800 = true :=
  Snake9.LocalRup.prove_clause [c1869, c1221, c2252, c2355, c2317, c1207, c1225, c1217, c1197, c1209, c1194, c159, c1989] c5800 (by decide) p (sat_cons (step1869 p h) (sat_cons (step1221 p h) (sat_cons (step2252 p h) (sat_cons (step2355 p h) (sat_cons (step2317 p h) (sat_cons (step1207 p h) (sat_cons (step1225 p h) (sat_cons (step1217 p h) (sat_cons (step1197 p h) (sat_cons (step1209 p h) (sat_cons (step1194 p h) (sat_cons (step159 p h) (sat_cons (step1989 p h) (sat_nil p))))))))))))))
def c5801 : List Lit := [(1714, true), (88, true), (73, true), (111, true), (115, true), (106, true), (107, false), (112, false)]
theorem step5801 (p : Nat → Bool) (h : Constraints p) : clause p c5801 = true :=
  Snake9.LocalRup.prove_clause [c1389, c1392, c1394, c1390, c1386, c296, c573, c2086] c5801 (by decide) p (sat_cons (step1389 p h) (sat_cons (step1392 p h) (sat_cons (step1394 p h) (sat_cons (step1390 p h) (sat_cons (step1386 p h) (sat_cons (step296 p h) (sat_cons (step573 p h) (sat_cons (step2086 p h) (sat_nil p)))))))))
def c5802 : List Lit := [(1726, false), (1749, true), (1738, false)]
theorem step5802 (p : Nat → Bool) (h : Constraints p) : clause p c5802 = true :=
  Snake9.LocalRup.prove_clause [c1442, c1470, c1428, c1466, c1429, c1446, c1908, c1431] c5802 (by decide) p (sat_cons (step1442 p h) (sat_cons (step1470 p h) (sat_cons (step1428 p h) (sat_cons (step1466 p h) (sat_cons (step1429 p h) (sat_cons (step1446 p h) (sat_cons (step1908 p h) (sat_cons (step1431 p h) (sat_nil p)))))))))
def c5803 : List Lit := [(1714, true), (1646, true), (73, true), (115, true), (93, false)]
theorem step5803 (p : Nat → Bool) (h : Constraints p) : clause p c5803 = true :=
  Snake9.LocalRup.prove_clause [c1389, c1392, c1394, c1390, c1386, c5774] c5803 (by decide) p (sat_cons (step1389 p h) (sat_cons (step1392 p h) (sat_cons (step1394 p h) (sat_cons (step1390 p h) (sat_cons (step1386 p h) (sat_cons (step5774 p h) (sat_nil p)))))))
def c5804 : List Lit := [(1622, true), (1604, false), (115, true), (109, false), (112, false)]
theorem step5804 (p : Nat → Bool) (h : Constraints p) : clause p c5804 = true :=
  Snake9.LocalRup.prove_clause [c1199, c1869, c4698, c1229, c1225, c1996, c1200, c1194, c597, c1989, c4410] c5804 (by decide) p (sat_cons (step1199 p h) (sat_cons (step1869 p h) (sat_cons (step4698 p h) (sat_cons (step1229 p h) (sat_cons (step1225 p h) (sat_cons (step1996 p h) (sat_cons (step1200 p h) (sat_cons (step1194 p h) (sat_cons (step597 p h) (sat_cons (step1989 p h) (sat_cons (step4410 p h) (sat_nil p))))))))))))
def c5805 : List Lit := [(1830, false), (1806, true), (1622, false), (1604, false), (1714, false), (1760, false), (1738, false), (1725, false), (115, true), (1644, false), (113, false)]
theorem step5805 (p : Nat → Bool) (h : Constraints p) : clause p c5805 = true :=
  Snake9.LocalRup.prove_clause [c1275, c1305, c1692, c4198, c2176, c4741, c2426, c4483, c1344, c1307, c1238, c1285, c2971, c5340, c4658, c2195, c5782, c1337, c1280, c1306] c5805 (by decide) p (sat_cons (step1275 p h) (sat_cons (step1305 p h) (sat_cons (step1692 p h) (sat_cons (step4198 p h) (sat_cons (step2176 p h) (sat_cons (step4741 p h) (sat_cons (step2426 p h) (sat_cons (step4483 p h) (sat_cons (step1344 p h) (sat_cons (step1307 p h) (sat_cons (step1238 p h) (sat_cons (step1285 p h) (sat_cons (step2971 p h) (sat_cons (step5340 p h) (sat_cons (step4658 p h) (sat_cons (step2195 p h) (sat_cons (step5782 p h) (sat_cons (step1337 p h) (sat_cons (step1280 p h) (sat_cons (step1306 p h) (sat_nil p)))))))))))))))))))))
def c5806 : List Lit := [(126, false), (86, false), (115, true), (93, false), (1789, true), (1775, false)]
theorem step5806 (p : Nat → Bool) (h : Constraints p) : clause p c5806 = true :=
  Snake9.LocalRup.prove_clause [c4055, c1522, c419, c4754, c4787, c1526, c4350] c5806 (by decide) p (sat_cons (step4055 p h) (sat_cons (step1522 p h) (sat_cons (step419 p h) (sat_cons (step4754 p h) (sat_cons (step4787 p h) (sat_cons (step1526 p h) (sat_cons (step4350 p h) (sat_nil p))))))))
def c5807 : List Lit := [(29, false), (101, false), (89, false), (93, false), (112, false), (1780, true), (1789, true)]
theorem step5807 (p : Nat → Bool) (h : Constraints p) : clause p c5807 = true :=
  Snake9.LocalRup.prove_clause [c497, c498, c1508, c1518, c1520, c1526, c1542, c1513, c1505, c445, c1936] c5807 (by decide) p (sat_cons (step497 p h) (sat_cons (step498 p h) (sat_cons (step1508 p h) (sat_cons (step1518 p h) (sat_cons (step1520 p h) (sat_cons (step1526 p h) (sat_cons (step1542 p h) (sat_cons (step1513 p h) (sat_cons (step1505 p h) (sat_cons (step445 p h) (sat_cons (step1936 p h) (sat_nil p))))))))))))
def c5808 : List Lit := [(1771, true), (88, true), (108, true), (89, false), (112, false)]
theorem step5808 (p : Nat → Bool) (h : Constraints p) : clause p c5808 = true :=
  Snake9.LocalRup.prove_clause [c1504, c1505, c445, c2056, c2059, c1752] c5808 (by decide) p (sat_cons (step1504 p h) (sat_cons (step1505 p h) (sat_cons (step445 p h) (sat_cons (step2056 p h) (sat_cons (step2059 p h) (sat_cons (step1752 p h) (sat_nil p)))))))
def c5809 : List Lit := [(95, false), (103, false), (89, false), (112, false)]
theorem step5809 (p : Nat → Bool) (h : Constraints p) : clause p c5809 = true :=
  Snake9.LocalRup.prove_clause [c445, c1936] c5809 (by decide) p (sat_cons (step445 p h) (sat_cons (step1936 p h) (sat_nil p)))
def c5810 : List Lit := [(1772, false), (93, false), (1789, true)]
theorem step5810 (p : Nat → Bool) (h : Constraints p) : clause p c5810 = true :=
  Snake9.LocalRup.prove_clause [c1546, c1515, c1516, c1542, c1508, c1526, c1518, c3535, c503] c5810 (by decide) p (sat_cons (step1546 p h) (sat_cons (step1515 p h) (sat_cons (step1516 p h) (sat_cons (step1542 p h) (sat_cons (step1508 p h) (sat_cons (step1526 p h) (sat_cons (step1518 p h) (sat_cons (step3535 p h) (sat_cons (step503 p h) (sat_nil p))))))))))
end B112E034
