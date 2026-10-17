import B112E050Part0140
namespace B112E050
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c10840 : List Lit := [(1742, false), (114, true), (1830, false), (1761, true), (1660, false)]
theorem step10840 (p : Nat → Bool) (h : Constraints p) : clause p c10840 = true :=
  Snake9.LocalRup.prove_clause [c10789, c10607, c7080, c10161, c1440, c1443, c8026, c7568, c1697, c1099, c2250, c1896, c10208] c10840 (by decide) p (sat_cons (step10789 p h) (sat_cons (step10607 p h) (sat_cons (step7080 p h) (sat_cons (step10161 p h) (sat_cons (step1440 p h) (sat_cons (step1443 p h) (sat_cons (step8026 p h) (sat_cons (step7568 p h) (sat_cons (step1697 p h) (sat_cons (step1099 p h) (sat_cons (step2250 p h) (sat_cons (step1896 p h) (sat_cons (step10208 p h) (sat_nil p))))))))))))))
def c10841 : List Lit := [(103, false), (1742, true), (1670, false), (1635, false), (1830, false), (1656, false), (27, true), (64, false)]
theorem step10841 (p : Nat → Bool) (h : Constraints p) : clause p c10841 = true :=
  Snake9.LocalRup.prove_clause [c10786, c10785, c9434, c10789, c10607, c10784, c1139, c1141, c237, c6339, c4393, c6321, c10791, c1439, c1125, c1235, c2251, c1457, c1864, c1689, c2227, c1155, c8258, c4388, c4269] c10841 (by decide) p (sat_cons (step10786 p h) (sat_cons (step10785 p h) (sat_cons (step9434 p h) (sat_cons (step10789 p h) (sat_cons (step10607 p h) (sat_cons (step10784 p h) (sat_cons (step1139 p h) (sat_cons (step1141 p h) (sat_cons (step237 p h) (sat_cons (step6339 p h) (sat_cons (step4393 p h) (sat_cons (step6321 p h) (sat_cons (step10791 p h) (sat_cons (step1439 p h) (sat_cons (step1125 p h) (sat_cons (step1235 p h) (sat_cons (step2251 p h) (sat_cons (step1457 p h) (sat_cons (step1864 p h) (sat_cons (step1689 p h) (sat_cons (step2227 p h) (sat_cons (step1155 p h) (sat_cons (step8258 p h) (sat_cons (step4388 p h) (sat_cons (step4269 p h) (sat_nil p))))))))))))))))))))))))))
def c10842 : List Lit := [(1580, true), (114, true), (102, false), (96, true)]
theorem step10842 (p : Nat → Bool) (h : Constraints p) : clause p c10842 = true :=
  Snake9.LocalRup.prove_clause [c10788, c10785, c10307, c10786, c9434, c10784, c10607, c8909, c10839, c570, c580, c5875, c5028, c2838, c6830, c7080, c10492, c1292, c10799, c10840, c10841, c1125, c1126, c2760, c3556, c2853, c1235, c1238, c1267, c4427, c2250, c1697, c10306, c8026, c10645, c1442] c10842 (by decide) p (sat_cons (step10788 p h) (sat_cons (step10785 p h) (sat_cons (step10307 p h) (sat_cons (step10786 p h) (sat_cons (step9434 p h) (sat_cons (step10784 p h) (sat_cons (step10607 p h) (sat_cons (step8909 p h) (sat_cons (step10839 p h) (sat_cons (step570 p h) (sat_cons (step580 p h) (sat_cons (step5875 p h) (sat_cons (step5028 p h) (sat_cons (step2838 p h) (sat_cons (step6830 p h) (sat_cons (step7080 p h) (sat_cons (step10492 p h) (sat_cons (step1292 p h) (sat_cons (step10799 p h) (sat_cons (step10840 p h) (sat_cons (step10841 p h) (sat_cons (step1125 p h) (sat_cons (step1126 p h) (sat_cons (step2760 p h) (sat_cons (step3556 p h) (sat_cons (step2853 p h) (sat_cons (step1235 p h) (sat_cons (step1238 p h) (sat_cons (step1267 p h) (sat_cons (step4427 p h) (sat_cons (step2250 p h) (sat_cons (step1697 p h) (sat_cons (step10306 p h) (sat_cons (step8026 p h) (sat_cons (step10645 p h) (sat_cons (step1442 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))
def c10843 : List Lit := [(1741, false), (114, true), (102, false), (96, true)]
theorem step10843 (p : Nat → Bool) (h : Constraints p) : clause p c10843 = true :=
  Snake9.LocalRup.prove_clause [c10788, c10785, c10786, c10307, c10607, c10784, c10839, c5028, c2838, c6830, c10492, c570, c10842, c1864, c4424, c2250, c1697, c10799, c10796, c8909, c580, c5875, c7080, c1292, c10840, c10841, c1442, c10197, c10645] c10843 (by decide) p (sat_cons (step10788 p h) (sat_cons (step10785 p h) (sat_cons (step10786 p h) (sat_cons (step10307 p h) (sat_cons (step10607 p h) (sat_cons (step10784 p h) (sat_cons (step10839 p h) (sat_cons (step5028 p h) (sat_cons (step2838 p h) (sat_cons (step6830 p h) (sat_cons (step10492 p h) (sat_cons (step570 p h) (sat_cons (step10842 p h) (sat_cons (step1864 p h) (sat_cons (step4424 p h) (sat_cons (step2250 p h) (sat_cons (step1697 p h) (sat_cons (step10799 p h) (sat_cons (step10796 p h) (sat_cons (step8909 p h) (sat_cons (step580 p h) (sat_cons (step5875 p h) (sat_cons (step7080 p h) (sat_cons (step1292 p h) (sat_cons (step10840 p h) (sat_cons (step10841 p h) (sat_cons (step1442 p h) (sat_cons (step10197 p h) (sat_cons (step10645 p h) (sat_nil p))))))))))))))))))))))))))))))
def c10844 : List Lit := [(114, true), (102, false), (96, true)]
theorem step10844 (p : Nat → Bool) (h : Constraints p) : clause p c10844 = true :=
  Snake9.LocalRup.prove_clause [c10788, c10786, c10785, c10307, c9434, c10790, c10789, c10607, c10784, c10839, c570, c1139, c1141, c5028, c2838, c6830, c580, c5875, c8909, c237, c10799, c10492, c7080, c1292, c10840, c10841, c10842, c1864, c1155, c10843, c1436, c1437, c1957, c5086, c4941, c1798, c1267, c1235, c4429, c2251, c1677, c1689, c10647, c1535, c372, c1434, c1441, c1457, c8258, c2227, c4269, c4388] c10844 (by decide) p (sat_cons (step10788 p h) (sat_cons (step10786 p h) (sat_cons (step10785 p h) (sat_cons (step10307 p h) (sat_cons (step9434 p h) (sat_cons (step10790 p h) (sat_cons (step10789 p h) (sat_cons (step10607 p h) (sat_cons (step10784 p h) (sat_cons (step10839 p h) (sat_cons (step570 p h) (sat_cons (step1139 p h) (sat_cons (step1141 p h) (sat_cons (step5028 p h) (sat_cons (step2838 p h) (sat_cons (step6830 p h) (sat_cons (step580 p h) (sat_cons (step5875 p h) (sat_cons (step8909 p h) (sat_cons (step237 p h) (sat_cons (step10799 p h) (sat_cons (step10492 p h) (sat_cons (step7080 p h) (sat_cons (step1292 p h) (sat_cons (step10840 p h) (sat_cons (step10841 p h) (sat_cons (step10842 p h) (sat_cons (step1864 p h) (sat_cons (step1155 p h) (sat_cons (step10843 p h) (sat_cons (step1436 p h) (sat_cons (step1437 p h) (sat_cons (step1957 p h) (sat_cons (step5086 p h) (sat_cons (step4941 p h) (sat_cons (step1798 p h) (sat_cons (step1267 p h) (sat_cons (step1235 p h) (sat_cons (step4429 p h) (sat_cons (step2251 p h) (sat_cons (step1677 p h) (sat_cons (step1689 p h) (sat_cons (step10647 p h) (sat_cons (step1535 p h) (sat_cons (step372 p h) (sat_cons (step1434 p h) (sat_cons (step1441 p h) (sat_cons (step1457 p h) (sat_cons (step8258 p h) (sat_cons (step2227 p h) (sat_cons (step4269 p h) (sat_cons (step4388 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))
def c10845 : List Lit := [(102, false), (96, true)]
theorem step10845 (p : Nat → Bool) (h : Constraints p) : clause p c10845 = true :=
  Snake9.LocalRup.prove_clause [c10786, c10785, c10788, c10307, c10790, c10784, c9434, c10607, c10789, c10839, c5028, c7452, c2249, c1584, c10492, c1519, c4591, c8909, c580, c570, c2838, c5875, c1139, c1528, c1141, c10844, c3838, c10800, c1698, c1676, c10505, c8026, c2252, c1864, c1440, c4424, c1155, c2250, c2202, c1690, c1344, c7662, c10506, c1235, c4941, c6321, c1439, c1533, c8035, c1540, c1561] c10845 (by decide) p (sat_cons (step10786 p h) (sat_cons (step10785 p h) (sat_cons (step10788 p h) (sat_cons (step10307 p h) (sat_cons (step10790 p h) (sat_cons (step10784 p h) (sat_cons (step9434 p h) (sat_cons (step10607 p h) (sat_cons (step10789 p h) (sat_cons (step10839 p h) (sat_cons (step5028 p h) (sat_cons (step7452 p h) (sat_cons (step2249 p h) (sat_cons (step1584 p h) (sat_cons (step10492 p h) (sat_cons (step1519 p h) (sat_cons (step4591 p h) (sat_cons (step8909 p h) (sat_cons (step580 p h) (sat_cons (step570 p h) (sat_cons (step2838 p h) (sat_cons (step5875 p h) (sat_cons (step1139 p h) (sat_cons (step1528 p h) (sat_cons (step1141 p h) (sat_cons (step10844 p h) (sat_cons (step3838 p h) (sat_cons (step10800 p h) (sat_cons (step1698 p h) (sat_cons (step1676 p h) (sat_cons (step10505 p h) (sat_cons (step8026 p h) (sat_cons (step2252 p h) (sat_cons (step1864 p h) (sat_cons (step1440 p h) (sat_cons (step4424 p h) (sat_cons (step1155 p h) (sat_cons (step2250 p h) (sat_cons (step2202 p h) (sat_cons (step1690 p h) (sat_cons (step1344 p h) (sat_cons (step7662 p h) (sat_cons (step10506 p h) (sat_cons (step1235 p h) (sat_cons (step4941 p h) (sat_cons (step6321 p h) (sat_cons (step1439 p h) (sat_cons (step1533 p h) (sat_cons (step8035 p h) (sat_cons (step1540 p h) (sat_cons (step1561 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))
def c10846 : List Lit := [(1830, true), (114, true), (96, true)]
theorem step10846 (p : Nat → Bool) (h : Constraints p) : clause p c10846 = true :=
  Snake9.LocalRup.prove_clause [c10785, c10307, c10839, c10845, c2119, c1519, c4591, c5028, c8536, c10484, c424, c10031] c10846 (by decide) p (sat_cons (step10785 p h) (sat_cons (step10307 p h) (sat_cons (step10839 p h) (sat_cons (step10845 p h) (sat_cons (step2119 p h) (sat_cons (step1519 p h) (sat_cons (step4591 p h) (sat_cons (step5028 p h) (sat_cons (step8536 p h) (sat_cons (step10484 p h) (sat_cons (step424 p h) (sat_cons (step10031 p h) (sat_nil p)))))))))))))
def c10847 : List Lit := [(103, false), (1761, true), (1830, false), (1739, false), (114, true), (1660, false)]
theorem step10847 (p : Nat → Bool) (h : Constraints p) : clause p c10847 = true :=
  Snake9.LocalRup.prove_clause [c9434, c10840, c6339, c4393, c1442, c1125, c10796] c10847 (by decide) p (sat_cons (step9434 p h) (sat_cons (step10840 p h) (sat_cons (step6339 p h) (sat_cons (step4393 p h) (sat_cons (step1442 p h) (sat_cons (step1125 p h) (sat_cons (step10796 p h) (sat_nil p))))))))
def c10848 : List Lit := [(1580, true), (114, true), (96, true)]
theorem step10848 (p : Nat → Bool) (h : Constraints p) : clause p c10848 = true :=
  Snake9.LocalRup.prove_clause [c10307, c10784, c9434, c10607, c10839, c10492, c10845, c4191, c10846, c5028, c7452, c2249, c1705, c10847, c10840, c2119, c1519, c4591, c1125, c1126, c2760, c4530, c2856, c401, c1442, c1574, c1579, c1522, c8026, c7046, c1698] c10848 (by decide) p (sat_cons (step10307 p h) (sat_cons (step10784 p h) (sat_cons (step9434 p h) (sat_cons (step10607 p h) (sat_cons (step10839 p h) (sat_cons (step10492 p h) (sat_cons (step10845 p h) (sat_cons (step4191 p h) (sat_cons (step10846 p h) (sat_cons (step5028 p h) (sat_cons (step7452 p h) (sat_cons (step2249 p h) (sat_cons (step1705 p h) (sat_cons (step10847 p h) (sat_cons (step10840 p h) (sat_cons (step2119 p h) (sat_cons (step1519 p h) (sat_cons (step4591 p h) (sat_cons (step1125 p h) (sat_cons (step1126 p h) (sat_cons (step2760 p h) (sat_cons (step4530 p h) (sat_cons (step2856 p h) (sat_cons (step401 p h) (sat_cons (step1442 p h) (sat_cons (step1574 p h) (sat_cons (step1579 p h) (sat_cons (step1522 p h) (sat_cons (step8026 p h) (sat_cons (step7046 p h) (sat_cons (step1698 p h) (sat_nil p))))))))))))))))))))))))))))))))
def c10849 : List Lit := [(114, true), (96, true)]
theorem step10849 (p : Nat → Bool) (h : Constraints p) : clause p c10849 = true :=
  Snake9.LocalRup.prove_clause [c10307, c9434, c10607, c10784, c10845, c10839, c5028, c7452, c2249, c10492, c1519, c4591, c4191, c3058, c2119, c2118, c1789, c10846, c1705, c10847, c10848, c1864, c10678, c10796, c1154, c2250, c1442, c1697, c1436, c1437, c1957, c5086, c10747, c8185, c1798, c2024, c913, c916, c917, c919, c956, c1007, c2200, c1091, c1045, c1044, c1033, c1032, c1031, c373, c2442, c1613, c10748, c10204, c10198] c10849 (by decide) p (sat_cons (step10307 p h) (sat_cons (step9434 p h) (sat_cons (step10607 p h) (sat_cons (step10784 p h) (sat_cons (step10845 p h) (sat_cons (step10839 p h) (sat_cons (step5028 p h) (sat_cons (step7452 p h) (sat_cons (step2249 p h) (sat_cons (step10492 p h) (sat_cons (step1519 p h) (sat_cons (step4591 p h) (sat_cons (step4191 p h) (sat_cons (step3058 p h) (sat_cons (step2119 p h) (sat_cons (step2118 p h) (sat_cons (step1789 p h) (sat_cons (step10846 p h) (sat_cons (step1705 p h) (sat_cons (step10847 p h) (sat_cons (step10848 p h) (sat_cons (step1864 p h) (sat_cons (step10678 p h) (sat_cons (step10796 p h) (sat_cons (step1154 p h) (sat_cons (step2250 p h) (sat_cons (step1442 p h) (sat_cons (step1697 p h) (sat_cons (step1436 p h) (sat_cons (step1437 p h) (sat_cons (step1957 p h) (sat_cons (step5086 p h) (sat_cons (step10747 p h) (sat_cons (step8185 p h) (sat_cons (step1798 p h) (sat_cons (step2024 p h) (sat_cons (step913 p h) (sat_cons (step916 p h) (sat_cons (step917 p h) (sat_cons (step919 p h) (sat_cons (step956 p h) (sat_cons (step1007 p h) (sat_cons (step2200 p h) (sat_cons (step1091 p h) (sat_cons (step1045 p h) (sat_cons (step1044 p h) (sat_cons (step1033 p h) (sat_cons (step1032 p h) (sat_cons (step1031 p h) (sat_cons (step373 p h) (sat_cons (step2442 p h) (sat_cons (step1613 p h) (sat_cons (step10748 p h) (sat_cons (step10204 p h) (sat_cons (step10198 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c10850 : List Lit := [(1742, false), (1783, false), (96, true)]
theorem step10850 (p : Nat → Bool) (h : Constraints p) : clause p c10850 = true :=
  Snake9.LocalRup.prove_clause [c10789, c10607, c10784, c10307, c10839, c5028, c7452, c2249, c1519, c4591, c10849, c3838, c10484, c1705, c10161, c1440, c1443, c8026, c1434, c1698, c4310, c10756, c1561] c10850 (by decide) p (sat_cons (step10789 p h) (sat_cons (step10607 p h) (sat_cons (step10784 p h) (sat_cons (step10307 p h) (sat_cons (step10839 p h) (sat_cons (step5028 p h) (sat_cons (step7452 p h) (sat_cons (step2249 p h) (sat_cons (step1519 p h) (sat_cons (step4591 p h) (sat_cons (step10849 p h) (sat_cons (step3838 p h) (sat_cons (step10484 p h) (sat_cons (step1705 p h) (sat_cons (step10161 p h) (sat_cons (step1440 p h) (sat_cons (step1443 p h) (sat_cons (step8026 p h) (sat_cons (step1434 p h) (sat_cons (step1698 p h) (sat_cons (step4310 p h) (sat_cons (step10756 p h) (sat_cons (step1561 p h) (sat_nil p))))))))))))))))))))))))
def c10851 : List Lit := [(103, false), (96, true)]
theorem step10851 (p : Nat → Bool) (h : Constraints p) : clause p c10851 = true :=
  Snake9.LocalRup.prove_clause [c10786, c10784, c10789, c9434, c10307, c10839, c5028, c1584, c1598, c10849, c3838, c1612, c10845, c10492, c6339, c628, c1439, c4206, c1457, c1540, c2227, c10850, c4393, c6394, c1125, c5842, c6259, c10678, c1683, c2250, c2251, c1684, c10833, c5823] c10851 (by decide) p (sat_cons (step10786 p h) (sat_cons (step10784 p h) (sat_cons (step10789 p h) (sat_cons (step9434 p h) (sat_cons (step10307 p h) (sat_cons (step10839 p h) (sat_cons (step5028 p h) (sat_cons (step1584 p h) (sat_cons (step1598 p h) (sat_cons (step10849 p h) (sat_cons (step3838 p h) (sat_cons (step1612 p h) (sat_cons (step10845 p h) (sat_cons (step10492 p h) (sat_cons (step6339 p h) (sat_cons (step628 p h) (sat_cons (step1439 p h) (sat_cons (step4206 p h) (sat_cons (step1457 p h) (sat_cons (step1540 p h) (sat_cons (step2227 p h) (sat_cons (step10850 p h) (sat_cons (step4393 p h) (sat_cons (step6394 p h) (sat_cons (step1125 p h) (sat_cons (step5842 p h) (sat_cons (step6259 p h) (sat_cons (step10678 p h) (sat_cons (step1683 p h) (sat_cons (step2250 p h) (sat_cons (step2251 p h) (sat_cons (step1684 p h) (sat_cons (step10833 p h) (sat_cons (step5823 p h) (sat_nil p)))))))))))))))))))))))))))))))))))
def c10852 : List Lit := [(1580, true), (96, true)]
theorem step10852 (p : Nat → Bool) (h : Constraints p) : clause p c10852 = true :=
  Snake9.LocalRup.prove_clause [c9434, c10307, c10789, c10607, c10851, c1533, c1540, c10850, c10839, c5028, c1584, c1598, c10849, c3838, c1612, c10845, c7452, c2249, c1125, c1126, c2760, c4530, c6690, c5842, c6259, c1457, c3732, c1698, c2227, c8026, c1685, c1442, c1662, c1434, c6486, c10755, c1563, c1651, c3799, c1623, c1618, c5284, c1650, c1384, c1691, c1936, c8258] c10852 (by decide) p (sat_cons (step9434 p h) (sat_cons (step10307 p h) (sat_cons (step10789 p h) (sat_cons (step10607 p h) (sat_cons (step10851 p h) (sat_cons (step1533 p h) (sat_cons (step1540 p h) (sat_cons (step10850 p h) (sat_cons (step10839 p h) (sat_cons (step5028 p h) (sat_cons (step1584 p h) (sat_cons (step1598 p h) (sat_cons (step10849 p h) (sat_cons (step3838 p h) (sat_cons (step1612 p h) (sat_cons (step10845 p h) (sat_cons (step7452 p h) (sat_cons (step2249 p h) (sat_cons (step1125 p h) (sat_cons (step1126 p h) (sat_cons (step2760 p h) (sat_cons (step4530 p h) (sat_cons (step6690 p h) (sat_cons (step5842 p h) (sat_cons (step6259 p h) (sat_cons (step1457 p h) (sat_cons (step3732 p h) (sat_cons (step1698 p h) (sat_cons (step2227 p h) (sat_cons (step8026 p h) (sat_cons (step1685 p h) (sat_cons (step1442 p h) (sat_cons (step1662 p h) (sat_cons (step1434 p h) (sat_cons (step6486 p h) (sat_cons (step10755 p h) (sat_cons (step1563 p h) (sat_cons (step1651 p h) (sat_cons (step3799 p h) (sat_cons (step1623 p h) (sat_cons (step1618 p h) (sat_cons (step5284 p h) (sat_cons (step1650 p h) (sat_cons (step1384 p h) (sat_cons (step1691 p h) (sat_cons (step1936 p h) (sat_cons (step8258 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))
def c10853 : List Lit := [(1741, false), (96, true)]
theorem step10853 (p : Nat → Bool) (h : Constraints p) : clause p c10853 = true :=
  Snake9.LocalRup.prove_clause [c10784, c10307, c10607, c10789, c10839, c5028, c1519, c4591, c10849, c3838, c10484, c10845, c10492, c10852, c10678, c2250, c1697, c8026, c10851, c1584, c1439, c1442, c1434, c10755, c10756, c8035, c1690] c10853 (by decide) p (sat_cons (step10784 p h) (sat_cons (step10307 p h) (sat_cons (step10607 p h) (sat_cons (step10789 p h) (sat_cons (step10839 p h) (sat_cons (step5028 p h) (sat_cons (step1519 p h) (sat_cons (step4591 p h) (sat_cons (step10849 p h) (sat_cons (step3838 p h) (sat_cons (step10484 p h) (sat_cons (step10845 p h) (sat_cons (step10492 p h) (sat_cons (step10852 p h) (sat_cons (step10678 p h) (sat_cons (step2250 p h) (sat_cons (step1697 p h) (sat_cons (step8026 p h) (sat_cons (step10851 p h) (sat_cons (step1584 p h) (sat_cons (step1439 p h) (sat_cons (step1442 p h) (sat_cons (step1434 p h) (sat_cons (step10755 p h) (sat_cons (step10756 p h) (sat_cons (step8035 p h) (sat_cons (step1690 p h) (sat_nil p))))))))))))))))))))))))))))
def c10854 : List Lit := [(1743, false), (96, true)]
theorem step10854 (p : Nat → Bool) (h : Constraints p) : clause p c10854 = true :=
  Snake9.LocalRup.prove_clause [c9434, c10307, c10784, c10607, c10789, c10845, c10839, c10492, c10852, c10678, c2250, c5028, c10849, c1584, c1598, c3838, c1612, c10853, c5972, c6259, c1690, c1519, c4591, c10851, c1533, c1540, c1556, c1526, c1457, c8258, c8035, c2227, c1936, c1553, c1684, c1384, c3799, c1644, c5284, c1623] c10854 (by decide) p (sat_cons (step9434 p h) (sat_cons (step10307 p h) (sat_cons (step10784 p h) (sat_cons (step10607 p h) (sat_cons (step10789 p h) (sat_cons (step10845 p h) (sat_cons (step10839 p h) (sat_cons (step10492 p h) (sat_cons (step10852 p h) (sat_cons (step10678 p h) (sat_cons (step2250 p h) (sat_cons (step5028 p h) (sat_cons (step10849 p h) (sat_cons (step1584 p h) (sat_cons (step1598 p h) (sat_cons (step3838 p h) (sat_cons (step1612 p h) (sat_cons (step10853 p h) (sat_cons (step5972 p h) (sat_cons (step6259 p h) (sat_cons (step1690 p h) (sat_cons (step1519 p h) (sat_cons (step4591 p h) (sat_cons (step10851 p h) (sat_cons (step1533 p h) (sat_cons (step1540 p h) (sat_cons (step1556 p h) (sat_cons (step1526 p h) (sat_cons (step1457 p h) (sat_cons (step8258 p h) (sat_cons (step8035 p h) (sat_cons (step2227 p h) (sat_cons (step1936 p h) (sat_cons (step1553 p h) (sat_cons (step1684 p h) (sat_cons (step1384 p h) (sat_cons (step3799 p h) (sat_cons (step1644 p h) (sat_cons (step5284 p h) (sat_cons (step1623 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))
def c10855 : List Lit := [(96, true)]
theorem step10855 (p : Nat → Bool) (h : Constraints p) : clause p c10855 = true :=
  Snake9.LocalRup.prove_clause [c10790, c9434, c10784, c10307, c10785, c10839, c5028, c10492, c7452, c2249, c10845, c10849, c10851, c1533, c10852, c10678, c2250, c1678, c10853, c1436, c1437, c1957, c5972, c1798, c5842, c3732, c1662, c10854, c1441, c1434, c4310, c372, c1563, c3306] c10855 (by decide) p (sat_cons (step10790 p h) (sat_cons (step9434 p h) (sat_cons (step10784 p h) (sat_cons (step10307 p h) (sat_cons (step10785 p h) (sat_cons (step10839 p h) (sat_cons (step5028 p h) (sat_cons (step10492 p h) (sat_cons (step7452 p h) (sat_cons (step2249 p h) (sat_cons (step10845 p h) (sat_cons (step10849 p h) (sat_cons (step10851 p h) (sat_cons (step1533 p h) (sat_cons (step10852 p h) (sat_cons (step10678 p h) (sat_cons (step2250 p h) (sat_cons (step1678 p h) (sat_cons (step10853 p h) (sat_cons (step1436 p h) (sat_cons (step1437 p h) (sat_cons (step1957 p h) (sat_cons (step5972 p h) (sat_cons (step1798 p h) (sat_cons (step5842 p h) (sat_cons (step3732 p h) (sat_cons (step1662 p h) (sat_cons (step10854 p h) (sat_cons (step1441 p h) (sat_cons (step1434 p h) (sat_cons (step4310 p h) (sat_cons (step372 p h) (sat_cons (step1563 p h) (sat_cons (step3306 p h) (sat_nil p)))))))))))))))))))))))))))))))))))
def c10856 : List Lit := [(1741, true)]
theorem step10856 (p : Nat → Bool) (h : Constraints p) : clause p c10856 = true :=
  Snake9.LocalRup.prove_clause [c10855, c9434, c3450] c10856 (by decide) p (sat_cons (step10855 p h) (sat_cons (step9434 p h) (sat_cons (step3450 p h) (sat_nil p))))
def c10857 : List Lit := [(1652, true)]
theorem step10857 (p : Nat → Bool) (h : Constraints p) : clause p c10857 = true :=
  Snake9.LocalRup.prove_clause [c10855, c10784, c3854] c10857 (by decide) p (sat_cons (step10855 p h) (sat_cons (step10784 p h) (sat_cons (step3854 p h) (sat_nil p))))
def c10858 : List Lit := [(1580, true)]
theorem step10858 (p : Nat → Bool) (h : Constraints p) : clause p c10858 = true :=
  Snake9.LocalRup.prove_clause [c10855, c10784, c9782] c10858 (by decide) p (sat_cons (step10855 p h) (sat_cons (step10784 p h) (sat_cons (step9782 p h) (sat_nil p))))
def c10859 : List Lit := [(106, false)]
theorem step10859 (p : Nat → Bool) (h : Constraints p) : clause p c10859 = true :=
  Snake9.LocalRup.prove_clause [c10855, c10786, c10307, c623] c10859 (by decide) p (sat_cons (step10855 p h) (sat_cons (step10786 p h) (sat_cons (step10307 p h) (sat_cons (step623 p h) (sat_nil p)))))
def c10860 : List Lit := [(64, true)]
theorem step10860 (p : Nat → Bool) (h : Constraints p) : clause p c10860 = true :=
  Snake9.LocalRup.prove_clause [c10855, c10786, c10788, c3026] c10860 (by decide) p (sat_cons (step10855 p h) (sat_cons (step10786 p h) (sat_cons (step10788 p h) (sat_cons (step3026 p h) (sat_nil p)))))
def c10861 : List Lit := [(1743, true)]
theorem step10861 (p : Nat → Bool) (h : Constraints p) : clause p c10861 = true :=
  Snake9.LocalRup.prove_clause [c10856, c1439] c10861 (by decide) p (sat_cons (step10856 p h) (sat_cons (step1439 p h) (sat_nil p)))
def c10862 : List Lit := [(1583, true)]
theorem step10862 (p : Nat → Bool) (h : Constraints p) : clause p c10862 = true :=
  Snake9.LocalRup.prove_clause [c10858, c1864] c10862 (by decide) p (sat_cons (step10858 p h) (sat_cons (step1864 p h) (sat_nil p)))
def c10863 : List Lit := [(1661, true)]
theorem step10863 (p : Nat → Bool) (h : Constraints p) : clause p c10863 = true :=
  Snake9.LocalRup.prove_clause [c10859, c10855, c10784, c3667] c10863 (by decide) p (sat_cons (step10859 p h) (sat_cons (step10855 p h) (sat_cons (step10784 p h) (sat_cons (step3667 p h) (sat_nil p)))))
def c10864 : List Lit := [(57, true)]
theorem step10864 (p : Nat → Bool) (h : Constraints p) : clause p c10864 = true :=
  Snake9.LocalRup.prove_clause [c10859, c10784, c3446] c10864 (by decide) p (sat_cons (step10859 p h) (sat_cons (step10784 p h) (sat_cons (step3446 p h) (sat_nil p))))
def c10865 : List Lit := [(56, false)]
theorem step10865 (p : Nat → Bool) (h : Constraints p) : clause p c10865 = true :=
  Snake9.LocalRup.prove_clause [c10860, c10786, c10785, c237] c10865 (by decide) p (sat_cons (step10860 p h) (sat_cons (step10786 p h) (sat_cons (step10785 p h) (sat_cons (step237 p h) (sat_nil p)))))
def c10866 : List Lit := [(1749, true)]
theorem step10866 (p : Nat → Bool) (h : Constraints p) : clause p c10866 = true :=
  Snake9.LocalRup.prove_clause [c10861, c10789, c1457] c10866 (by decide) p (sat_cons (step10861 p h) (sat_cons (step10789 p h) (sat_cons (step1457 p h) (sat_nil p))))
def c10867 : List Lit := [(1670, true)]
theorem step10867 (p : Nat → Bool) (h : Constraints p) : clause p c10867 = true :=
  Snake9.LocalRup.prove_clause [c10863, c2209] c10867 (by decide) p (sat_cons (step10863 p h) (sat_cons (step2209 p h) (sat_nil p)))
def c10868 : List Lit := [(117, false)]
theorem step10868 (p : Nat → Bool) (h : Constraints p) : clause p c10868 = true :=
  Snake9.LocalRup.prove_clause [c10864, c9434, c10855, c518] c10868 (by decide) p (sat_cons (step10864 p h) (sat_cons (step9434 p h) (sat_cons (step10855 p h) (sat_cons (step518 p h) (sat_nil p)))))
def c10869 : List Lit := [(89, false)]
theorem step10869 (p : Nat → Bool) (h : Constraints p) : clause p c10869 = true :=
  Snake9.LocalRup.prove_clause [c10864, c9434, c10855, c514] c10869 (by decide) p (sat_cons (step10864 p h) (sat_cons (step9434 p h) (sat_cons (step10855 p h) (sat_cons (step514 p h) (sat_nil p)))))
def c10870 : List Lit := [(1644, true)]
theorem step10870 (p : Nat → Bool) (h : Constraints p) : clause p c10870 = true :=
  Snake9.LocalRup.prove_clause [c10864, c10855, c2404] c10870 (by decide) p (sat_cons (step10864 p h) (sat_cons (step10855 p h) (sat_cons (step2404 p h) (sat_nil p))))
def c10871 : List Lit := [(1650, true)]
theorem step10871 (p : Nat → Bool) (h : Constraints p) : clause p c10871 = true :=
  Snake9.LocalRup.prove_clause [c10865, c1247] c10871 (by decide) p (sat_cons (step10865 p h) (sat_cons (step1247 p h) (sat_nil p)))
def c10872 : List Lit := [(1694, true)]
theorem step10872 (p : Nat → Bool) (h : Constraints p) : clause p c10872 = true :=
  Snake9.LocalRup.prove_clause [c10865, c10860, c10855, c10784, c10307, c4281] c10872 (by decide) p (sat_cons (step10865 p h) (sat_cons (step10860 p h) (sat_cons (step10855 p h) (sat_cons (step10784 p h) (sat_cons (step10307 p h) (sat_cons (step4281 p h) (sat_nil p)))))))
def c10873 : List Lit := [(1758, true)]
theorem step10873 (p : Nat → Bool) (h : Constraints p) : clause p c10873 = true :=
  Snake9.LocalRup.prove_clause [c10866, c2227] c10873 (by decide) p (sat_cons (step10866 p h) (sat_cons (step2227 p h) (sat_nil p)))
def c10874 : List Lit := [(1807, true)]
theorem step10874 (p : Nat → Bool) (h : Constraints p) : clause p c10874 = true :=
  Snake9.LocalRup.prove_clause [c10868, c10859, c3010] c10874 (by decide) p (sat_cons (step10868 p h) (sat_cons (step10859 p h) (sat_cons (step3010 p h) (sat_nil p))))
def c10875 : List Lit := [(1646, true)]
theorem step10875 (p : Nat → Bool) (h : Constraints p) : clause p c10875 = true :=
  Snake9.LocalRup.prove_clause [c10870, c1238] c10875 (by decide) p (sat_cons (step10870 p h) (sat_cons (step1238 p h) (sat_nil p)))
def c10876 : List Lit := [(1655, true)]
theorem step10876 (p : Nat → Bool) (h : Constraints p) : clause p c10876 = true :=
  Snake9.LocalRup.prove_clause [c10871, c10857, c1255] c10876 (by decide) p (sat_cons (step10871 p h) (sat_cons (step10857 p h) (sat_cons (step1255 p h) (sat_nil p))))
def c10877 : List Lit := [(1852, false)]
theorem step10877 (p : Nat → Bool) (h : Constraints p) : clause p c10877 = true :=
  Snake9.LocalRup.prove_clause [c10872, c2251] c10877 (by decide) p (sat_cons (step10872 p h) (sat_cons (step2251 p h) (sat_nil p)))
def c10878 : List Lit := [(1810, true)]
theorem step10878 (p : Nat → Bool) (h : Constraints p) : clause p c10878 = true :=
  Snake9.LocalRup.prove_clause [c10874, c1595] c10878 (by decide) p (sat_cons (step10874 p h) (sat_cons (step1595 p h) (sat_nil p)))
def c10879 : List Lit := [(1660, true)]
theorem step10879 (p : Nat → Bool) (h : Constraints p) : clause p c10879 = true :=
  Snake9.LocalRup.prove_clause [c10875, c10876, c1266] c10879 (by decide) p (sat_cons (step10875 p h) (sat_cons (step10876 p h) (sat_cons (step1266 p h) (sat_nil p))))
def c10880 : List Lit := [(1761, false)]
theorem step10880 (p : Nat → Bool) (h : Constraints p) : clause p c10880 = true :=
  Snake9.LocalRup.prove_clause [c10877, c3620] c10880 (by decide) p (sat_cons (step10877 p h) (sat_cons (step3620 p h) (sat_nil p)))
def c10881 : List Lit := [(1831, false)]
theorem step10881 (p : Nat → Bool) (h : Constraints p) : clause p c10881 = true :=
  Snake9.LocalRup.prove_clause [c10877, c10873, c1683] c10881 (by decide) p (sat_cons (step10877 p h) (sat_cons (step10873 p h) (sat_cons (step1683 p h) (sat_nil p))))
def c10882 : List Lit := [(1692, true)]
theorem step10882 (p : Nat → Bool) (h : Constraints p) : clause p c10882 = true :=
  Snake9.LocalRup.prove_clause [c10879, c10858, c5740] c10882 (by decide) p (sat_cons (step10879 p h) (sat_cons (step10858 p h) (sat_cons (step5740 p h) (sat_nil p))))
def c10883 : List Lit := [(1745, false)]
theorem step10883 (p : Nat → Bool) (h : Constraints p) : clause p c10883 = true :=
  Snake9.LocalRup.prove_clause [c10880, c10607, c10789, c10161] c10883 (by decide) p (sat_cons (step10880 p h) (sat_cons (step10607 p h) (sat_cons (step10789 p h) (sat_cons (step10161 p h) (sat_nil p)))))
def c10884 : List Lit := [(1854, false)]
theorem step10884 (p : Nat → Bool) (h : Constraints p) : clause p c10884 = true :=
  Snake9.LocalRup.prove_clause [c10882, c2249] c10884 (by decide) p (sat_cons (step10882 p h) (sat_cons (step2249 p h) (sat_nil p)))
def c10885 : List Lit := [(1740, false)]
theorem step10885 (p : Nat → Bool) (h : Constraints p) : clause p c10885 = true :=
  Snake9.LocalRup.prove_clause [c10883, c10856, c1445] c10885 (by decide) p (sat_cons (step10883 p h) (sat_cons (step10856 p h) (sat_cons (step1445 p h) (sat_nil p))))
def c10886 : List Lit := [(91, true)]
theorem step10886 (p : Nat → Bool) (h : Constraints p) : clause p c10886 = true :=
  Snake9.LocalRup.prove_clause [c10885, c10856, c10784, c10307, c10607, c10877, c1433, c1435, c1442, c4310, c8026, c3626, c1696] c10886 (by decide) p (sat_cons (step10885 p h) (sat_cons (step10856 p h) (sat_cons (step10784 p h) (sat_cons (step10307 p h) (sat_cons (step10607 p h) (sat_cons (step10877 p h) (sat_cons (step1433 p h) (sat_cons (step1435 p h) (sat_cons (step1442 p h) (sat_cons (step4310 p h) (sat_cons (step8026 p h) (sat_cons (step3626 p h) (sat_cons (step1696 p h) (sat_nil p))))))))))))))
def c10887 : List Lit := [(123, false)]
theorem step10887 (p : Nat → Bool) (h : Constraints p) : clause p c10887 = true :=
  Snake9.LocalRup.prove_clause [c10886, c5028] c10887 (by decide) p (sat_cons (step10886 p h) (sat_cons (step5028 p h) (sat_nil p)))
def c10888 : List Lit := [(1803, true)]
theorem step10888 (p : Nat → Bool) (h : Constraints p) : clause p c10888 = true :=
  Snake9.LocalRup.prove_clause [c10887, c1584] c10888 (by decide) p (sat_cons (step10887 p h) (sat_cons (step1584 p h) (sat_nil p)))
def c10889 : List Lit := [(1811, true)]
theorem step10889 (p : Nat → Bool) (h : Constraints p) : clause p c10889 = true :=
  Snake9.LocalRup.prove_clause [c10888, c10874, c1599] c10889 (by decide) p (sat_cons (step10888 p h) (sat_cons (step10874 p h) (sat_cons (step1599 p h) (sat_nil p))))
def c10890 : List Lit := [(1817, true)]
theorem step10890 (p : Nat → Bool) (h : Constraints p) : clause p c10890 = true :=
  Snake9.LocalRup.prove_clause [c10889, c2234] c10890 (by decide) p (sat_cons (step10889 p h) (sat_cons (step2234 p h) (sat_nil p)))
def c10891 : List Lit := [(102, false)]
theorem step10891 (p : Nat → Bool) (h : Constraints p) : clause p c10891 = true :=
  Snake9.LocalRup.prove_clause [c10886, c10884, c10887, c10877, c10862, c10607, c10867, c10866, c10873, c10856, c10890, c10855, c10786, c10784, c10307, c580, c570, c2838, c7591, c1139, c10652, c1141, c1696, c1155, c8026, c4388, c1440, c1442, c1648, c4205, c1434, c1561, c4310] c10891 (by decide) p (sat_cons (step10886 p h) (sat_cons (step10884 p h) (sat_cons (step10887 p h) (sat_cons (step10877 p h) (sat_cons (step10862 p h) (sat_cons (step10607 p h) (sat_cons (step10867 p h) (sat_cons (step10866 p h) (sat_cons (step10873 p h) (sat_cons (step10856 p h) (sat_cons (step10890 p h) (sat_cons (step10855 p h) (sat_cons (step10786 p h) (sat_cons (step10784 p h) (sat_cons (step10307 p h) (sat_cons (step580 p h) (sat_cons (step570 p h) (sat_cons (step2838 p h) (sat_cons (step7591 p h) (sat_cons (step1139 p h) (sat_cons (step10652 p h) (sat_cons (step1141 p h) (sat_cons (step1696 p h) (sat_cons (step1155 p h) (sat_cons (step8026 p h) (sat_cons (step4388 p h) (sat_cons (step1440 p h) (sat_cons (step1442 p h) (sat_cons (step1648 p h) (sat_cons (step4205 p h) (sat_cons (step1434 p h) (sat_cons (step1561 p h) (sat_cons (step4310 p h) (sat_nil p))))))))))))))))))))))))))))))))))
def c10892 : List Lit := [(1779, true)]
theorem step10892 (p : Nat → Bool) (h : Constraints p) : clause p c10892 = true :=
  Snake9.LocalRup.prove_clause [c10891, c10307, c10859, c10784, c4206] c10892 (by decide) p (sat_cons (step10891 p h) (sat_cons (step10307 p h) (sat_cons (step10859 p h) (sat_cons (step10784 p h) (sat_cons (step4206 p h) (sat_nil p))))))
def c10893 : List Lit := [(114, true)]
theorem step10893 (p : Nat → Bool) (h : Constraints p) : clause p c10893 = true :=
  Snake9.LocalRup.prove_clause [c10891, c10869, c10886, c2119] c10893 (by decide) p (sat_cons (step10891 p h) (sat_cons (step10869 p h) (sat_cons (step10886 p h) (sat_cons (step2119 p h) (sat_nil p)))))
def c10894 : List Lit := [(90, true)]
theorem step10894 (p : Nat → Bool) (h : Constraints p) : clause p c10894 = true :=
  Snake9.LocalRup.prove_clause [c10891, c10869, c10886, c2121] c10894 (by decide) p (sat_cons (step10891 p h) (sat_cons (step10869 p h) (sat_cons (step10886 p h) (sat_cons (step2121 p h) (sat_nil p)))))
def c10895 : List Lit := [(1783, true)]
theorem step10895 (p : Nat → Bool) (h : Constraints p) : clause p c10895 = true :=
  Snake9.LocalRup.prove_clause [c10892, c1540] c10895 (by decide) p (sat_cons (step10892 p h) (sat_cons (step1540 p h) (sat_nil p)))
def c10896 : List Lit := [(1818, true)]
theorem step10896 (p : Nat → Bool) (h : Constraints p) : clause p c10896 = true :=
  Snake9.LocalRup.prove_clause [c10893, c10878, c10855, c10786, c10886, c7691] c10896 (by decide) p (sat_cons (step10893 p h) (sat_cons (step10878 p h) (sat_cons (step10855 p h) (sat_cons (step10786 p h) (sat_cons (step10886 p h) (sat_cons (step7691 p h) (sat_nil p)))))))
def c10897 : List Lit := [(1775, true)]
theorem step10897 (p : Nat → Bool) (h : Constraints p) : clause p c10897 = true :=
  Snake9.LocalRup.prove_clause [c10894, c10886, c3697] c10897 (by decide) p (sat_cons (step10894 p h) (sat_cons (step10886 p h) (sat_cons (step3697 p h) (sat_nil p))))
def c10898 : List Lit := [(1788, true)]
theorem step10898 (p : Nat → Bool) (h : Constraints p) : clause p c10898 = true :=
  Snake9.LocalRup.prove_clause [c10895, c10897, c1551] c10898 (by decide) p (sat_cons (step10895 p h) (sat_cons (step10897 p h) (sat_cons (step1551 p h) (sat_nil p))))
def c10899 : List Lit := [(1829, true)]
theorem step10899 (p : Nat → Bool) (h : Constraints p) : clause p c10899 = true :=
  Snake9.LocalRup.prove_clause [c10896, c10898, c1635] c10899 (by decide) p (sat_cons (step10896 p h) (sat_cons (step10898 p h) (sat_cons (step1635 p h) (sat_nil p))))
def c10900 : List Lit := [(1790, false)]
theorem step10900 (p : Nat → Bool) (h : Constraints p) : clause p c10900 = true :=
  Snake9.LocalRup.prove_clause [c10896, c10881, c1649] c10900 (by decide) p (sat_cons (step10896 p h) (sat_cons (step10881 p h) (sat_cons (step1649 p h) (sat_nil p))))
def c10901 : List Lit := [(1760, false)]
theorem step10901 (p : Nat → Bool) (h : Constraints p) : clause p c10901 = true :=
  Snake9.LocalRup.prove_clause [c10899, c10877, c1696] c10901 (by decide) p (sat_cons (step10899 p h) (sat_cons (step10877 p h) (sat_cons (step1696 p h) (sat_nil p))))
def c10902 : List Lit := [(1777, false)]
theorem step10902 (p : Nat → Bool) (h : Constraints p) : clause p c10902 = true :=
  Snake9.LocalRup.prove_clause [c10900, c10895, c1561] c10902 (by decide) p (sat_cons (step10900 p h) (sat_cons (step10895 p h) (sat_cons (step1561 p h) (sat_nil p))))
def c10903 : List Lit := [(1744, false)]
theorem step10903 (p : Nat → Bool) (h : Constraints p) : clause p c10903 = true :=
  Snake9.LocalRup.prove_clause [c10901, c10607, c8026] c10903 (by decide) p (sat_cons (step10901 p h) (sat_cons (step10607 p h) (sat_cons (step8026 p h) (sat_nil p))))
end B112E050
