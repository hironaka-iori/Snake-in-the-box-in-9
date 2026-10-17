import B112E034Part0045
namespace B112E034
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c4723 : List Lit := [(1748, false), (1622, false), (1714, false), (1831, false)]
theorem step4723 (p : Nat → Bool) (h : Constraints p) : clause p c4723 = true :=
  Snake9.LocalRup.prove_clause [c4222, c2174, c1699, c2163, c1487, c1493, c1693, c1408, c2175, c4699, c2430] c4723 (by decide) p (sat_cons (step4222 p h) (sat_cons (step2174 p h) (sat_cons (step1699 p h) (sat_cons (step2163 p h) (sat_cons (step1487 p h) (sat_cons (step1493 p h) (sat_cons (step1693 p h) (sat_cons (step1408 p h) (sat_cons (step2175 p h) (sat_cons (step4699 p h) (sat_cons (step2430 p h) (sat_nil p))))))))))))
def c4724 : List Lit := [(122, true), (1813, true), (115, false), (1805, false), (117, true), (1748, true), (1789, true), (1821, true), (92, false), (86, false)]
theorem step4724 (p : Nat → Bool) (h : Constraints p) : clause p c4724 = true :=
  Snake9.LocalRup.prove_clause [c4701, c4702, c4722, c2241, c2074, c2401, c2075, c1762, c2869, c2235, c1577, c699, c1584, c1588, c1433, c1614, c1570, c4385, c754, c1417, c1884, c1439, c2767, c576, c445, c2475] c4724 (by decide) p (sat_cons (step4701 p h) (sat_cons (step4702 p h) (sat_cons (step4722 p h) (sat_cons (step2241 p h) (sat_cons (step2074 p h) (sat_cons (step2401 p h) (sat_cons (step2075 p h) (sat_cons (step1762 p h) (sat_cons (step2869 p h) (sat_cons (step2235 p h) (sat_cons (step1577 p h) (sat_cons (step699 p h) (sat_cons (step1584 p h) (sat_cons (step1588 p h) (sat_cons (step1433 p h) (sat_cons (step1614 p h) (sat_cons (step1570 p h) (sat_cons (step4385 p h) (sat_cons (step754 p h) (sat_cons (step1417 p h) (sat_cons (step1884 p h) (sat_cons (step1439 p h) (sat_cons (step2767 p h) (sat_cons (step576 p h) (sat_cons (step445 p h) (sat_cons (step2475 p h) (sat_nil p)))))))))))))))))))))))))))
def c4725 : List Lit := [(42, true), (1623, true), (37, true), (1604, false)]
theorem step4725 (p : Nat → Bool) (h : Constraints p) : clause p c4725 = true :=
  Snake9.LocalRup.prove_clause [c1205, c1199, c1226, c1215, c1208, c1210, c1214, c1230, c1200, c1194, c1195, c1846, c1847, c2000] c4725 (by decide) p (sat_cons (step1205 p h) (sat_cons (step1199 p h) (sat_cons (step1226 p h) (sat_cons (step1215 p h) (sat_cons (step1208 p h) (sat_cons (step1210 p h) (sat_cons (step1214 p h) (sat_cons (step1230 p h) (sat_cons (step1200 p h) (sat_cons (step1194 p h) (sat_cons (step1195 p h) (sat_cons (step1846 p h) (sat_cons (step1847 p h) (sat_cons (step2000 p h) (sat_nil p)))))))))))))))
def c4726 : List Lit := [(89, false), (112, false), (1789, true), (92, false), (86, false)]
theorem step4726 (p : Nat → Bool) (h : Constraints p) : clause p c4726 = true :=
  Snake9.LocalRup.prove_clause [c2869, c2767, c576, c445, c2475] c4726 (by decide) p (sat_cons (step2869 p h) (sat_cons (step2767 p h) (sat_cons (step576 p h) (sat_cons (step445 p h) (sat_cons (step2475 p h) (sat_nil p))))))
def c4727 : List Lit := [(1798, false), (115, false), (113, true), (117, true), (125, true), (1686, true), (1748, true), (37, true), (1604, false), (1789, true), (1821, true), (92, false), (86, false)]
theorem step4727 (p : Nat → Bool) (h : Constraints p) : clause p c4727 = true :=
  Snake9.LocalRup.prove_clause [c1572, c1574, c1554, c4701, c4702, c4722, c2241, c2074, c2075, c1762, c2869, c1564, c1609, c4724, c2340, c4725, c748, c1570, c1587, c1588, c1614, c1575, c1567, c1573, c1556, c699, c1433, c4726, c743, c1439, c1417, c1884] c4727 (by decide) p (sat_cons (step1572 p h) (sat_cons (step1574 p h) (sat_cons (step1554 p h) (sat_cons (step4701 p h) (sat_cons (step4702 p h) (sat_cons (step4722 p h) (sat_cons (step2241 p h) (sat_cons (step2074 p h) (sat_cons (step2075 p h) (sat_cons (step1762 p h) (sat_cons (step2869 p h) (sat_cons (step1564 p h) (sat_cons (step1609 p h) (sat_cons (step4724 p h) (sat_cons (step2340 p h) (sat_cons (step4725 p h) (sat_cons (step748 p h) (sat_cons (step1570 p h) (sat_cons (step1587 p h) (sat_cons (step1588 p h) (sat_cons (step1614 p h) (sat_cons (step1575 p h) (sat_cons (step1567 p h) (sat_cons (step1573 p h) (sat_cons (step1556 p h) (sat_cons (step699 p h) (sat_cons (step1433 p h) (sat_cons (step4726 p h) (sat_cons (step743 p h) (sat_cons (step1439 p h) (sat_cons (step1417 p h) (sat_cons (step1884 p h) (sat_nil p)))))))))))))))))))))))))))))))))
def c4728 : List Lit := [(117, false), (1623, true), (37, true), (1604, false), (112, false), (92, false)]
theorem step4728 (p : Nat → Bool) (h : Constraints p) : clause p c4728 = true :=
  Snake9.LocalRup.prove_clause [c1199, c1226, c4124, c656, c1207, c1216, c1217, c1230, c1209, c1200, c1194, c600, c159, c1989] c4728 (by decide) p (sat_cons (step1199 p h) (sat_cons (step1226 p h) (sat_cons (step4124 p h) (sat_cons (step656 p h) (sat_cons (step1207 p h) (sat_cons (step1216 p h) (sat_cons (step1217 p h) (sat_cons (step1230 p h) (sat_cons (step1209 p h) (sat_cons (step1200 p h) (sat_cons (step1194 p h) (sat_cons (step600 p h) (sat_cons (step159 p h) (sat_cons (step1989 p h) (sat_nil p)))))))))))))))
def c4729 : List Lit := [(1617, false), (51, false), (1686, true), (1623, true), (1604, false), (1632, false), (92, false)]
theorem step4729 (p : Nat → Bool) (h : Constraints p) : clause p c4729 = true :=
  Snake9.LocalRup.prove_clause [c1831, c1818, c1825, c2195, c1337, c1949, c2268, c1199, c1226, c2153, c1225, c1230, c1305, c1306, c1200, c1344, c1280, c1195, c1182, c1176, c3994, c1826, c4110, c4048, c1100, c4712, c1971, c1815, c11] c4729 (by decide) p (sat_cons (step1831 p h) (sat_cons (step1818 p h) (sat_cons (step1825 p h) (sat_cons (step2195 p h) (sat_cons (step1337 p h) (sat_cons (step1949 p h) (sat_cons (step2268 p h) (sat_cons (step1199 p h) (sat_cons (step1226 p h) (sat_cons (step2153 p h) (sat_cons (step1225 p h) (sat_cons (step1230 p h) (sat_cons (step1305 p h) (sat_cons (step1306 p h) (sat_cons (step1200 p h) (sat_cons (step1344 p h) (sat_cons (step1280 p h) (sat_cons (step1195 p h) (sat_cons (step1182 p h) (sat_cons (step1176 p h) (sat_cons (step3994 p h) (sat_cons (step1826 p h) (sat_cons (step4110 p h) (sat_cons (step4048 p h) (sat_cons (step1100 p h) (sat_cons (step4712 p h) (sat_cons (step1971 p h) (sat_cons (step1815 p h) (sat_cons (step11 p h) (sat_nil p))))))))))))))))))))))))))))))
def c4730 : List Lit := [(70, false), (74, false), (1644, true)]
theorem step4730 (p : Nat → Bool) (h : Constraints p) : clause p c4730 = true :=
  Snake9.LocalRup.prove_clause [c3699, c3994, c329] c4730 (by decide) p (sat_cons (step3699 p h) (sat_cons (step3994 p h) (sat_cons (step329 p h) (sat_nil p))))
def c4731 : List Lit := [(51, false), (1686, true), (1714, true), (1623, true), (37, true), (1604, false), (1632, false), (92, false)]
theorem step4731 (p : Nat → Bool) (h : Constraints p) : clause p c4731 = true :=
  Snake9.LocalRup.prove_clause [c2153, c2335, c1298, c1351, c1392, c1831, c2195, c1818, c1337, c1825, c1177, c4729, c1216, c4108, c1207, c651, c4292, c1389, c1390, c4721, c1394, c1306, c1386, c1280, c4730] c4731 (by decide) p (sat_cons (step2153 p h) (sat_cons (step2335 p h) (sat_cons (step1298 p h) (sat_cons (step1351 p h) (sat_cons (step1392 p h) (sat_cons (step1831 p h) (sat_cons (step2195 p h) (sat_cons (step1818 p h) (sat_cons (step1337 p h) (sat_cons (step1825 p h) (sat_cons (step1177 p h) (sat_cons (step4729 p h) (sat_cons (step1216 p h) (sat_cons (step4108 p h) (sat_cons (step1207 p h) (sat_cons (step651 p h) (sat_cons (step4292 p h) (sat_cons (step1389 p h) (sat_cons (step1390 p h) (sat_cons (step4721 p h) (sat_cons (step1394 p h) (sat_cons (step1306 p h) (sat_cons (step1386 p h) (sat_cons (step1280 p h) (sat_cons (step4730 p h) (sat_nil p))))))))))))))))))))))))))
def c4732 : List Lit := [(1760, true), (89, false), (1737, false), (1803, true), (1711, false), (92, false), (74, false), (1644, true)]
theorem step4732 (p : Nat → Bool) (h : Constraints p) : clause p c4732 = true :=
  Snake9.LocalRup.prove_clause [c2206, c1569, c1568, c4699, c4730, c1386, c1394, c1408, c3994, c1857, c4677, c236, c2391, c1371, c1497, c1492, c1413, c1409, c1849, c2438, c1381, c1397, c211, c400, c405, c1417, c1418, c1387, c2017, c756, c2302, c333, c2047, c2049, c1423, c2048, c2019, c1459, c1445, c1431, c369, c1374, c1376, c1383, c276, c1373, c2025, c312, c2104, c776, c778, c2058] c4732 (by decide) p (sat_cons (step2206 p h) (sat_cons (step1569 p h) (sat_cons (step1568 p h) (sat_cons (step4699 p h) (sat_cons (step4730 p h) (sat_cons (step1386 p h) (sat_cons (step1394 p h) (sat_cons (step1408 p h) (sat_cons (step3994 p h) (sat_cons (step1857 p h) (sat_cons (step4677 p h) (sat_cons (step236 p h) (sat_cons (step2391 p h) (sat_cons (step1371 p h) (sat_cons (step1497 p h) (sat_cons (step1492 p h) (sat_cons (step1413 p h) (sat_cons (step1409 p h) (sat_cons (step1849 p h) (sat_cons (step2438 p h) (sat_cons (step1381 p h) (sat_cons (step1397 p h) (sat_cons (step211 p h) (sat_cons (step400 p h) (sat_cons (step405 p h) (sat_cons (step1417 p h) (sat_cons (step1418 p h) (sat_cons (step1387 p h) (sat_cons (step2017 p h) (sat_cons (step756 p h) (sat_cons (step2302 p h) (sat_cons (step333 p h) (sat_cons (step2047 p h) (sat_cons (step2049 p h) (sat_cons (step1423 p h) (sat_cons (step2048 p h) (sat_cons (step2019 p h) (sat_cons (step1459 p h) (sat_cons (step1445 p h) (sat_cons (step1431 p h) (sat_cons (step369 p h) (sat_cons (step1374 p h) (sat_cons (step1376 p h) (sat_cons (step1383 p h) (sat_cons (step276 p h) (sat_cons (step1373 p h) (sat_cons (step2025 p h) (sat_cons (step312 p h) (sat_cons (step2104 p h) (sat_cons (step776 p h) (sat_cons (step778 p h) (sat_cons (step2058 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))
def c4733 : List Lit := [(123, false), (80, false), (88, true), (87, true), (89, false), (120, false)]
theorem step4733 (p : Nat → Bool) (h : Constraints p) : clause p c4733 = true :=
  Snake9.LocalRup.prove_clause [c776, c778, c2058] c4733 (by decide) p (sat_cons (step776 p h) (sat_cons (step778 p h) (sat_cons (step2058 p h) (sat_nil p))))
def c4734 : List Lit := [(1621, true), (119, true), (1803, true)]
theorem step4734 (p : Nat → Bool) (h : Constraints p) : clause p c4734 = true :=
  Snake9.LocalRup.prove_clause [c1569, c1228, c4426, c1198, c1194, c1196, c1197, c4255, c1224, c1208, c1211] c4734 (by decide) p (sat_cons (step1569 p h) (sat_cons (step1228 p h) (sat_cons (step4426 p h) (sat_cons (step1198 p h) (sat_cons (step1194 p h) (sat_cons (step1196 p h) (sat_cons (step1197 p h) (sat_cons (step4255 p h) (sat_cons (step1224 p h) (sat_cons (step1208 p h) (sat_cons (step1211 p h) (sat_nil p))))))))))))
def c4735 : List Lit := [(1802, false), (1819, true), (1832, true), (1604, true), (115, false), (107, true), (86, false), (1803, true)]
theorem step4735 (p : Nat → Bool) (h : Constraints p) : clause p c4735 = true :=
  Snake9.LocalRup.prove_clause [c1611, c1612, c1645, c1579, c4276, c1574] c4735 (by decide) p (sat_cons (step1611 p h) (sat_cons (step1612 p h) (sat_cons (step1645 p h) (sat_cons (step1579 p h) (sat_cons (step4276 p h) (sat_cons (step1574 p h) (sat_nil p)))))))
def c4736 : List Lit := [(119, true), (1622, true), (1604, false), (1803, true)]
theorem step4736 (p : Nat → Bool) (h : Constraints p) : clause p c4736 = true :=
  Snake9.LocalRup.prove_clause [c1569, c4275, c4428] c4736 (by decide) p (sat_cons (step1569 p h) (sat_cons (step4275 p h) (sat_cons (step4428 p h) (sat_nil p))))
def c4737 : List Lit := [(1622, true), (1604, false), (1803, true)]
theorem step4737 (p : Nat → Bool) (h : Constraints p) : clause p c4737 = true :=
  Snake9.LocalRup.prove_clause [c1199, c1569, c1568, c1225, c4736, c750, c1208, c2278, c1211, c3012, c1229, c1194, c1200] c4737 (by decide) p (sat_cons (step1199 p h) (sat_cons (step1569 p h) (sat_cons (step1568 p h) (sat_cons (step1225 p h) (sat_cons (step4736 p h) (sat_cons (step750 p h) (sat_cons (step1208 p h) (sat_cons (step2278 p h) (sat_cons (step1211 p h) (sat_cons (step3012 p h) (sat_cons (step1229 p h) (sat_cons (step1194 p h) (sat_cons (step1200 p h) (sat_nil p))))))))))))))
def c4738 : List Lit := [(1623, false), (1805, false), (1800, false), (1790, false), (1760, false)]
theorem step4738 (p : Nat → Bool) (h : Constraints p) : clause p c4738 = true :=
  Snake9.LocalRup.prove_clause [c4181, c1636, c1692, c2176, c2260, c2340, c2175, c1577, c1693, c1580, c1637, c1601] c4738 (by decide) p (sat_cons (step4181 p h) (sat_cons (step1636 p h) (sat_cons (step1692 p h) (sat_cons (step2176 p h) (sat_cons (step2260 p h) (sat_cons (step2340 p h) (sat_cons (step2175 p h) (sat_cons (step1577 p h) (sat_cons (step1693 p h) (sat_cons (step1580 p h) (sat_cons (step1637 p h) (sat_cons (step1601 p h) (sat_nil p)))))))))))))
def c4739 : List Lit := [(1622, true), (1617, false), (115, true), (119, true), (1803, true)]
theorem step4739 (p : Nat → Bool) (h : Constraints p) : clause p c4739 = true :=
  Snake9.LocalRup.prove_clause [c1569, c4530, c4609] c4739 (by decide) p (sat_cons (step1569 p h) (sat_cons (step4530 p h) (sat_cons (step4609 p h) (sat_nil p))))
def c4740 : List Lit := [(1685, true), (122, false), (1661, false), (1622, false)]
theorem step4740 (p : Nat → Bool) (h : Constraints p) : clause p c4740 = true :=
  Snake9.LocalRup.prove_clause [c2425, c1336, c1306, c2195, c2154, c2324] c4740 (by decide) p (sat_cons (step2425 p h) (sat_cons (step1336 p h) (sat_cons (step1306 p h) (sat_cons (step2195 p h) (sat_cons (step2154 p h) (sat_cons (step2324 p h) (sat_nil p)))))))
def c4741 : List Lit := [(1604, false), (42, true), (1623, true), (115, true)]
theorem step4741 (p : Nat → Bool) (h : Constraints p) : clause p c4741 = true :=
  Snake9.LocalRup.prove_clause [c1877, c1230, c4725, c1200, c2355, c1195] c4741 (by decide) p (sat_cons (step1877 p h) (sat_cons (step1230 p h) (sat_cons (step4725 p h) (sat_cons (step1200 p h) (sat_cons (step2355 p h) (sat_cons (step1195 p h) (sat_nil p)))))))
def c4742 : List Lit := [(1712, false), (1737, false), (1760, true), (1706, false), (1803, true)]
theorem step4742 (p : Nat → Bool) (h : Constraints p) : clause p c4742 = true :=
  Snake9.LocalRup.prove_clause [c2206, c1497, c1409, c1392, c1395, c1408, c1386, c1492, c2762, c2438, c1417] c4742 (by decide) p (sat_cons (step2206 p h) (sat_cons (step1497 p h) (sat_cons (step1409 p h) (sat_cons (step1392 p h) (sat_cons (step1395 p h) (sat_cons (step1408 p h) (sat_cons (step1386 p h) (sat_cons (step1492 p h) (sat_cons (step2762 p h) (sat_cons (step2438 p h) (sat_cons (step1417 p h) (sat_nil p))))))))))))
def c4743 : List Lit := [(1725, true), (73, false), (1710, true), (58, false), (1803, true)]
theorem step4743 (p : Nat → Bool) (h : Constraints p) : clause p c4743 = true :=
  Snake9.LocalRup.prove_clause [c1417, c1418, c2762, c332, c1387, c2041, c339] c4743 (by decide) p (sat_cons (step1417 p h) (sat_cons (step1418 p h) (sat_cons (step2762 p h) (sat_cons (step332 p h) (sat_cons (step1387 p h) (sat_cons (step2041 p h) (sat_cons (step339 p h) (sat_nil p))))))))
def c4744 : List Lit := [(1737, false), (1760, true), (1712, true), (73, false), (1725, false), (1644, true), (74, true), (1803, true)]
theorem step4744 (p : Nat → Bool) (h : Constraints p) : clause p c4744 = true :=
  Snake9.LocalRup.prove_clause [c1388, c1391, c4699, c1407, c1487, c3994, c1883, c2438, c1492, c1408, c1394, c4683, c1385, c1386, c2041, c2762, c339, c1419] c4744 (by decide) p (sat_cons (step1388 p h) (sat_cons (step1391 p h) (sat_cons (step4699 p h) (sat_cons (step1407 p h) (sat_cons (step1487 p h) (sat_cons (step3994 p h) (sat_cons (step1883 p h) (sat_cons (step2438 p h) (sat_cons (step1492 p h) (sat_cons (step1408 p h) (sat_cons (step1394 p h) (sat_cons (step4683 p h) (sat_cons (step1385 p h) (sat_cons (step1386 p h) (sat_cons (step2041 p h) (sat_cons (step2762 p h) (sat_cons (step339 p h) (sat_cons (step1419 p h) (sat_nil p)))))))))))))))))))
def c4745 : List Lit := [(70, false), (86, false), (1726, true), (1855, true), (1737, true), (73, false), (1746, false), (1644, true), (1711, false), (1803, true)]
theorem step4745 (p : Nat → Bool) (h : Constraints p) : clause p c4745 = true :=
  Snake9.LocalRup.prove_clause [c1857, c3994, c4677, c236, c1438, c1436, c1433, c409, c211, c2015, c3533, c2068, c1759, c1434, c4699, c2762, c328, c294, c1419, c2041, c2040, c2448, c2905, c339, c663, c661, c1385, c1573, c1394, c2224, c1408, c1638, c1491, c1685] c4745 (by decide) p (sat_cons (step1857 p h) (sat_cons (step3994 p h) (sat_cons (step4677 p h) (sat_cons (step236 p h) (sat_cons (step1438 p h) (sat_cons (step1436 p h) (sat_cons (step1433 p h) (sat_cons (step409 p h) (sat_cons (step211 p h) (sat_cons (step2015 p h) (sat_cons (step3533 p h) (sat_cons (step2068 p h) (sat_cons (step1759 p h) (sat_cons (step1434 p h) (sat_cons (step4699 p h) (sat_cons (step2762 p h) (sat_cons (step328 p h) (sat_cons (step294 p h) (sat_cons (step1419 p h) (sat_cons (step2041 p h) (sat_cons (step2040 p h) (sat_cons (step2448 p h) (sat_cons (step2905 p h) (sat_cons (step339 p h) (sat_cons (step663 p h) (sat_cons (step661 p h) (sat_cons (step1385 p h) (sat_cons (step1573 p h) (sat_cons (step1394 p h) (sat_cons (step2224 p h) (sat_cons (step1408 p h) (sat_cons (step1638 p h) (sat_cons (step1491 p h) (sat_cons (step1685 p h) (sat_nil p)))))))))))))))))))))))))))))))))))
def c4746 : List Lit := [(1685, true), (1661, false), (1612, false), (35, true), (119, true), (120, false)]
theorem step4746 (p : Nat → Bool) (h : Constraints p) : clause p c4746 = true :=
  Snake9.LocalRup.prove_clause [c2260, c1336, c4519, c4462] c4746 (by decide) p (sat_cons (step2260 p h) (sat_cons (step1336 p h) (sat_cons (step4519 p h) (sat_cons (step4462 p h) (sat_nil p)))))
def c4747 : List Lit := [(1806, false), (1796, false), (113, true), (1809, true), (1820, true), (92, false), (1832, true), (109, true), (117, true), (119, true), (1803, true)]
theorem step4747 (p : Nat → Bool) (h : Constraints p) : clause p c4747 = true :=
  Snake9.LocalRup.prove_clause [c3157, c1575, c2224, c1578, c1580, c1638, c2958, c1613, c2197, c1567, c1523, c4666] c4747 (by decide) p (sat_cons (step3157 p h) (sat_cons (step1575 p h) (sat_cons (step2224 p h) (sat_cons (step1578 p h) (sat_cons (step1580 p h) (sat_cons (step1638 p h) (sat_cons (step2958 p h) (sat_cons (step1613 p h) (sat_cons (step2197 p h) (sat_cons (step1567 p h) (sat_cons (step1523 p h) (sat_cons (step4666 p h) (sat_nil p)))))))))))))
def c4748 : List Lit := [(107, false), (125, false), (1796, false), (113, true), (1805, false), (1820, true), (1789, false), (115, false), (93, false), (1759, false), (117, true), (35, true), (36, true), (119, true), (1803, true)]
theorem step4748 (p : Nat → Bool) (h : Constraints p) : clause p c4748 = true :=
  Snake9.LocalRup.prove_clause [c1569, c677, c698, c1207, c1559, c4689, c4137, c1567, c1631, c1613, c1684, c4641, c2176, c2340] c4748 (by decide) p (sat_cons (step1569 p h) (sat_cons (step677 p h) (sat_cons (step698 p h) (sat_cons (step1207 p h) (sat_cons (step1559 p h) (sat_cons (step4689 p h) (sat_cons (step4137 p h) (sat_cons (step1567 p h) (sat_cons (step1631 p h) (sat_cons (step1613 p h) (sat_cons (step1684 p h) (sat_cons (step4641 p h) (sat_cons (step2176 p h) (sat_cons (step2340 p h) (sat_nil p)))))))))))))))
def c4749 : List Lit := [(113, true), (126, true), (115, false), (92, false), (93, false), (1832, true), (1759, false), (109, true), (112, true), (117, true), (35, true), (36, true), (119, true), (1803, true)]
theorem step4749 (p : Nat → Bool) (h : Constraints p) : clause p c4749 = true :=
  Snake9.LocalRup.prove_clause [c2820, c1571, c1574, c1579, c1606, c3157, c1521, c4055, c1632, c1608, c1581, c1569, c1556, c4747, c1573, c4748, c1523, c2197, c1638, c1637, c1612, c1607, c1684, c1567, c4641, c2176, c1559, c2340, c679, c4137, c1207] c4749 (by decide) p (sat_cons (step2820 p h) (sat_cons (step1571 p h) (sat_cons (step1574 p h) (sat_cons (step1579 p h) (sat_cons (step1606 p h) (sat_cons (step3157 p h) (sat_cons (step1521 p h) (sat_cons (step4055 p h) (sat_cons (step1632 p h) (sat_cons (step1608 p h) (sat_cons (step1581 p h) (sat_cons (step1569 p h) (sat_cons (step1556 p h) (sat_cons (step4747 p h) (sat_cons (step1573 p h) (sat_cons (step4748 p h) (sat_cons (step1523 p h) (sat_cons (step2197 p h) (sat_cons (step1638 p h) (sat_cons (step1637 p h) (sat_cons (step1612 p h) (sat_cons (step1607 p h) (sat_cons (step1684 p h) (sat_cons (step1567 p h) (sat_cons (step4641 p h) (sat_cons (step2176 p h) (sat_cons (step1559 p h) (sat_cons (step2340 p h) (sat_cons (step679 p h) (sat_cons (step4137 p h) (sat_cons (step1207 p h) (sat_nil p))))))))))))))))))))))))))))))))
def c4750 : List Lit := [(58, false), (69, false), (75, false), (88, false), (74, false), (1737, false), (1760, true), (93, false), (107, true), (70, true), (1727, false)]
theorem step4750 (p : Nat → Bool) (h : Constraints p) : clause p c4750 = true :=
  Snake9.LocalRup.prove_clause [c1386, c331, c333, c1389, c1418, c1394, c1426, c2438, c2163, c1487, c1492, c1465, c2185, c1408, c1445, c406, c1431, c300, c2053, c992, c4098, c993, c371, c994, c1012, c1007, c1016, c2131, c1017, c1025] c4750 (by decide) p (sat_cons (step1386 p h) (sat_cons (step331 p h) (sat_cons (step333 p h) (sat_cons (step1389 p h) (sat_cons (step1418 p h) (sat_cons (step1394 p h) (sat_cons (step1426 p h) (sat_cons (step2438 p h) (sat_cons (step2163 p h) (sat_cons (step1487 p h) (sat_cons (step1492 p h) (sat_cons (step1465 p h) (sat_cons (step2185 p h) (sat_cons (step1408 p h) (sat_cons (step1445 p h) (sat_cons (step406 p h) (sat_cons (step1431 p h) (sat_cons (step300 p h) (sat_cons (step2053 p h) (sat_cons (step992 p h) (sat_cons (step4098 p h) (sat_cons (step993 p h) (sat_cons (step371 p h) (sat_cons (step994 p h) (sat_cons (step1012 p h) (sat_cons (step1007 p h) (sat_cons (step1016 p h) (sat_cons (step2131 p h) (sat_cons (step1017 p h) (sat_cons (step1025 p h) (sat_nil p)))))))))))))))))))))))))))))))
def c4751 : List Lit := [(85, false), (77, true), (213, true), (1706, true)]
theorem step4751 (p : Nat → Bool) (h : Constraints p) : clause p c4751 = true :=
  Snake9.LocalRup.prove_clause [c4098, c371] c4751 (by decide) p (sat_cons (step4098 p h) (sat_cons (step371 p h) (sat_nil p)))
def c4752 : List Lit := [(100, false), (102, true), (86, false)]
theorem step4752 (p : Nat → Bool) (h : Constraints p) : clause p c4752 = true :=
  Snake9.LocalRup.prove_clause [c2080, c2081, c1751] c4752 (by decide) p (sat_cons (step2080 p h) (sat_cons (step2081 p h) (sat_cons (step1751 p h) (sat_nil p))))
def c4753 : List Lit := [(1831, false), (1584, false), (1713, false), (1758, false), (1747, false), (1854, true), (1621, false), (122, false)]
theorem step4753 (p : Nat → Bool) (h : Constraints p) : clause p c4753 = true :=
  Snake9.LocalRup.prove_clause [c1676, c1684, c2177, c1486, c2902, c1407, c4699] c4753 (by decide) p (sat_cons (step1676 p h) (sat_cons (step1684 p h) (sat_cons (step2177 p h) (sat_cons (step1486 p h) (sat_cons (step2902 p h) (sat_cons (step1407 p h) (sat_cons (step4699 p h) (sat_nil p))))))))
def c4754 : List Lit := [(1779, true), (93, false), (126, false)]
theorem step4754 (p : Nat → Bool) (h : Constraints p) : clause p c4754 = true :=
  Snake9.LocalRup.prove_clause [c1518, c3535, c505] c4754 (by decide) p (sat_cons (step1518 p h) (sat_cons (step3535 p h) (sat_cons (step505 p h) (sat_nil p))))
def c4755 : List Lit := [(1748, true), (97, false), (119, true), (120, false), (1725, false), (1735, false)]
theorem step4755 (p : Nat → Bool) (h : Constraints p) : clause p c4755 = true :=
  Snake9.LocalRup.prove_clause [c1436, c1884, c2185, c1439, c401, c489, c2073] c4755 (by decide) p (sat_cons (step1436 p h) (sat_cons (step1884 p h) (sat_cons (step2185 p h) (sat_cons (step1439 p h) (sat_cons (step401 p h) (sat_cons (step489 p h) (sat_cons (step2073 p h) (sat_nil p))))))))
def c4756 : List Lit := [(89, false), (86, false), (97, false), (119, true), (120, false)]
theorem step4756 (p : Nat → Bool) (h : Constraints p) : clause p c4756 = true :=
  Snake9.LocalRup.prove_clause [c401, c489, c2073] c4756 (by decide) p (sat_cons (step401 p h) (sat_cons (step489 p h) (sat_cons (step2073 p h) (sat_nil p))))
def c4757 : List Lit := [(117, true), (1795, false), (122, true), (1818, true), (1803, true)]
theorem step4757 (p : Nat → Bool) (h : Constraints p) : clause p c4757 = true :=
  Snake9.LocalRup.prove_clause [c1558, c4641, c1601, c1563] c4757 (by decide) p (sat_cons (step1558 p h) (sat_cons (step4641 p h) (sat_cons (step1601 p h) (sat_cons (step1563 p h) (sat_nil p)))))
def c4758 : List Lit := [(1714, true), (72, true), (117, false)]
theorem step4758 (p : Nat → Bool) (h : Constraints p) : clause p c4758 = true :=
  Snake9.LocalRup.prove_clause [c1385, c1396, c1394, c1387, c1388, c1389, c334, c2448] c4758 (by decide) p (sat_cons (step1385 p h) (sat_cons (step1396 p h) (sat_cons (step1394 p h) (sat_cons (step1387 p h) (sat_cons (step1388 p h) (sat_cons (step1389 p h) (sat_cons (step334 p h) (sat_cons (step2448 p h) (sat_nil p)))))))))
def c4759 : List Lit := [(39, false), (73, false), (110, false), (117, false)]
theorem step4759 (p : Nat → Bool) (h : Constraints p) : clause p c4759 = true :=
  Snake9.LocalRup.prove_clause [c719, c723, c2039] c4759 (by decide) p (sat_cons (step719 p h) (sat_cons (step723 p h) (sat_cons (step2039 p h) (sat_nil p))))
def c4760 : List Lit := [(1800, true), (74, false), (116, true), (112, true)]
theorem step4760 (p : Nat → Bool) (h : Constraints p) : clause p c4760 = true :=
  Snake9.LocalRup.prove_clause [c1555, c1565, c1563, c1556, c1557, c694, c2098] c4760 (by decide) p (sat_cons (step1555 p h) (sat_cons (step1565 p h) (sat_cons (step1563 p h) (sat_cons (step1556 p h) (sat_cons (step1557 p h) (sat_cons (step694 p h) (sat_cons (step2098 p h) (sat_nil p))))))))
def c4761 : List Lit := [(1800, true), (1806, true), (80, false), (120, false), (119, true), (121, false), (117, false)]
theorem step4761 (p : Nat → Bool) (h : Constraints p) : clause p c4761 = true :=
  Snake9.LocalRup.prove_clause [c2187, c800, c1555, c1565, c1563, c1556, c1557, c4127, c1573, c4096, c670] c4761 (by decide) p (sat_cons (step2187 p h) (sat_cons (step800 p h) (sat_cons (step1555 p h) (sat_cons (step1565 p h) (sat_cons (step1563 p h) (sat_cons (step1556 p h) (sat_cons (step1557 p h) (sat_cons (step4127 p h) (sat_cons (step1573 p h) (sat_cons (step4096 p h) (sat_cons (step670 p h) (sat_nil p))))))))))))
def c4762 : List Lit := [(1644, true), (74, false), (1721, true), (1711, false), (72, true)]
theorem step4762 (p : Nat → Bool) (h : Constraints p) : clause p c4762 = true :=
  Snake9.LocalRup.prove_clause [c4699, c4730, c1409, c1387, c1397] c4762 (by decide) p (sat_cons (step4699 p h) (sat_cons (step4730 p h) (sat_cons (step1409 p h) (sat_cons (step1387 p h) (sat_cons (step1397 p h) (sat_nil p))))))
def c4763 : List Lit := [(1725, false), (1747, true), (80, false), (120, false), (123, false)]
theorem step4763 (p : Nat → Bool) (h : Constraints p) : clause p c4763 = true :=
  Snake9.LocalRup.prove_clause [c2438, c2439, c1436, c1438, c1433, c1434, c415, c400, c4733] c4763 (by decide) p (sat_cons (step2438 p h) (sat_cons (step2439 p h) (sat_cons (step1436 p h) (sat_cons (step1438 p h) (sat_cons (step1433 p h) (sat_cons (step1434 p h) (sat_cons (step415 p h) (sat_cons (step400 p h) (sat_cons (step4733 p h) (sat_nil p))))))))))
def c4764 : List Lit := [(1760, true), (1712, false), (72, true), (80, false), (120, false), (123, false)]
theorem step4764 (p : Nat → Bool) (h : Constraints p) : clause p c4764 = true :=
  Snake9.LocalRup.prove_clause [c1385, c1395, c2164, c778, c776, c2296, c1492, c4763, c1417, c2302, c355, c1423, c1387, c1458, c1398, c1497, c2165] c4764 (by decide) p (sat_cons (step1385 p h) (sat_cons (step1395 p h) (sat_cons (step2164 p h) (sat_cons (step778 p h) (sat_cons (step776 p h) (sat_cons (step2296 p h) (sat_cons (step1492 p h) (sat_cons (step4763 p h) (sat_cons (step1417 p h) (sat_cons (step2302 p h) (sat_cons (step355 p h) (sat_cons (step1423 p h) (sat_cons (step1387 p h) (sat_cons (step1458 p h) (sat_cons (step1398 p h) (sat_cons (step1497 p h) (sat_cons (step2165 p h) (sat_nil p))))))))))))))))))
def c4765 : List Lit := [(1830, false), (1716, false), (1746, false), (1760, false), (1623, false)]
theorem step4765 (p : Nat → Bool) (h : Constraints p) : clause p c4765 = true :=
  Snake9.LocalRup.prove_clause [c2260, c2175, c1692, c1698, c2176, c1502, c2449, c1410, c4699] c4765 (by decide) p (sat_cons (step2260 p h) (sat_cons (step2175 p h) (sat_cons (step1692 p h) (sat_cons (step1698 p h) (sat_cons (step2176 p h) (sat_cons (step1502 p h) (sat_cons (step2449 p h) (sat_cons (step1410 p h) (sat_cons (step4699 p h) (sat_nil p))))))))))
def c4766 : List Lit := [(1830, true), (1808, false), (1818, false), (1781, false), (1800, false), (117, false)]
theorem step4766 (p : Nat → Bool) (h : Constraints p) : clause p c4766 = true :=
  Snake9.LocalRup.prove_clause [c1904, c1524, c1625, c1630, c1602, c1542, c1584, c3157, c1538, c2435, c1527] c4766 (by decide) p (sat_cons (step1904 p h) (sat_cons (step1524 p h) (sat_cons (step1625 p h) (sat_cons (step1630 p h) (sat_cons (step1602 p h) (sat_cons (step1542 p h) (sat_cons (step1584 p h) (sat_cons (step3157 p h) (sat_cons (step1538 p h) (sat_cons (step2435 p h) (sat_cons (step1527 p h) (sat_nil p))))))))))))
def c4767 : List Lit := [(1712, false), (1830, false), (1623, false), (72, true), (80, false), (120, false), (123, false)]
theorem step4767 (p : Nat → Bool) (h : Constraints p) : clause p c4767 = true :=
  Snake9.LocalRup.prove_clause [c2260, c2175, c1698, c1385, c778, c776, c2296, c1395, c4764, c1692, c2176, c2449, c4699, c1409, c1498, c4763, c1417, c2302, c355, c1423, c1387, c1458, c1398, c4765] c4767 (by decide) p (sat_cons (step2260 p h) (sat_cons (step2175 p h) (sat_cons (step1698 p h) (sat_cons (step1385 p h) (sat_cons (step778 p h) (sat_cons (step776 p h) (sat_cons (step2296 p h) (sat_cons (step1395 p h) (sat_cons (step4764 p h) (sat_cons (step1692 p h) (sat_cons (step2176 p h) (sat_cons (step2449 p h) (sat_cons (step4699 p h) (sat_cons (step1409 p h) (sat_cons (step1498 p h) (sat_cons (step4763 p h) (sat_cons (step1417 p h) (sat_cons (step2302 p h) (sat_cons (step355 p h) (sat_cons (step1423 p h) (sat_cons (step1387 p h) (sat_cons (step1458 p h) (sat_cons (step1398 p h) (sat_cons (step4765 p h) (sat_nil p)))))))))))))))))))))))))
def c4768 : List Lit := [(1644, true), (1737, false), (75, false), (73, false), (1711, false), (1761, true), (72, true)]
theorem step4768 (p : Nat → Bool) (h : Constraints p) : clause p c4768 = true :=
  Snake9.LocalRup.prove_clause [c3994, c4699, c332, c328, c1418, c1387, c2438, c1397, c1498, c1409] c4768 (by decide) p (sat_cons (step3994 p h) (sat_cons (step4699 p h) (sat_cons (step332 p h) (sat_cons (step328 p h) (sat_cons (step1418 p h) (sat_cons (step1387 p h) (sat_cons (step2438 p h) (sat_cons (step1397 p h) (sat_cons (step1498 p h) (sat_cons (step1409 p h) (sat_nil p)))))))))))
def c4769 : List Lit := [(86, false), (89, false), (1735, true), (80, false), (120, false), (123, false)]
theorem step4769 (p : Nat → Bool) (h : Constraints p) : clause p c4769 = true :=
  Snake9.LocalRup.prove_clause [c1434, c1433, c415, c400, c4733] c4769 (by decide) p (sat_cons (step1434 p h) (sat_cons (step1433 p h) (sat_cons (step415 p h) (sat_cons (step400 p h) (sat_cons (step4733 p h) (sat_nil p))))))
def c4770 : List Lit := [(77, false), (58, false), (74, false), (76, true)]
theorem step4770 (p : Nat → Bool) (h : Constraints p) : clause p c4770 = true :=
  Snake9.LocalRup.prove_clause [c2048, c333] c4770 (by decide) p (sat_cons (step2048 p h) (sat_cons (step333 p h) (sat_nil p)))
def c4771 : List Lit := [(1735, false), (1776, true), (1790, true), (1748, true), (1738, true), (1725, false), (1779, false), (99, true), (120, false), (119, true)]
theorem step4771 (p : Nat → Bool) (h : Constraints p) : clause p c4771 = true :=
  Snake9.LocalRup.prove_clause [c1436, c4755, c1439, c2185, c1504, c2608, c1513, c1539, c1507, c1508, c4294, c473, c420, c2079] c4771 (by decide) p (sat_cons (step1436 p h) (sat_cons (step4755 p h) (sat_cons (step1439 p h) (sat_cons (step2185 p h) (sat_cons (step1504 p h) (sat_cons (step2608 p h) (sat_cons (step1513 p h) (sat_cons (step1539 p h) (sat_cons (step1507 p h) (sat_cons (step1508 p h) (sat_cons (step4294 p h) (sat_cons (step473 p h) (sat_cons (step420 p h) (sat_cons (step2079 p h) (sat_nil p)))))))))))))))
def c4772 : List Lit := [(1790, true), (1748, true), (1735, false), (1725, false), (1784, false), (1779, false), (99, true), (120, false), (119, true)]
theorem step4772 (p : Nat → Bool) (h : Constraints p) : clause p c4772 = true :=
  Snake9.LocalRup.prove_clause [c1884, c1543, c4771] c4772 (by decide) p (sat_cons (step1884 p h) (sat_cons (step1543 p h) (sat_cons (step4771 p h) (sat_nil p))))
def c4773 : List Lit := [(126, false), (113, false), (46, false), (74, false), (127, true)]
theorem step4773 (p : Nat → Bool) (h : Constraints p) : clause p c4773 = true :=
  Snake9.LocalRup.prove_clause [c695, c2113, c807] c4773 (by decide) p (sat_cons (step695 p h) (sat_cons (step2113 p h) (sat_cons (step807 p h) (sat_nil p))))
def c4774 : List Lit := [(1831, true), (1809, false), (1819, false), (1784, false), (1788, false), (1800, false)]
theorem step4774 (p : Nat → Bool) (h : Constraints p) : clause p c4774 = true :=
  Snake9.LocalRup.prove_clause [c1626, c1631, c1603, c1538, c1585, c3157] c4774 (by decide) p (sat_cons (step1626 p h) (sat_cons (step1631 p h) (sat_cons (step1603 p h) (sat_cons (step1538 p h) (sat_cons (step1585 p h) (sat_cons (step3157 p h) (sat_nil p)))))))
def c4775 : List Lit := [(93, false), (1747, true), (1646, true), (115, true), (107, false), (74, false)]
theorem step4775 (p : Nat → Bool) (h : Constraints p) : clause p c4775 = true :=
  Snake9.LocalRup.prove_clause [c3748, c2067, c422, c419, c1438, c1849] c4775 (by decide) p (sat_cons (step3748 p h) (sat_cons (step2067 p h) (sat_cons (step422 p h) (sat_cons (step419 p h) (sat_cons (step1438 p h) (sat_cons (step1849 p h) (sat_nil p)))))))
def c4776 : List Lit := [(117, false), (21, false), (1583, true), (95, false), (87, true), (92, false), (86, false)]
theorem step4776 (p : Nat → Bool) (h : Constraints p) : clause p c4776 = true :=
  Snake9.LocalRup.prove_clause [c462, c2453, c2064, c4110] c4776 (by decide) p (sat_cons (step462 p h) (sat_cons (step2453 p h) (sat_cons (step2064 p h) (sat_cons (step4110 p h) (sat_nil p)))))
def c4777 : List Lit := [(20, false), (21, false), (1583, true), (92, false)]
theorem step4777 (p : Nat → Bool) (h : Constraints p) : clause p c4777 = true :=
  Snake9.LocalRup.prove_clause [c4110, c57] c4777 (by decide) p (sat_cons (step4110 p h) (sat_cons (step57 p h) (sat_nil p)))
def c4778 : List Lit := [(15, false), (20, true), (1688, true), (87, true), (86, false), (1628, false), (1623, false), (1644, false)]
theorem step4778 (p : Nat → Bool) (h : Constraints p) : clause p c4778 = true :=
  Snake9.LocalRup.prove_clause [c1949, c1962, c1241, c32, c1247, c4068, c1285, c1339, c1314] c4778 (by decide) p (sat_cons (step1949 p h) (sat_cons (step1962 p h) (sat_cons (step1241 p h) (sat_cons (step32 p h) (sat_cons (step1247 p h) (sat_cons (step4068 p h) (sat_cons (step1285 p h) (sat_cons (step1339 p h) (sat_cons (step1314 p h) (sat_nil p))))))))))
def c4779 : List Lit := [(1803, false), (1819, true), (107, false), (115, true), (117, true), (114, false), (92, false)]
theorem step4779 (p : Nat → Bool) (h : Constraints p) : clause p c4779 = true :=
  Snake9.LocalRup.prove_clause [c3576, c4669, c668, c1572] c4779 (by decide) p (sat_cons (step3576 p h) (sat_cons (step4669 p h) (sat_cons (step668 p h) (sat_cons (step1572 p h) (sat_nil p)))))
def c4780 : List Lit := [(98, true), (1782, false), (1771, false), (89, false), (86, false), (1791, true), (92, false), (107, true)]
theorem step4780 (p : Nat → Bool) (h : Constraints p) : clause p c4780 = true :=
  Snake9.LocalRup.prove_clause [c1525, c1508, c2548, c1513, c1915, c1544, c1528] c4780 (by decide) p (sat_cons (step1525 p h) (sat_cons (step1508 p h) (sat_cons (step2548 p h) (sat_cons (step1513 p h) (sat_cons (step1915 p h) (sat_cons (step1544 p h) (sat_cons (step1528 p h) (sat_nil p))))))))
def c4781 : List Lit := [(1773, false), (1782, false), (97, true), (1791, true), (92, false)]
theorem step4781 (p : Nat → Bool) (h : Constraints p) : clause p c4781 = true :=
  Snake9.LocalRup.prove_clause [c1525, c1548, c1504, c1513, c1516, c1544, c1506, c1528, c1915] c4781 (by decide) p (sat_cons (step1525 p h) (sat_cons (step1548 p h) (sat_cons (step1504 p h) (sat_cons (step1513 p h) (sat_cons (step1516 p h) (sat_cons (step1544 p h) (sat_cons (step1506 p h) (sat_cons (step1528 p h) (sat_cons (step1915 p h) (sat_nil p))))))))))
def c4782 : List Lit := [(1803, false), (1818, true), (117, true), (114, false), (92, false), (115, true)]
theorem step4782 (p : Nat → Bool) (h : Constraints p) : clause p c4782 = true :=
  Snake9.LocalRup.prove_clause [c2864, c3117, c1572, c668] c4782 (by decide) p (sat_cons (step2864 p h) (sat_cons (step3117 p h) (sat_cons (step1572 p h) (sat_cons (step668 p h) (sat_nil p)))))
def c4783 : List Lit := [(89, false), (96, true), (86, false), (98, false), (120, false)]
theorem step4783 (p : Nat → Bool) (h : Constraints p) : clause p c4783 = true :=
  Snake9.LocalRup.prove_clause [c490, c416, c2079] c4783 (by decide) p (sat_cons (step490 p h) (sat_cons (step416 p h) (sat_cons (step2079 p h) (sat_nil p))))
def c4784 : List Lit := [(1806, false), (1818, true), (1803, true), (117, true)]
theorem step4784 (p : Nat → Bool) (h : Constraints p) : clause p c4784 = true :=
  Snake9.LocalRup.prove_clause [c1558, c1560, c1596, c1581, c1575, c1578, c1580, c2958, c1601, c1561, c1563, c1559, c1555, c625] c4784 (by decide) p (sat_cons (step1558 p h) (sat_cons (step1560 p h) (sat_cons (step1596 p h) (sat_cons (step1581 p h) (sat_cons (step1575 p h) (sat_cons (step1578 p h) (sat_cons (step1580 p h) (sat_cons (step2958 p h) (sat_cons (step1601 p h) (sat_cons (step1561 p h) (sat_cons (step1563 p h) (sat_cons (step1559 p h) (sat_cons (step1555 p h) (sat_cons (step625 p h) (sat_nil p)))))))))))))))
def c4785 : List Lit := [(1713, true), (108, true), (80, true)]
theorem step4785 (p : Nat → Bool) (h : Constraints p) : clause p c4785 = true :=
  Snake9.LocalRup.prove_clause [c1391, c1393, c1388, c1389, c1386, c334, c2032] c4785 (by decide) p (sat_cons (step1391 p h) (sat_cons (step1393 p h) (sat_cons (step1388 p h) (sat_cons (step1389 p h) (sat_cons (step1386 p h) (sat_cons (step334 p h) (sat_cons (step2032 p h) (sat_nil p))))))))
def c4786 : List Lit := [(1749, false), (1830, false), (1713, false), (1623, false)]
theorem step4786 (p : Nat → Bool) (h : Constraints p) : clause p c4786 = true :=
  Snake9.LocalRup.prove_clause [c2260, c2175, c1698, c2162, c1482, c1488, c1692, c1407, c2176, c4699, c2449] c4786 (by decide) p (sat_cons (step2260 p h) (sat_cons (step2175 p h) (sat_cons (step1698 p h) (sat_cons (step2162 p h) (sat_cons (step1482 p h) (sat_cons (step1488 p h) (sat_cons (step1692 p h) (sat_cons (step1407 p h) (sat_cons (step2176 p h) (sat_cons (step4699 p h) (sat_cons (step2449 p h) (sat_nil p))))))))))))
end B112E034
