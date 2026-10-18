import B112E034Part0044
namespace B112E034
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c4659 : List Lit := [(1583, false), (1628, false), (1623, false), (1687, true)]
theorem step4659 (p : Nat → Bool) (h : Constraints p) : clause p c4659 = true :=
  Snake9.LocalRup.prove_clause [c1246, c2153, c1312, c1345, c2144, c1176, c1338, c1825, c1313, c1818, c2154, c1831, c1247, c1241] c4659 (by decide) p (sat_cons (step1246 p h) (sat_cons (step2153 p h) (sat_cons (step1312 p h) (sat_cons (step1345 p h) (sat_cons (step2144 p h) (sat_cons (step1176 p h) (sat_cons (step1338 p h) (sat_cons (step1825 p h) (sat_cons (step1313 p h) (sat_cons (step1818 p h) (sat_cons (step2154 p h) (sat_cons (step1831 p h) (sat_cons (step1247 p h) (sat_cons (step1241 p h) (sat_nil p)))))))))))))))
def c4660 : List Lit := [(112, false), (1784, true), (1803, true), (125, false)]
theorem step4660 (p : Nat → Bool) (h : Constraints p) : clause p c4660 = true :=
  Snake9.LocalRup.prove_clause [c1569, c1568, c762, c800, c2104, c2101, c610, c839, c1521, c1519, c1527] c4660 (by decide) p (sat_cons (step1569 p h) (sat_cons (step1568 p h) (sat_cons (step762 p h) (sat_cons (step800 p h) (sat_cons (step2104 p h) (sat_cons (step2101 p h) (sat_cons (step610 p h) (sat_cons (step839 p h) (sat_cons (step1521 p h) (sat_cons (step1519 p h) (sat_cons (step1527 p h) (sat_nil p))))))))))))
def c4661 : List Lit := [(1784, true), (1803, true), (1798, false), (1805, false), (1819, true), (125, false)]
theorem step4661 (p : Nat → Bool) (h : Constraints p) : clause p c4661 = true :=
  Snake9.LocalRup.prove_clause [c1569, c1568, c762, c4660, c1555, c1564, c1607, c1580, c1577, c2958, c1945, c2190, c2101, c1527, c839, c1519] c4661 (by decide) p (sat_cons (step1569 p h) (sat_cons (step1568 p h) (sat_cons (step762 p h) (sat_cons (step4660 p h) (sat_cons (step1555 p h) (sat_cons (step1564 p h) (sat_cons (step1607 p h) (sat_cons (step1580 p h) (sat_cons (step1577 p h) (sat_cons (step2958 p h) (sat_cons (step1945 p h) (sat_cons (step2190 p h) (sat_cons (step2101 p h) (sat_cons (step1527 p h) (sat_cons (step839 p h) (sat_cons (step1519 p h) (sat_nil p)))))))))))))))))
def c4662 : List Lit := [(74, false), (107, false), (1644, true), (113, false)]
theorem step4662 (p : Nat → Bool) (h : Constraints p) : clause p c4662 = true :=
  Snake9.LocalRup.prove_clause [c3200, c691] c4662 (by decide) p (sat_cons (step3200 p h) (sat_cons (step691 p h) (sat_nil p)))
def c4663 : List Lit := [(93, false), (107, false), (1644, true), (113, false)]
theorem step4663 (p : Nat → Bool) (h : Constraints p) : clause p c4663 = true :=
  Snake9.LocalRup.prove_clause [c697, c3207] c4663 (by decide) p (sat_cons (step697 p h) (sat_cons (step3207 p h) (sat_nil p)))
def c4664 : List Lit := [(1798, false), (1830, true), (1803, true), (1805, false), (107, false), (1819, true), (125, false)]
theorem step4664 (p : Nat → Bool) (h : Constraints p) : clause p c4664 = true :=
  Snake9.LocalRup.prove_clause [c3157, c1574, c1561, c4661, c1602, c1538, c1587, c1630, c3591] c4664 (by decide) p (sat_cons (step3157 p h) (sat_cons (step1574 p h) (sat_cons (step1561 p h) (sat_cons (step4661 p h) (sat_cons (step1602 p h) (sat_cons (step1538 p h) (sat_cons (step1587 p h) (sat_cons (step1630 p h) (sat_cons (step3591 p h) (sat_nil p))))))))))
def c4665 : List Lit := [(1811, true), (1798, true), (119, true), (1803, true), (1805, false), (107, false)]
theorem step4665 (p : Nat → Bool) (h : Constraints p) : clause p c4665 = true :=
  Snake9.LocalRup.prove_clause [c1580, c2189, c1577, c1559, c2958, c621] c4665 (by decide) p (sat_cons (step1580 p h) (sat_cons (step2189 p h) (sat_cons (step1577 p h) (sat_cons (step1559 p h) (sat_cons (step2958 p h) (sat_cons (step621 p h) (sat_nil p)))))))
def c4666 : List Lit := [(122, false), (111, false), (1798, true), (119, true), (1803, true), (107, false)]
theorem step4666 (p : Nat → Bool) (h : Constraints p) : clause p c4666 = true :=
  Snake9.LocalRup.prove_clause [c1568, c1945, c621, c2187, c1559] c4666 (by decide) p (sat_cons (step1568 p h) (sat_cons (step1945 p h) (sat_cons (step621 p h) (sat_cons (step2187 p h) (sat_cons (step1559 p h) (sat_nil p))))))
def c4667 : List Lit := [(117, true), (111, false), (1800, true), (1798, true), (107, false)]
theorem step4667 (p : Nat → Bool) (h : Constraints p) : clause p c4667 = true :=
  Snake9.LocalRup.prove_clause [c1558, c1559, c1563, c619, c1555] c4667 (by decide) p (sat_cons (step1558 p h) (sat_cons (step1559 p h) (sat_cons (step1563 p h) (sat_cons (step619 p h) (sat_cons (step1555 p h) (sat_nil p))))))
def c4668 : List Lit := [(117, false), (1803, true), (124, true), (113, false), (125, false)]
theorem step4668 (p : Nat → Bool) (h : Constraints p) : clause p c4668 = true :=
  Snake9.LocalRup.prove_clause [c1569, c1568, c762, c840, c670, c2111] c4668 (by decide) p (sat_cons (step1569 p h) (sat_cons (step1568 p h) (sat_cons (step762 p h) (sat_cons (step840 p h) (sat_cons (step670 p h) (sat_cons (step2111 p h) (sat_nil p)))))))
def c4669 : List Lit := [(117, true), (1803, false), (1805, false), (107, false), (1819, true), (113, false)]
theorem step4669 (p : Nat → Bool) (h : Constraints p) : clause p c4669 = true :=
  Snake9.LocalRup.prove_clause [c3214, c1559, c703, c2100, c4667, c621, c1602, c1577, c1584] c4669 (by decide) p (sat_cons (step3214 p h) (sat_cons (step1559 p h) (sat_cons (step703 p h) (sat_cons (step2100 p h) (sat_cons (step4667 p h) (sat_cons (step621 p h) (sat_cons (step1602 p h) (sat_cons (step1577 p h) (sat_cons (step1584 p h) (sat_nil p))))))))))
def c4670 : List Lit := [(118, false), (117, false), (107, false), (113, false)]
theorem step4670 (p : Nat → Bool) (h : Constraints p) : clause p c4670 = true :=
  Snake9.LocalRup.prove_clause [c703, c2098, c714] c4670 (by decide) p (sat_cons (step703 p h) (sat_cons (step2098 p h) (sat_cons (step714 p h) (sat_nil p))))
def c4671 : List Lit := [(1761, true), (86, true), (1720, false), (114, true), (117, false), (1737, false), (74, true), (1644, true)]
theorem step4671 (p : Nat → Bool) (h : Constraints p) : clause p c4671 = true :=
  Snake9.LocalRup.prove_clause [c2391, c3994, c2451, c1493, c2460] c4671 (by decide) p (sat_cons (step2391 p h) (sat_cons (step3994 p h) (sat_cons (step2451 p h) (sat_cons (step1493 p h) (sat_cons (step2460 p h) (sat_nil p))))))
def c4672 : List Lit := [(1818, true), (1797, false), (1803, false), (1805, false), (107, false)]
theorem step4672 (p : Nat → Bool) (h : Constraints p) : clause p c4672 = true :=
  Snake9.LocalRup.prove_clause [c1560, c1574, c1583, c1601, c1596, c1563, c2944, c1555] c4672 (by decide) p (sat_cons (step1560 p h) (sat_cons (step1574 p h) (sat_cons (step1583 p h) (sat_cons (step1601 p h) (sat_cons (step1596 p h) (sat_cons (step1563 p h) (sat_cons (step2944 p h) (sat_cons (step1555 p h) (sat_nil p)))))))))
def c4673 : List Lit := [(109, false), (114, true), (117, false), (107, false), (124, true), (113, false)]
theorem step4673 (p : Nat → Bool) (h : Constraints p) : clause p c4673 = true :=
  Snake9.LocalRup.prove_clause [c536, c711, c2095] c4673 (by decide) p (sat_cons (step536 p h) (sat_cons (step711 p h) (sat_cons (step2095 p h) (sat_nil p))))
def c4674 : List Lit := [(1761, true), (1712, false), (1736, false), (107, false), (1644, true)]
theorem step4674 (p : Nat → Bool) (h : Constraints p) : clause p c4674 = true :=
  Snake9.LocalRup.prove_clause [c2391, c3994, c2451, c1392, c1408, c1437, c2218, c1857, c1493, c1498, c1903, c1884, c1409, c1440, c1418, c1395, c2443, c1386] c4674 (by decide) p (sat_cons (step2391 p h) (sat_cons (step3994 p h) (sat_cons (step2451 p h) (sat_cons (step1392 p h) (sat_cons (step1408 p h) (sat_cons (step1437 p h) (sat_cons (step2218 p h) (sat_cons (step1857 p h) (sat_cons (step1493 p h) (sat_cons (step1498 p h) (sat_cons (step1903 p h) (sat_cons (step1884 p h) (sat_cons (step1409 p h) (sat_cons (step1440 p h) (sat_cons (step1418 p h) (sat_cons (step1395 p h) (sat_cons (step2443 p h) (sat_cons (step1386 p h) (sat_nil p)))))))))))))))))))
def c4675 : List Lit := [(56, true), (57, true), (1644, true)]
theorem step4675 (p : Nat → Bool) (h : Constraints p) : clause p c4675 = true :=
  Snake9.LocalRup.prove_clause [c1857, c1264, c1260, c1261, c1267, c1255, c1252, c2023, c228] c4675 (by decide) p (sat_cons (step1857 p h) (sat_cons (step1264 p h) (sat_cons (step1260 p h) (sat_cons (step1261 p h) (sat_cons (step1267 p h) (sat_cons (step1255 p h) (sat_cons (step1252 p h) (sat_cons (step2023 p h) (sat_cons (step228 p h) (sat_nil p))))))))))
def c4676 : List Lit := [(93, true), (1738, true), (86, false), (113, false), (125, false), (15, true), (1583, true)]
theorem step4676 (p : Nat → Bool) (h : Constraints p) : clause p c4676 = true :=
  Snake9.LocalRup.prove_clause [c1437, c1433, c1435, c1439, c668, c400, c4110, c2063] c4676 (by decide) p (sat_cons (step1437 p h) (sat_cons (step1433 p h) (sat_cons (step1435 p h) (sat_cons (step1439 p h) (sat_cons (step668 p h) (sat_cons (step400 p h) (sat_cons (step4110 p h) (sat_cons (step2063 p h) (sat_nil p)))))))))
def c4677 : List Lit := [(56, true), (1644, true)]
theorem step4677 (p : Nat → Bool) (h : Constraints p) : clause p c4677 = true :=
  Snake9.LocalRup.prove_clause [c3994, c1857, c1264, c1261, c4675, c1255, c240] c4677 (by decide) p (sat_cons (step3994 p h) (sat_cons (step1857 p h) (sat_cons (step1264 p h) (sat_cons (step1261 p h) (sat_cons (step4675 p h) (sat_cons (step1255 p h) (sat_cons (step240 p h) (sat_nil p))))))))
def c4678 : List Lit := [(20, true), (86, true), (142, true), (27, true), (19, false), (15, true)]
theorem step4678 (p : Nat → Bool) (h : Constraints p) : clause p c4678 = true :=
  Snake9.LocalRup.prove_clause [c1969, c1968, c35, c1720] c4678 (by decide) p (sat_cons (step1969 p h) (sat_cons (step1968 p h) (sat_cons (step35 p h) (sat_cons (step1720 p h) (sat_nil p)))))
def c4679 : List Lit := [(1628, true), (27, true), (113, false), (125, false)]
theorem step4679 (p : Nat → Bool) (h : Constraints p) : clause p c4679 = true :=
  Snake9.LocalRup.prove_clause [c1238, c4658, c806] c4679 (by decide) p (sat_cons (step1238 p h) (sat_cons (step4658 p h) (sat_cons (step806 p h) (sat_nil p))))
def c4680 : List Lit := [(38, false), (36, true), (1624, true), (1605, false), (21, false)]
theorem step4680 (p : Nat → Bool) (h : Constraints p) : clause p c4680 = true :=
  Snake9.LocalRup.prove_clause [c1202, c1231, c4070, c4071, c1235, c1195, c1203] c4680 (by decide) p (sat_cons (step1202 p h) (sat_cons (step1231 p h) (sat_cons (step4070 p h) (sat_cons (step4071 p h) (sat_cons (step1235 p h) (sat_cons (step1195 p h) (sat_cons (step1203 p h) (sat_nil p))))))))
def c4681 : List Lit := [(38, false), (1624, true), (21, false), (1605, false)]
theorem step4681 (p : Nat → Bool) (h : Constraints p) : clause p c4681 = true :=
  Snake9.LocalRup.prove_clause [c4680, c149, c150, c146, c1205, c1209, c1195, c1214, c1203, c1235] c4681 (by decide) p (sat_cons (step4680 p h) (sat_cons (step149 p h) (sat_cons (step150 p h) (sat_cons (step146 p h) (sat_cons (step1205 p h) (sat_cons (step1209 p h) (sat_cons (step1195 p h) (sat_cons (step1214 p h) (sat_cons (step1203 p h) (sat_cons (step1235 p h) (sat_nil p)))))))))))
def c4682 : List Lit := [(69, false), (1712, true), (75, false), (58, false), (197, true), (107, true), (115, false)]
theorem step4682 (p : Nat → Bool) (h : Constraints p) : clause p c4682 = true :=
  Snake9.LocalRup.prove_clause [c323, c299, c1390, c328] c4682 (by decide) p (sat_cons (step323 p h) (sat_cons (step299 p h) (sat_cons (step1390 p h) (sat_cons (step328 p h) (sat_nil p)))))
def c4683 : List Lit := [(74, true), (1712, true), (1714, true), (75, false), (58, false)]
theorem step4683 (p : Nat → Bool) (h : Constraints p) : clause p c4683 = true :=
  Snake9.LocalRup.prove_clause [c1388, c1390, c1394, c328, c1386] c4683 (by decide) p (sat_cons (step1388 p h) (sat_cons (step1390 p h) (sat_cons (step1394 p h) (sat_cons (step328 p h) (sat_cons (step1386 p h) (sat_nil p))))))
def c4684 : List Lit := [(62, false), (53, false), (52, false)]
theorem step4684 (p : Nat → Bool) (h : Constraints p) : clause p c4684 = true :=
  Snake9.LocalRup.prove_clause [c2028, c229] c4684 (by decide) p (sat_cons (step2028 p h) (sat_cons (step229 p h) (sat_nil p)))
def c4685 : List Lit := [(57, false), (93, false), (58, true), (52, false), (1642, true)]
theorem step4685 (p : Nat → Bool) (h : Constraints p) : clause p c4685 = true :=
  Snake9.LocalRup.prove_clause [c239, c244, c1262, c1257] c4685 (by decide) p (sat_cons (step239 p h) (sat_cons (step244 p h) (sat_cons (step1262 p h) (sat_cons (step1257 p h) (sat_nil p)))))
def c4686 : List Lit := [(1706, false), (93, true), (1759, true), (86, false), (1819, false), (107, true), (1854, true), (125, false)]
theorem step4686 (p : Nat → Bool) (h : Constraints p) : clause p c4686 = true :=
  Snake9.LocalRup.prove_clause [c1433, c1436, c2206, c4539, c1437, c1439, c1435, c4319, c2905, c1407, c1638, c1485, c1677] c4686 (by decide) p (sat_cons (step1433 p h) (sat_cons (step1436 p h) (sat_cons (step2206 p h) (sat_cons (step4539 p h) (sat_cons (step1437 p h) (sat_cons (step1439 p h) (sat_cons (step1435 p h) (sat_cons (step4319 p h) (sat_cons (step2905 p h) (sat_cons (step1407 p h) (sat_cons (step1638 p h) (sat_cons (step1485 p h) (sat_cons (step1677 p h) (sat_nil p))))))))))))))
def c4687 : List Lit := [(1820, true), (1801, false), (93, false), (117, true), (35, false), (115, false), (37, false), (1808, false), (122, true)]
theorem step4687 (p : Nat → Bool) (h : Constraints p) : clause p c4687 = true :=
  Snake9.LocalRup.prove_clause [c4064, c1608, c1584] c4687 (by decide) p (sat_cons (step4064 p h) (sat_cons (step1608 p h) (sat_cons (step1584 p h) (sat_nil p))))
def c4688 : List Lit := [(1803, true), (117, false), (113, true), (1819, true), (1805, false), (1797, false), (125, false)]
theorem step4688 (p : Nat → Bool) (h : Constraints p) : clause p c4688 = true :=
  Snake9.LocalRup.prove_clause [c1568, c1569, c840, c762, c2280, c2189, c612, c1607, c1556, c1566] c4688 (by decide) p (sat_cons (step1568 p h) (sat_cons (step1569 p h) (sat_cons (step840 p h) (sat_cons (step762 p h) (sat_cons (step2280 p h) (sat_cons (step2189 p h) (sat_cons (step612 p h) (sat_cons (step1607 p h) (sat_cons (step1556 p h) (sat_cons (step1566 p h) (sat_nil p)))))))))))
def c4689 : List Lit := [(113, true), (107, false), (1819, true), (1805, false), (118, true), (125, false)]
theorem step4689 (p : Nat → Bool) (h : Constraints p) : clause p c4689 = true :=
  Snake9.LocalRup.prove_clause [c1574, c1557, c1554, c3332, c1563, c1559, c1602, c4688, c1583, c2944, c1607, c1556, c1566] c4689 (by decide) p (sat_cons (step1574 p h) (sat_cons (step1557 p h) (sat_cons (step1554 p h) (sat_cons (step3332 p h) (sat_cons (step1563 p h) (sat_cons (step1559 p h) (sat_cons (step1602 p h) (sat_cons (step4688 p h) (sat_cons (step1583 p h) (sat_cons (step2944 p h) (sat_cons (step1607 p h) (sat_cons (step1556 p h) (sat_cons (step1566 p h) (sat_nil p))))))))))))))
def c4690 : List Lit := [(121, false), (119, true), (120, false), (122, false), (117, false)]
theorem step4690 (p : Nat → Bool) (h : Constraints p) : clause p c4690 = true :=
  Snake9.LocalRup.prove_clause [c803, c2187] c4690 (by decide) p (sat_cons (step803 p h) (sat_cons (step2187 p h) (sat_nil p)))
def c4691 : List Lit := [(21, false), (1623, true), (20, false), (92, false), (1606, false), (38, false), (37, false)]
theorem step4691 (p : Nat → Bool) (h : Constraints p) : clause p c4691 = true :=
  Snake9.LocalRup.prove_clause [c4322, c68, c1230, c1192, c1200] c4691 (by decide) p (sat_cons (step4322 p h) (sat_cons (step68 p h) (sat_cons (step1230 p h) (sat_cons (step1192 p h) (sat_cons (step1200 p h) (sat_nil p))))))
def c4692 : List Lit := [(1616, true), (38, false)]
theorem step4692 (p : Nat → Bool) (h : Constraints p) : clause p c4692 = true :=
  Snake9.LocalRup.prove_clause [c1211, c1213, c2293, c1209, c1206, c1732] c4692 (by decide) p (sat_cons (step1211 p h) (sat_cons (step1213 p h) (sat_cons (step2293 p h) (sat_cons (step1209 p h) (sat_cons (step1206 p h) (sat_cons (step1732 p h) (sat_nil p)))))))
def c4693 : List Lit := [(1790, true), (107, true), (97, true), (86, false), (92, false)]
theorem step4693 (p : Nat → Bool) (h : Constraints p) : clause p c4693 = true :=
  Snake9.LocalRup.prove_clause [c1522, c1504, c1512, c2197, c4113, c1523, c2347] c4693 (by decide) p (sat_cons (step1522 p h) (sat_cons (step1504 p h) (sat_cons (step1512 p h) (sat_cons (step2197 p h) (sat_cons (step4113 p h) (sat_cons (step1523 p h) (sat_cons (step2347 p h) (sat_nil p))))))))
def c4694 : List Lit := [(1621, true), (37, true), (20, false), (92, false)]
theorem step4694 (p : Nat → Bool) (h : Constraints p) : clause p c4694 = true :=
  Snake9.LocalRup.prove_clause [c1220, c2335, c1216, c1192, c1207, c70] c4694 (by decide) p (sat_cons (step1220 p h) (sat_cons (step2335 p h) (sat_cons (step1216 p h) (sat_cons (step1192 p h) (sat_cons (step1207 p h) (sat_cons (step70 p h) (sat_nil p)))))))
def c4695 : List Lit := [(1644, true), (1711, false), (1720, true), (114, true)]
theorem step4695 (p : Nat → Bool) (h : Constraints p) : clause p c4695 = true :=
  Snake9.LocalRup.prove_clause [c1857, c2391, c3994, c4677, c236, c2451, c1408, c1394, c2876, c1386, c2813] c4695 (by decide) p (sat_cons (step1857 p h) (sat_cons (step2391 p h) (sat_cons (step3994 p h) (sat_cons (step4677 p h) (sat_cons (step236 p h) (sat_cons (step2451 p h) (sat_cons (step1408 p h) (sat_cons (step1394 p h) (sat_cons (step2876 p h) (sat_cons (step1386 p h) (sat_cons (step2813 p h) (sat_nil p))))))))))))
def c4696 : List Lit := [(52, false), (58, false), (70, false), (74, false)]
theorem step4696 (p : Nat → Bool) (h : Constraints p) : clause p c4696 = true :=
  Snake9.LocalRup.prove_clause [c241, c2813] c4696 (by decide) p (sat_cons (step241 p h) (sat_cons (step2813 p h) (sat_nil p)))
def c4697 : List Lit := [(115, false), (117, true), (1803, false), (74, false), (1832, true), (37, false), (1775, false), (92, false)]
theorem step4697 (p : Nat → Bool) (h : Constraints p) : clause p c4697 = true :=
  Snake9.LocalRup.prove_clause [c673, c674, c676, c675, c1522, c1571, c1559, c2799, c3114, c1632, c1638, c3248, c2197, c1523] c4697 (by decide) p (sat_cons (step673 p h) (sat_cons (step674 p h) (sat_cons (step676 p h) (sat_cons (step675 p h) (sat_cons (step1522 p h) (sat_cons (step1571 p h) (sat_cons (step1559 p h) (sat_cons (step2799 p h) (sat_cons (step3114 p h) (sat_cons (step1632 p h) (sat_cons (step1638 p h) (sat_cons (step3248 p h) (sat_cons (step2197 p h) (sat_cons (step1523 p h) (sat_nil p)))))))))))))))
def c4698 : List Lit := [(1622, true), (1604, false), (38, false)]
theorem step4698 (p : Nat → Bool) (h : Constraints p) : clause p c4698 = true :=
  Snake9.LocalRup.prove_clause [c1199, c4692, c1229, c1225, c1200, c1891, c1195] c4698 (by decide) p (sat_cons (step1199 p h) (sat_cons (step4692 p h) (sat_cons (step1229 p h) (sat_cons (step1225 p h) (sat_cons (step1200 p h) (sat_cons (step1891 p h) (sat_cons (step1195 p h) (sat_nil p))))))))
def c4699 : List Lit := [(1644, true), (1706, true)]
theorem step4699 (p : Nat → Bool) (h : Constraints p) : clause p c4699 = true :=
  Snake9.LocalRup.prove_clause [c2391, c3994, c2451] c4699 (by decide) p (sat_cons (step2391 p h) (sat_cons (step3994 p h) (sat_cons (step2451 p h) (sat_nil p))))
def c4700 : List Lit := [(28, false), (1584, true), (15, true), (20, false), (92, false)]
theorem step4700 (p : Nat → Bool) (h : Constraints p) : clause p c4700 = true :=
  Snake9.LocalRup.prove_clause [c68, c65, c2838] c4700 (by decide) p (sat_cons (step68 p h) (sat_cons (step65 p h) (sat_cons (step2838 p h) (sat_nil p))))
def c4701 : List Lit := [(86, false), (97, true), (92, false), (1789, true)]
theorem step4701 (p : Nat → Bool) (h : Constraints p) : clause p c4701 = true :=
  Snake9.LocalRup.prove_clause [c3036, c1504, c1512] c4701 (by decide) p (sat_cons (step3036 p h) (sat_cons (step1504 p h) (sat_cons (step1512 p h) (sat_nil p))))
def c4702 : List Lit := [(86, false), (1789, true), (87, false), (92, false)]
theorem step4702 (p : Nat → Bool) (h : Constraints p) : clause p c4702 = true :=
  Snake9.LocalRup.prove_clause [c402, c4701] c4702 (by decide) p (sat_cons (step402 p h) (sat_cons (step4701 p h) (sat_nil p)))
def c4703 : List Lit := [(1604, false), (89, false), (1803, true), (1622, true), (1623, true)]
theorem step4703 (p : Nat → Bool) (h : Constraints p) : clause p c4703 = true :=
  Snake9.LocalRup.prove_clause [c1569, c1568, c1199, c4273, c1225, c3012, c4428, c2278, c750] c4703 (by decide) p (sat_cons (step1569 p h) (sat_cons (step1568 p h) (sat_cons (step1199 p h) (sat_cons (step4273 p h) (sat_cons (step1225 p h) (sat_cons (step3012 p h) (sat_cons (step4428 p h) (sat_cons (step2278 p h) (sat_cons (step750 p h) (sat_nil p))))))))))
def c4704 : List Lit := [(1829, true), (117, true), (1805, false), (1787, false), (1803, false)]
theorem step4704 (p : Nat → Bool) (h : Constraints p) : clause p c4704 = true :=
  Snake9.LocalRup.prove_clause [c2864, c1620, c1624, c3114, c1904, c4669, c1522] c4704 (by decide) p (sat_cons (step2864 p h) (sat_cons (step1620 p h) (sat_cons (step1624 p h) (sat_cons (step3114 p h) (sat_cons (step1904 p h) (sat_cons (step4669 p h) (sat_cons (step1522 p h) (sat_nil p))))))))
def c4705 : List Lit := [(107, false), (126, false), (1738, false), (86, true), (1760, true), (114, true)]
theorem step4705 (p : Nat → Bool) (h : Constraints p) : clause p c4705 = true :=
  Snake9.LocalRup.prove_clause [c3178, c4047, c693] c4705 (by decide) p (sat_cons (step3178 p h) (sat_cons (step4047 p h) (sat_cons (step693 p h) (sat_nil p))))
def c4706 : List Lit := [(1621, true), (1832, true), (117, true), (1775, false), (1803, false), (74, false), (20, false), (92, false)]
theorem step4706 (p : Nat → Bool) (h : Constraints p) : clause p c4706 = true :=
  Snake9.LocalRup.prove_clause [c2335, c4694, c1192, c4697, c70, c4085] c4706 (by decide) p (sat_cons (step2335 p h) (sat_cons (step4694 p h) (sat_cons (step1192 p h) (sat_cons (step4697 p h) (sat_cons (step70 p h) (sat_cons (step4085 p h) (sat_nil p)))))))
def c4707 : List Lit := [(1621, true), (74, false), (93, false), (20, false), (92, false)]
theorem step4707 (p : Nat → Bool) (h : Constraints p) : clause p c4707 = true :=
  Snake9.LocalRup.prove_clause [c2335, c4694, c1192, c672, c70, c4085] c4707 (by decide) p (sat_cons (step2335 p h) (sat_cons (step4694 p h) (sat_cons (step1192 p h) (sat_cons (step672 p h) (sat_cons (step70 p h) (sat_cons (step4085 p h) (sat_nil p)))))))
def c4708 : List Lit := [(1594, true), (20, false), (92, false)]
theorem step4708 (p : Nat → Bool) (h : Constraints p) : clause p c4708 = true :=
  Snake9.LocalRup.prove_clause [c4068, c4077, c55] c4708 (by decide) p (sat_cons (step4068 p h) (sat_cons (step4077 p h) (sat_cons (step55 p h) (sat_nil p))))
def c4709 : List Lit := [(1644, true), (1761, true), (75, false), (115, true), (93, false), (74, false), (114, true)]
theorem step4709 (p : Nat → Bool) (h : Constraints p) : clause p c4709 = true :=
  Snake9.LocalRup.prove_clause [c3994, c3533, c4529, c2812, c333, c1438, c4695, c1418, c1493, c2185] c4709 (by decide) p (sat_cons (step3994 p h) (sat_cons (step3533 p h) (sat_cons (step4529 p h) (sat_cons (step2812 p h) (sat_cons (step333 p h) (sat_cons (step1438 p h) (sat_cons (step4695 p h) (sat_cons (step1418 p h) (sat_cons (step1493 p h) (sat_cons (step2185 p h) (sat_nil p)))))))))))
def c4710 : List Lit := [(1622, true), (1604, false), (115, true), (1584, true), (92, false), (114, true)]
theorem step4710 (p : Nat → Bool) (h : Constraints p) : clause p c4710 = true :=
  Snake9.LocalRup.prove_clause [c1199, c4698, c1225, c1996, c4108] c4710 (by decide) p (sat_cons (step1199 p h) (sat_cons (step4698 p h) (sat_cons (step1225 p h) (sat_cons (step1996 p h) (sat_cons (step4108 p h) (sat_nil p))))))
def c4711 : List Lit := [(4, false), (1541, true), (21, false), (61, false), (62, false), (1645, true), (1594, true)]
theorem step4711 (p : Nat → Bool) (h : Constraints p) : clause p c4711 = true :=
  Snake9.LocalRup.prove_clause [c4065, c1822, c1103, c1960, c2452, c1815, c11, c10, c13, c1924, c1093, c1952, c222] c4711 (by decide) p (sat_cons (step4065 p h) (sat_cons (step1822 p h) (sat_cons (step1103 p h) (sat_cons (step1960 p h) (sat_cons (step2452 p h) (sat_cons (step1815 p h) (sat_cons (step11 p h) (sat_cons (step10 p h) (sat_cons (step13 p h) (sat_cons (step1924 p h) (sat_cons (step1093 p h) (sat_cons (step1952 p h) (sat_cons (step222 p h) (sat_nil p))))))))))))))
def c4712 : List Lit := [(38, false), (33, false), (21, false), (1618, true)]
theorem step4712 (p : Nat → Bool) (h : Constraints p) : clause p c4712 = true :=
  Snake9.LocalRup.prove_clause [c4071, c146] c4712 (by decide) p (sat_cons (step4071 p h) (sat_cons (step146 p h) (sat_nil p)))
def c4713 : List Lit := [(1617, true), (21, false), (38, false)]
theorem step4713 (p : Nat → Bool) (h : Constraints p) : clause p c4713 = true :=
  Snake9.LocalRup.prove_clause [c4322, c4070, c1205, c150, c1214, c1209] c4713 (by decide) p (sat_cons (step4322 p h) (sat_cons (step4070 p h) (sat_cons (step1205 p h) (sat_cons (step150 p h) (sat_cons (step1214 p h) (sat_cons (step1209 p h) (sat_nil p)))))))
def c4714 : List Lit := [(1714, true), (115, true), (73, true), (1645, true), (1646, true), (62, false)]
theorem step4714 (p : Nat → Bool) (h : Constraints p) : clause p c4714 = true :=
  Snake9.LocalRup.prove_clause [c1389, c1392, c1394, c1390, c1386, c2319, c1887, c2322, c1268, c4684, c1253] c4714 (by decide) p (sat_cons (step1389 p h) (sat_cons (step1392 p h) (sat_cons (step1394 p h) (sat_cons (step1390 p h) (sat_cons (step1386 p h) (sat_cons (step2319 p h) (sat_cons (step1887 p h) (sat_cons (step2322 p h) (sat_cons (step1268 p h) (sat_cons (step4684 p h) (sat_cons (step1253 p h) (sat_nil p))))))))))))
def c4715 : List Lit := [(1789, false), (107, true), (1719, false), (1805, false), (113, true), (117, true), (92, false), (1852, true)]
theorem step4715 (p : Nat → Bool) (h : Constraints p) : clause p c4715 = true :=
  Snake9.LocalRup.prove_clause [c3190, c1668, c1631, c3114, c1568, c3162, c1630, c1637, c1675, c1485, c2206, c2200, c1438, c2905] c4715 (by decide) p (sat_cons (step3190 p h) (sat_cons (step1668 p h) (sat_cons (step1631 p h) (sat_cons (step3114 p h) (sat_cons (step1568 p h) (sat_cons (step3162 p h) (sat_cons (step1630 p h) (sat_cons (step1637 p h) (sat_cons (step1675 p h) (sat_cons (step1485 p h) (sat_cons (step2206 p h) (sat_cons (step2200 p h) (sat_cons (step1438 p h) (sat_cons (step2905 p h) (sat_nil p)))))))))))))))
def c4716 : List Lit := [(107, true), (1719, false), (115, true), (1805, false), (113, true), (117, true), (92, false), (1852, true)]
theorem step4716 (p : Nat → Bool) (h : Constraints p) : clause p c4716 = true :=
  Snake9.LocalRup.prove_clause [c3190, c1668, c1522, c1904, c4715, c1626, c1843, c2799, c1523, c3157, c3122, c3248, c1559] c4716 (by decide) p (sat_cons (step3190 p h) (sat_cons (step1668 p h) (sat_cons (step1522 p h) (sat_cons (step1904 p h) (sat_cons (step4715 p h) (sat_cons (step1626 p h) (sat_cons (step1843 p h) (sat_cons (step2799 p h) (sat_cons (step1523 p h) (sat_cons (step3157 p h) (sat_cons (step3122 p h) (sat_cons (step3248 p h) (sat_cons (step1559 p h) (sat_nil p))))))))))))))
def c4717 : List Lit := [(111, false), (118, false), (1820, true), (1803, false), (107, false), (1797, false), (1805, false), (113, true)]
theorem step4717 (p : Nat → Bool) (h : Constraints p) : clause p c4717 = true :=
  Snake9.LocalRup.prove_clause [c619, c621, c1556, c1577, c1566, c1584, c1608] c4717 (by decide) p (sat_cons (step619 p h) (sat_cons (step621 p h) (sat_cons (step1556 p h) (sat_cons (step1577 p h) (sat_cons (step1566 p h) (sat_cons (step1584 p h) (sat_cons (step1608 p h) (sat_nil p))))))))
def c4718 : List Lit := [(1820, true), (1803, false), (107, false), (113, true), (117, true), (125, true)]
theorem step4718 (p : Nat → Bool) (h : Constraints p) : clause p c4718 = true :=
  Snake9.LocalRup.prove_clause [c1558, c1554, c1563, c1572, c3174, c1603, c1559, c1585, c4717, c2100, c705, c2946, c1573, c1575, c1578, c1584, c2342, c1608, c1556, c1566] c4718 (by decide) p (sat_cons (step1558 p h) (sat_cons (step1554 p h) (sat_cons (step1563 p h) (sat_cons (step1572 p h) (sat_cons (step3174 p h) (sat_cons (step1603 p h) (sat_cons (step1559 p h) (sat_cons (step1585 p h) (sat_cons (step4717 p h) (sat_cons (step2100 p h) (sat_cons (step705 p h) (sat_cons (step2946 p h) (sat_cons (step1573 p h) (sat_cons (step1575 p h) (sat_cons (step1578 p h) (sat_cons (step1584 p h) (sat_cons (step2342 p h) (sat_cons (step1608 p h) (sat_cons (step1556 p h) (sat_cons (step1566 p h) (sat_nil p)))))))))))))))))))))
def c4719 : List Lit := [(1644, false), (1633, false), (1685, true), (122, false), (1620, false)]
theorem step4719 (p : Nat → Bool) (h : Constraints p) : clause p c4719 = true :=
  Snake9.LocalRup.prove_clause [c4088, c1285, c2335, c1295, c4462, c1336] c4719 (by decide) p (sat_cons (step4088 p h) (sat_cons (step1285 p h) (sat_cons (step2335 p h) (sat_cons (step1295 p h) (sat_cons (step4462 p h) (sat_cons (step1336 p h) (sat_nil p)))))))
def c4720 : List Lit := [(1633, false), (1748, false), (122, false), (1620, false), (1831, false), (1714, false)]
theorem step4720 (p : Nat → Bool) (h : Constraints p) : clause p c4720 = true :=
  Snake9.LocalRup.prove_clause [c2163, c1487, c1693, c2175, c2154, c1294, c4719, c4699, c1408, c1493, c1699, c2174, c4092, c1335, c2335, c4462] c4720 (by decide) p (sat_cons (step2163 p h) (sat_cons (step1487 p h) (sat_cons (step1693 p h) (sat_cons (step2175 p h) (sat_cons (step2154 p h) (sat_cons (step1294 p h) (sat_cons (step4719 p h) (sat_cons (step4699 p h) (sat_cons (step1408 p h) (sat_cons (step1493 p h) (sat_cons (step1699 p h) (sat_cons (step2174 p h) (sat_cons (step4092 p h) (sat_cons (step1335 p h) (sat_cons (step2335 p h) (sat_cons (step4462 p h) (sat_nil p)))))))))))))))))
def c4721 : List Lit := [(1622, true), (37, true), (20, true), (36, false), (1604, false)]
theorem step4721 (p : Nat → Bool) (h : Constraints p) : clause p c4721 = true :=
  Snake9.LocalRup.prove_clause [c1205, c1213, c1199, c1229, c4698, c1225, c1200, c1995, c1194, c4410] c4721 (by decide) p (sat_cons (step1205 p h) (sat_cons (step1213 p h) (sat_cons (step1199 p h) (sat_cons (step1229 p h) (sat_cons (step4698 p h) (sat_cons (step1225 p h) (sat_cons (step1200 p h) (sat_cons (step1995 p h) (sat_cons (step1194 p h) (sat_cons (step4410 p h) (sat_nil p)))))))))))
def c4722 : List Lit := [(1774, false), (1789, true), (92, false)]
theorem step4722 (p : Nat → Bool) (h : Constraints p) : clause p c4722 = true :=
  Snake9.LocalRup.prove_clause [c1546, c1511, c1514, c1542, c1505, c1526, c1915] c4722 (by decide) p (sat_cons (step1546 p h) (sat_cons (step1511 p h) (sat_cons (step1514 p h) (sat_cons (step1542 p h) (sat_cons (step1505 p h) (sat_cons (step1526 p h) (sat_cons (step1915 p h) (sat_nil p))))))))
end B112E034
