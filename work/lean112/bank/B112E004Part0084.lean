import B112E004Part0083
namespace B112E004
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c7110 : List Lit := [(42, false), (1540, false), (1530, false), (1549, false)]
theorem step7110 (p : Nat → Bool) (h : Constraints p) : clause p c7110 = true :=
  Snake9.LocalRup.prove_clause [c6009, c6980, c6900, c6506, c7065, c2135, c7096, c5747, c1309, c1356, c2090, c2324, c1420, c7109, c1445, c7104, c2116, c1317, c1310, c1348, c2094, c2449, c2970, c7106, c2089, c4541, c2177, c2115, c2134, c1645, c1311, c7046, c198, c189, c1382, c1200, c1403, c1404, c1202, c1467, c1466, c1391, c1393, c1228, c1446, c1640, c1388, c1389, c1386, c5861, c6110, c5734, c6834, c1426, c1210, c1435, c6949] c7110 (by decide) p (sat_cons (step6009 p h) (sat_cons (step6980 p h) (sat_cons (step6900 p h) (sat_cons (step6506 p h) (sat_cons (step7065 p h) (sat_cons (step2135 p h) (sat_cons (step7096 p h) (sat_cons (step5747 p h) (sat_cons (step1309 p h) (sat_cons (step1356 p h) (sat_cons (step2090 p h) (sat_cons (step2324 p h) (sat_cons (step1420 p h) (sat_cons (step7109 p h) (sat_cons (step1445 p h) (sat_cons (step7104 p h) (sat_cons (step2116 p h) (sat_cons (step1317 p h) (sat_cons (step1310 p h) (sat_cons (step1348 p h) (sat_cons (step2094 p h) (sat_cons (step2449 p h) (sat_cons (step2970 p h) (sat_cons (step7106 p h) (sat_cons (step2089 p h) (sat_cons (step4541 p h) (sat_cons (step2177 p h) (sat_cons (step2115 p h) (sat_cons (step2134 p h) (sat_cons (step1645 p h) (sat_cons (step1311 p h) (sat_cons (step7046 p h) (sat_cons (step198 p h) (sat_cons (step189 p h) (sat_cons (step1382 p h) (sat_cons (step1200 p h) (sat_cons (step1403 p h) (sat_cons (step1404 p h) (sat_cons (step1202 p h) (sat_cons (step1467 p h) (sat_cons (step1466 p h) (sat_cons (step1391 p h) (sat_cons (step1393 p h) (sat_cons (step1228 p h) (sat_cons (step1446 p h) (sat_cons (step1640 p h) (sat_cons (step1388 p h) (sat_cons (step1389 p h) (sat_cons (step1386 p h) (sat_cons (step5861 p h) (sat_cons (step6110 p h) (sat_cons (step5734 p h) (sat_cons (step6834 p h) (sat_cons (step1426 p h) (sat_cons (step1210 p h) (sat_cons (step1435 p h) (sat_cons (step6949 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c7111 : List Lit := [(1540, false), (1530, false), (1549, false)]
theorem step7111 (p : Nat → Bool) (h : Constraints p) : clause p c7111 = true :=
  Snake9.LocalRup.prove_clause [c6506, c6009, c6980, c6900, c7104, c7065, c2135, c7096, c5747, c1309, c1356, c2090, c2324, c1420, c2116, c1311, c7046, c1317, c1310, c2115, c1348, c2134, c2094, c1645, c2177, c2449, c7109, c1445, c7110, c7107, c1199, c1200, c2143, c191, c170, c1425, c1382, c1403, c1467, c1466, c1446, c1640, c5861, c1435, c6087] c7111 (by decide) p (sat_cons (step6506 p h) (sat_cons (step6009 p h) (sat_cons (step6980 p h) (sat_cons (step6900 p h) (sat_cons (step7104 p h) (sat_cons (step7065 p h) (sat_cons (step2135 p h) (sat_cons (step7096 p h) (sat_cons (step5747 p h) (sat_cons (step1309 p h) (sat_cons (step1356 p h) (sat_cons (step2090 p h) (sat_cons (step2324 p h) (sat_cons (step1420 p h) (sat_cons (step2116 p h) (sat_cons (step1311 p h) (sat_cons (step7046 p h) (sat_cons (step1317 p h) (sat_cons (step1310 p h) (sat_cons (step2115 p h) (sat_cons (step1348 p h) (sat_cons (step2134 p h) (sat_cons (step2094 p h) (sat_cons (step1645 p h) (sat_cons (step2177 p h) (sat_cons (step2449 p h) (sat_cons (step7109 p h) (sat_cons (step1445 p h) (sat_cons (step7110 p h) (sat_cons (step7107 p h) (sat_cons (step1199 p h) (sat_cons (step1200 p h) (sat_cons (step2143 p h) (sat_cons (step191 p h) (sat_cons (step170 p h) (sat_cons (step1425 p h) (sat_cons (step1382 p h) (sat_cons (step1403 p h) (sat_cons (step1467 p h) (sat_cons (step1466 p h) (sat_cons (step1446 p h) (sat_cons (step1640 p h) (sat_cons (step5861 p h) (sat_cons (step1435 p h) (sat_cons (step6087 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))
def c7112 : List Lit := [(1530, false), (1549, false)]
theorem step7112 (p : Nat → Bool) (h : Constraints p) : clause p c7112 = true :=
  Snake9.LocalRup.prove_clause [c6900, c6980, c6506, c6773, c7096, c7065, c2135, c2116, c7046, c5747, c1324, c1309, c1356, c2090, c2324, c1420, c7104, c1400, c1392, c7111, c7018, c5741, c1380, c1382, c1388, c6579, c5881, c1390, c1377, c1378, c5854, c1394, c2449, c2970, c5390, c1992, c2146, c198, c191, c341, c339, c1212, c1254, c1244, c1217, c1246, c1233, c1279, c1203, c1263, c1201, c1258, c3459] c7112 (by decide) p (sat_cons (step6900 p h) (sat_cons (step6980 p h) (sat_cons (step6506 p h) (sat_cons (step6773 p h) (sat_cons (step7096 p h) (sat_cons (step7065 p h) (sat_cons (step2135 p h) (sat_cons (step2116 p h) (sat_cons (step7046 p h) (sat_cons (step5747 p h) (sat_cons (step1324 p h) (sat_cons (step1309 p h) (sat_cons (step1356 p h) (sat_cons (step2090 p h) (sat_cons (step2324 p h) (sat_cons (step1420 p h) (sat_cons (step7104 p h) (sat_cons (step1400 p h) (sat_cons (step1392 p h) (sat_cons (step7111 p h) (sat_cons (step7018 p h) (sat_cons (step5741 p h) (sat_cons (step1380 p h) (sat_cons (step1382 p h) (sat_cons (step1388 p h) (sat_cons (step6579 p h) (sat_cons (step5881 p h) (sat_cons (step1390 p h) (sat_cons (step1377 p h) (sat_cons (step1378 p h) (sat_cons (step5854 p h) (sat_cons (step1394 p h) (sat_cons (step2449 p h) (sat_cons (step2970 p h) (sat_cons (step5390 p h) (sat_cons (step1992 p h) (sat_cons (step2146 p h) (sat_cons (step198 p h) (sat_cons (step191 p h) (sat_cons (step341 p h) (sat_cons (step339 p h) (sat_cons (step1212 p h) (sat_cons (step1254 p h) (sat_cons (step1244 p h) (sat_cons (step1217 p h) (sat_cons (step1246 p h) (sat_cons (step1233 p h) (sat_cons (step1279 p h) (sat_cons (step1203 p h) (sat_cons (step1263 p h) (sat_cons (step1201 p h) (sat_cons (step1258 p h) (sat_cons (step3459 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c7113 : List Lit := [(1516, false), (1551, true), (1604, false), (5, false)]
theorem step7113 (p : Nat → Bool) (h : Constraints p) : clause p c7113 = true :=
  Snake9.LocalRup.prove_clause [c6508, c1315, c1316, c7021] c7113 (by decide) p (sat_cons (step6508 p h) (sat_cons (step1315 p h) (sat_cons (step1316 p h) (sat_cons (step7021 p h) (sat_nil p)))))
def c7114 : List Lit := [(1539, true), (36, false), (1455, true), (44, false), (32, false), (1588, true), (38, false)]
theorem step7114 (p : Nat → Bool) (h : Constraints p) : clause p c7114 = true :=
  Snake9.LocalRup.prove_clause [c6506, c2970, c5751, c5752, c1390, c177, c268, c116, c332, c1941, c1993, c5395, c255] c7114 (by decide) p (sat_cons (step6506 p h) (sat_cons (step2970 p h) (sat_cons (step5751 p h) (sat_cons (step5752 p h) (sat_cons (step1390 p h) (sat_cons (step177 p h) (sat_cons (step268 p h) (sat_cons (step116 p h) (sat_cons (step332 p h) (sat_cons (step1941 p h) (sat_cons (step1993 p h) (sat_cons (step5395 p h) (sat_cons (step255 p h) (sat_nil p))))))))))))))
def c7115 : List Lit := [(73, true), (1539, false), (1516, true), (1604, false), (1540, true), (1502, false), (61, false), (1507, false), (1549, false)]
theorem step7115 (p : Nat → Bool) (h : Constraints p) : clause p c7115 = true :=
  Snake9.LocalRup.prove_clause [c6506, c6009, c6772, c6980, c7112, c1789, c1377, c1380, c4152, c1388, c7100, c4064, c5760, c2292, c4534] c7115 (by decide) p (sat_cons (step6506 p h) (sat_cons (step6009 p h) (sat_cons (step6772 p h) (sat_cons (step6980 p h) (sat_cons (step7112 p h) (sat_cons (step1789 p h) (sat_cons (step1377 p h) (sat_cons (step1380 p h) (sat_cons (step4152 p h) (sat_cons (step1388 p h) (sat_cons (step7100 p h) (sat_cons (step4064 p h) (sat_cons (step5760 p h) (sat_cons (step2292 p h) (sat_cons (step4534 p h) (sat_nil p))))))))))))))))
def c7116 : List Lit := [(36, false), (1455, true), (44, false), (32, false), (1516, true), (1588, true), (1604, false), (1540, true), (1502, false), (61, false), (1507, false), (1549, false)]
theorem step7116 (p : Nat → Bool) (h : Constraints p) : clause p c7116 = true :=
  Snake9.LocalRup.prove_clause [c6009, c6506, c7112, c1257, c2146, c1393, c4152, c7096, c7046, c7114, c1309, c2114, c2133, c1651, c1474, c1446, c7115, c7072, c5738, c1381, c7097, c1408] c7116 (by decide) p (sat_cons (step6009 p h) (sat_cons (step6506 p h) (sat_cons (step7112 p h) (sat_cons (step1257 p h) (sat_cons (step2146 p h) (sat_cons (step1393 p h) (sat_cons (step4152 p h) (sat_cons (step7096 p h) (sat_cons (step7046 p h) (sat_cons (step7114 p h) (sat_cons (step1309 p h) (sat_cons (step2114 p h) (sat_cons (step2133 p h) (sat_cons (step1651 p h) (sat_cons (step1474 p h) (sat_cons (step1446 p h) (sat_cons (step7115 p h) (sat_cons (step7072 p h) (sat_cons (step5738 p h) (sat_cons (step1381 p h) (sat_cons (step7097 p h) (sat_cons (step1408 p h) (sat_nil p)))))))))))))))))))))))
def c7117 : List Lit := [(1604, false), (1540, true), (5, false), (61, false), (1507, false), (1549, false)]
theorem step7117 (p : Nat → Bool) (h : Constraints p) : clause p c7117 = true :=
  Snake9.LocalRup.prove_clause [c6980, c6773, c6900, c6009, c6506, c191, c1200, c1202, c202, c1216, c7112, c1789, c1377, c1380, c1257, c2146, c4152, c7096, c7065, c2135, c7046, c1773, c7073, c7102, c1406, c1395, c7113, c3733, c3721, c1232, c1203, c1201, c7116, c2094, c6560, c1346, c6111, c2133, c1445, c1823, c1651, c1480, c1309, c5771] c7117 (by decide) p (sat_cons (step6980 p h) (sat_cons (step6773 p h) (sat_cons (step6900 p h) (sat_cons (step6009 p h) (sat_cons (step6506 p h) (sat_cons (step191 p h) (sat_cons (step1200 p h) (sat_cons (step1202 p h) (sat_cons (step202 p h) (sat_cons (step1216 p h) (sat_cons (step7112 p h) (sat_cons (step1789 p h) (sat_cons (step1377 p h) (sat_cons (step1380 p h) (sat_cons (step1257 p h) (sat_cons (step2146 p h) (sat_cons (step4152 p h) (sat_cons (step7096 p h) (sat_cons (step7065 p h) (sat_cons (step2135 p h) (sat_cons (step7046 p h) (sat_cons (step1773 p h) (sat_cons (step7073 p h) (sat_cons (step7102 p h) (sat_cons (step1406 p h) (sat_cons (step1395 p h) (sat_cons (step7113 p h) (sat_cons (step3733 p h) (sat_cons (step3721 p h) (sat_cons (step1232 p h) (sat_cons (step1203 p h) (sat_cons (step1201 p h) (sat_cons (step7116 p h) (sat_cons (step2094 p h) (sat_cons (step6560 p h) (sat_cons (step1346 p h) (sat_cons (step6111 p h) (sat_cons (step2133 p h) (sat_cons (step1445 p h) (sat_cons (step1823 p h) (sat_cons (step1651 p h) (sat_cons (step1480 p h) (sat_cons (step1309 p h) (sat_cons (step5771 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))
def c7118 : List Lit := [(1602, true), (5, false), (61, false), (1549, false)]
theorem step7118 (p : Nat → Bool) (h : Constraints p) : clause p c7118 = true :=
  Snake9.LocalRup.prove_clause [c6980, c6508, c7065, c2135, c1363, c1417, c6286, c6709, c3733, c1356, c1315] c7118 (by decide) p (sat_cons (step6980 p h) (sat_cons (step6508 p h) (sat_cons (step7065 p h) (sat_cons (step2135 p h) (sat_cons (step1363 p h) (sat_cons (step1417 p h) (sat_cons (step6286 p h) (sat_cons (step6709 p h) (sat_cons (step3733 p h) (sat_cons (step1356 p h) (sat_cons (step1315 p h) (sat_nil p))))))))))))
def c7119 : List Lit := [(5, false), (61, false), (1507, false), (1549, false)]
theorem step7119 (p : Nat → Bool) (h : Constraints p) : clause p c7119 = true :=
  Snake9.LocalRup.prove_clause [c6980, c7112, c4152, c7096, c7046, c1773, c202, c7118, c1420, c7102, c7117, c1310] c7119 (by decide) p (sat_cons (step6980 p h) (sat_cons (step7112 p h) (sat_cons (step4152 p h) (sat_cons (step7096 p h) (sat_cons (step7046 p h) (sat_cons (step1773 p h) (sat_cons (step202 p h) (sat_cons (step7118 p h) (sat_cons (step1420 p h) (sat_cons (step7102 p h) (sat_cons (step7117 p h) (sat_cons (step1310 p h) (sat_nil p)))))))))))))
def c7120 : List Lit := [(5, true), (1549, false)]
theorem step7120 (p : Nat → Bool) (h : Constraints p) : clause p c7120 = true :=
  Snake9.LocalRup.prove_clause [c6009, c6900, c7112, c1257, c2146, c4152, c7096, c7065, c2135, c1363, c7046, c1773, c2449, c2094, c1190, c6560, c1346, c1348, c2324, c2133, c1310, c1420, c1651, c6710, c1474, c1446, c6561, c1309, c6579, c1356, c6593, c6826, c1109] c7120 (by decide) p (sat_cons (step6009 p h) (sat_cons (step6900 p h) (sat_cons (step7112 p h) (sat_cons (step1257 p h) (sat_cons (step2146 p h) (sat_cons (step4152 p h) (sat_cons (step7096 p h) (sat_cons (step7065 p h) (sat_cons (step2135 p h) (sat_cons (step1363 p h) (sat_cons (step7046 p h) (sat_cons (step1773 p h) (sat_cons (step2449 p h) (sat_cons (step2094 p h) (sat_cons (step1190 p h) (sat_cons (step6560 p h) (sat_cons (step1346 p h) (sat_cons (step1348 p h) (sat_cons (step2324 p h) (sat_cons (step2133 p h) (sat_cons (step1310 p h) (sat_cons (step1420 p h) (sat_cons (step1651 p h) (sat_cons (step6710 p h) (sat_cons (step1474 p h) (sat_cons (step1446 p h) (sat_cons (step6561 p h) (sat_cons (step1309 p h) (sat_cons (step6579 p h) (sat_cons (step1356 p h) (sat_cons (step6593 p h) (sat_cons (step6826 p h) (sat_cons (step1109 p h) (sat_nil p))))))))))))))))))))))))))))))))))
def c7121 : List Lit := [(1550, false), (1604, false), (61, true), (1549, false)]
theorem step7121 (p : Nat → Bool) (h : Constraints p) : clause p c7121 = true :=
  Snake9.LocalRup.prove_clause [c6009, c6776, c6506, c6900, c7096, c7112, c7025, c7046, c1773, c1444, c1479, c1645, c2134, c2115, c1310, c2113, c2132, c1655, c1481, c5834, c7120, c4152, c2114, c7021, c6733, c7097, c2133, c5738, c6710, c1388, c2829] c7121 (by decide) p (sat_cons (step6009 p h) (sat_cons (step6776 p h) (sat_cons (step6506 p h) (sat_cons (step6900 p h) (sat_cons (step7096 p h) (sat_cons (step7112 p h) (sat_cons (step7025 p h) (sat_cons (step7046 p h) (sat_cons (step1773 p h) (sat_cons (step1444 p h) (sat_cons (step1479 p h) (sat_cons (step1645 p h) (sat_cons (step2134 p h) (sat_cons (step2115 p h) (sat_cons (step1310 p h) (sat_cons (step2113 p h) (sat_cons (step2132 p h) (sat_cons (step1655 p h) (sat_cons (step1481 p h) (sat_cons (step5834 p h) (sat_cons (step7120 p h) (sat_cons (step4152 p h) (sat_cons (step2114 p h) (sat_cons (step7021 p h) (sat_cons (step6733 p h) (sat_cons (step7097 p h) (sat_cons (step2133 p h) (sat_cons (step5738 p h) (sat_cons (step6710 p h) (sat_cons (step1388 p h) (sat_cons (step2829 p h) (sat_nil p))))))))))))))))))))))))))))))))
def c7122 : List Lit := [(1604, false), (1507, false), (1549, false)]
theorem step7122 (p : Nat → Bool) (h : Constraints p) : clause p c7122 = true :=
  Snake9.LocalRup.prove_clause [c6773, c6009, c6506, c6900, c2113, c2132, c1655, c7112, c7120, c7119, c7025, c1481, c5834, c1216, c7096, c7046, c1773, c1444, c1479, c1645, c2134, c2115, c7113, c1232, c1203, c7121, c1309, c5751, c5752, c1388, c5372, c2829, c1487, c2264, c1445, c5861, c1432, c312, c2168, c1943] c7122 (by decide) p (sat_cons (step6773 p h) (sat_cons (step6009 p h) (sat_cons (step6506 p h) (sat_cons (step6900 p h) (sat_cons (step2113 p h) (sat_cons (step2132 p h) (sat_cons (step1655 p h) (sat_cons (step7112 p h) (sat_cons (step7120 p h) (sat_cons (step7119 p h) (sat_cons (step7025 p h) (sat_cons (step1481 p h) (sat_cons (step5834 p h) (sat_cons (step1216 p h) (sat_cons (step7096 p h) (sat_cons (step7046 p h) (sat_cons (step1773 p h) (sat_cons (step1444 p h) (sat_cons (step1479 p h) (sat_cons (step1645 p h) (sat_cons (step2134 p h) (sat_cons (step2115 p h) (sat_cons (step7113 p h) (sat_cons (step1232 p h) (sat_cons (step1203 p h) (sat_cons (step7121 p h) (sat_cons (step1309 p h) (sat_cons (step5751 p h) (sat_cons (step5752 p h) (sat_cons (step1388 p h) (sat_cons (step5372 p h) (sat_cons (step2829 p h) (sat_cons (step1487 p h) (sat_cons (step2264 p h) (sat_cons (step1445 p h) (sat_cons (step5861 p h) (sat_cons (step1432 p h) (sat_cons (step312 p h) (sat_cons (step2168 p h) (sat_cons (step1943 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))
def c7123 : List Lit := [(1507, false), (1549, false)]
theorem step7123 (p : Nat → Bool) (h : Constraints p) : clause p c7123 = true :=
  Snake9.LocalRup.prove_clause [c6009, c7120, c7112, c7065, c2135, c1363, c7046, c1773, c1439, c7119, c7122, c1420, c1417, c2324, c6709, c1190, c1355, c2970, c2134, c6620, c1645, c1389, c1485, c2829] c7123 (by decide) p (sat_cons (step6009 p h) (sat_cons (step7120 p h) (sat_cons (step7112 p h) (sat_cons (step7065 p h) (sat_cons (step2135 p h) (sat_cons (step1363 p h) (sat_cons (step7046 p h) (sat_cons (step1773 p h) (sat_cons (step1439 p h) (sat_cons (step7119 p h) (sat_cons (step7122 p h) (sat_cons (step1420 p h) (sat_cons (step1417 p h) (sat_cons (step2324 p h) (sat_cons (step6709 p h) (sat_cons (step1190 p h) (sat_cons (step1355 p h) (sat_cons (step2970 p h) (sat_cons (step2134 p h) (sat_cons (step6620 p h) (sat_cons (step1645 p h) (sat_cons (step1389 p h) (sat_cons (step1485 p h) (sat_cons (step2829 p h) (sat_nil p)))))))))))))))))))))))))
def c7124 : List Lit := [(1712, true), (1549, false)]
theorem step7124 (p : Nat → Bool) (h : Constraints p) : clause p c7124 = true :=
  Snake9.LocalRup.prove_clause [c6980, c6009, c6900, c7120, c7123, c1211, c199, c1498, c1505, c7046, c1773, c1439, c7112, c198, c7025, c1478, c1645, c1640, c1479, c6661] c7124 (by decide) p (sat_cons (step6980 p h) (sat_cons (step6009 p h) (sat_cons (step6900 p h) (sat_cons (step7120 p h) (sat_cons (step7123 p h) (sat_cons (step1211 p h) (sat_cons (step199 p h) (sat_cons (step1498 p h) (sat_cons (step1505 p h) (sat_cons (step7046 p h) (sat_cons (step1773 p h) (sat_cons (step1439 p h) (sat_cons (step7112 p h) (sat_cons (step198 p h) (sat_cons (step7025 p h) (sat_cons (step1478 p h) (sat_cons (step1645 p h) (sat_cons (step1640 p h) (sat_cons (step1479 p h) (sat_cons (step6661 p h) (sat_nil p)))))))))))))))))))))
def c7125 : List Lit := [(1549, false)]
theorem step7125 (p : Nat → Bool) (h : Constraints p) : clause p c7125 = true :=
  Snake9.LocalRup.prove_clause [c6980, c6774, c6775, c6508, c6506, c7096, c7112, c7120, c7123, c1211, c198, c199, c189, c1200, c7124, c2134, c6424, c1420, c7121, c7073, c1309, c2829, c5751, c1388] c7125 (by decide) p (sat_cons (step6980 p h) (sat_cons (step6774 p h) (sat_cons (step6775 p h) (sat_cons (step6508 p h) (sat_cons (step6506 p h) (sat_cons (step7096 p h) (sat_cons (step7112 p h) (sat_cons (step7120 p h) (sat_cons (step7123 p h) (sat_cons (step1211 p h) (sat_cons (step198 p h) (sat_cons (step199 p h) (sat_cons (step189 p h) (sat_cons (step1200 p h) (sat_cons (step7124 p h) (sat_cons (step2134 p h) (sat_cons (step6424 p h) (sat_cons (step1420 p h) (sat_cons (step7121 p h) (sat_cons (step7073 p h) (sat_cons (step1309 p h) (sat_cons (step2829 p h) (sat_cons (step5751 p h) (sat_cons (step1388 p h) (sat_nil p)))))))))))))))))))))))))
def c7126 : List Lit := [(1516, false)]
theorem step7126 (p : Nat → Bool) (h : Constraints p) : clause p c7126 = true :=
  Snake9.LocalRup.prove_clause [c7125, c5671] c7126 (by decide) p (sat_cons (step7125 p h) (sat_cons (step5671 p h) (sat_nil p)))
def c7127 : List Lit := [(1515, false)]
theorem step7127 (p : Nat → Bool) (h : Constraints p) : clause p c7127 = true :=
  Snake9.LocalRup.prove_clause [c7125, c6508, c1308] c7127 (by decide) p (sat_cons (step7125 p h) (sat_cons (step6508 p h) (sat_cons (step1308 p h) (sat_nil p))))
def c7128 : List Lit := [(1539, false)]
theorem step7128 (p : Nat → Bool) (h : Constraints p) : clause p c7128 = true :=
  Snake9.LocalRup.prove_clause [c7125, c6775, c1301] c7128 (by decide) p (sat_cons (step7125 p h) (sat_cons (step6775 p h) (sat_cons (step1301 p h) (sat_nil p))))
def c7129 : List Lit := [(1503, false)]
theorem step7129 (p : Nat → Bool) (h : Constraints p) : clause p c7129 = true :=
  Snake9.LocalRup.prove_clause [c7127, c6774, c1231] c7129 (by decide) p (sat_cons (step7127 p h) (sat_cons (step6774 p h) (sat_cons (step1231 p h) (sat_nil p))))
def c7130 : List Lit := [(1530, false)]
theorem step7130 (p : Nat → Bool) (h : Constraints p) : clause p c7130 = true :=
  Snake9.LocalRup.prove_clause [c7128, c6506, c5747] c7130 (by decide) p (sat_cons (step7128 p h) (sat_cons (step6506 p h) (sat_cons (step5747 p h) (sat_nil p))))
def c7131 : List Lit := [(1595, true)]
theorem step7131 (p : Nat → Bool) (h : Constraints p) : clause p c7131 = true :=
  Snake9.LocalRup.prove_clause [c7128, c6506, c5771] c7131 (by decide) p (sat_cons (step7128 p h) (sat_cons (step6506 p h) (sat_cons (step5771 p h) (sat_nil p))))
def c7132 : List Lit := [(73, false)]
theorem step7132 (p : Nat → Bool) (h : Constraints p) : clause p c7132 = true :=
  Snake9.LocalRup.prove_clause [c7128, c6506, c5751] c7132 (by decide) p (sat_cons (step7128 p h) (sat_cons (step6506 p h) (sat_cons (step5751 p h) (sat_nil p))))
def c7133 : List Lit := [(46, true)]
theorem step7133 (p : Nat → Bool) (h : Constraints p) : clause p c7133 = true :=
  Snake9.LocalRup.prove_clause [c7128, c6506, c5752] c7133 (by decide) p (sat_cons (step7128 p h) (sat_cons (step6506 p h) (sat_cons (step5752 p h) (sat_nil p))))
def c7134 : List Lit := [(1501, false)]
theorem step7134 (p : Nat → Bool) (h : Constraints p) : clause p c7134 = true :=
  Snake9.LocalRup.prove_clause [c7129, c1203] c7134 (by decide) p (sat_cons (step7129 p h) (sat_cons (step1203 p h) (sat_nil p)))
def c7135 : List Lit := [(60, true)]
theorem step7135 (p : Nat → Bool) (h : Constraints p) : clause p c7135 = true :=
  Snake9.LocalRup.prove_clause [c7130, c1256] c7135 (by decide) p (sat_cons (step7130 p h) (sat_cons (step1256 p h) (sat_nil p)))
def c7136 : List Lit := [(59, true)]
theorem step7136 (p : Nat → Bool) (h : Constraints p) : clause p c7136 = true :=
  Snake9.LocalRup.prove_clause [c7130, c1257] c7136 (by decide) p (sat_cons (step7130 p h) (sat_cons (step1257 p h) (sat_nil p)))
def c7137 : List Lit := [(64, false)]
theorem step7137 (p : Nat → Bool) (h : Constraints p) : clause p c7137 = true :=
  Snake9.LocalRup.prove_clause [c7130, c1789] c7137 (by decide) p (sat_cons (step7130 p h) (sat_cons (step1789 p h) (sat_nil p)))
def c7138 : List Lit := [(1587, true)]
theorem step7138 (p : Nat → Bool) (h : Constraints p) : clause p c7138 = true :=
  Snake9.LocalRup.prove_clause [c7132, c1388] c7138 (by decide) p (sat_cons (step7132 p h) (sat_cons (step1388 p h) (sat_nil p)))
def c7139 : List Lit := [(38, true)]
theorem step7139 (p : Nat → Bool) (h : Constraints p) : clause p c7139 = true :=
  Snake9.LocalRup.prove_clause [c7133, c7127, c7009] c7139 (by decide) p (sat_cons (step7133 p h) (sat_cons (step7127 p h) (sat_cons (step7009 p h) (sat_nil p))))
def c7140 : List Lit := [(37, false)]
theorem step7140 (p : Nat → Bool) (h : Constraints p) : clause p c7140 = true :=
  Snake9.LocalRup.prove_clause [c7133, c7139, c7127, c6558] c7140 (by decide) p (sat_cons (step7133 p h) (sat_cons (step7139 p h) (sat_cons (step7127 p h) (sat_cons (step6558 p h) (sat_nil p)))))
def c7141 : List Lit := [(1612, true)]
theorem step7141 (p : Nat → Bool) (h : Constraints p) : clause p c7141 = true :=
  Snake9.LocalRup.prove_clause [c7133, c7127, c7126, c6980, c6890] c7141 (by decide) p (sat_cons (step7133 p h) (sat_cons (step7127 p h) (sat_cons (step7126 p h) (sat_cons (step6980 p h) (sat_cons (step6890 p h) (sat_nil p))))))
def c7142 : List Lit := [(1585, true)]
theorem step7142 (p : Nat → Bool) (h : Constraints p) : clause p c7142 = true :=
  Snake9.LocalRup.prove_clause [c7136, c2146] c7142 (by decide) p (sat_cons (step7136 p h) (sat_cons (step2146 p h) (sat_nil p)))
def c7143 : List Lit := [(1590, true)]
theorem step7143 (p : Nat → Bool) (h : Constraints p) : clause p c7143 = true :=
  Snake9.LocalRup.prove_clause [c7138, c7142, c1394] c7143 (by decide) p (sat_cons (step7138 p h) (sat_cons (step7142 p h) (sat_cons (step1394 p h) (sat_nil p))))
def c7144 : List Lit := [(42, true)]
theorem step7144 (p : Nat → Bool) (h : Constraints p) : clause p c7144 = true :=
  Snake9.LocalRup.prove_clause [c7139, c6773, c7127, c2603] c7144 (by decide) p (sat_cons (step7139 p h) (sat_cons (step6773 p h) (sat_cons (step7127 p h) (sat_cons (step2603 p h) (sat_nil p)))))
def c7145 : List Lit := [(1616, true)]
theorem step7145 (p : Nat → Bool) (h : Constraints p) : clause p c7145 = true :=
  Snake9.LocalRup.prove_clause [c7141, c1439] c7145 (by decide) p (sat_cons (step7141 p h) (sat_cons (step1439 p h) (sat_nil p)))
def c7146 : List Lit := [(1627, true)]
theorem step7146 (p : Nat → Bool) (h : Constraints p) : clause p c7146 = true :=
  Snake9.LocalRup.prove_clause [c7145, c7131, c1478] c7146 (by decide) p (sat_cons (step7145 p h) (sat_cons (step7131 p h) (sat_cons (step1478 p h) (sat_nil p))))
def c7147 : List Lit := [(1711, true)]
theorem step7147 (p : Nat → Bool) (h : Constraints p) : clause p c7147 = true :=
  Snake9.LocalRup.prove_clause [c7146, c6009, c1639] c7147 (by decide) p (sat_cons (step7146 p h) (sat_cons (step6009 p h) (sat_cons (step1639 p h) (sat_nil p))))
def c7148 : List Lit := [(1570, false)]
theorem step7148 (p : Nat → Bool) (h : Constraints p) : clause p c7148 = true :=
  Snake9.LocalRup.prove_clause [c7147, c2135] c7148 (by decide) p (sat_cons (step7147 p h) (sat_cons (step2135 p h) (sat_nil p)))
def c7149 : List Lit := [(5, false), (1692, true), (1604, false)]
theorem step7149 (p : Nat → Bool) (h : Constraints p) : clause p c7149 = true :=
  Snake9.LocalRup.prove_clause [c7144, c6980, c7138, c7130, c6779, c6900, c7139, c7133, c7127, c6772, c5476, c3779, c189, c2829, c6110, c1200, c1488, c1426, c1202, c1446, c1435, c5861, c2168, c5947] c7149 (by decide) p (sat_cons (step7144 p h) (sat_cons (step6980 p h) (sat_cons (step7138 p h) (sat_cons (step7130 p h) (sat_cons (step6779 p h) (sat_cons (step6900 p h) (sat_cons (step7139 p h) (sat_cons (step7133 p h) (sat_cons (step7127 p h) (sat_cons (step6772 p h) (sat_cons (step5476 p h) (sat_cons (step3779 p h) (sat_cons (step189 p h) (sat_cons (step2829 p h) (sat_cons (step6110 p h) (sat_cons (step1200 p h) (sat_cons (step1488 p h) (sat_cons (step1426 p h) (sat_cons (step1202 p h) (sat_cons (step1446 p h) (sat_cons (step1435 p h) (sat_cons (step5861 p h) (sat_cons (step2168 p h) (sat_cons (step5947 p h) (sat_nil p)))))))))))))))))))))))))
def c7150 : List Lit := [(1614, true), (1692, true)]
theorem step7150 (p : Nat → Bool) (h : Constraints p) : clause p c7150 = true :=
  Snake9.LocalRup.prove_clause [c7139, c7140, c7127, c7133, c6900, c5861, c312, c6852, c1943, c1425, c2168, c1435] c7150 (by decide) p (sat_cons (step7139 p h) (sat_cons (step7140 p h) (sat_cons (step7127 p h) (sat_cons (step7133 p h) (sat_cons (step6900 p h) (sat_cons (step5861 p h) (sat_cons (step312 p h) (sat_cons (step6852 p h) (sat_cons (step1943 p h) (sat_cons (step1425 p h) (sat_cons (step2168 p h) (sat_cons (step1435 p h) (sat_nil p)))))))))))))
def c7151 : List Lit := [(1692, true), (1604, false)]
theorem step7151 (p : Nat → Bool) (h : Constraints p) : clause p c7151 = true :=
  Snake9.LocalRup.prove_clause [c7131, c6009, c6776, c7149, c2449, c2094, c1345, c2132, c1655, c1481, c1446, c7150] c7151 (by decide) p (sat_cons (step7131 p h) (sat_cons (step6009 p h) (sat_cons (step6776 p h) (sat_cons (step7149 p h) (sat_cons (step2449 p h) (sat_cons (step2094 p h) (sat_cons (step1345 p h) (sat_cons (step2132 p h) (sat_cons (step1655 p h) (sat_cons (step1481 p h) (sat_cons (step1446 p h) (sat_cons (step7150 p h) (sat_nil p)))))))))))))
def c7152 : List Lit := [(5, true), (1604, false)]
theorem step7152 (p : Nat → Bool) (h : Constraints p) : clause p c7152 = true :=
  Snake9.LocalRup.prove_clause [c7141, c7131, c6776, c6980, c7148, c7130, c7133, c7127, c7139, c1444, c1479, c7151, c1646, c2133, c1354, c2095, c1098, c2449, c1101, c2094, c2339, c1126, c1345, c1117, c2132, c6086, c1652, c294, c7084, c6856] c7152 (by decide) p (sat_cons (step7141 p h) (sat_cons (step7131 p h) (sat_cons (step6776 p h) (sat_cons (step6980 p h) (sat_cons (step7148 p h) (sat_cons (step7130 p h) (sat_cons (step7133 p h) (sat_cons (step7127 p h) (sat_cons (step7139 p h) (sat_cons (step1444 p h) (sat_cons (step1479 p h) (sat_cons (step7151 p h) (sat_cons (step1646 p h) (sat_cons (step2133 p h) (sat_cons (step1354 p h) (sat_cons (step2095 p h) (sat_cons (step1098 p h) (sat_cons (step2449 p h) (sat_cons (step1101 p h) (sat_cons (step2094 p h) (sat_cons (step2339 p h) (sat_cons (step1126 p h) (sat_cons (step1345 p h) (sat_cons (step1117 p h) (sat_cons (step2132 p h) (sat_cons (step6086 p h) (sat_cons (step1652 p h) (sat_cons (step294 p h) (sat_cons (step7084 p h) (sat_cons (step6856 p h) (sat_nil p)))))))))))))))))))))))))))))))
def c7153 : List Lit := [(1604, false)]
theorem step7153 (p : Nat → Bool) (h : Constraints p) : clause p c7153 = true :=
  Snake9.LocalRup.prove_clause [c7141, c6778, c7143, c7127, c7139, c6773, c7144, c6980, c7134, c7137, c7133, c7135, c7140, c1444, c7151, c1656, c1493, c1414, c7152, c5476, c6586, c189, c1384, c1210, c1201, c1379, c268, c463, c1938] c7153 (by decide) p (sat_cons (step7141 p h) (sat_cons (step6778 p h) (sat_cons (step7143 p h) (sat_cons (step7127 p h) (sat_cons (step7139 p h) (sat_cons (step6773 p h) (sat_cons (step7144 p h) (sat_cons (step6980 p h) (sat_cons (step7134 p h) (sat_cons (step7137 p h) (sat_cons (step7133 p h) (sat_cons (step7135 p h) (sat_cons (step7140 p h) (sat_cons (step1444 p h) (sat_cons (step7151 p h) (sat_cons (step1656 p h) (sat_cons (step1493 p h) (sat_cons (step1414 p h) (sat_cons (step7152 p h) (sat_cons (step5476 p h) (sat_cons (step6586 p h) (sat_cons (step189 p h) (sat_cons (step1384 p h) (sat_cons (step1210 p h) (sat_cons (step1201 p h) (sat_cons (step1379 p h) (sat_cons (step268 p h) (sat_cons (step463 p h) (sat_cons (step1938 p h) (sat_nil p))))))))))))))))))))))))))))))
def c7154 : List Lit := [(1602, false)]
theorem step7154 (p : Nat → Bool) (h : Constraints p) : clause p c7154 = true :=
  Snake9.LocalRup.prove_clause [c7153, c1420] c7154 (by decide) p (sat_cons (step7153 p h) (sat_cons (step1420 p h) (sat_nil p)))
def c7155 : List Lit := [(1490, true)]
theorem step7155 (p : Nat → Bool) (h : Constraints p) : clause p c7155 = true :=
  Snake9.LocalRup.prove_clause [c7154, c7129, c7144, c7067] c7155 (by decide) p (sat_cons (step7154 p h) (sat_cons (step7129 p h) (sat_cons (step7144 p h) (sat_cons (step7067 p h) (sat_nil p)))))
def c7156 : List Lit := [(1568, true)]
theorem step7156 (p : Nat → Bool) (h : Constraints p) : clause p c7156 = true :=
  Snake9.LocalRup.prove_clause [c7155, c6510, c1361] c7156 (by decide) p (sat_cons (step7155 p h) (sat_cons (step6510 p h) (sat_cons (step1361 p h) (sat_nil p))))
def c7157 : List Lit := [(1569, true)]
theorem step7157 (p : Nat → Bool) (h : Constraints p) : clause p c7157 = true :=
  Snake9.LocalRup.prove_clause [c7155, c6776, c1362] c7157 (by decide) p (sat_cons (step7155 p h) (sat_cons (step6776 p h) (sat_cons (step1362 p h) (sat_nil p))))
def c7158 : List Lit := [(1713, false)]
theorem step7158 (p : Nat → Bool) (h : Constraints p) : clause p c7158 = true :=
  Snake9.LocalRup.prove_clause [c7156, c2133] c7158 (by decide) p (sat_cons (step7156 p h) (sat_cons (step2133 p h) (sat_nil p)))
def c7159 : List Lit := [(1712, false)]
theorem step7159 (p : Nat → Bool) (h : Constraints p) : clause p c7159 = true :=
  Snake9.LocalRup.prove_clause [c7157, c2134] c7159 (by decide) p (sat_cons (step7157 p h) (sat_cons (step2134 p h) (sat_nil p)))
def c7160 : List Lit := [(1629, false)]
theorem step7160 (p : Nat → Bool) (h : Constraints p) : clause p c7160 = true :=
  Snake9.LocalRup.prove_clause [c7158, c6009, c1651] c7160 (by decide) p (sat_cons (step7158 p h) (sat_cons (step6009 p h) (sat_cons (step1651 p h) (sat_nil p))))
def c7161 : List Lit := [(1692, false)]
theorem step7161 (p : Nat → Bool) (h : Constraints p) : clause p c7161 = true :=
  Snake9.LocalRup.prove_clause [c7159, c7146, c1640] c7161 (by decide) p (sat_cons (step7159 p h) (sat_cons (step7146 p h) (sat_cons (step1640 p h) (sat_nil p))))
def c7162 : List Lit := [(1618, false)]
theorem step7162 (p : Nat → Bool) (h : Constraints p) : clause p c7162 = true :=
  Snake9.LocalRup.prove_clause [c7160, c7131, c1480] c7162 (by decide) p (sat_cons (step7160 p h) (sat_cons (step7131 p h) (sat_cons (step1480 p h) (sat_nil p))))
def c7163 : List Lit := [(1614, true)]
theorem step7163 (p : Nat → Bool) (h : Constraints p) : clause p c7163 = true :=
  Snake9.LocalRup.prove_clause [c7161, c7150] c7163 (by decide) p (sat_cons (step7161 p h) (sat_cons (step7150 p h) (sat_nil p)))
def c7164 : List Lit := []
theorem step7164 (p : Nat → Bool) (h : Constraints p) : clause p c7164 = true :=
  Snake9.LocalRup.prove_clause [c7162, c7163, c1441] c7164 (by decide) p (sat_cons (step7162 p h) (sat_cons (step7163 p h) (sat_cons (step1441 p h) (sat_nil p))))
end B112E004
