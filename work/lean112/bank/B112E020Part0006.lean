import B112E020Part0005
namespace B112E020
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1996 : List Lit := [(1548, false), (1630, true)]
theorem step1996 (p : Nat → Bool) (h : Constraints p) : clause p c1996 = true :=
  Snake9.LocalRup.prove_clause [c1769, c1245] c1996 (by decide) p (sat_cons (step1769 p h) (sat_cons (step1245 p h) (sat_nil p)))
def c1997 : List Lit := [(1549, false), (1631, true)]
theorem step1997 (p : Nat → Bool) (h : Constraints p) : clause p c1997 = true :=
  Snake9.LocalRup.prove_clause [c1769, c1251] c1997 (by decide) p (sat_cons (step1769 p h) (sat_cons (step1251 p h) (sat_nil p)))
def c1998 : List Lit := [(1550, false), (1632, true)]
theorem step1998 (p : Nat → Bool) (h : Constraints p) : clause p c1998 = true :=
  Snake9.LocalRup.prove_clause [c1769, c1256] c1998 (by decide) p (sat_cons (step1769 p h) (sat_cons (step1256 p h) (sat_nil p)))
def c1999 : List Lit := [(1551, false), (1633, true)]
theorem step1999 (p : Nat → Bool) (h : Constraints p) : clause p c1999 = true :=
  Snake9.LocalRup.prove_clause [c1769, c1261] c1999 (by decide) p (sat_cons (step1769 p h) (sat_cons (step1261 p h) (sat_nil p)))
def c2000 : List Lit := [(1683, false), (1692, true)]
theorem step2000 (p : Nat → Bool) (h : Constraints p) : clause p c2000 = true :=
  Snake9.LocalRup.prove_clause [c1648, c1352] c2000 (by decide) p (sat_cons (step1648 p h) (sat_cons (step1352 p h) (sat_nil p)))
def c2001 : List Lit := [(1684, false), (1693, true)]
theorem step2001 (p : Nat → Bool) (h : Constraints p) : clause p c2001 = true :=
  Snake9.LocalRup.prove_clause [c1648, c1353] c2001 (by decide) p (sat_cons (step1648 p h) (sat_cons (step1353 p h) (sat_nil p)))
def c2002 : List Lit := [(1685, false), (1694, true)]
theorem step2002 (p : Nat → Bool) (h : Constraints p) : clause p c2002 = true :=
  Snake9.LocalRup.prove_clause [c1648, c1354] c2002 (by decide) p (sat_cons (step1648 p h) (sat_cons (step1354 p h) (sat_nil p)))
def c2003 : List Lit := [(1686, false), (1695, true)]
theorem step2003 (p : Nat → Bool) (h : Constraints p) : clause p c2003 = true :=
  Snake9.LocalRup.prove_clause [c1648, c1355] c2003 (by decide) p (sat_cons (step1648 p h) (sat_cons (step1355 p h) (sat_nil p)))
def c2004 : List Lit := [(1760, false), (1777, true)]
theorem step2004 (p : Nat → Bool) (h : Constraints p) : clause p c2004 = true :=
  Snake9.LocalRup.prove_clause [c1652, c1510] c2004 (by decide) p (sat_cons (step1652 p h) (sat_cons (step1510 p h) (sat_nil p)))
def c2005 : List Lit := [(1761, false), (1778, true)]
theorem step2005 (p : Nat → Bool) (h : Constraints p) : clause p c2005 = true :=
  Snake9.LocalRup.prove_clause [c1652, c1511] c2005 (by decide) p (sat_cons (step1652 p h) (sat_cons (step1511 p h) (sat_nil p)))
def c2006 : List Lit := [(1762, false), (1779, true)]
theorem step2006 (p : Nat → Bool) (h : Constraints p) : clause p c2006 = true :=
  Snake9.LocalRup.prove_clause [c1652, c1512] c2006 (by decide) p (sat_cons (step1652 p h) (sat_cons (step1512 p h) (sat_nil p)))
def c2007 : List Lit := [(1763, false), (1780, true)]
theorem step2007 (p : Nat → Bool) (h : Constraints p) : clause p c2007 = true :=
  Snake9.LocalRup.prove_clause [c1652, c1513] c2007 (by decide) p (sat_cons (step1652 p h) (sat_cons (step1513 p h) (sat_nil p)))
def c2008 : List Lit := [(1776, true), (1692, false)]
theorem step2008 (p : Nat → Bool) (h : Constraints p) : clause p c2008 = true :=
  Snake9.LocalRup.prove_clause [c1704, c1514] c2008 (by decide) p (sat_cons (step1704 p h) (sat_cons (step1514 p h) (sat_nil p)))
def c2009 : List Lit := [(1777, true), (1693, false)]
theorem step2009 (p : Nat → Bool) (h : Constraints p) : clause p c2009 = true :=
  Snake9.LocalRup.prove_clause [c1704, c1520] c2009 (by decide) p (sat_cons (step1704 p h) (sat_cons (step1520 p h) (sat_nil p)))
def c2010 : List Lit := [(1778, true), (1694, false)]
theorem step2010 (p : Nat → Bool) (h : Constraints p) : clause p c2010 = true :=
  Snake9.LocalRup.prove_clause [c1704, c1526] c2010 (by decide) p (sat_cons (step1704 p h) (sat_cons (step1526 p h) (sat_nil p)))
def c2011 : List Lit := [(1779, true), (1695, false)]
theorem step2011 (p : Nat → Bool) (h : Constraints p) : clause p c2011 = true :=
  Snake9.LocalRup.prove_clause [c1704, c1531] c2011 (by decide) p (sat_cons (step1704 p h) (sat_cons (step1531 p h) (sat_nil p)))
def c2012 : List Lit := [(1780, true), (1696, false)]
theorem step2012 (p : Nat → Bool) (h : Constraints p) : clause p c2012 = true :=
  Snake9.LocalRup.prove_clause [c1704, c1535] c2012 (by decide) p (sat_cons (step1704 p h) (sat_cons (step1535 p h) (sat_nil p)))
def c2013 : List Lit := [(1697, false), (1781, true)]
theorem step2013 (p : Nat → Bool) (h : Constraints p) : clause p c2013 = true :=
  Snake9.LocalRup.prove_clause [c1704, c1539] c2013 (by decide) p (sat_cons (step1704 p h) (sat_cons (step1539 p h) (sat_nil p)))
def c2014 : List Lit := [(1698, false), (1782, true)]
theorem step2014 (p : Nat → Bool) (h : Constraints p) : clause p c2014 = true :=
  Snake9.LocalRup.prove_clause [c1704, c1542] c2014 (by decide) p (sat_cons (step1704 p h) (sat_cons (step1542 p h) (sat_nil p)))
def c2015 : List Lit := [(1699, false), (1783, true)]
theorem step2015 (p : Nat → Bool) (h : Constraints p) : clause p c2015 = true :=
  Snake9.LocalRup.prove_clause [c1704, c1543] c2015 (by decide) p (sat_cons (step1704 p h) (sat_cons (step1543 p h) (sat_nil p)))
def c2016 : List Lit := [(1629, false), (1783, false)]
theorem step2016 (p : Nat → Bool) (h : Constraints p) : clause p c2016 = true :=
  Snake9.LocalRup.prove_clause [c1552, c1544] c2016 (by decide) p (sat_cons (step1552 p h) (sat_cons (step1544 p h) (sat_nil p)))
def c2017 : List Lit := [(1630, false), (1782, false)]
theorem step2017 (p : Nat → Bool) (h : Constraints p) : clause p c2017 = true :=
  Snake9.LocalRup.prove_clause [c1552, c1545] c2017 (by decide) p (sat_cons (step1552 p h) (sat_cons (step1545 p h) (sat_nil p)))
def c2018 : List Lit := [(1631, false), (1781, false)]
theorem step2018 (p : Nat → Bool) (h : Constraints p) : clause p c2018 = true :=
  Snake9.LocalRup.prove_clause [c1552, c1546] c2018 (by decide) p (sat_cons (step1552 p h) (sat_cons (step1546 p h) (sat_nil p)))
def c2019 : List Lit := [(1632, false), (1780, false)]
theorem step2019 (p : Nat → Bool) (h : Constraints p) : clause p c2019 = true :=
  Snake9.LocalRup.prove_clause [c1552, c1547] c2019 (by decide) p (sat_cons (step1552 p h) (sat_cons (step1547 p h) (sat_nil p)))
def c2020 : List Lit := [(1633, false), (1779, false)]
theorem step2020 (p : Nat → Bool) (h : Constraints p) : clause p c2020 = true :=
  Snake9.LocalRup.prove_clause [c1552, c1548] c2020 (by decide) p (sat_cons (step1552 p h) (sat_cons (step1548 p h) (sat_nil p)))
def c2021 : List Lit := [(1634, false), (1778, false)]
theorem step2021 (p : Nat → Bool) (h : Constraints p) : clause p c2021 = true :=
  Snake9.LocalRup.prove_clause [c1552, c1549] c2021 (by decide) p (sat_cons (step1552 p h) (sat_cons (step1549 p h) (sat_nil p)))
def c2022 : List Lit := [(1635, false), (1777, false)]
theorem step2022 (p : Nat → Bool) (h : Constraints p) : clause p c2022 = true :=
  Snake9.LocalRup.prove_clause [c1552, c1550] c2022 (by decide) p (sat_cons (step1552 p h) (sat_cons (step1550 p h) (sat_nil p)))
def c2023 : List Lit := [(1636, false), (1776, false)]
theorem step2023 (p : Nat → Bool) (h : Constraints p) : clause p c2023 = true :=
  Snake9.LocalRup.prove_clause [c1552, c1551] c2023 (by decide) p (sat_cons (step1552 p h) (sat_cons (step1551 p h) (sat_nil p)))
def c2024 : List Lit := [(1513, true), (1502, false), (5, true), (12, true)]
theorem step2024 (p : Nat → Bool) (h : Constraints p) : clause p c2024 = true :=
  Snake9.LocalRup.prove_clause [c1016, c1019, c1024, c1030, c1044, c1040, c1020, c1031, c1018, c1026, c1785] c2024 (by decide) p (sat_cons (step1016 p h) (sat_cons (step1019 p h) (sat_cons (step1024 p h) (sat_cons (step1030 p h) (sat_cons (step1044 p h) (sat_cons (step1040 p h) (sat_cons (step1020 p h) (sat_cons (step1031 p h) (sat_cons (step1018 p h) (sat_cons (step1026 p h) (sat_cons (step1785 p h) (sat_nil p))))))))))))
def c2025 : List Lit := [(259, true), (6, false), (3, true), (22, true), (5, true)]
theorem step2025 (p : Nat → Bool) (h : Constraints p) : clause p c2025 = true :=
  Snake9.LocalRup.prove_clause [c830, c831, c829, c825, c828, c824, c19, c8, c1794] c2025 (by decide) p (sat_cons (step830 p h) (sat_cons (step831 p h) (sat_cons (step829 p h) (sat_cons (step825 p h) (sat_cons (step828 p h) (sat_cons (step824 p h) (sat_cons (step19 p h) (sat_cons (step8 p h) (sat_cons (step1794 p h) (sat_nil p))))))))))
def c2026 : List Lit := [(91, false), (1760, true), (75, false), (86, true), (1739, false)]
theorem step2026 (p : Nat → Bool) (h : Constraints p) : clause p c2026 = true :=
  Snake9.LocalRup.prove_clause [c1905, c1776, c572] c2026 (by decide) p (sat_cons (step1905 p h) (sat_cons (step1776 p h) (sat_cons (step572 p h) (sat_nil p))))
def c2027 : List Lit := [(76, false), (1677, false), (1685, true), (77, true), (30, false)]
theorem step2027 (p : Nat → Bool) (h : Constraints p) : clause p c2027 = true :=
  Snake9.LocalRup.prove_clause [c1888, c462, c461, c1326, c1316, c1334, c1318, c1343] c2027 (by decide) p (sat_cons (step1888 p h) (sat_cons (step462 p h) (sat_cons (step461 p h) (sat_cons (step1326 p h) (sat_cons (step1316 p h) (sat_cons (step1334 p h) (sat_cons (step1318 p h) (sat_cons (step1343 p h) (sat_nil p)))))))))
def c2028 : List Lit := [(1661, true), (73, true), (66, true), (67, true)]
theorem step2028 (p : Nat → Bool) (h : Constraints p) : clause p c2028 = true :=
  Snake9.LocalRup.prove_clause [c1277, c1279, c1285, c1292, c1296, c1288, c1286, c1268, c1270, c1278, c1281, c1265, c1262, c1710] c2028 (by decide) p (sat_cons (step1277 p h) (sat_cons (step1279 p h) (sat_cons (step1285 p h) (sat_cons (step1292 p h) (sat_cons (step1296 p h) (sat_cons (step1288 p h) (sat_cons (step1286 p h) (sat_cons (step1268 p h) (sat_cons (step1270 p h) (sat_cons (step1278 p h) (sat_cons (step1281 p h) (sat_cons (step1265 p h) (sat_cons (step1262 p h) (sat_cons (step1710 p h) (sat_nil p)))))))))))))))
def c2029 : List Lit := [(1677, false), (1684, true), (1685, true), (77, true), (30, false)]
theorem step2029 (p : Nat → Bool) (h : Constraints p) : clause p c2029 = true :=
  Snake9.LocalRup.prove_clause [c1331, c2027, c1342, c1312, c1320] c2029 (by decide) p (sat_cons (step1331 p h) (sat_cons (step2027 p h) (sat_cons (step1342 p h) (sat_cons (step1312 p h) (sat_cons (step1320 p h) (sat_nil p))))))
def c2030 : List Lit := [(1759, true), (78, false), (82, true), (83, false), (1731, false), (118, true)]
theorem step2030 (p : Nat → Bool) (h : Constraints p) : clause p c2030 = true :=
  Snake9.LocalRup.prove_clause [c1689, c1749, c1891, c1698, c455, c1439] c2030 (by decide) p (sat_cons (step1689 p h) (sat_cons (step1749 p h) (sat_cons (step1891 p h) (sat_cons (step1698 p h) (sat_cons (step455 p h) (sat_cons (step1439 p h) (sat_nil p)))))))
def c2031 : List Lit := [(1660, true), (66, true), (67, true)]
theorem step2031 (p : Nat → Bool) (h : Constraints p) : clause p c2031 = true :=
  Snake9.LocalRup.prove_clause [c1277, c1284, c1291, c1295, c1287, c1285, c1268, c1270, c1278, c1280, c1265, c1262, c1710] c2031 (by decide) p (sat_cons (step1277 p h) (sat_cons (step1284 p h) (sat_cons (step1291 p h) (sat_cons (step1295 p h) (sat_cons (step1287 p h) (sat_cons (step1285 p h) (sat_cons (step1268 p h) (sat_cons (step1270 p h) (sat_cons (step1278 p h) (sat_cons (step1280 p h) (sat_cons (step1265 p h) (sat_cons (step1262 p h) (sat_cons (step1710 p h) (sat_nil p))))))))))))))
def c2032 : List Lit := [(58, true), (1660, true), (67, true)]
theorem step2032 (p : Nat → Bool) (h : Constraints p) : clause p c2032 = true :=
  Snake9.LocalRup.prove_clause [c1299, c1273, c1263, c1264, c1270, c1271, c1295, c1265, c1282, c1284, c1280, c1276, c1710] c2032 (by decide) p (sat_cons (step1299 p h) (sat_cons (step1273 p h) (sat_cons (step1263 p h) (sat_cons (step1264 p h) (sat_cons (step1270 p h) (sat_cons (step1271 p h) (sat_cons (step1295 p h) (sat_cons (step1265 p h) (sat_cons (step1282 p h) (sat_cons (step1284 p h) (sat_cons (step1280 p h) (sat_cons (step1276 p h) (sat_cons (step1710 p h) (sat_nil p))))))))))))))
def c2033 : List Lit := [(84, false), (1761, true), (1732, false), (1739, false), (122, false), (69, false)]
theorem step2033 (p : Nat → Bool) (h : Constraints p) : clause p c2033 = true :=
  Snake9.LocalRup.prove_clause [c726, c1739, c1394, c1483, c1401, c1407] c2033 (by decide) p (sat_cons (step726 p h) (sat_cons (step1739 p h) (sat_cons (step1394 p h) (sat_cons (step1483 p h) (sat_cons (step1401 p h) (sat_cons (step1407 p h) (sat_nil p)))))))
def c2034 : List Lit := [(1723, true), (1732, false), (1753, true), (122, false), (118, true), (69, false)]
theorem step2034 (p : Nat → Bool) (h : Constraints p) : clause p c2034 = true :=
  Snake9.LocalRup.prove_clause [c1407, c1411, c1399, c1401, c1663, c1386, c1388, c1397, c1394, c1383, c1380, c1691, c730, c731, c651, c1439, c1441, c1428, c1449, c1436, c1473] c2034 (by decide) p (sat_cons (step1407 p h) (sat_cons (step1411 p h) (sat_cons (step1399 p h) (sat_cons (step1401 p h) (sat_cons (step1663 p h) (sat_cons (step1386 p h) (sat_cons (step1388 p h) (sat_cons (step1397 p h) (sat_cons (step1394 p h) (sat_cons (step1383 p h) (sat_cons (step1380 p h) (sat_cons (step1691 p h) (sat_cons (step730 p h) (sat_cons (step731 p h) (sat_cons (step651 p h) (sat_cons (step1439 p h) (sat_cons (step1441 p h) (sat_cons (step1428 p h) (sat_cons (step1449 p h) (sat_cons (step1436 p h) (sat_cons (step1473 p h) (sat_nil p))))))))))))))))))))))
def c2035 : List Lit := [(1740, false), (1732, false), (69, false), (122, false), (1752, true)]
theorem step2035 (p : Nat → Bool) (h : Constraints p) : clause p c2035 = true :=
  Snake9.LocalRup.prove_clause [c1723, c734, c735, c1427, c1441, c1435, c1449, c1468] c2035 (by decide) p (sat_cons (step1723 p h) (sat_cons (step734 p h) (sat_cons (step735 p h) (sat_cons (step1427 p h) (sat_cons (step1441 p h) (sat_cons (step1435 p h) (sat_cons (step1449 p h) (sat_cons (step1468 p h) (sat_nil p)))))))))
def c2036 : List Lit := [(121, true), (1742, true), (1737, false), (116, false), (1761, true), (122, false), (1739, false), (69, false)]
theorem step2036 (p : Nat → Bool) (h : Constraints p) : clause p c2036 = true :=
  Snake9.LocalRup.prove_clause [c1441, c1442, c1446, c732, c1467, c1394, c1489, c1401, c1408, c1412, c1404, c1402, c1386, c1388, c1395, c1397, c1383, c1691, c1681] c2036 (by decide) p (sat_cons (step1441 p h) (sat_cons (step1442 p h) (sat_cons (step1446 p h) (sat_cons (step732 p h) (sat_cons (step1467 p h) (sat_cons (step1394 p h) (sat_cons (step1489 p h) (sat_cons (step1401 p h) (sat_cons (step1408 p h) (sat_cons (step1412 p h) (sat_cons (step1404 p h) (sat_cons (step1402 p h) (sat_cons (step1386 p h) (sat_cons (step1388 p h) (sat_cons (step1395 p h) (sat_cons (step1397 p h) (sat_cons (step1383 p h) (sat_cons (step1691 p h) (sat_cons (step1681 p h) (sat_nil p))))))))))))))))))))
def c2037 : List Lit := [(1742, true), (1737, false), (69, false), (116, false), (1761, true), (122, false), (1739, false)]
theorem step2037 (p : Nat → Bool) (h : Constraints p) : clause p c2037 = true :=
  Snake9.LocalRup.prove_clause [c2036, c731, c735, c1394, c1440, c1401, c1446, c1467, c1489, c1408, c1412, c1404, c1402, c1386, c1388, c1395, c1397, c1383, c1691, c1681] c2037 (by decide) p (sat_cons (step2036 p h) (sat_cons (step731 p h) (sat_cons (step735 p h) (sat_cons (step1394 p h) (sat_cons (step1440 p h) (sat_cons (step1401 p h) (sat_cons (step1446 p h) (sat_cons (step1467 p h) (sat_cons (step1489 p h) (sat_cons (step1408 p h) (sat_cons (step1412 p h) (sat_cons (step1404 p h) (sat_cons (step1402 p h) (sat_cons (step1386 p h) (sat_cons (step1388 p h) (sat_cons (step1395 p h) (sat_cons (step1397 p h) (sat_cons (step1383 p h) (sat_cons (step1691 p h) (sat_cons (step1681 p h) (sat_nil p)))))))))))))))))))))
def c2038 : List Lit := [(1737, false), (116, false), (1752, true), (1761, true), (122, false), (1739, false), (69, false)]
theorem step2038 (p : Nat → Bool) (h : Constraints p) : clause p c2038 = true :=
  Snake9.LocalRup.prove_clause [c1468, c1447, c2037] c2038 (by decide) p (sat_cons (step1468 p h) (sat_cons (step1447 p h) (sat_cons (step2037 p h) (sat_nil p))))
def c2039 : List Lit := [(1732, false), (1761, true), (122, false), (118, true), (69, false)]
theorem step2039 (p : Nat → Bool) (h : Constraints p) : clause p c2039 = true :=
  Snake9.LocalRup.prove_clause [c1478, c1437, c1434, c2034, c1483, c2035, c1439, c2038, c1435, c1427, c730, c733, c734, c1394, c1442, c1401, c1447, c1463, c1489, c1408, c1412, c1404, c1402, c1386, c1388, c1395, c1397, c1383, c1691, c1681] c2039 (by decide) p (sat_cons (step1478 p h) (sat_cons (step1437 p h) (sat_cons (step1434 p h) (sat_cons (step2034 p h) (sat_cons (step1483 p h) (sat_cons (step2035 p h) (sat_cons (step1439 p h) (sat_cons (step2038 p h) (sat_cons (step1435 p h) (sat_cons (step1427 p h) (sat_cons (step730 p h) (sat_cons (step733 p h) (sat_cons (step734 p h) (sat_cons (step1394 p h) (sat_cons (step1442 p h) (sat_cons (step1401 p h) (sat_cons (step1447 p h) (sat_cons (step1463 p h) (sat_cons (step1489 p h) (sat_cons (step1408 p h) (sat_cons (step1412 p h) (sat_cons (step1404 p h) (sat_cons (step1402 p h) (sat_cons (step1386 p h) (sat_cons (step1388 p h) (sat_cons (step1395 p h) (sat_cons (step1397 p h) (sat_cons (step1383 p h) (sat_cons (step1691 p h) (sat_cons (step1681 p h) (sat_nil p)))))))))))))))))))))))))))))))
def c2040 : List Lit := [(94, false), (115, true), (99, false), (116, false)]
theorem step2040 (p : Nat → Bool) (h : Constraints p) : clause p c2040 = true :=
  Snake9.LocalRup.prove_clause [c1910, c501] c2040 (by decide) p (sat_cons (step1910 p h) (sat_cons (step501 p h) (sat_nil p)))
def c2041 : List Lit := [(104, false), (115, true), (113, false), (116, false), (1732, true)]
theorem step2041 (p : Nat → Bool) (h : Constraints p) : clause p c2041 = true :=
  Snake9.LocalRup.prove_clause [c1920, c1919, c526, c548, c1425] c2041 (by decide) p (sat_cons (step1920 p h) (sat_cons (step1919 p h) (sat_cons (step526 p h) (sat_cons (step548 p h) (sat_cons (step1425 p h) (sat_nil p))))))
def c2042 : List Lit := [(100, true), (1712, false), (1717, false), (1733, false), (1761, true), (116, false), (1739, false)]
theorem step2042 (p : Nat → Bool) (h : Constraints p) : clause p c2042 = true :=
  Snake9.LocalRup.prove_clause [c1445, c1429, c1456, c1505, c1419, c1405, c1394, c1395, c1402, c1403, c1418, c1500, c1461, c1457, c1432, c1446, c1423, c1440, c1692] c2042 (by decide) p (sat_cons (step1445 p h) (sat_cons (step1429 p h) (sat_cons (step1456 p h) (sat_cons (step1505 p h) (sat_cons (step1419 p h) (sat_cons (step1405 p h) (sat_cons (step1394 p h) (sat_cons (step1395 p h) (sat_cons (step1402 p h) (sat_cons (step1403 p h) (sat_cons (step1418 p h) (sat_cons (step1500 p h) (sat_cons (step1461 p h) (sat_cons (step1457 p h) (sat_cons (step1432 p h) (sat_cons (step1446 p h) (sat_cons (step1423 p h) (sat_cons (step1440 p h) (sat_cons (step1692 p h) (sat_nil p))))))))))))))))))))
def c2043 : List Lit := [(91, false), (108, true), (92, false), (107, false)]
theorem step2043 (p : Nat → Bool) (h : Constraints p) : clause p c2043 = true :=
  Snake9.LocalRup.prove_clause [c1904, c489] c2043 (by decide) p (sat_cons (step1904 p h) (sat_cons (step489 p h) (sat_nil p)))
def c2044 : List Lit := [(1591, false), (1599, true), (53, true)]
theorem step2044 (p : Nat → Bool) (h : Constraints p) : clause p c2044 = true :=
  Snake9.LocalRup.prove_clause [c1183, c1166, c1176, c1179, c1187, c1168, c1658] c2044 (by decide) p (sat_cons (step1183 p h) (sat_cons (step1166 p h) (sat_cons (step1176 p h) (sat_cons (step1179 p h) (sat_cons (step1187 p h) (sat_cons (step1168 p h) (sat_cons (step1658 p h) (sat_nil p))))))))
def c2045 : List Lit := [(98, true), (44, true), (89, false), (92, false), (120, true), (100, false), (1709, true), (122, false)]
theorem step2045 (p : Nat → Bool) (h : Constraints p) : clause p c2045 = true :=
  Snake9.LocalRup.prove_clause [c1384, c1383, c1906, c1915, c1695, c518, c1914] c2045 (by decide) p (sat_cons (step1384 p h) (sat_cons (step1383 p h) (sat_cons (step1906 p h) (sat_cons (step1915 p h) (sat_cons (step1695 p h) (sat_cons (step518 p h) (sat_cons (step1914 p h) (sat_nil p))))))))
def c2046 : List Lit := [(44, false), (96, false), (45, false), (1598, true), (1582, false)]
theorem step2046 (p : Nat → Bool) (h : Constraints p) : clause p c2046 = true :=
  Snake9.LocalRup.prove_clause [c226, c224, c1167, c1153, c1174, c1161, c1189] c2046 (by decide) p (sat_cons (step226 p h) (sat_cons (step224 p h) (sat_cons (step1167 p h) (sat_cons (step1153 p h) (sat_cons (step1174 p h) (sat_cons (step1161 p h) (sat_cons (step1189 p h) (sat_nil p))))))))
def c2047 : List Lit := [(1574, true), (1556, false)]
theorem step2047 (p : Nat → Bool) (h : Constraints p) : clause p c2047 = true :=
  Snake9.LocalRup.prove_clause [c1117, c1977, c1141, c1118, c1112, c1771, c1770, c1124, c1132] c2047 (by decide) p (sat_cons (step1117 p h) (sat_cons (step1977 p h) (sat_cons (step1141 p h) (sat_cons (step1118 p h) (sat_cons (step1112 p h) (sat_cons (step1771 p h) (sat_cons (step1770 p h) (sat_cons (step1124 p h) (sat_cons (step1132 p h) (sat_nil p))))))))))
def c2048 : List Lit := [(1569, true), (34, false)]
theorem step2048 (p : Nat → Bool) (h : Constraints p) : clause p c2048 = true :=
  Snake9.LocalRup.prove_clause [c1771, c1124, c1770, c1132] c2048 (by decide) p (sat_cons (step1771 p h) (sat_cons (step1124 p h) (sat_cons (step1770 p h) (sat_cons (step1132 p h) (sat_nil p)))))
def c2049 : List Lit := [(1525, true), (29, false), (31, false), (75, false)]
theorem step2049 (p : Nat → Bool) (h : Constraints p) : clause p c2049 = true :=
  Snake9.LocalRup.prove_clause [c1058, c1059, c80, c79, c1813] c2049 (by decide) p (sat_cons (step1058 p h) (sat_cons (step1059 p h) (sat_cons (step80 p h) (sat_cons (step79 p h) (sat_cons (step1813 p h) (sat_nil p))))))
def c2050 : List Lit := [(34, true), (21, false), (22, false), (1561, true)]
theorem step2050 (p : Nat → Bool) (h : Constraints p) : clause p c2050 = true :=
  Snake9.LocalRup.prove_clause [c1116, c1114, c1722, c80, c1827] c2050 (by decide) p (sat_cons (step1116 p h) (sat_cons (step1114 p h) (sat_cons (step1722 p h) (sat_cons (step80 p h) (sat_cons (step1827 p h) (sat_nil p))))))
def c2051 : List Lit := [(1525, true), (31, false), (30, false)]
theorem step2051 (p : Nat → Bool) (h : Constraints p) : clause p c2051 = true :=
  Snake9.LocalRup.prove_clause [c1058, c1059, c179, c80, c1827] c2051 (by decide) p (sat_cons (step1058 p h) (sat_cons (step1059 p h) (sat_cons (step179 p h) (sat_cons (step80 p h) (sat_cons (step1827 p h) (sat_nil p))))))
def c2052 : List Lit := [(1652, false), (1649, false), (22, false), (1669, false), (1697, true)]
theorem step2052 (p : Nat → Bool) (h : Constraints p) : clause p c2052 = true :=
  Snake9.LocalRup.prove_clause [c1318, c1341, c1375, c1307, c1287, c1288, c1306, c1279, c1372, c1883, c445, c1345, c1312, c1321] c2052 (by decide) p (sat_cons (step1318 p h) (sat_cons (step1341 p h) (sat_cons (step1375 p h) (sat_cons (step1307 p h) (sat_cons (step1287 p h) (sat_cons (step1288 p h) (sat_cons (step1306 p h) (sat_cons (step1279 p h) (sat_cons (step1372 p h) (sat_cons (step1883 p h) (sat_cons (step445 p h) (sat_cons (step1345 p h) (sat_cons (step1312 p h) (sat_cons (step1321 p h) (sat_nil p)))))))))))))))
def c2053 : List Lit := [(49, false), (46, false), (66, false), (1586, true)]
theorem step2053 (p : Nat → Bool) (h : Constraints p) : clause p c2053 = true :=
  Snake9.LocalRup.prove_clause [c1762, c237, c1162, c1153] c2053 (by decide) p (sat_cons (step1762 p h) (sat_cons (step237 p h) (sat_cons (step1162 p h) (sat_cons (step1153 p h) (sat_nil p)))))
def c2054 : List Lit := [(66, false), (113, false), (107, false), (67, true), (1593, true), (1586, true)]
theorem step2054 (p : Nat → Bool) (h : Constraints p) : clause p c2054 = true :=
  Snake9.LocalRup.prove_clause [c688, c1871, c1872, c283, c1169, c2053, c1175, c1167] c2054 (by decide) p (sat_cons (step688 p h) (sat_cons (step1871 p h) (sat_cons (step1872 p h) (sat_cons (step283 p h) (sat_cons (step1169 p h) (sat_cons (step2053 p h) (sat_cons (step1175 p h) (sat_cons (step1167 p h) (sat_nil p)))))))))
def c2055 : List Lit := [(1585, true), (46, false), (48, true), (49, false), (1582, false)]
theorem step2055 (p : Nat → Bool) (h : Constraints p) : clause p c2055 = true :=
  Snake9.LocalRup.prove_clause [c1159, c1161, c1157, c1153, c233] c2055 (by decide) p (sat_cons (step1159 p h) (sat_cons (step1161 p h) (sat_cons (step1157 p h) (sat_cons (step1153 p h) (sat_cons (step233 p h) (sat_nil p))))))
def c2056 : List Lit := [(1537, true), (30, false), (24, true), (18, true), (1525, false)]
theorem step2056 (p : Nat → Bool) (h : Constraints p) : clause p c2056 = true :=
  Snake9.LocalRup.prove_clause [c1062, c1067, c1049, c1644, c1077, c1081, c1068, c1645, c1056, c1063, c1051, c1642, c63, c138, c1806] c2056 (by decide) p (sat_cons (step1062 p h) (sat_cons (step1067 p h) (sat_cons (step1049 p h) (sat_cons (step1644 p h) (sat_cons (step1077 p h) (sat_cons (step1081 p h) (sat_cons (step1068 p h) (sat_cons (step1645 p h) (sat_cons (step1056 p h) (sat_cons (step1063 p h) (sat_cons (step1051 p h) (sat_cons (step1642 p h) (sat_cons (step63 p h) (sat_cons (step138 p h) (sat_cons (step1806 p h) (sat_nil p))))))))))))))))
def c2057 : List Lit := [(1575, true), (31, true), (1556, false)]
theorem step2057 (p : Nat → Bool) (h : Constraints p) : clause p c2057 = true :=
  Snake9.LocalRup.prove_clause [c1113, c1118, c1978, c1145, c1119, c2048, c1114] c2057 (by decide) p (sat_cons (step1113 p h) (sat_cons (step1118 p h) (sat_cons (step1978 p h) (sat_cons (step1145 p h) (sat_cons (step1119 p h) (sat_cons (step2048 p h) (sat_cons (step1114 p h) (sat_nil p))))))))
def c2058 : List Lit := [(44, true), (49, false), (1585, true), (39, true), (45, false)]
theorem step2058 (p : Nat → Bool) (h : Constraints p) : clause p c2058 = true :=
  Snake9.LocalRup.prove_clause [c1840, c1851, c262, c1155, c2055] c2058 (by decide) p (sat_cons (step1840 p h) (sat_cons (step1851 p h) (sat_cons (step262 p h) (sat_cons (step1155 p h) (sat_cons (step2055 p h) (sat_nil p))))))
def c2059 : List Lit := [(1749, true), (110, true), (107, true), (1739, false), (69, false)]
theorem step2059 (p : Nat → Bool) (h : Constraints p) : clause p c2059 = true :=
  Snake9.LocalRup.prove_clause [c1424, c1431, c1445, c1461, c1457, c1434, c1432, c1446, c1425, c1427, c1440, c612, c734, c1927] c2059 (by decide) p (sat_cons (step1424 p h) (sat_cons (step1431 p h) (sat_cons (step1445 p h) (sat_cons (step1461 p h) (sat_cons (step1457 p h) (sat_cons (step1434 p h) (sat_cons (step1432 p h) (sat_cons (step1446 p h) (sat_cons (step1425 p h) (sat_cons (step1427 p h) (sat_cons (step1440 p h) (sat_cons (step612 p h) (sat_cons (step734 p h) (sat_cons (step1927 p h) (sat_nil p)))))))))))))))
end B112E020
