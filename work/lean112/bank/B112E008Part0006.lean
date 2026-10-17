import B112E008Part0005
namespace B112E008
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1991 : List Lit := [(395, false), (425, false)]
theorem step1991 (p : Nat → Bool) (h : Constraints p) : clause p c1991 = true :=
  Snake9.LocalRup.prove_clause [c1616, c951] c1991 (by decide) p (sat_cons (step1616 p h) (sat_cons (step951 p h) (sat_nil p)))
def c1992 : List Lit := [(431, false), (437, false)]
theorem step1992 (p : Nat → Bool) (h : Constraints p) : clause p c1992 = true :=
  Snake9.LocalRup.prove_clause [c1630, c959] c1992 (by decide) p (sat_cons (step1630 p h) (sat_cons (step959 p h) (sat_nil p)))
def c1993 : List Lit := [(447, false), (449, false)]
theorem step1993 (p : Nat → Bool) (h : Constraints p) : clause p c1993 = true :=
  Snake9.LocalRup.prove_clause [c1641, c966] c1993 (by decide) p (sat_cons (step1641 p h) (sat_cons (step966 p h) (sat_nil p)))
def c1994 : List Lit := [(439, false), (453, false)]
theorem step1994 (p : Nat → Bool) (h : Constraints p) : clause p c1994 = true :=
  Snake9.LocalRup.prove_clause [c1620, c973] c1994 (by decide) p (sat_cons (step1620 p h) (sat_cons (step973 p h) (sat_nil p)))
def c1995 : List Lit := [(457, false), (459, false)]
theorem step1995 (p : Nat → Bool) (h : Constraints p) : clause p c1995 = true :=
  Snake9.LocalRup.prove_clause [c1640, c979] c1995 (by decide) p (sat_cons (step1640 p h) (sat_cons (step979 p h) (sat_nil p)))
def c1996 : List Lit := [(461, false), (467, false)]
theorem step1996 (p : Nat → Bool) (h : Constraints p) : clause p c1996 = true :=
  Snake9.LocalRup.prove_clause [c1628, c984] c1996 (by decide) p (sat_cons (step1628 p h) (sat_cons (step984 p h) (sat_nil p)))
def c1997 : List Lit := [(241, false), (242, false)]
theorem step1997 (p : Nat → Bool) (h : Constraints p) : clause p c1997 = true :=
  Snake9.LocalRup.prove_clause [c1646, c988] c1997 (by decide) p (sat_cons (step1646 p h) (sat_cons (step988 p h) (sat_nil p)))
def c1998 : List Lit := [(469, false), (483, false)]
theorem step1998 (p : Nat → Bool) (h : Constraints p) : clause p c1998 = true :=
  Snake9.LocalRup.prove_clause [c1619, c1001] c1998 (by decide) p (sat_cons (step1619 p h) (sat_cons (step1001 p h) (sat_nil p)))
def c1999 : List Lit := [(455, false), (485, false)]
theorem step1999 (p : Nat → Bool) (h : Constraints p) : clause p c1999 = true :=
  Snake9.LocalRup.prove_clause [c1615, c1006] c1999 (by decide) p (sat_cons (step1615 p h) (sat_cons (step1006 p h) (sat_nil p)))
def c2000 : List Lit := [(427, false), (487, false)]
theorem step2000 (p : Nat → Bool) (h : Constraints p) : clause p c2000 = true :=
  Snake9.LocalRup.prove_clause [c1613, c1011] c2000 (by decide) p (sat_cons (step1613 p h) (sat_cons (step1011 p h) (sat_nil p)))
def c2001 : List Lit := [(367, false), (489, false)]
theorem step2001 (p : Nat → Bool) (h : Constraints p) : clause p c2001 = true :=
  Snake9.LocalRup.prove_clause [c1016, c1014] c2001 (by decide) p (sat_cons (step1016 p h) (sat_cons (step1014 p h) (sat_nil p)))
def c2002 : List Lit := [(1600, false), (1605, true)]
theorem step2002 (p : Nat → Bool) (h : Constraints p) : clause p c2002 = true :=
  Snake9.LocalRup.prove_clause [c1663, c1199] c2002 (by decide) p (sat_cons (step1663 p h) (sat_cons (step1199 p h) (sat_nil p)))
def c2003 : List Lit := [(1601, false), (1606, true)]
theorem step2003 (p : Nat → Bool) (h : Constraints p) : clause p c2003 = true :=
  Snake9.LocalRup.prove_clause [c1663, c1200] c2003 (by decide) p (sat_cons (step1663 p h) (sat_cons (step1200 p h) (sat_nil p)))
def c2004 : List Lit := [(1602, false), (1607, true)]
theorem step2004 (p : Nat → Bool) (h : Constraints p) : clause p c2004 = true :=
  Snake9.LocalRup.prove_clause [c1663, c1201] c2004 (by decide) p (sat_cons (step1663 p h) (sat_cons (step1201 p h) (sat_nil p)))
def c2005 : List Lit := [(1603, false), (1608, true)]
theorem step2005 (p : Nat → Bool) (h : Constraints p) : clause p c2005 = true :=
  Snake9.LocalRup.prove_clause [c1663, c1202] c2005 (by decide) p (sat_cons (step1663 p h) (sat_cons (step1202 p h) (sat_nil p)))
def c2006 : List Lit := [(1581, false), (1614, true)]
theorem step2006 (p : Nat → Bool) (h : Constraints p) : clause p c2006 = true :=
  Snake9.LocalRup.prove_clause [c1664, c1221] c2006 (by decide) p (sat_cons (step1664 p h) (sat_cons (step1221 p h) (sat_nil p)))
def c2007 : List Lit := [(1615, true), (1582, false)]
theorem step2007 (p : Nat → Bool) (h : Constraints p) : clause p c2007 = true :=
  Snake9.LocalRup.prove_clause [c1664, c1229] c2007 (by decide) p (sat_cons (step1664 p h) (sat_cons (step1229 p h) (sat_nil p)))
def c2008 : List Lit := [(1616, true), (1583, false)]
theorem step2008 (p : Nat → Bool) (h : Constraints p) : clause p c2008 = true :=
  Snake9.LocalRup.prove_clause [c1664, c1235] c2008 (by decide) p (sat_cons (step1664 p h) (sat_cons (step1235 p h) (sat_nil p)))
def c2009 : List Lit := [(1617, true), (1584, false)]
theorem step2009 (p : Nat → Bool) (h : Constraints p) : clause p c2009 = true :=
  Snake9.LocalRup.prove_clause [c1664, c1240] c2009 (by decide) p (sat_cons (step1664 p h) (sat_cons (step1240 p h) (sat_nil p)))
def c2010 : List Lit := [(1618, true), (1585, false)]
theorem step2010 (p : Nat → Bool) (h : Constraints p) : clause p c2010 = true :=
  Snake9.LocalRup.prove_clause [c1664, c1245] c2010 (by decide) p (sat_cons (step1664 p h) (sat_cons (step1245 p h) (sat_nil p)))
def c2011 : List Lit := [(1586, false), (1619, true)]
theorem step2011 (p : Nat → Bool) (h : Constraints p) : clause p c2011 = true :=
  Snake9.LocalRup.prove_clause [c1664, c1248] c2011 (by decide) p (sat_cons (step1664 p h) (sat_cons (step1248 p h) (sat_nil p)))
def c2012 : List Lit := [(1637, true), (1556, false)]
theorem step2012 (p : Nat → Bool) (h : Constraints p) : clause p c2012 = true :=
  Snake9.LocalRup.prove_clause [c1665, c1273] c2012 (by decide) p (sat_cons (step1665 p h) (sat_cons (step1273 p h) (sat_nil p)))
def c2013 : List Lit := [(1557, false), (1638, true)]
theorem step2013 (p : Nat → Bool) (h : Constraints p) : clause p c2013 = true :=
  Snake9.LocalRup.prove_clause [c1665, c1279] c2013 (by decide) p (sat_cons (step1665 p h) (sat_cons (step1279 p h) (sat_nil p)))
def c2014 : List Lit := [(60, true), (1653, true)]
theorem step2014 (p : Nat → Bool) (h : Constraints p) : clause p c2014 = true :=
  Snake9.LocalRup.prove_clause [c1659, c1291] c2014 (by decide) p (sat_cons (step1659 p h) (sat_cons (step1291 p h) (sat_nil p)))
def c2015 : List Lit := [(1660, false), (1665, true)]
theorem step2015 (p : Nat → Bool) (h : Constraints p) : clause p c2015 = true :=
  Snake9.LocalRup.prove_clause [c1660, c1308] c2015 (by decide) p (sat_cons (step1660 p h) (sat_cons (step1308 p h) (sat_nil p)))
def c2016 : List Lit := [(1661, false), (1666, true)]
theorem step2016 (p : Nat → Bool) (h : Constraints p) : clause p c2016 = true :=
  Snake9.LocalRup.prove_clause [c1660, c1309] c2016 (by decide) p (sat_cons (step1660 p h) (sat_cons (step1309 p h) (sat_nil p)))
def c2017 : List Lit := [(1653, false), (1665, true)]
theorem step2017 (p : Nat → Bool) (h : Constraints p) : clause p c2017 = true :=
  Snake9.LocalRup.prove_clause [c1657, c1310] c2017 (by decide) p (sat_cons (step1657 p h) (sat_cons (step1310 p h) (sat_nil p)))
def c2018 : List Lit := [(1654, false), (1666, true)]
theorem step2018 (p : Nat → Bool) (h : Constraints p) : clause p c2018 = true :=
  Snake9.LocalRup.prove_clause [c1657, c1313] c2018 (by decide) p (sat_cons (step1657 p h) (sat_cons (step1313 p h) (sat_nil p)))
def c2019 : List Lit := [(1688, false), (1697, true)]
theorem step2019 (p : Nat → Bool) (h : Constraints p) : clause p c2019 = true :=
  Snake9.LocalRup.prove_clause [c1658, c1353] c2019 (by decide) p (sat_cons (step1658 p h) (sat_cons (step1353 p h) (sat_nil p)))
def c2020 : List Lit := [(1689, false), (1698, true)]
theorem step2020 (p : Nat → Bool) (h : Constraints p) : clause p c2020 = true :=
  Snake9.LocalRup.prove_clause [c1658, c1354] c2020 (by decide) p (sat_cons (step1658 p h) (sat_cons (step1354 p h) (sat_nil p)))
def c2021 : List Lit := [(1687, false), (1697, true)]
theorem step2021 (p : Nat → Bool) (h : Constraints p) : clause p c2021 = true :=
  Snake9.LocalRup.prove_clause [c1661, c1357] c2021 (by decide) p (sat_cons (step1661 p h) (sat_cons (step1357 p h) (sat_nil p)))
def c2022 : List Lit := [(1688, false), (1698, true)]
theorem step2022 (p : Nat → Bool) (h : Constraints p) : clause p c2022 = true :=
  Snake9.LocalRup.prove_clause [c1661, c1358] c2022 (by decide) p (sat_cons (step1661 p h) (sat_cons (step1358 p h) (sat_nil p)))
def c2023 : List Lit := [(1689, false), (1699, true)]
theorem step2023 (p : Nat → Bool) (h : Constraints p) : clause p c2023 = true :=
  Snake9.LocalRup.prove_clause [c1661, c1359] c2023 (by decide) p (sat_cons (step1661 p h) (sat_cons (step1359 p h) (sat_nil p)))
def c2024 : List Lit := [(1690, false), (1700, true)]
theorem step2024 (p : Nat → Bool) (h : Constraints p) : clause p c2024 = true :=
  Snake9.LocalRup.prove_clause [c1661, c1360] c2024 (by decide) p (sat_cons (step1661 p h) (sat_cons (step1360 p h) (sat_nil p)))
def c2025 : List Lit := [(1691, false), (1701, true)]
theorem step2025 (p : Nat → Bool) (h : Constraints p) : clause p c2025 = true :=
  Snake9.LocalRup.prove_clause [c1661, c1361] c2025 (by decide) p (sat_cons (step1661 p h) (sat_cons (step1361 p h) (sat_nil p)))
def c2026 : List Lit := [(1763, false), (1781, true)]
theorem step2026 (p : Nat → Bool) (h : Constraints p) : clause p c2026 = true :=
  Snake9.LocalRup.prove_clause [c1666, c1504] c2026 (by decide) p (sat_cons (step1666 p h) (sat_cons (step1504 p h) (sat_nil p)))
def c2027 : List Lit := [(1764, false), (1782, true)]
theorem step2027 (p : Nat → Bool) (h : Constraints p) : clause p c2027 = true :=
  Snake9.LocalRup.prove_clause [c1666, c1505] c2027 (by decide) p (sat_cons (step1666 p h) (sat_cons (step1505 p h) (sat_nil p)))
def c2028 : List Lit := [(1761, false), (1780, true)]
theorem step2028 (p : Nat → Bool) (h : Constraints p) : clause p c2028 = true :=
  Snake9.LocalRup.prove_clause [c1772, c1507] c2028 (by decide) p (sat_cons (step1772 p h) (sat_cons (step1507 p h) (sat_nil p)))
def c2029 : List Lit := [(1762, false), (1781, true)]
theorem step2029 (p : Nat → Bool) (h : Constraints p) : clause p c2029 = true :=
  Snake9.LocalRup.prove_clause [c1772, c1508] c2029 (by decide) p (sat_cons (step1772 p h) (sat_cons (step1508 p h) (sat_nil p)))
def c2030 : List Lit := [(1763, false), (1782, true)]
theorem step2030 (p : Nat → Bool) (h : Constraints p) : clause p c2030 = true :=
  Snake9.LocalRup.prove_clause [c1772, c1509] c2030 (by decide) p (sat_cons (step1772 p h) (sat_cons (step1509 p h) (sat_nil p)))
def c2031 : List Lit := [(1764, false), (1783, true)]
theorem step2031 (p : Nat → Bool) (h : Constraints p) : clause p c2031 = true :=
  Snake9.LocalRup.prove_clause [c1772, c1510] c2031 (by decide) p (sat_cons (step1772 p h) (sat_cons (step1510 p h) (sat_nil p)))
def c2032 : List Lit := [(1765, false), (1784, true)]
theorem step2032 (p : Nat → Bool) (h : Constraints p) : clause p c2032 = true :=
  Snake9.LocalRup.prove_clause [c1772, c1511] c2032 (by decide) p (sat_cons (step1772 p h) (sat_cons (step1511 p h) (sat_nil p)))
def c2033 : List Lit := [(1699, false), (1780, true)]
theorem step2033 (p : Nat → Bool) (h : Constraints p) : clause p c2033 = true :=
  Snake9.LocalRup.prove_clause [c1735, c1525] c2033 (by decide) p (sat_cons (step1735 p h) (sat_cons (step1525 p h) (sat_nil p)))
def c2034 : List Lit := [(1700, false), (1781, true)]
theorem step2034 (p : Nat → Bool) (h : Constraints p) : clause p c2034 = true :=
  Snake9.LocalRup.prove_clause [c1735, c1532] c2034 (by decide) p (sat_cons (step1735 p h) (sat_cons (step1532 p h) (sat_nil p)))
def c2035 : List Lit := [(1701, false), (1782, true)]
theorem step2035 (p : Nat → Bool) (h : Constraints p) : clause p c2035 = true :=
  Snake9.LocalRup.prove_clause [c1735, c1538] c2035 (by decide) p (sat_cons (step1735 p h) (sat_cons (step1538 p h) (sat_nil p)))
def c2036 : List Lit := [(1702, false), (1783, true)]
theorem step2036 (p : Nat → Bool) (h : Constraints p) : clause p c2036 = true :=
  Snake9.LocalRup.prove_clause [c1735, c1541] c2036 (by decide) p (sat_cons (step1735 p h) (sat_cons (step1541 p h) (sat_nil p)))
def c2037 : List Lit := [(1635, false), (1786, false)]
theorem step2037 (p : Nat → Bool) (h : Constraints p) : clause p c2037 = true :=
  Snake9.LocalRup.prove_clause [c1550, c1542] c2037 (by decide) p (sat_cons (step1550 p h) (sat_cons (step1542 p h) (sat_nil p)))
def c2038 : List Lit := [(1636, false), (1785, false)]
theorem step2038 (p : Nat → Bool) (h : Constraints p) : clause p c2038 = true :=
  Snake9.LocalRup.prove_clause [c1550, c1543] c2038 (by decide) p (sat_cons (step1550 p h) (sat_cons (step1543 p h) (sat_nil p)))
def c2039 : List Lit := [(1637, false), (1784, false)]
theorem step2039 (p : Nat → Bool) (h : Constraints p) : clause p c2039 = true :=
  Snake9.LocalRup.prove_clause [c1550, c1544] c2039 (by decide) p (sat_cons (step1550 p h) (sat_cons (step1544 p h) (sat_nil p)))
def c2040 : List Lit := [(1638, false), (1783, false)]
theorem step2040 (p : Nat → Bool) (h : Constraints p) : clause p c2040 = true :=
  Snake9.LocalRup.prove_clause [c1550, c1545] c2040 (by decide) p (sat_cons (step1550 p h) (sat_cons (step1545 p h) (sat_nil p)))
def c2041 : List Lit := [(1639, false), (1782, false)]
theorem step2041 (p : Nat → Bool) (h : Constraints p) : clause p c2041 = true :=
  Snake9.LocalRup.prove_clause [c1550, c1546] c2041 (by decide) p (sat_cons (step1550 p h) (sat_cons (step1546 p h) (sat_nil p)))
def c2042 : List Lit := [(1640, false), (1781, false)]
theorem step2042 (p : Nat → Bool) (h : Constraints p) : clause p c2042 = true :=
  Snake9.LocalRup.prove_clause [c1550, c1547] c2042 (by decide) p (sat_cons (step1550 p h) (sat_cons (step1547 p h) (sat_nil p)))
def c2043 : List Lit := [(1641, false), (1780, false)]
theorem step2043 (p : Nat → Bool) (h : Constraints p) : clause p c2043 = true :=
  Snake9.LocalRup.prove_clause [c1550, c1548] c2043 (by decide) p (sat_cons (step1550 p h) (sat_cons (step1548 p h) (sat_nil p)))
def c2044 : List Lit := [(1642, false), (1779, false)]
theorem step2044 (p : Nat → Bool) (h : Constraints p) : clause p c2044 = true :=
  Snake9.LocalRup.prove_clause [c1550, c1549] c2044 (by decide) p (sat_cons (step1550 p h) (sat_cons (step1549 p h) (sat_nil p)))
def c2045 : List Lit := [(1519, true), (12, true)]
theorem step2045 (p : Nat → Bool) (h : Constraints p) : clause p c2045 = true :=
  Snake9.LocalRup.prove_clause [c1029, c1031, c1039, c1042, c1788, c1032, c1034, c1022, c1030, c1025, c57, c1818] c2045 (by decide) p (sat_cons (step1029 p h) (sat_cons (step1031 p h) (sat_cons (step1039 p h) (sat_cons (step1042 p h) (sat_cons (step1788 p h) (sat_cons (step1032 p h) (sat_cons (step1034 p h) (sat_cons (step1022 p h) (sat_cons (step1030 p h) (sat_cons (step1025 p h) (sat_cons (step57 p h) (sat_cons (step1818 p h) (sat_nil p)))))))))))))
def c2046 : List Lit := [(1564, false), (1594, true), (1583, true), (1574, false), (51, true), (43, true), (47, false), (103, false), (33, true)]
theorem step2046 (p : Nat → Bool) (h : Constraints p) : clause p c2046 = true :=
  Snake9.LocalRup.prove_clause [c1138, c1161, c1122, c1127, c1128, c1157, c1123, c1141, c1801] c2046 (by decide) p (sat_cons (step1138 p h) (sat_cons (step1161 p h) (sat_cons (step1122 p h) (sat_cons (step1127 p h) (sat_cons (step1128 p h) (sat_cons (step1157 p h) (sat_cons (step1123 p h) (sat_cons (step1141 p h) (sat_cons (step1801 p h) (sat_nil p))))))))))
def c2047 : List Lit := [(29, false), (1526, true), (15, false), (83, false)]
theorem step2047 (p : Nat → Bool) (h : Constraints p) : clause p c2047 = true :=
  Snake9.LocalRup.prove_clause [c87, c86, c1055] c2047 (by decide) p (sat_cons (step87 p h) (sat_cons (step86 p h) (sat_cons (step1055 p h) (sat_nil p))))
def c2048 : List Lit := [(1564, false), (1618, true), (1574, false), (51, true), (43, true), (47, false), (103, false), (1600, false), (33, true)]
theorem step2048 (p : Nat → Bool) (h : Constraints p) : clause p c2048 = true :=
  Snake9.LocalRup.prove_clause [c2002, c1241, c1172, c1122, c1127, c1793, c1158, c1232, c1144, c1209, c2046, c1237, c1204, c1176, c1178, c1174, c1169, c293, c1880, c1132, c1134, c1141, c209, c1162, c1123, c1128] c2048 (by decide) p (sat_cons (step2002 p h) (sat_cons (step1241 p h) (sat_cons (step1172 p h) (sat_cons (step1122 p h) (sat_cons (step1127 p h) (sat_cons (step1793 p h) (sat_cons (step1158 p h) (sat_cons (step1232 p h) (sat_cons (step1144 p h) (sat_cons (step1209 p h) (sat_cons (step2046 p h) (sat_cons (step1237 p h) (sat_cons (step1204 p h) (sat_cons (step1176 p h) (sat_cons (step1178 p h) (sat_cons (step1174 p h) (sat_cons (step1169 p h) (sat_cons (step293 p h) (sat_cons (step1880 p h) (sat_cons (step1132 p h) (sat_cons (step1134 p h) (sat_cons (step1141 p h) (sat_cons (step209 p h) (sat_cons (step1162 p h) (sat_cons (step1123 p h) (sat_cons (step1128 p h) (sat_nil p)))))))))))))))))))))))))))
def c2049 : List Lit := [(1569, false), (1617, true), (1574, false), (51, true), (47, false), (103, false), (1600, false)]
theorem step2049 (p : Nat → Bool) (h : Constraints p) : clause p c2049 = true :=
  Snake9.LocalRup.prove_clause [c2002, c1236, c1138, c1156, c1157, c1231, c1141, c1204, c1132, c1176, c293, c1174] c2049 (by decide) p (sat_cons (step2002 p h) (sat_cons (step1236 p h) (sat_cons (step1138 p h) (sat_cons (step1156 p h) (sat_cons (step1157 p h) (sat_cons (step1231 p h) (sat_cons (step1141 p h) (sat_cons (step1204 p h) (sat_cons (step1132 p h) (sat_cons (step1176 p h) (sat_cons (step293 p h) (sat_cons (step1174 p h) (sat_nil p)))))))))))))
def c2050 : List Lit := [(105, false), (104, false), (1722, true), (83, false), (101, false), (99, false)]
theorem step2050 (p : Nat → Bool) (h : Constraints p) : clause p c2050 = true :=
  Snake9.LocalRup.prove_clause [c639, c660, c1395, c1398, c1403] c2050 (by decide) p (sat_cons (step639 p h) (sat_cons (step660 p h) (sat_cons (step1395 p h) (sat_cons (step1398 p h) (sat_cons (step1403 p h) (sat_nil p))))))
def c2051 : List Lit := [(104, false), (1722, true), (83, false), (101, false), (99, false)]
theorem step2051 (p : Nat → Bool) (h : Constraints p) : clause p c2051 = true :=
  Snake9.LocalRup.prove_clause [c1401, c2050, c1397, c1399, c1403, c656, c1395] c2051 (by decide) p (sat_cons (step1401 p h) (sat_cons (step2050 p h) (sat_cons (step1397 p h) (sat_cons (step1399 p h) (sat_cons (step1403 p h) (sat_cons (step656 p h) (sat_cons (step1395 p h) (sat_nil p))))))))
def c2052 : List Lit := [(1593, true), (40, false), (1573, true), (34, false), (51, true), (100, false), (47, false), (103, false)]
theorem step2052 (p : Nat → Bool) (h : Constraints p) : clause p c2052 = true :=
  Snake9.LocalRup.prove_clause [c1176, c1697, c1174, c269, c1880, c293, c209, c1134] c2052 (by decide) p (sat_cons (step1176 p h) (sat_cons (step1697 p h) (sat_cons (step1174 p h) (sat_cons (step269 p h) (sat_cons (step1880 p h) (sat_cons (step293 p h) (sat_cons (step209 p h) (sat_cons (step1134 p h) (sat_nil p)))))))))
def c2053 : List Lit := [(45, false), (43, true), (35, false), (34, false)]
theorem step2053 (p : Nat → Bool) (h : Constraints p) : clause p c2053 = true :=
  Snake9.LocalRup.prove_clause [c1880, c209] c2053 (by decide) p (sat_cons (step1880 p h) (sat_cons (step209 p h) (sat_nil p)))
def c2054 : List Lit := [(1507, true), (15, true), (40, false), (34, false)]
theorem step2054 (p : Nat → Bool) (h : Constraints p) : clause p c2054 = true :=
  Snake9.LocalRup.prove_clause [c1020, c1022, c1017, c225, c13, c1812] c2054 (by decide) p (sat_cons (step1020 p h) (sat_cons (step1022 p h) (sat_cons (step1017 p h) (sat_cons (step225 p h) (sat_cons (step13 p h) (sat_cons (step1812 p h) (sat_nil p)))))))
end B112E008
