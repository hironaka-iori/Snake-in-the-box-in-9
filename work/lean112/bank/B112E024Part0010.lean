import B112E024Part0009
namespace B112E024
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2002 : List Lit := [(1520, true), (1507, false)]
theorem step2002 (p : Nat → Bool) (h : Constraints p) : clause p c2002 = true :=
  Snake9.LocalRup.prove_clause [c1720, c916] c2002 (by decide) p (sat_cons (step1720 p h) (sat_cons (step916 p h) (sat_nil p)))
def c2003 : List Lit := [(1508, false), (1521, true)]
theorem step2003 (p : Nat → Bool) (h : Constraints p) : clause p c2003 = true :=
  Snake9.LocalRup.prove_clause [c1720, c919] c2003 (by decide) p (sat_cons (step1720 p h) (sat_cons (step919 p h) (sat_nil p)))
def c2004 : List Lit := [(1509, false), (1522, true)]
theorem step2004 (p : Nat → Bool) (h : Constraints p) : clause p c2004 = true :=
  Snake9.LocalRup.prove_clause [c1720, c922] c2004 (by decide) p (sat_cons (step1720 p h) (sat_cons (step922 p h) (sat_nil p)))
def c2005 : List Lit := [(1543, false), (1552, true)]
theorem step2005 (p : Nat → Bool) (h : Constraints p) : clause p c2005 = true :=
  Snake9.LocalRup.prove_clause [c1724, c972] c2005 (by decide) p (sat_cons (step1724 p h) (sat_cons (step972 p h) (sat_nil p)))
def c2006 : List Lit := [(1553, true), (1544, false)]
theorem step2006 (p : Nat → Bool) (h : Constraints p) : clause p c2006 = true :=
  Snake9.LocalRup.prove_clause [c1724, c973] c2006 (by decide) p (sat_cons (step1724 p h) (sat_cons (step973 p h) (sat_nil p)))
def c2007 : List Lit := [(1545, false), (1554, true)]
theorem step2007 (p : Nat → Bool) (h : Constraints p) : clause p c2007 = true :=
  Snake9.LocalRup.prove_clause [c1724, c974] c2007 (by decide) p (sat_cons (step1724 p h) (sat_cons (step974 p h) (sat_nil p)))
def c2008 : List Lit := [(1546, false), (1555, true)]
theorem step2008 (p : Nat → Bool) (h : Constraints p) : clause p c2008 = true :=
  Snake9.LocalRup.prove_clause [c1724, c975] c2008 (by decide) p (sat_cons (step1724 p h) (sat_cons (step975 p h) (sat_nil p)))
def c2009 : List Lit := [(1547, false), (1556, true)]
theorem step2009 (p : Nat → Bool) (h : Constraints p) : clause p c2009 = true :=
  Snake9.LocalRup.prove_clause [c1724, c976] c2009 (by decide) p (sat_cons (step1724 p h) (sat_cons (step976 p h) (sat_nil p)))
def c2010 : List Lit := [(1552, true), (1519, false)]
theorem step2010 (p : Nat → Bool) (h : Constraints p) : clause p c2010 = true :=
  Snake9.LocalRup.prove_clause [c1954, c977] c2010 (by decide) p (sat_cons (step1954 p h) (sat_cons (step977 p h) (sat_nil p)))
def c2011 : List Lit := [(1553, true), (1520, false)]
theorem step2011 (p : Nat → Bool) (h : Constraints p) : clause p c2011 = true :=
  Snake9.LocalRup.prove_clause [c1954, c983] c2011 (by decide) p (sat_cons (step1954 p h) (sat_cons (step983 p h) (sat_nil p)))
def c2012 : List Lit := [(1521, false), (1554, true)]
theorem step2012 (p : Nat → Bool) (h : Constraints p) : clause p c2012 = true :=
  Snake9.LocalRup.prove_clause [c1954, c988] c2012 (by decide) p (sat_cons (step1954 p h) (sat_cons (step988 p h) (sat_nil p)))
def c2013 : List Lit := [(1522, false), (1555, true)]
theorem step2013 (p : Nat → Bool) (h : Constraints p) : clause p c2013 = true :=
  Snake9.LocalRup.prove_clause [c1954, c993] c2013 (by decide) p (sat_cons (step1954 p h) (sat_cons (step993 p h) (sat_nil p)))
def c2014 : List Lit := [(1523, false), (1556, true)]
theorem step2014 (p : Nat → Bool) (h : Constraints p) : clause p c2014 = true :=
  Snake9.LocalRup.prove_clause [c1954, c997] c2014 (by decide) p (sat_cons (step1954 p h) (sat_cons (step997 p h) (sat_nil p)))
def c2015 : List Lit := [(1573, true), (1492, false)]
theorem step2015 (p : Nat → Bool) (h : Constraints p) : clause p c2015 = true :=
  Snake9.LocalRup.prove_clause [c1955, c1011] c2015 (by decide) p (sat_cons (step1955 p h) (sat_cons (step1011 p h) (sat_nil p)))
def c2016 : List Lit := [(1574, true), (1493, false)]
theorem step2016 (p : Nat → Bool) (h : Constraints p) : clause p c2016 = true :=
  Snake9.LocalRup.prove_clause [c1955, c1019] c2016 (by decide) p (sat_cons (step1955 p h) (sat_cons (step1019 p h) (sat_nil p)))
def c2017 : List Lit := [(1494, false), (1575, true)]
theorem step2017 (p : Nat → Bool) (h : Constraints p) : clause p c2017 = true :=
  Snake9.LocalRup.prove_clause [c1955, c1027] c2017 (by decide) p (sat_cons (step1955 p h) (sat_cons (step1027 p h) (sat_nil p)))
def c2018 : List Lit := [(1495, false), (1576, true)]
theorem step2018 (p : Nat → Bool) (h : Constraints p) : clause p c2018 = true :=
  Snake9.LocalRup.prove_clause [c1955, c1034] c2018 (by decide) p (sat_cons (step1955 p h) (sat_cons (step1034 p h) (sat_nil p)))
def c2019 : List Lit := [(1496, false), (1577, true)]
theorem step2019 (p : Nat → Bool) (h : Constraints p) : clause p c2019 = true :=
  Snake9.LocalRup.prove_clause [c1955, c1039] c2019 (by decide) p (sat_cons (step1955 p h) (sat_cons (step1039 p h) (sat_nil p)))
def c2020 : List Lit := [(1723, true), (1705, false)]
theorem step2020 (p : Nat → Bool) (h : Constraints p) : clause p c2020 = true :=
  Snake9.LocalRup.prove_clause [c1744, c1262] c2020 (by decide) p (sat_cons (step1744 p h) (sat_cons (step1262 p h) (sat_nil p)))
def c2021 : List Lit := [(1724, true), (1706, false)]
theorem step2021 (p : Nat → Bool) (h : Constraints p) : clause p c2021 = true :=
  Snake9.LocalRup.prove_clause [c1744, c1263] c2021 (by decide) p (sat_cons (step1744 p h) (sat_cons (step1263 p h) (sat_nil p)))
def c2022 : List Lit := [(1725, true), (1707, false)]
theorem step2022 (p : Nat → Bool) (h : Constraints p) : clause p c2022 = true :=
  Snake9.LocalRup.prove_clause [c1744, c1264] c2022 (by decide) p (sat_cons (step1744 p h) (sat_cons (step1264 p h) (sat_nil p)))
def c2023 : List Lit := [(1726, true), (1708, false)]
theorem step2023 (p : Nat → Bool) (h : Constraints p) : clause p c2023 = true :=
  Snake9.LocalRup.prove_clause [c1744, c1265] c2023 (by decide) p (sat_cons (step1744 p h) (sat_cons (step1265 p h) (sat_nil p)))
def c2024 : List Lit := [(1709, false), (1727, true)]
theorem step2024 (p : Nat → Bool) (h : Constraints p) : clause p c2024 = true :=
  Snake9.LocalRup.prove_clause [c1744, c1266] c2024 (by decide) p (sat_cons (step1744 p h) (sat_cons (step1266 p h) (sat_nil p)))
def c2025 : List Lit := [(1553, true), (1539, false)]
theorem step2025 (p : Nat → Bool) (h : Constraints p) : clause p c2025 = true :=
  Snake9.LocalRup.prove_clause [c1720, c1435] c2025 (by decide) p (sat_cons (step1720 p h) (sat_cons (step1435 p h) (sat_nil p)))
def c2026 : List Lit := [(1553, true), (1538, false), (1519, false), (1504, false)]
theorem step2026 (p : Nat → Bool) (h : Constraints p) : clause p c2026 = true :=
  Snake9.LocalRup.prove_clause [c1720, c1477] c2026 (by decide) p (sat_cons (step1720 p h) (sat_cons (step1477 p h) (sat_nil p)))
def c2027 : List Lit := [(1522, true), (38, true), (161, true), (35, true), (36, true), (1503, false), (15, true), (14, false)]
theorem step2027 (p : Nat → Bool) (h : Constraints p) : clause p c2027 = true :=
  Snake9.LocalRup.prove_clause [c894, c2004, c918, c896, c1975, c888, c1557, c170] c2027 (by decide) p (sat_cons (step894 p h) (sat_cons (step2004 p h) (sat_cons (step918 p h) (sat_cons (step896 p h) (sat_cons (step1975 p h) (sat_cons (step888 p h) (sat_cons (step1557 p h) (sat_cons (step170 p h) (sat_nil p)))))))))
def c2028 : List Lit := [(33, false), (37, false), (38, true), (15, true), (14, false)]
theorem step2028 (p : Nat → Bool) (h : Constraints p) : clause p c2028 = true :=
  Snake9.LocalRup.prove_clause [c1557, c170] c2028 (by decide) p (sat_cons (step1557 p h) (sat_cons (step170 p h) (sat_nil p)))
def c2029 : List Lit := [(1705, true), (20, false), (19, false), (94, true), (1661, false), (15, true)]
theorem step2029 (p : Nat → Bool) (h : Constraints p) : clause p c2029 = true :=
  Snake9.LocalRup.prove_clause [c1148, c1166, c1680, c1894, c1186, c1167, c1162, c1997, c1144, c1153, c1154, c1181, c1149, c1241, c1796, c1675] c2029 (by decide) p (sat_cons (step1148 p h) (sat_cons (step1166 p h) (sat_cons (step1680 p h) (sat_cons (step1894 p h) (sat_cons (step1186 p h) (sat_cons (step1167 p h) (sat_cons (step1162 p h) (sat_cons (step1997 p h) (sat_cons (step1144 p h) (sat_cons (step1153 p h) (sat_cons (step1154 p h) (sat_cons (step1181 p h) (sat_cons (step1149 p h) (sat_cons (step1241 p h) (sat_cons (step1796 p h) (sat_cons (step1675 p h) (sat_nil p)))))))))))))))))
def c2030 : List Lit := [(91, false), (1707, true), (1593, true), (1627, true), (85, false), (88, true), (1666, false), (94, true), (99, true)]
theorem step2030 (p : Nat → Bool) (h : Constraints p) : clause p c2030 = true :=
  Snake9.LocalRup.prove_clause [c1609, c1766, c348, c1144, c1149, c1991, c1154, c1753, c1851, c1161] c2030 (by decide) p (sat_cons (step1609 p h) (sat_cons (step1766 p h) (sat_cons (step348 p h) (sat_cons (step1144 p h) (sat_cons (step1149 p h) (sat_cons (step1991 p h) (sat_cons (step1154 p h) (sat_cons (step1753 p h) (sat_cons (step1851 p h) (sat_cons (step1161 p h) (sat_nil p)))))))))))
def c2031 : List Lit := [(1707, true), (1593, true), (1627, true), (85, false), (88, true), (1666, false), (94, true), (99, true)]
theorem step2031 (p : Nat → Bool) (h : Constraints p) : clause p c2031 = true :=
  Snake9.LocalRup.prove_clause [c1148, c2030, c1145, c1991, c1850, c1753, c1872, c1161, c1146, c1851, c1156] c2031 (by decide) p (sat_cons (step1148 p h) (sat_cons (step2030 p h) (sat_cons (step1145 p h) (sat_cons (step1991 p h) (sat_cons (step1850 p h) (sat_cons (step1753 p h) (sat_cons (step1872 p h) (sat_cons (step1161 p h) (sat_cons (step1146 p h) (sat_cons (step1851 p h) (sat_cons (step1156 p h) (sat_nil p))))))))))))
def c2032 : List Lit := [(1593, true), (1627, true), (85, false), (88, true), (1666, false), (1726, true), (19, false), (94, true), (99, true)]
theorem step2032 (p : Nat → Bool) (h : Constraints p) : clause p c2032 = true :=
  Snake9.LocalRup.prove_clause [c2023, c1683, c1148, c1158, c2031, c1270, c1706, c1093, c1095, c1090, c1091, c1088, c338, c1852, c1497, c1156, c1993, c1494, c1897, c1747, c1193, c1750] c2032 (by decide) p (sat_cons (step2023 p h) (sat_cons (step1683 p h) (sat_cons (step1148 p h) (sat_cons (step1158 p h) (sat_cons (step2031 p h) (sat_cons (step1270 p h) (sat_cons (step1706 p h) (sat_cons (step1093 p h) (sat_cons (step1095 p h) (sat_cons (step1090 p h) (sat_cons (step1091 p h) (sat_cons (step1088 p h) (sat_cons (step338 p h) (sat_cons (step1852 p h) (sat_cons (step1497 p h) (sat_cons (step1156 p h) (sat_cons (step1993 p h) (sat_cons (step1494 p h) (sat_cons (step1897 p h) (sat_cons (step1747 p h) (sat_cons (step1193 p h) (sat_cons (step1750 p h) (sat_nil p)))))))))))))))))))))))
def c2033 : List Lit := [(1654, false), (1707, true), (1666, false), (94, true)]
theorem step2033 (p : Nat → Bool) (h : Constraints p) : clause p c2033 = true :=
  Snake9.LocalRup.prove_clause [c1682, c1192, c1148, c1156, c1157, c1187, c1149, c1252, c1796, c1675] c2033 (by decide) p (sat_cons (step1682 p h) (sat_cons (step1192 p h) (sat_cons (step1148 p h) (sat_cons (step1156 p h) (sat_cons (step1157 p h) (sat_cons (step1187 p h) (sat_cons (step1149 p h) (sat_cons (step1252 p h) (sat_cons (step1796 p h) (sat_cons (step1675 p h) (sat_nil p)))))))))))
def c2034 : List Lit := [(1623, false), (96, false), (1632, true), (1627, true), (85, true), (1666, false), (1726, true), (94, true)]
theorem step2034 (p : Nat → Bool) (h : Constraints p) : clause p c2034 = true :=
  Snake9.LocalRup.prove_clause [c1087, c1894, c1282, c1099, c1096, c1089, c1388, c1108, c1130, c1384, c1067, c1076, c1077, c1909, c1596, c1053, c1061, c1062, c1066, c1056, c1124, c1593, c1275, c302, c1996, c1611, c1145, c345] c2034 (by decide) p (sat_cons (step1087 p h) (sat_cons (step1894 p h) (sat_cons (step1282 p h) (sat_cons (step1099 p h) (sat_cons (step1096 p h) (sat_cons (step1089 p h) (sat_cons (step1388 p h) (sat_cons (step1108 p h) (sat_cons (step1130 p h) (sat_cons (step1384 p h) (sat_cons (step1067 p h) (sat_cons (step1076 p h) (sat_cons (step1077 p h) (sat_cons (step1909 p h) (sat_cons (step1596 p h) (sat_cons (step1053 p h) (sat_cons (step1061 p h) (sat_cons (step1062 p h) (sat_cons (step1066 p h) (sat_cons (step1056 p h) (sat_cons (step1124 p h) (sat_cons (step1593 p h) (sat_cons (step1275 p h) (sat_cons (step302 p h) (sat_cons (step1996 p h) (sat_cons (step1611 p h) (sat_cons (step1145 p h) (sat_cons (step345 p h) (sat_nil p)))))))))))))))))))))))))))))
def c2035 : List Lit := [(1653, true), (86, false), (1666, false), (1726, true), (94, true)]
theorem step2035 (p : Nat → Bool) (h : Constraints p) : clause p c2035 = true :=
  Snake9.LocalRup.prove_clause [c1894, c1282, c1144, c1145, c1852, c1427, c1914, c1087, c1349, c349, c1095, c1089, c1149, c1706, c1098, c1151, c1270, c1725, c1182, c1443, c1248, c370, c371, c1854, c1629, c1223, c1196, c1206, c1712, c1204, c1197, c1198, c1870] c2035 (by decide) p (sat_cons (step1894 p h) (sat_cons (step1282 p h) (sat_cons (step1144 p h) (sat_cons (step1145 p h) (sat_cons (step1852 p h) (sat_cons (step1427 p h) (sat_cons (step1914 p h) (sat_cons (step1087 p h) (sat_cons (step1349 p h) (sat_cons (step349 p h) (sat_cons (step1095 p h) (sat_cons (step1089 p h) (sat_cons (step1149 p h) (sat_cons (step1706 p h) (sat_cons (step1098 p h) (sat_cons (step1151 p h) (sat_cons (step1270 p h) (sat_cons (step1725 p h) (sat_cons (step1182 p h) (sat_cons (step1443 p h) (sat_cons (step1248 p h) (sat_cons (step370 p h) (sat_cons (step371 p h) (sat_cons (step1854 p h) (sat_cons (step1629 p h) (sat_cons (step1223 p h) (sat_cons (step1196 p h) (sat_cons (step1206 p h) (sat_cons (step1712 p h) (sat_cons (step1204 p h) (sat_cons (step1197 p h) (sat_cons (step1198 p h) (sat_cons (step1870 p h) (sat_nil p))))))))))))))))))))))))))))))))))
def c2036 : List Lit := [(1621, true), (84, false), (86, false)]
theorem step2036 (p : Nat → Bool) (h : Constraints p) : clause p c2036 = true :=
  Snake9.LocalRup.prove_clause [c1087, c1088, c340] c2036 (by decide) p (sat_cons (step1087 p h) (sat_cons (step1088 p h) (sat_cons (step340 p h) (sat_nil p))))
def c2037 : List Lit := [(93, false), (99, false), (96, false), (1632, true), (1683, true), (1682, true), (94, true), (1666, false), (1726, true), (86, false)]
theorem step2037 (p : Nat → Bool) (h : Constraints p) : clause p c2037 = true :=
  Snake9.LocalRup.prove_clause [c1389, c1872, c1904, c2034, c1090, c422, c1773, c1901] c2037 (by decide) p (sat_cons (step1389 p h) (sat_cons (step1872 p h) (sat_cons (step1904 p h) (sat_cons (step2034 p h) (sat_cons (step1090 p h) (sat_cons (step422 p h) (sat_cons (step1773 p h) (sat_cons (step1901 p h) (sat_nil p)))))))))
def c2038 : List Lit := [(1673, true), (1593, true), (1666, false), (1707, true), (1726, true), (84, true), (86, false)]
theorem step2038 (p : Nat → Bool) (h : Constraints p) : clause p c2038 = true :=
  Snake9.LocalRup.prove_clause [c1427, c1418, c1148, c1153, c1182, c1248, c1676, c1996, c1275, c1119, c1389, c2033, c2023, c1834, c1850, c1049, c1042, c1759, c1443, c1187, c1183, c1154, c1149, c1920, c478, c479, c1162, c1170, c1160, c2037, c1146, c1609, c420, c1608, c423, c417, c1090, c372, c1849, c1089, c1099] c2038 (by decide) p (sat_cons (step1427 p h) (sat_cons (step1418 p h) (sat_cons (step1148 p h) (sat_cons (step1153 p h) (sat_cons (step1182 p h) (sat_cons (step1248 p h) (sat_cons (step1676 p h) (sat_cons (step1996 p h) (sat_cons (step1275 p h) (sat_cons (step1119 p h) (sat_cons (step1389 p h) (sat_cons (step2033 p h) (sat_cons (step2023 p h) (sat_cons (step1834 p h) (sat_cons (step1850 p h) (sat_cons (step1049 p h) (sat_cons (step1042 p h) (sat_cons (step1759 p h) (sat_cons (step1443 p h) (sat_cons (step1187 p h) (sat_cons (step1183 p h) (sat_cons (step1154 p h) (sat_cons (step1149 p h) (sat_cons (step1920 p h) (sat_cons (step478 p h) (sat_cons (step479 p h) (sat_cons (step1162 p h) (sat_cons (step1170 p h) (sat_cons (step1160 p h) (sat_cons (step2037 p h) (sat_cons (step1146 p h) (sat_cons (step1609 p h) (sat_cons (step420 p h) (sat_cons (step1608 p h) (sat_cons (step423 p h) (sat_cons (step417 p h) (sat_cons (step1090 p h) (sat_cons (step372 p h) (sat_cons (step1849 p h) (sat_cons (step1089 p h) (sat_cons (step1099 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))
def c2039 : List Lit := [(1593, true), (1666, false), (1707, true), (1726, true), (84, true), (86, false)]
theorem step2039 (p : Nat → Bool) (h : Constraints p) : clause p c2039 = true :=
  Snake9.LocalRup.prove_clause [c1427, c1418, c1443, c1850, c2033, c1206, c2038, c1252, c1675, c1216, c1854, c1208, c373, c374, c531, c1608, c1196, c1197, c1146, c1204, c1712, c1198, c1870] c2039 (by decide) p (sat_cons (step1427 p h) (sat_cons (step1418 p h) (sat_cons (step1443 p h) (sat_cons (step1850 p h) (sat_cons (step2033 p h) (sat_cons (step1206 p h) (sat_cons (step2038 p h) (sat_cons (step1252 p h) (sat_cons (step1675 p h) (sat_cons (step1216 p h) (sat_cons (step1854 p h) (sat_cons (step1208 p h) (sat_cons (step373 p h) (sat_cons (step374 p h) (sat_cons (step531 p h) (sat_cons (step1608 p h) (sat_cons (step1196 p h) (sat_cons (step1197 p h) (sat_cons (step1146 p h) (sat_cons (step1204 p h) (sat_cons (step1712 p h) (sat_cons (step1198 p h) (sat_cons (step1870 p h) (sat_nil p))))))))))))))))))))))))
def c2040 : List Lit := [(87, true), (108, false), (93, false), (1682, true)]
theorem step2040 (p : Nat → Bool) (h : Constraints p) : clause p c2040 = true :=
  Snake9.LocalRup.prove_clause [c1712, c1870, c1198, c1204, c1196, c549, c1628] c2040 (by decide) p (sat_cons (step1712 p h) (sat_cons (step1870 p h) (sat_cons (step1198 p h) (sat_cons (step1204 p h) (sat_cons (step1196 p h) (sat_cons (step549 p h) (sat_cons (step1628 p h) (sat_nil p))))))))
def c2041 : List Lit := [(108, false), (93, false), (1682, true), (86, false)]
theorem step2041 (p : Nat → Bool) (h : Constraints p) : clause p c2041 = true :=
  Snake9.LocalRup.prove_clause [c2040, c391, c1196, c1204, c1198, c1199, c1870] c2041 (by decide) p (sat_cons (step2040 p h) (sat_cons (step391 p h) (sat_cons (step1196 p h) (sat_cons (step1204 p h) (sat_cons (step1198 p h) (sat_cons (step1199 p h) (sat_cons (step1870 p h) (sat_nil p))))))))
def c2042 : List Lit := [(1705, true), (1666, false), (1653, false)]
theorem step2042 (p : Nat → Bool) (h : Constraints p) : clause p c2042 = true :=
  Snake9.LocalRup.prove_clause [c1152, c1177, c1680, c1241, c1182, c1675, c1153, c1796, c1147] c2042 (by decide) p (sat_cons (step1152 p h) (sat_cons (step1177 p h) (sat_cons (step1680 p h) (sat_cons (step1241 p h) (sat_cons (step1182 p h) (sat_cons (step1675 p h) (sat_cons (step1153 p h) (sat_cons (step1796 p h) (sat_cons (step1147 p h) (sat_nil p))))))))))
def c2043 : List Lit := [(1593, false), (1666, false), (1726, true), (86, true), (1625, false), (93, true)]
theorem step2043 (p : Nat → Bool) (h : Constraints p) : clause p c2043 = true :=
  Snake9.LocalRup.prove_clause [c1144, c2042, c1282, c1091, c1697, c1275, c1681, c1187, c1725, c1094, c1096, c1092, c1087, c1088, c1488, c1156, c1146, c341, c414, c1609] c2043 (by decide) p (sat_cons (step1144 p h) (sat_cons (step2042 p h) (sat_cons (step1282 p h) (sat_cons (step1091 p h) (sat_cons (step1697 p h) (sat_cons (step1275 p h) (sat_cons (step1681 p h) (sat_cons (step1187 p h) (sat_cons (step1725 p h) (sat_cons (step1094 p h) (sat_cons (step1096 p h) (sat_cons (step1092 p h) (sat_cons (step1087 p h) (sat_cons (step1088 p h) (sat_cons (step1488 p h) (sat_cons (step1156 p h) (sat_cons (step1146 p h) (sat_cons (step341 p h) (sat_cons (step414 p h) (sat_cons (step1609 p h) (sat_nil p)))))))))))))))))))))
def c2044 : List Lit := [(1661, false), (1593, true), (1666, false), (1707, true), (105, true), (1653, false)]
theorem step2044 (p : Nat → Bool) (h : Constraints p) : clause p c2044 = true :=
  Snake9.LocalRup.prove_clause [c1418, c1148, c1153, c1182, c1248, c1676, c1049, c1042, c1759, c1682, c1867, c1149, c1154, c1187, c1188, c1252, c1168, c1675, c1163, c1216, c479, c1209] c2044 (by decide) p (sat_cons (step1418 p h) (sat_cons (step1148 p h) (sat_cons (step1153 p h) (sat_cons (step1182 p h) (sat_cons (step1248 p h) (sat_cons (step1676 p h) (sat_cons (step1049 p h) (sat_cons (step1042 p h) (sat_cons (step1759 p h) (sat_cons (step1682 p h) (sat_cons (step1867 p h) (sat_cons (step1149 p h) (sat_cons (step1154 p h) (sat_cons (step1187 p h) (sat_cons (step1188 p h) (sat_cons (step1252 p h) (sat_cons (step1168 p h) (sat_cons (step1675 p h) (sat_cons (step1163 p h) (sat_cons (step1216 p h) (sat_cons (step479 p h) (sat_cons (step1209 p h) (sat_nil p)))))))))))))))))))))))
def c2045 : List Lit := [(1593, true), (1654, false), (1706, true)]
theorem step2045 (p : Nat → Bool) (h : Constraints p) : clause p c2045 = true :=
  Snake9.LocalRup.prove_clause [c1418, c1848, c1998] c2045 (by decide) p (sat_cons (step1418 p h) (sat_cons (step1848 p h) (sat_cons (step1998 p h) (sat_nil p))))
def c2046 : List Lit := [(1665, false), (108, false), (1694, false), (86, false), (99, false), (1654, false), (1706, true), (1726, true)]
theorem step2046 (p : Nat → Bool) (h : Constraints p) : clause p c2046 = true :=
  Snake9.LocalRup.prove_clause [c1155, c1247, c1182, c2045, c1186, c1998, c1181, c1156, c1241, c1147, c1508, c1282, c1725, c1098, c1089, c419, c344, c1493, c1612, c1161, c490, c1167, c1159] c2046 (by decide) p (sat_cons (step1155 p h) (sat_cons (step1247 p h) (sat_cons (step1182 p h) (sat_cons (step2045 p h) (sat_cons (step1186 p h) (sat_cons (step1998 p h) (sat_cons (step1181 p h) (sat_cons (step1156 p h) (sat_cons (step1241 p h) (sat_cons (step1147 p h) (sat_cons (step1508 p h) (sat_cons (step1282 p h) (sat_cons (step1725 p h) (sat_cons (step1098 p h) (sat_cons (step1089 p h) (sat_cons (step419 p h) (sat_cons (step344 p h) (sat_cons (step1493 p h) (sat_cons (step1612 p h) (sat_cons (step1161 p h) (sat_cons (step490 p h) (sat_cons (step1167 p h) (sat_cons (step1159 p h) (sat_nil p))))))))))))))))))))))))
def c2047 : List Lit := [(108, false), (1694, false), (86, false), (99, false), (1654, false), (1706, true), (1726, true)]
theorem step2047 (p : Nat → Bool) (h : Constraints p) : clause p c2047 = true :=
  Snake9.LocalRup.prove_clause [c2045, c1155, c1180, c1236, c1288, c1717, c1247, c1190, c1157, c2046, c1164, c1166, c1161, c1162, c1159, c1753, c1930, c480, c483, c1148, c1149, c1156, c1920, c1185, c1676, c1242] c2047 (by decide) p (sat_cons (step2045 p h) (sat_cons (step1155 p h) (sat_cons (step1180 p h) (sat_cons (step1236 p h) (sat_cons (step1288 p h) (sat_cons (step1717 p h) (sat_cons (step1247 p h) (sat_cons (step1190 p h) (sat_cons (step1157 p h) (sat_cons (step2046 p h) (sat_cons (step1164 p h) (sat_cons (step1166 p h) (sat_cons (step1161 p h) (sat_cons (step1162 p h) (sat_cons (step1159 p h) (sat_cons (step1753 p h) (sat_cons (step1930 p h) (sat_cons (step480 p h) (sat_cons (step483 p h) (sat_cons (step1148 p h) (sat_cons (step1149 p h) (sat_cons (step1156 p h) (sat_cons (step1920 p h) (sat_cons (step1185 p h) (sat_cons (step1676 p h) (sat_cons (step1242 p h) (sat_nil p)))))))))))))))))))))))))))
def c2048 : List Lit := [(1682, true), (98, false), (108, true), (86, false)]
theorem step2048 (p : Nat → Bool) (h : Constraints p) : clause p c2048 = true :=
  Snake9.LocalRup.prove_clause [c1195, c1206, c1204, c1197, c1198, c1199, c392, c1479] c2048 (by decide) p (sat_cons (step1195 p h) (sat_cons (step1206 p h) (sat_cons (step1204 p h) (sat_cons (step1197 p h) (sat_cons (step1198 p h) (sat_cons (step1199 p h) (sat_cons (step392 p h) (sat_cons (step1479 p h) (sat_nil p)))))))))
def c2049 : List Lit := [(1689, true), (1656, true)]
theorem step2049 (p : Nat → Bool) (h : Constraints p) : clause p c2049 = true :=
  Snake9.LocalRup.prove_clause [c1214, c1216, c1407, c1777, c1796, c1212, c1209, c569, c1149, c1411] c2049 (by decide) p (sat_cons (step1214 p h) (sat_cons (step1216 p h) (sat_cons (step1407 p h) (sat_cons (step1777 p h) (sat_cons (step1796 p h) (sat_cons (step1212 p h) (sat_cons (step1209 p h) (sat_cons (step569 p h) (sat_cons (step1149 p h) (sat_cons (step1411 p h) (sat_nil p)))))))))))
def c2050 : List Lit := [(98, false), (1689, false), (1654, false), (108, true), (86, false), (1706, true), (1726, true)]
theorem step2050 (p : Nat → Bool) (h : Constraints p) : clause p c2050 = true :=
  Snake9.LocalRup.prove_clause [c1155, c1180, c2045, c2048, c1223, c1237, c1242, c1282, c1185, c1725, c1156, c1098, c1147, c1148, c1508, c1089, c490, c344, c1612] c2050 (by decide) p (sat_cons (step1155 p h) (sat_cons (step1180 p h) (sat_cons (step2045 p h) (sat_cons (step2048 p h) (sat_cons (step1223 p h) (sat_cons (step1237 p h) (sat_cons (step1242 p h) (sat_cons (step1282 p h) (sat_cons (step1185 p h) (sat_cons (step1725 p h) (sat_cons (step1156 p h) (sat_cons (step1098 p h) (sat_cons (step1147 p h) (sat_cons (step1148 p h) (sat_cons (step1508 p h) (sat_cons (step1089 p h) (sat_cons (step490 p h) (sat_cons (step344 p h) (sat_cons (step1612 p h) (sat_nil p))))))))))))))))))))
def c2051 : List Lit := [(108, true), (86, false), (1682, true)]
theorem step2051 (p : Nat → Bool) (h : Constraints p) : clause p c2051 = true :=
  Snake9.LocalRup.prove_clause [c1206, c1195, c1197, c1204, c1198, c1199, c552, c1479, c1627, c1352] c2051 (by decide) p (sat_cons (step1206 p h) (sat_cons (step1195 p h) (sat_cons (step1197 p h) (sat_cons (step1204 p h) (sat_cons (step1198 p h) (sat_cons (step1199 p h) (sat_cons (step552 p h) (sat_cons (step1479 p h) (sat_cons (step1627 p h) (sat_cons (step1352 p h) (sat_nil p)))))))))))
def c2052 : List Lit := [(1666, false), (108, false), (86, true), (1726, true), (1593, false), (1682, true), (1694, false)]
theorem step2052 (p : Nat → Bool) (h : Constraints p) : clause p c2052 = true :=
  Snake9.LocalRup.prove_clause [c1091, c1093, c1173, c2043, c1236, c1872, c1288, c1087, c1717, c1096, c1097, c1099, c1725, c1092, c1089, c1282, c416, c2042, c1766, c1145] c2052 (by decide) p (sat_cons (step1091 p h) (sat_cons (step1093 p h) (sat_cons (step1173 p h) (sat_cons (step2043 p h) (sat_cons (step1236 p h) (sat_cons (step1872 p h) (sat_cons (step1288 p h) (sat_cons (step1087 p h) (sat_cons (step1717 p h) (sat_cons (step1096 p h) (sat_cons (step1097 p h) (sat_cons (step1099 p h) (sat_cons (step1725 p h) (sat_cons (step1092 p h) (sat_cons (step1089 p h) (sat_cons (step1282 p h) (sat_cons (step416 p h) (sat_cons (step2042 p h) (sat_cons (step1766 p h) (sat_cons (step1145 p h) (sat_nil p)))))))))))))))))))))
def c2053 : List Lit := [(1663, true), (115, false), (94, false)]
theorem step2053 (p : Nat → Bool) (h : Constraints p) : clause p c2053 = true :=
  Snake9.LocalRup.prove_clause [c1161, c1162, c553, c482, c1639] c2053 (by decide) p (sat_cons (step1161 p h) (sat_cons (step1162 p h) (sat_cons (step553 p h) (sat_cons (step482 p h) (sat_cons (step1639 p h) (sat_nil p))))))
def c2054 : List Lit := [(91, false), (1491, false), (1536, false), (1624, false), (1530, false), (1520, false), (88, false), (53, true), (85, true), (1704, false), (84, false), (99, false), (96, false), (1593, false)]
theorem step2054 (p : Nat → Bool) (h : Constraints p) : clause p c2054 = true :=
  Snake9.LocalRup.prove_clause [c345, c411, c1089, c940, c1100, c950, c1952, c959, c1294, c986, c1689, c1008] c2054 (by decide) p (sat_cons (step345 p h) (sat_cons (step411 p h) (sat_cons (step1089 p h) (sat_cons (step940 p h) (sat_cons (step1100 p h) (sat_cons (step950 p h) (sat_cons (step1952 p h) (sat_cons (step959 p h) (sat_cons (step1294 p h) (sat_cons (step986 p h) (sat_cons (step1689 p h) (sat_cons (step1008 p h) (sat_nil p)))))))))))))
def c2055 : List Lit := [(108, true), (86, true), (1695, true), (1506, false), (100, true), (102, false), (105, true), (87, false), (93, true), (1665, false), (95, true), (114, false), (116, false), (84, false), (98, false), (99, false), (96, false), (1593, false)]
theorem step2055 (p : Nat → Bool) (h : Constraints p) : clause p c2055 = true :=
  Snake9.TreeRup.prove_clause [c1796, c1223, c1206, c1676, c1675, c1144, c1152, c1176, c1236, c1195, c1197, c1204, c389, c383, c1198, c1199, c1087, c939, c542, c552, c1433, c1627, c567, c1208, c1217, c1211, c1212, c562, c574, c510, c1414, c1642, c1617, c1618, c1623, c914, c1761, c1331, c447, c444, c1813, c1092, c942, c1663, c1097, c947, c1717, c958, c985, c1007, c1688, c2054, c1146, c1155, c1181, c1241, c1289, c1295, c1689, c1952, c1008, c1100, c986, c1089, c959, c1480, c950, c940] c2055 (by decide) p (sat_cons (step1796 p h) (sat_cons (step1223 p h) (sat_cons (step1206 p h) (sat_cons (step1676 p h) (sat_cons (step1675 p h) (sat_cons (step1144 p h) (sat_cons (step1152 p h) (sat_cons (step1176 p h) (sat_cons (step1236 p h) (sat_cons (step1195 p h) (sat_cons (step1197 p h) (sat_cons (step1204 p h) (sat_cons (step389 p h) (sat_cons (step383 p h) (sat_cons (step1198 p h) (sat_cons (step1199 p h) (sat_cons (step1087 p h) (sat_cons (step939 p h) (sat_cons (step542 p h) (sat_cons (step552 p h) (sat_cons (step1433 p h) (sat_cons (step1627 p h) (sat_cons (step567 p h) (sat_cons (step1208 p h) (sat_cons (step1217 p h) (sat_cons (step1211 p h) (sat_cons (step1212 p h) (sat_cons (step562 p h) (sat_cons (step574 p h) (sat_cons (step510 p h) (sat_cons (step1414 p h) (sat_cons (step1642 p h) (sat_cons (step1617 p h) (sat_cons (step1618 p h) (sat_cons (step1623 p h) (sat_cons (step914 p h) (sat_cons (step1761 p h) (sat_cons (step1331 p h) (sat_cons (step447 p h) (sat_cons (step444 p h) (sat_cons (step1813 p h) (sat_cons (step1092 p h) (sat_cons (step942 p h) (sat_cons (step1663 p h) (sat_cons (step1097 p h) (sat_cons (step947 p h) (sat_cons (step1717 p h) (sat_cons (step958 p h) (sat_cons (step985 p h) (sat_cons (step1007 p h) (sat_cons (step1688 p h) (sat_cons (step2054 p h) (sat_cons (step1146 p h) (sat_cons (step1155 p h) (sat_cons (step1181 p h) (sat_cons (step1241 p h) (sat_cons (step1289 p h) (sat_cons (step1295 p h) (sat_cons (step1689 p h) (sat_cons (step1952 p h) (sat_cons (step1008 p h) (sat_cons (step1100 p h) (sat_cons (step986 p h) (sat_cons (step1089 p h) (sat_cons (step959 p h) (sat_cons (step1480 p h) (sat_cons (step950 p h) (sat_cons (step940 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c2056 : List Lit := [(27, false), (1539, false), (1555, true), (54, true), (31, true), (99, false)]
theorem step2056 (p : Nat → Bool) (h : Constraints p) : clause p c2056 = true :=
  Snake9.LocalRup.prove_clause [c953, c989, c1764, c1950, c958, c924, c1401, c154, c1971, c885] c2056 (by decide) p (sat_cons (step953 p h) (sat_cons (step989 p h) (sat_cons (step1764 p h) (sat_cons (step1950 p h) (sat_cons (step958 p h) (sat_cons (step924 p h) (sat_cons (step1401 p h) (sat_cons (step154 p h) (sat_cons (step1971 p h) (sat_cons (step885 p h) (sat_nil p)))))))))))
def c2057 : List Lit := [(118, true), (235, true), (1688, true), (114, false), (116, false), (96, false)]
theorem step2057 (p : Nat → Bool) (h : Constraints p) : clause p c2057 = true :=
  Snake9.LocalRup.prove_clause [c557, c1213, c566] c2057 (by decide) p (sat_cons (step557 p h) (sat_cons (step1213 p h) (sat_cons (step566 p h) (sat_nil p))))
def c2058 : List Lit := [(88, false), (85, true), (91, true), (1705, false), (108, false), (86, true), (1695, true), (31, true), (100, true), (102, false), (87, false), (95, true), (114, false), (116, false), (84, false), (98, false), (99, false), (96, false), (1593, false)]
theorem step2058 (p : Nat → Bool) (h : Constraints p) : clause p c2058 = true :=
  Snake9.LocalRup.prove_clause [c1676, c1215, c1796, c1223, c407, c413, c419, c422, c1813, c938, c1089, c351, c1092, c1663, c1100, c736, c1952, c737, c1295, c738, c1688, c739, c1007, c742, c1657, c771, c769, c768, c767, c766, c2057, c510, c1618, c1623, c2056, c949, c947, c940, c942, c383, c444, c1196, c1199, c1204] c2058 (by decide) p (sat_cons (step1676 p h) (sat_cons (step1215 p h) (sat_cons (step1796 p h) (sat_cons (step1223 p h) (sat_cons (step407 p h) (sat_cons (step413 p h) (sat_cons (step419 p h) (sat_cons (step422 p h) (sat_cons (step1813 p h) (sat_cons (step938 p h) (sat_cons (step1089 p h) (sat_cons (step351 p h) (sat_cons (step1092 p h) (sat_cons (step1663 p h) (sat_cons (step1100 p h) (sat_cons (step736 p h) (sat_cons (step1952 p h) (sat_cons (step737 p h) (sat_cons (step1295 p h) (sat_cons (step738 p h) (sat_cons (step1688 p h) (sat_cons (step739 p h) (sat_cons (step1007 p h) (sat_cons (step742 p h) (sat_cons (step1657 p h) (sat_cons (step771 p h) (sat_cons (step769 p h) (sat_cons (step768 p h) (sat_cons (step767 p h) (sat_cons (step766 p h) (sat_cons (step2057 p h) (sat_cons (step510 p h) (sat_cons (step1618 p h) (sat_cons (step1623 p h) (sat_cons (step2056 p h) (sat_cons (step949 p h) (sat_cons (step947 p h) (sat_cons (step940 p h) (sat_cons (step942 p h) (sat_cons (step383 p h) (sat_cons (step444 p h) (sat_cons (step1196 p h) (sat_cons (step1199 p h) (sat_cons (step1204 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))
def c2059 : List Lit := [(118, true), (1690, true), (116, false), (96, false)]
theorem step2059 (p : Nat → Bool) (h : Constraints p) : clause p c2059 = true :=
  Snake9.LocalRup.prove_clause [c1215, c1212, c1213, c1217, c566, c1208] c2059 (by decide) p (sat_cons (step1215 p h) (sat_cons (step1212 p h) (sat_cons (step1213 p h) (sat_cons (step1217 p h) (sat_cons (step566 p h) (sat_cons (step1208 p h) (sat_nil p)))))))
def c2060 : List Lit := [(85, false), (1545, true), (54, true), (108, false), (119, false), (90, false), (101, true), (118, false), (1682, true), (102, false), (87, false), (116, false), (98, false)]
theorem step2060 (p : Nat → Bool) (h : Constraints p) : clause p c2060 = true :=
  Snake9.LocalRup.prove_clause [c389, c377, c1196, c940, c1204, c1198, c1199, c541, c444, c1635, c942, c574, c950, c1642, c959, c1761] c2060 (by decide) p (sat_cons (step389 p h) (sat_cons (step377 p h) (sat_cons (step1196 p h) (sat_cons (step940 p h) (sat_cons (step1204 p h) (sat_cons (step1198 p h) (sat_cons (step1199 p h) (sat_cons (step541 p h) (sat_cons (step444 p h) (sat_cons (step1635 p h) (sat_cons (step942 p h) (sat_cons (step574 p h) (sat_cons (step950 p h) (sat_cons (step1642 p h) (sat_cons (step959 p h) (sat_cons (step1761 p h) (sat_nil p)))))))))))))))))
def c2061 : List Lit := [(1705, false), (108, false), (86, true), (119, false), (1695, true), (31, true), (100, true), (102, false), (87, false), (95, true), (114, false), (116, false), (84, false), (98, false), (99, false), (96, false), (1593, false)]
theorem step2061 (p : Nat → Bool) (h : Constraints p) : clause p c2061 = true :=
  Snake9.LocalRup.prove_clause [c1676, c2059, c510, c1617, c423, c419, c1088, c422, c1092, c1097, c1717, c407, c1813, c1663, c413, c883, c891, c562, c1414, c914, c1623, c1796, c1223, c1289, c1689, c1008, c986, c2060, c2058] c2061 (by decide) p (sat_cons (step1676 p h) (sat_cons (step2059 p h) (sat_cons (step510 p h) (sat_cons (step1617 p h) (sat_cons (step423 p h) (sat_cons (step419 p h) (sat_cons (step1088 p h) (sat_cons (step422 p h) (sat_cons (step1092 p h) (sat_cons (step1097 p h) (sat_cons (step1717 p h) (sat_cons (step407 p h) (sat_cons (step1813 p h) (sat_cons (step1663 p h) (sat_cons (step413 p h) (sat_cons (step883 p h) (sat_cons (step891 p h) (sat_cons (step562 p h) (sat_cons (step1414 p h) (sat_cons (step914 p h) (sat_cons (step1623 p h) (sat_cons (step1796 p h) (sat_cons (step1223 p h) (sat_cons (step1289 p h) (sat_cons (step1689 p h) (sat_cons (step1008 p h) (sat_cons (step986 p h) (sat_cons (step2060 p h) (sat_cons (step2058 p h) (sat_nil p))))))))))))))))))))))))))))))
def c2062 : List Lit := [(86, true), (119, false), (1695, true), (31, true), (100, true), (102, false), (105, true), (87, false), (93, true), (1665, false), (95, true), (114, false), (116, false), (84, false), (98, false), (99, false), (96, false), (1593, false)]
theorem step2062 (p : Nat → Bool) (h : Constraints p) : clause p c2062 = true :=
  Snake9.LocalRup.prove_clause [c1676, c2059, c510, c1617, c883, c891, c1796, c1675, c2055, c423, c2061, c1146, c1241, c1155, c1181] c2062 (by decide) p (sat_cons (step1676 p h) (sat_cons (step2059 p h) (sat_cons (step510 p h) (sat_cons (step1617 p h) (sat_cons (step883 p h) (sat_cons (step891 p h) (sat_cons (step1796 p h) (sat_cons (step1675 p h) (sat_cons (step2055 p h) (sat_cons (step423 p h) (sat_cons (step2061 p h) (sat_cons (step1146 p h) (sat_cons (step1241 p h) (sat_cons (step1155 p h) (sat_cons (step1181 p h) (sat_nil p))))))))))))))))
def c2063 : List Lit := [(1695, true), (102, false), (115, false), (1661, true), (96, false), (94, false)]
theorem step2063 (p : Nat → Bool) (h : Constraints p) : clause p c2063 = true :=
  Snake9.LocalRup.prove_clause [c1159, c490, c481, c1613, c520, c1158, c503, c1639, c553, c1616, c1797, c2053, c1164, c1411, c1610, c1612, c1796, c1675, c1418, c1676, c1223, c2059, c510, c556, c1617, c1618, c1208, c1217, c1211, c2062, c1331, c2051, c1430, c344, c349, c380, c1772, c413, c422, c1089, c1146, c940, c1664, c1090, c1099, c1155, c949, c1717, c1181, c2056, c1241, c1015, c1289, c1689] c2063 (by decide) p (sat_cons (step1159 p h) (sat_cons (step490 p h) (sat_cons (step481 p h) (sat_cons (step1613 p h) (sat_cons (step520 p h) (sat_cons (step1158 p h) (sat_cons (step503 p h) (sat_cons (step1639 p h) (sat_cons (step553 p h) (sat_cons (step1616 p h) (sat_cons (step1797 p h) (sat_cons (step2053 p h) (sat_cons (step1164 p h) (sat_cons (step1411 p h) (sat_cons (step1610 p h) (sat_cons (step1612 p h) (sat_cons (step1796 p h) (sat_cons (step1675 p h) (sat_cons (step1418 p h) (sat_cons (step1676 p h) (sat_cons (step1223 p h) (sat_cons (step2059 p h) (sat_cons (step510 p h) (sat_cons (step556 p h) (sat_cons (step1617 p h) (sat_cons (step1618 p h) (sat_cons (step1208 p h) (sat_cons (step1217 p h) (sat_cons (step1211 p h) (sat_cons (step2062 p h) (sat_cons (step1331 p h) (sat_cons (step2051 p h) (sat_cons (step1430 p h) (sat_cons (step344 p h) (sat_cons (step349 p h) (sat_cons (step380 p h) (sat_cons (step1772 p h) (sat_cons (step413 p h) (sat_cons (step422 p h) (sat_cons (step1089 p h) (sat_cons (step1146 p h) (sat_cons (step940 p h) (sat_cons (step1664 p h) (sat_cons (step1090 p h) (sat_cons (step1099 p h) (sat_cons (step1155 p h) (sat_cons (step949 p h) (sat_cons (step1717 p h) (sat_cons (step1181 p h) (sat_cons (step2056 p h) (sat_cons (step1241 p h) (sat_cons (step1015 p h) (sat_cons (step1289 p h) (sat_cons (step1689 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c2064 : List Lit := [(1627, false), (1644, true), (1705, false), (1593, false), (1492, false), (31, true), (54, true), (27, false), (99, false)]
theorem step2064 (p : Nat → Bool) (h : Constraints p) : clause p c2064 = true :=
  Snake9.LocalRup.prove_clause [c938, c1717, c1289, c1689, c1015, c2056, c947, c942, c1448, c1927, c1580] c2064 (by decide) p (sat_cons (step938 p h) (sat_cons (step1717 p h) (sat_cons (step1289 p h) (sat_cons (step1689 p h) (sat_cons (step1015 p h) (sat_cons (step2056 p h) (sat_cons (step947 p h) (sat_cons (step942 p h) (sat_cons (step1448 p h) (sat_cons (step1927 p h) (sat_cons (step1580 p h) (sat_nil p))))))))))))
def c2065 : List Lit := [(85, false), (86, false), (98, false), (96, false)]
theorem step2065 (p : Nat → Bool) (h : Constraints p) : clause p c2065 = true :=
  Snake9.LocalRup.prove_clause [c489, c347, c1612] c2065 (by decide) p (sat_cons (step489 p h) (sat_cons (step347 p h) (sat_cons (step1612 p h) (sat_nil p))))
end B112E024
