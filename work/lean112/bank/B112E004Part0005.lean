import B112E004Part0004
namespace B112E004
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2054 : List Lit := [(115, true), (119, false), (120, true)]
theorem step2054 (p : Nat → Bool) (h : Constraints p) : clause p c2054 = true :=
  Snake9.LocalRup.prove_clause [c835, c771] c2054 (by decide) p (sat_cons (step835 p h) (sat_cons (step771 p h) (sat_nil p)))
def c2055 : List Lit := [(120, true), (110, true), (119, false)]
theorem step2055 (p : Nat → Bool) (h : Constraints p) : clause p c2055 = true :=
  Snake9.LocalRup.prove_clause [c835, c772] c2055 (by decide) p (sat_cons (step835 p h) (sat_cons (step772 p h) (sat_nil p)))
def c2056 : List Lit := [(115, true), (119, false), (110, true)]
theorem step2056 (p : Nat → Bool) (h : Constraints p) : clause p c2056 = true :=
  Snake9.LocalRup.prove_clause [c835, c773] c2056 (by decide) p (sat_cons (step835 p h) (sat_cons (step773 p h) (sat_nil p)))
def c2057 : List Lit := [(129, false), (130, false)]
theorem step2057 (p : Nat → Bool) (h : Constraints p) : clause p c2057 = true :=
  Snake9.LocalRup.prove_clause [c1766, c845] c2057 (by decide) p (sat_cons (step1766 p h) (sat_cons (step845 p h) (sat_nil p)))
def c2058 : List Lit := [(128, false), (253, false)]
theorem step2058 (p : Nat → Bool) (h : Constraints p) : clause p c2058 = true :=
  Snake9.LocalRup.prove_clause [c1765, c849] c2058 (by decide) p (sat_cons (step1765 p h) (sat_cons (step849 p h) (sat_nil p)))
def c2059 : List Lit := [(255, false), (261, false)]
theorem step2059 (p : Nat → Bool) (h : Constraints p) : clause p c2059 = true :=
  Snake9.LocalRup.prove_clause [c1760, c856] c2059 (by decide) p (sat_cons (step1760 p h) (sat_cons (step856 p h) (sat_nil p)))
def c2060 : List Lit := [(251, false), (263, false)]
theorem step2060 (p : Nat → Bool) (h : Constraints p) : clause p c2060 = true :=
  Snake9.LocalRup.prove_clause [c1751, c861] c2060 (by decide) p (sat_cons (step1751 p h) (sat_cons (step861 p h) (sat_nil p)))
def c2061 : List Lit := [(279, false), (281, false)]
theorem step2061 (p : Nat → Bool) (h : Constraints p) : clause p c2061 = true :=
  Snake9.LocalRup.prove_clause [c1764, c873] c2061 (by decide) p (sat_cons (step1764 p h) (sat_cons (step873 p h) (sat_nil p)))
def c2062 : List Lit := [(283, false), (289, false)]
theorem step2062 (p : Nat → Bool) (h : Constraints p) : clause p c2062 = true :=
  Snake9.LocalRup.prove_clause [c1759, c880] c2062 (by decide) p (sat_cons (step1759 p h) (sat_cons (step880 p h) (sat_nil p)))
def c2063 : List Lit := [(277, false), (291, false)]
theorem step2063 (p : Nat → Bool) (h : Constraints p) : clause p c2063 = true :=
  Snake9.LocalRup.prove_clause [c1750, c885] c2063 (by decide) p (sat_cons (step1750 p h) (sat_cons (step885 p h) (sat_nil p)))
def c2064 : List Lit := [(265, false), (293, false)]
theorem step2064 (p : Nat → Bool) (h : Constraints p) : clause p c2064 = true :=
  Snake9.LocalRup.prove_clause [c1743, c889] c2064 (by decide) p (sat_cons (step1743 p h) (sat_cons (step889 p h) (sat_nil p)))
def c2065 : List Lit := [(299, false), (305, false)]
theorem step2065 (p : Nat → Bool) (h : Constraints p) : clause p c2065 = true :=
  Snake9.LocalRup.prove_clause [c1758, c898] c2065 (by decide) p (sat_cons (step1758 p h) (sat_cons (step898 p h) (sat_nil p)))
def c2066 : List Lit := [(307, false), (321, false)]
theorem step2066 (p : Nat → Bool) (h : Constraints p) : clause p c2066 = true :=
  Snake9.LocalRup.prove_clause [c1749, c911] c2066 (by decide) p (sat_cons (step1749 p h) (sat_cons (step911 p h) (sat_nil p)))
def c2067 : List Lit := [(335, false), (349, false)]
theorem step2067 (p : Nat → Bool) (h : Constraints p) : clause p c2067 = true :=
  Snake9.LocalRup.prove_clause [c1748, c931] c2067 (by decide) p (sat_cons (step1748 p h) (sat_cons (step931 p h) (sat_nil p)))
def c2068 : List Lit := [(323, false), (351, false)]
theorem step2068 (p : Nat → Bool) (h : Constraints p) : clause p c2068 = true :=
  Snake9.LocalRup.prove_clause [c1742, c935] c2068 (by decide) p (sat_cons (step1742 p h) (sat_cons (step935 p h) (sat_nil p)))
def c2069 : List Lit := [(295, false), (353, false)]
theorem step2069 (p : Nat → Bool) (h : Constraints p) : clause p c2069 = true :=
  Snake9.LocalRup.prove_clause [c1739, c940] c2069 (by decide) p (sat_cons (step1739 p h) (sat_cons (step940 p h) (sat_nil p)))
def c2070 : List Lit := [(361, false), (363, false)]
theorem step2070 (p : Nat → Bool) (h : Constraints p) : clause p c2070 = true :=
  Snake9.LocalRup.prove_clause [c1763, c947] c2070 (by decide) p (sat_cons (step1763 p h) (sat_cons (step947 p h) (sat_nil p)))
def c2071 : List Lit := [(373, false), (379, false)]
theorem step2071 (p : Nat → Bool) (h : Constraints p) : clause p c2071 = true :=
  Snake9.LocalRup.prove_clause [c1756, c960] c2071 (by decide) p (sat_cons (step1756 p h) (sat_cons (step960 p h) (sat_nil p)))
def c2072 : List Lit := [(367, false), (381, false)]
theorem step2072 (p : Nat → Bool) (h : Constraints p) : clause p c2072 = true :=
  Snake9.LocalRup.prove_clause [c1747, c964] c2072 (by decide) p (sat_cons (step1747 p h) (sat_cons (step964 p h) (sat_nil p)))
def c2073 : List Lit := [(196, false), (385, false)]
theorem step2073 (p : Nat → Bool) (h : Constraints p) : clause p c2073 = true :=
  Snake9.LocalRup.prove_clause [c1762, c969] c2073 (by decide) p (sat_cons (step1762 p h) (sat_cons (step969 p h) (sat_nil p)))
def c2074 : List Lit := [(387, false), (393, false)]
theorem step2074 (p : Nat → Bool) (h : Constraints p) : clause p c2074 = true :=
  Snake9.LocalRup.prove_clause [c1755, c976] c2074 (by decide) p (sat_cons (step1755 p h) (sat_cons (step976 p h) (sat_nil p)))
def c2075 : List Lit := [(395, false), (409, false)]
theorem step2075 (p : Nat → Bool) (h : Constraints p) : clause p c2075 = true :=
  Snake9.LocalRup.prove_clause [c1746, c988] c2075 (by decide) p (sat_cons (step1746 p h) (sat_cons (step988 p h) (sat_nil p)))
def c2076 : List Lit := [(383, false), (411, false)]
theorem step2076 (p : Nat → Bool) (h : Constraints p) : clause p c2076 = true :=
  Snake9.LocalRup.prove_clause [c1741, c993] c2076 (by decide) p (sat_cons (step1741 p h) (sat_cons (step993 p h) (sat_nil p)))
def c2077 : List Lit := [(417, false), (423, false)]
theorem step2077 (p : Nat → Bool) (h : Constraints p) : clause p c2077 = true :=
  Snake9.LocalRup.prove_clause [c1754, c1005] c2077 (by decide) p (sat_cons (step1754 p h) (sat_cons (step1005 p h) (sat_nil p)))
def c2078 : List Lit := [(425, false), (439, false)]
theorem step2078 (p : Nat → Bool) (h : Constraints p) : clause p c2078 = true :=
  Snake9.LocalRup.prove_clause [c1745, c1016] c2078 (by decide) p (sat_cons (step1745 p h) (sat_cons (step1016 p h) (sat_nil p)))
def c2079 : List Lit := [(445, false), (451, false)]
theorem step2079 (p : Nat → Bool) (h : Constraints p) : clause p c2079 = true :=
  Snake9.LocalRup.prove_clause [c1753, c1026] c2079 (by decide) p (sat_cons (step1753 p h) (sat_cons (step1026 p h) (sat_nil p)))
def c2080 : List Lit := [(455, false), (457, false)]
theorem step2080 (p : Nat → Bool) (h : Constraints p) : clause p c2080 = true :=
  Snake9.LocalRup.prove_clause [c1761, c1031] c2080 (by decide) p (sat_cons (step1761 p h) (sat_cons (step1031 p h) (sat_nil p)))
def c2081 : List Lit := [(453, false), (467, false)]
theorem step2081 (p : Nat → Bool) (h : Constraints p) : clause p c2081 = true :=
  Snake9.LocalRup.prove_clause [c1744, c1042] c2081 (by decide) p (sat_cons (step1744 p h) (sat_cons (step1042 p h) (sat_nil p)))
def c2082 : List Lit := [(441, false), (469, false)]
theorem step2082 (p : Nat → Bool) (h : Constraints p) : clause p c2082 = true :=
  Snake9.LocalRup.prove_clause [c1740, c1047] c2082 (by decide) p (sat_cons (step1740 p h) (sat_cons (step1047 p h) (sat_nil p)))
def c2083 : List Lit := [(413, false), (471, false)]
theorem step2083 (p : Nat → Bool) (h : Constraints p) : clause p c2083 = true :=
  Snake9.LocalRup.prove_clause [c1738, c1052] c2083 (by decide) p (sat_cons (step1738 p h) (sat_cons (step1052 p h) (sat_nil p)))
def c2084 : List Lit := [(355, false), (473, false)]
theorem step2084 (p : Nat → Bool) (h : Constraints p) : clause p c2084 = true :=
  Snake9.LocalRup.prove_clause [c1057, c1055] c2084 (by decide) p (sat_cons (step1057 p h) (sat_cons (step1055 p h) (sat_nil p)))
def c2085 : List Lit := [(927, false), (1071, false)]
theorem step2085 (p : Nat → Bool) (h : Constraints p) : clause p c2085 = true :=
  Snake9.LocalRup.prove_clause [c1097, c1096] c2085 (by decide) p (sat_cons (step1097 p h) (sat_cons (step1096 p h) (sat_nil p)))
def c2086 : List Lit := [(1466, false), (1479, true)]
theorem step2086 (p : Nat → Bool) (h : Constraints p) : clause p c2086 = true :=
  Snake9.LocalRup.prove_clause [c1768, c1167] c2086 (by decide) p (sat_cons (step1768 p h) (sat_cons (step1167 p h) (sat_nil p)))
def c2087 : List Lit := [(1467, false), (1480, true)]
theorem step2087 (p : Nat → Bool) (h : Constraints p) : clause p c2087 = true :=
  Snake9.LocalRup.prove_clause [c1768, c1170] c2087 (by decide) p (sat_cons (step1768 p h) (sat_cons (step1170 p h) (sat_nil p)))
def c2088 : List Lit := [(1468, false), (1481, true)]
theorem step2088 (p : Nat → Bool) (h : Constraints p) : clause p c2088 = true :=
  Snake9.LocalRup.prove_clause [c1768, c1174] c2088 (by decide) p (sat_cons (step1768 p h) (sat_cons (step1174 p h) (sat_nil p)))
def c2089 : List Lit := [(1488, true), (1479, false)]
theorem step2089 (p : Nat → Bool) (h : Constraints p) : clause p c2089 = true :=
  Snake9.LocalRup.prove_clause [c1841, c1183] c2089 (by decide) p (sat_cons (step1841 p h) (sat_cons (step1183 p h) (sat_nil p)))
def c2090 : List Lit := [(1480, false), (1489, true)]
theorem step2090 (p : Nat → Bool) (h : Constraints p) : clause p c2090 = true :=
  Snake9.LocalRup.prove_clause [c1841, c1184] c2090 (by decide) p (sat_cons (step1841 p h) (sat_cons (step1184 p h) (sat_nil p)))
def c2091 : List Lit := [(1481, false), (1490, true)]
theorem step2091 (p : Nat → Bool) (h : Constraints p) : clause p c2091 = true :=
  Snake9.LocalRup.prove_clause [c1841, c1185] c2091 (by decide) p (sat_cons (step1841 p h) (sat_cons (step1185 p h) (sat_nil p)))
def c2092 : List Lit := [(1482, false), (1491, true)]
theorem step2092 (p : Nat → Bool) (h : Constraints p) : clause p c2092 = true :=
  Snake9.LocalRup.prove_clause [c1841, c1186] c2092 (by decide) p (sat_cons (step1841 p h) (sat_cons (step1186 p h) (sat_nil p)))
def c2093 : List Lit := [(1483, false), (1492, true)]
theorem step2093 (p : Nat → Bool) (h : Constraints p) : clause p c2093 = true :=
  Snake9.LocalRup.prove_clause [c1841, c1187] c2093 (by decide) p (sat_cons (step1841 p h) (sat_cons (step1187 p h) (sat_nil p)))
def c2094 : List Lit := [(1455, false), (1488, true)]
theorem step2094 (p : Nat → Bool) (h : Constraints p) : clause p c2094 = true :=
  Snake9.LocalRup.prove_clause [c1796, c1188] c2094 (by decide) p (sat_cons (step1796 p h) (sat_cons (step1188 p h) (sat_nil p)))
def c2095 : List Lit := [(1456, false), (1489, true)]
theorem step2095 (p : Nat → Bool) (h : Constraints p) : clause p c2095 = true :=
  Snake9.LocalRup.prove_clause [c1796, c1193] c2095 (by decide) p (sat_cons (step1796 p h) (sat_cons (step1193 p h) (sat_nil p)))
def c2096 : List Lit := [(1489, true), (1457, false)]
theorem step2096 (p : Nat → Bool) (h : Constraints p) : clause p c2096 = true :=
  Snake9.LocalRup.prove_clause [c1769, c1196] c2096 (by decide) p (sat_cons (step1769 p h) (sat_cons (step1196 p h) (sat_nil p)))
def c2097 : List Lit := [(1457, false), (1490, true)]
theorem step2097 (p : Nat → Bool) (h : Constraints p) : clause p c2097 = true :=
  Snake9.LocalRup.prove_clause [c1796, c1197] c2097 (by decide) p (sat_cons (step1796 p h) (sat_cons (step1197 p h) (sat_nil p)))
def c2098 : List Lit := [(1537, false), (1546, true)]
theorem step2098 (p : Nat → Bool) (h : Constraints p) : clause p c2098 = true :=
  Snake9.LocalRup.prove_clause [c1772, c1291] c2098 (by decide) p (sat_cons (step1772 p h) (sat_cons (step1291 p h) (sat_nil p)))
def c2099 : List Lit := [(1538, false), (1547, true)]
theorem step2099 (p : Nat → Bool) (h : Constraints p) : clause p c2099 = true :=
  Snake9.LocalRup.prove_clause [c1772, c1292] c2099 (by decide) p (sat_cons (step1772 p h) (sat_cons (step1292 p h) (sat_nil p)))
def c2100 : List Lit := [(1539, false), (1548, true)]
theorem step2100 (p : Nat → Bool) (h : Constraints p) : clause p c2100 = true :=
  Snake9.LocalRup.prove_clause [c1772, c1293] c2100 (by decide) p (sat_cons (step1772 p h) (sat_cons (step1293 p h) (sat_nil p)))
def c2101 : List Lit := [(1540, false), (1549, true)]
theorem step2101 (p : Nat → Bool) (h : Constraints p) : clause p c2101 = true :=
  Snake9.LocalRup.prove_clause [c1772, c1294] c2101 (by decide) p (sat_cons (step1772 p h) (sat_cons (step1294 p h) (sat_nil p)))
def c2102 : List Lit := [(1541, false), (1550, true)]
theorem step2102 (p : Nat → Bool) (h : Constraints p) : clause p c2102 = true :=
  Snake9.LocalRup.prove_clause [c1772, c1295] c2102 (by decide) p (sat_cons (step1772 p h) (sat_cons (step1295 p h) (sat_nil p)))
def c2103 : List Lit := [(1542, false), (1551, true)]
theorem step2103 (p : Nat → Bool) (h : Constraints p) : clause p c2103 = true :=
  Snake9.LocalRup.prove_clause [c1772, c1296] c2103 (by decide) p (sat_cons (step1772 p h) (sat_cons (step1296 p h) (sat_nil p)))
def c2104 : List Lit := [(1543, false), (1552, true)]
theorem step2104 (p : Nat → Bool) (h : Constraints p) : clause p c2104 = true :=
  Snake9.LocalRup.prove_clause [c1772, c1297] c2104 (by decide) p (sat_cons (step1772 p h) (sat_cons (step1297 p h) (sat_nil p)))
def c2105 : List Lit := [(1514, false), (1546, true)]
theorem step2105 (p : Nat → Bool) (h : Constraints p) : clause p c2105 = true :=
  Snake9.LocalRup.prove_clause [c1771, c1298] c2105 (by decide) p (sat_cons (step1771 p h) (sat_cons (step1298 p h) (sat_nil p)))
def c2106 : List Lit := [(1515, false), (1547, true)]
theorem step2106 (p : Nat → Bool) (h : Constraints p) : clause p c2106 = true :=
  Snake9.LocalRup.prove_clause [c1771, c1306] c2106 (by decide) p (sat_cons (step1771 p h) (sat_cons (step1306 p h) (sat_nil p)))
def c2107 : List Lit := [(1516, false), (1548, true)]
theorem step2107 (p : Nat → Bool) (h : Constraints p) : clause p c2107 = true :=
  Snake9.LocalRup.prove_clause [c1771, c1313] c2107 (by decide) p (sat_cons (step1771 p h) (sat_cons (step1313 p h) (sat_nil p)))
def c2108 : List Lit := [(1517, false), (1549, true)]
theorem step2108 (p : Nat → Bool) (h : Constraints p) : clause p c2108 = true :=
  Snake9.LocalRup.prove_clause [c1771, c1321] c2108 (by decide) p (sat_cons (step1771 p h) (sat_cons (step1321 p h) (sat_nil p)))
def c2109 : List Lit := [(1552, false), (1569, true)]
theorem step2109 (p : Nat → Bool) (h : Constraints p) : clause p c2109 = true :=
  Snake9.LocalRup.prove_clause [c1770, c1332] c2109 (by decide) p (sat_cons (step1770 p h) (sat_cons (step1332 p h) (sat_nil p)))
def c2110 : List Lit := [(1564, true), (1546, false)]
theorem step2110 (p : Nat → Bool) (h : Constraints p) : clause p c2110 = true :=
  Snake9.LocalRup.prove_clause [c1842, c1333] c2110 (by decide) p (sat_cons (step1842 p h) (sat_cons (step1333 p h) (sat_nil p)))
def c2111 : List Lit := [(1565, true), (1547, false)]
theorem step2111 (p : Nat → Bool) (h : Constraints p) : clause p c2111 = true :=
  Snake9.LocalRup.prove_clause [c1842, c1334] c2111 (by decide) p (sat_cons (step1842 p h) (sat_cons (step1334 p h) (sat_nil p)))
def c2112 : List Lit := [(1566, true), (1548, false)]
theorem step2112 (p : Nat → Bool) (h : Constraints p) : clause p c2112 = true :=
  Snake9.LocalRup.prove_clause [c1842, c1335] c2112 (by decide) p (sat_cons (step1842 p h) (sat_cons (step1335 p h) (sat_nil p)))
def c2113 : List Lit := [(1567, true), (1549, false)]
theorem step2113 (p : Nat → Bool) (h : Constraints p) : clause p c2113 = true :=
  Snake9.LocalRup.prove_clause [c1842, c1336] c2113 (by decide) p (sat_cons (step1842 p h) (sat_cons (step1336 p h) (sat_nil p)))
def c2114 : List Lit := [(1568, true), (1550, false)]
theorem step2114 (p : Nat → Bool) (h : Constraints p) : clause p c2114 = true :=
  Snake9.LocalRup.prove_clause [c1842, c1337] c2114 (by decide) p (sat_cons (step1842 p h) (sat_cons (step1337 p h) (sat_nil p)))
def c2115 : List Lit := [(1551, false), (1569, true)]
theorem step2115 (p : Nat → Bool) (h : Constraints p) : clause p c2115 = true :=
  Snake9.LocalRup.prove_clause [c1842, c1338] c2115 (by decide) p (sat_cons (step1842 p h) (sat_cons (step1338 p h) (sat_nil p)))
def c2116 : List Lit := [(1552, false), (1570, true)]
theorem step2116 (p : Nat → Bool) (h : Constraints p) : clause p c2116 = true :=
  Snake9.LocalRup.prove_clause [c1842, c1339] c2116 (by decide) p (sat_cons (step1842 p h) (sat_cons (step1339 p h) (sat_nil p)))
def c2117 : List Lit := [(1553, false), (1571, true)]
theorem step2117 (p : Nat → Bool) (h : Constraints p) : clause p c2117 = true :=
  Snake9.LocalRup.prove_clause [c1842, c1340] c2117 (by decide) p (sat_cons (step1842 p h) (sat_cons (step1340 p h) (sat_nil p)))
end B112E004
