import B112E256Part0002
namespace B112E256
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2036 : List Lit := [(265, false), (279, false)]
theorem step2036 (p : Nat → Bool) (h : Constraints p) : clause p c2036 = true :=
  Snake9.LocalRup.prove_clause [c1859, c867] c2036 (by decide) p (sat_cons (step1859 p h) (sat_cons (step867 p h) (sat_nil p)))
def c2037 : List Lit := [(145, false), (146, false)]
theorem step2037 (p : Nat → Bool) (h : Constraints p) : clause p c2037 = true :=
  Snake9.LocalRup.prove_clause [c1890, c871] c2037 (by decide) p (sat_cons (step1890 p h) (sat_cons (step871 p h) (sat_nil p)))
def c2038 : List Lit := [(289, false), (291, false)]
theorem step2038 (p : Nat → Bool) (h : Constraints p) : clause p c2038 = true :=
  Snake9.LocalRup.prove_clause [c1881, c878] c2038 (by decide) p (sat_cons (step1881 p h) (sat_cons (step878 p h) (sat_nil p)))
def c2039 : List Lit := [(287, false), (293, false)]
theorem step2039 (p : Nat → Bool) (h : Constraints p) : clause p c2039 = true :=
  Snake9.LocalRup.prove_clause [c1870, c882] c2039 (by decide) p (sat_cons (step1870 p h) (sat_cons (step882 p h) (sat_nil p)))
def c2040 : List Lit := [(303, false), (305, false)]
theorem step2040 (p : Nat → Bool) (h : Constraints p) : clause p c2040 = true :=
  Snake9.LocalRup.prove_clause [c1880, c890] c2040 (by decide) p (sat_cons (step1880 p h) (sat_cons (step890 p h) (sat_nil p)))
def c2041 : List Lit := [(301, false), (307, false)]
theorem step2041 (p : Nat → Bool) (h : Constraints p) : clause p c2041 = true :=
  Snake9.LocalRup.prove_clause [c1869, c894] c2041 (by decide) p (sat_cons (step1869 p h) (sat_cons (step894 p h) (sat_nil p)))
def c2042 : List Lit := [(295, false), (309, false)]
theorem step2042 (p : Nat → Bool) (h : Constraints p) : clause p c2042 = true :=
  Snake9.LocalRup.prove_clause [c1858, c898] c2042 (by decide) p (sat_cons (step1858 p h) (sat_cons (step898 p h) (sat_nil p)))
def c2043 : List Lit := [(281, false), (311, false)]
theorem step2043 (p : Nat → Bool) (h : Constraints p) : clause p c2043 = true :=
  Snake9.LocalRup.prove_clause [c1851, c903] c2043 (by decide) p (sat_cons (step1851 p h) (sat_cons (step903 p h) (sat_nil p)))
def c2044 : List Lit := [(319, false), (325, false)]
theorem step2044 (p : Nat → Bool) (h : Constraints p) : clause p c2044 = true :=
  Snake9.LocalRup.prove_clause [c1868, c913] c2044 (by decide) p (sat_cons (step1868 p h) (sat_cons (step913 p h) (sat_nil p)))
def c2045 : List Lit := [(171, false), (172, false)]
theorem step2045 (p : Nat → Bool) (h : Constraints p) : clause p c2045 = true :=
  Snake9.LocalRup.prove_clause [c1889, c921] c2045 (by decide) p (sat_cons (step1889 p h) (sat_cons (step921 p h) (sat_nil p)))
def c2046 : List Lit := [(335, false), (337, false)]
theorem step2046 (p : Nat → Bool) (h : Constraints p) : clause p c2046 = true :=
  Snake9.LocalRup.prove_clause [c1879, c925] c2046 (by decide) p (sat_cons (step1879 p h) (sat_cons (step925 p h) (sat_nil p)))
def c2047 : List Lit := [(333, false), (339, false)]
theorem step2047 (p : Nat → Bool) (h : Constraints p) : clause p c2047 = true :=
  Snake9.LocalRup.prove_clause [c1867, c930] c2047 (by decide) p (sat_cons (step1867 p h) (sat_cons (step930 p h) (sat_nil p)))
def c2048 : List Lit := [(327, false), (341, false)]
theorem step2048 (p : Nat → Bool) (h : Constraints p) : clause p c2048 = true :=
  Snake9.LocalRup.prove_clause [c1857, c934] c2048 (by decide) p (sat_cons (step1857 p h) (sat_cons (step934 p h) (sat_nil p)))
def c2049 : List Lit := [(359, false), (361, false)]
theorem step2049 (p : Nat → Bool) (h : Constraints p) : clause p c2049 = true :=
  Snake9.LocalRup.prove_clause [c1878, c946] c2049 (by decide) p (sat_cons (step1878 p h) (sat_cons (step946 p h) (sat_nil p)))
def c2050 : List Lit := [(187, false), (188, false)]
theorem step2050 (p : Nat → Bool) (h : Constraints p) : clause p c2050 = true :=
  Snake9.LocalRup.prove_clause [c1888, c949] c2050 (by decide) p (sat_cons (step1888 p h) (sat_cons (step949 p h) (sat_nil p)))
def c2051 : List Lit := [(365, false), (367, false)]
theorem step2051 (p : Nat → Bool) (h : Constraints p) : clause p c2051 = true :=
  Snake9.LocalRup.prove_clause [c1877, c954] c2051 (by decide) p (sat_cons (step1877 p h) (sat_cons (step954 p h) (sat_nil p)))
def c2052 : List Lit := [(363, false), (369, false)]
theorem step2052 (p : Nat → Bool) (h : Constraints p) : clause p c2052 = true :=
  Snake9.LocalRup.prove_clause [c1866, c959] c2052 (by decide) p (sat_cons (step1866 p h) (sat_cons (step959 p h) (sat_nil p)))
def c2053 : List Lit := [(357, false), (371, false)]
theorem step2053 (p : Nat → Bool) (h : Constraints p) : clause p c2053 = true :=
  Snake9.LocalRup.prove_clause [c1856, c964] c2053 (by decide) p (sat_cons (step1856 p h) (sat_cons (step964 p h) (sat_nil p)))
def c2054 : List Lit := [(343, false), (373, false)]
theorem step2054 (p : Nat → Bool) (h : Constraints p) : clause p c2054 = true :=
  Snake9.LocalRup.prove_clause [c1850, c968] c2054 (by decide) p (sat_cons (step1850 p h) (sat_cons (step968 p h) (sat_nil p)))
def c2055 : List Lit := [(313, false), (375, false)]
theorem step2055 (p : Nat → Bool) (h : Constraints p) : clause p c2055 = true :=
  Snake9.LocalRup.prove_clause [c1847, c973] c2055 (by decide) p (sat_cons (step1847 p h) (sat_cons (step973 p h) (sat_nil p)))
def c2056 : List Lit := [(194, false), (195, false)]
theorem step2056 (p : Nat → Bool) (h : Constraints p) : clause p c2056 = true :=
  Snake9.LocalRup.prove_clause [c1887, c979] c2056 (by decide) p (sat_cons (step1887 p h) (sat_cons (step979 p h) (sat_nil p)))
def c2057 : List Lit := [(383, false), (385, false)]
theorem step2057 (p : Nat → Bool) (h : Constraints p) : clause p c2057 = true :=
  Snake9.LocalRup.prove_clause [c1876, c983] c2057 (by decide) p (sat_cons (step1876 p h) (sat_cons (step983 p h) (sat_nil p)))
def c2058 : List Lit := [(397, false), (399, false)]
theorem step2058 (p : Nat → Bool) (h : Constraints p) : clause p c2058 = true :=
  Snake9.LocalRup.prove_clause [c1875, c994] c2058 (by decide) p (sat_cons (step1875 p h) (sat_cons (step994 p h) (sat_nil p)))
def c2059 : List Lit := [(395, false), (401, false)]
theorem step2059 (p : Nat → Bool) (h : Constraints p) : clause p c2059 = true :=
  Snake9.LocalRup.prove_clause [c1864, c998] c2059 (by decide) p (sat_cons (step1864 p h) (sat_cons (step998 p h) (sat_nil p)))
def c2060 : List Lit := [(389, false), (403, false)]
theorem step2060 (p : Nat → Bool) (h : Constraints p) : clause p c2060 = true :=
  Snake9.LocalRup.prove_clause [c1855, c1002] c2060 (by decide) p (sat_cons (step1855 p h) (sat_cons (step1002 p h) (sat_nil p)))
def c2061 : List Lit := [(419, false), (433, false)]
theorem step2061 (p : Nat → Bool) (h : Constraints p) : clause p c2061 = true :=
  Snake9.LocalRup.prove_clause [c1854, c1023] c2061 (by decide) p (sat_cons (step1854 p h) (sat_cons (step1023 p h) (sat_nil p)))
def c2062 : List Lit := [(405, false), (435, false)]
theorem step2062 (p : Nat → Bool) (h : Constraints p) : clause p c2062 = true :=
  Snake9.LocalRup.prove_clause [c1849, c1027] c2062 (by decide) p (sat_cons (step1849 p h) (sat_cons (step1027 p h) (sat_nil p)))
def c2063 : List Lit := [(443, false), (449, false)]
theorem step2063 (p : Nat → Bool) (h : Constraints p) : clause p c2063 = true :=
  Snake9.LocalRup.prove_clause [c1863, c1037] c2063 (by decide) p (sat_cons (step1863 p h) (sat_cons (step1037 p h) (sat_nil p)))
def c2064 : List Lit := [(457, false), (463, false)]
theorem step2064 (p : Nat → Bool) (h : Constraints p) : clause p c2064 = true :=
  Snake9.LocalRup.prove_clause [c1862, c1049] c2064 (by decide) p (sat_cons (step1862 p h) (sat_cons (step1049 p h) (sat_nil p)))
def c2065 : List Lit := [(451, false), (465, false)]
theorem step2065 (p : Nat → Bool) (h : Constraints p) : clause p c2065 = true :=
  Snake9.LocalRup.prove_clause [c1853, c1053] c2065 (by decide) p (sat_cons (step1853 p h) (sat_cons (step1053 p h) (sat_nil p)))
def c2066 : List Lit := [(475, false), (477, false)]
theorem step2066 (p : Nat → Bool) (h : Constraints p) : clause p c2066 = true :=
  Snake9.LocalRup.prove_clause [c1874, c1061] c2066 (by decide) p (sat_cons (step1874 p h) (sat_cons (step1061 p h) (sat_nil p)))
def c2067 : List Lit := [(483, false), (485, false)]
theorem step2067 (p : Nat → Bool) (h : Constraints p) : clause p c2067 = true :=
  Snake9.LocalRup.prove_clause [c1873, c1069] c2067 (by decide) p (sat_cons (step1873 p h) (sat_cons (step1069 p h) (sat_nil p)))
def c2068 : List Lit := [(487, false), (493, false)]
theorem step2068 (p : Nat → Bool) (h : Constraints p) : clause p c2068 = true :=
  Snake9.LocalRup.prove_clause [c1860, c1076] c2068 (by decide) p (sat_cons (step1860 p h) (sat_cons (step1076 p h) (sat_nil p)))
def c2069 : List Lit := [(481, false), (495, false)]
theorem step2069 (p : Nat → Bool) (h : Constraints p) : clause p c2069 = true :=
  Snake9.LocalRup.prove_clause [c1852, c1081] c2069 (by decide) p (sat_cons (step1852 p h) (sat_cons (step1081 p h) (sat_nil p)))
def c2070 : List Lit := [(467, false), (497, false)]
theorem step2070 (p : Nat → Bool) (h : Constraints p) : clause p c2070 = true :=
  Snake9.LocalRup.prove_clause [c1848, c1086] c2070 (by decide) p (sat_cons (step1848 p h) (sat_cons (step1086 p h) (sat_nil p)))
def c2071 : List Lit := [(437, false), (499, false)]
theorem step2071 (p : Nat → Bool) (h : Constraints p) : clause p c2071 = true :=
  Snake9.LocalRup.prove_clause [c1846, c1091] c2071 (by decide) p (sat_cons (step1846 p h) (sat_cons (step1091 p h) (sat_nil p)))
def c2072 : List Lit := [(377, false), (501, false)]
theorem step2072 (p : Nat → Bool) (h : Constraints p) : clause p c2072 = true :=
  Snake9.LocalRup.prove_clause [c1096, c1094] c2072 (by decide) p (sat_cons (step1096 p h) (sat_cons (step1094 p h) (sat_nil p)))
def c2073 : List Lit := [(973, false), (1124, false)]
theorem step2073 (p : Nat → Bool) (h : Constraints p) : clause p c2073 = true :=
  Snake9.LocalRup.prove_clause [c1740, c1730] c2073 (by decide) p (sat_cons (step1740 p h) (sat_cons (step1730 p h) (sat_nil p)))
def c2074 : List Lit := [(974, false), (1123, false)]
theorem step2074 (p : Nat → Bool) (h : Constraints p) : clause p c2074 = true :=
  Snake9.LocalRup.prove_clause [c1740, c1731] c2074 (by decide) p (sat_cons (step1740 p h) (sat_cons (step1731 p h) (sat_nil p)))
def c2075 : List Lit := [(975, false), (1122, false)]
theorem step2075 (p : Nat → Bool) (h : Constraints p) : clause p c2075 = true :=
  Snake9.LocalRup.prove_clause [c1740, c1732] c2075 (by decide) p (sat_cons (step1740 p h) (sat_cons (step1732 p h) (sat_nil p)))
def c2076 : List Lit := [(976, false), (1121, false)]
theorem step2076 (p : Nat → Bool) (h : Constraints p) : clause p c2076 = true :=
  Snake9.LocalRup.prove_clause [c1740, c1733] c2076 (by decide) p (sat_cons (step1740 p h) (sat_cons (step1733 p h) (sat_nil p)))
def c2077 : List Lit := [(977, false), (1120, false)]
theorem step2077 (p : Nat → Bool) (h : Constraints p) : clause p c2077 = true :=
  Snake9.LocalRup.prove_clause [c1740, c1734] c2077 (by decide) p (sat_cons (step1740 p h) (sat_cons (step1734 p h) (sat_nil p)))
def c2078 : List Lit := [(978, false), (1119, false)]
theorem step2078 (p : Nat → Bool) (h : Constraints p) : clause p c2078 = true :=
  Snake9.LocalRup.prove_clause [c1740, c1735] c2078 (by decide) p (sat_cons (step1740 p h) (sat_cons (step1735 p h) (sat_nil p)))
def c2079 : List Lit := [(979, false), (1118, false)]
theorem step2079 (p : Nat → Bool) (h : Constraints p) : clause p c2079 = true :=
  Snake9.LocalRup.prove_clause [c1740, c1736] c2079 (by decide) p (sat_cons (step1740 p h) (sat_cons (step1736 p h) (sat_nil p)))
def c2080 : List Lit := [(980, false), (1117, false)]
theorem step2080 (p : Nat → Bool) (h : Constraints p) : clause p c2080 = true :=
  Snake9.LocalRup.prove_clause [c1740, c1737] c2080 (by decide) p (sat_cons (step1740 p h) (sat_cons (step1737 p h) (sat_nil p)))
def c2081 : List Lit := [(981, false), (1116, false)]
theorem step2081 (p : Nat → Bool) (h : Constraints p) : clause p c2081 = true :=
  Snake9.LocalRup.prove_clause [c1740, c1738] c2081 (by decide) p (sat_cons (step1740 p h) (sat_cons (step1738 p h) (sat_nil p)))
def c2082 : List Lit := [(982, false), (1115, false)]
theorem step2082 (p : Nat → Bool) (h : Constraints p) : clause p c2082 = true :=
  Snake9.LocalRup.prove_clause [c1740, c1739] c2082 (by decide) p (sat_cons (step1740 p h) (sat_cons (step1739 p h) (sat_nil p)))
def c2083 : List Lit := [(1677, false), (1833, false)]
theorem step2083 (p : Nat → Bool) (h : Constraints p) : clause p c2083 = true :=
  Snake9.LocalRup.prove_clause [c1801, c1800] c2083 (by decide) p (sat_cons (step1801 p h) (sat_cons (step1800 p h) (sat_nil p)))
def c2084 : List Lit := [(76, true), (90, true), (1036, true), (1010, false), (405, true)]
theorem step2084 (p : Nat → Bool) (h : Constraints p) : clause p c2084 = true :=
  Snake9.LocalRup.prove_clause [c1494, c1496, c1001, c985, c982, c977, c999, c997, c989, c988, c1477, c1995, c1485, c499, c1514, c1446, c1538, c1449, c1458, c1462, c1450, c1452, c1438, c1440, c1448, c1443, c1444, c1436, c492, c460, c471] c2084 (by decide) p (sat_cons (step1494 p h) (sat_cons (step1496 p h) (sat_cons (step1001 p h) (sat_cons (step985 p h) (sat_cons (step982 p h) (sat_cons (step977 p h) (sat_cons (step999 p h) (sat_cons (step997 p h) (sat_cons (step989 p h) (sat_cons (step988 p h) (sat_cons (step1477 p h) (sat_cons (step1995 p h) (sat_cons (step1485 p h) (sat_cons (step499 p h) (sat_cons (step1514 p h) (sat_cons (step1446 p h) (sat_cons (step1538 p h) (sat_cons (step1449 p h) (sat_cons (step1458 p h) (sat_cons (step1462 p h) (sat_cons (step1450 p h) (sat_cons (step1452 p h) (sat_cons (step1438 p h) (sat_cons (step1440 p h) (sat_cons (step1448 p h) (sat_cons (step1443 p h) (sat_cons (step1444 p h) (sat_cons (step1436 p h) (sat_cons (step492 p h) (sat_cons (step460 p h) (sat_cons (step471 p h) (sat_nil p))))))))))))))))))))))))))))))))
def c2085 : List Lit := [(993, true), (63, false), (66, false)]
theorem step2085 (p : Nat → Bool) (h : Constraints p) : clause p c2085 = true :=
  Snake9.LocalRup.prove_clause [c1443, c1444, c460] c2085 (by decide) p (sat_cons (step1443 p h) (sat_cons (step1444 p h) (sat_cons (step460 p h) (sat_nil p))))
def c2086 : List Lit := [(851, true), (6, false), (78, false)]
theorem step2086 (p : Nat → Bool) (h : Constraints p) : clause p c2086 = true :=
  Snake9.LocalRup.prove_clause [c1101, c1103, c1098, c27] c2086 (by decide) p (sat_cons (step1101 p h) (sat_cons (step1103 p h) (sat_cons (step1098 p h) (sat_cons (step27 p h) (sat_nil p)))))
def c2087 : List Lit := [(945, true), (938, false), (63, false), (66, false)]
theorem step2087 (p : Nat → Bool) (h : Constraints p) : clause p c2087 = true :=
  Snake9.LocalRup.prove_clause [c1296, c1305, c1309, c1299, c1284, c1291, c1276, c446] c2087 (by decide) p (sat_cons (step1296 p h) (sat_cons (step1305 p h) (sat_cons (step1309 p h) (sat_cons (step1299 p h) (sat_cons (step1284 p h) (sat_cons (step1291 p h) (sat_cons (step1276 p h) (sat_cons (step446 p h) (sat_nil p)))))))))
def c2088 : List Lit := [(293, false), (19, false), (28, false), (27, true), (63, false), (66, false)]
theorem step2088 (p : Nat → Bool) (h : Constraints p) : clause p c2088 = true :=
  Snake9.LocalRup.prove_clause [c879, c2039, c2042, c872, c891, c869, c889, c138, c886, c418, c182] c2088 (by decide) p (sat_cons (step879 p h) (sat_cons (step2039 p h) (sat_cons (step2042 p h) (sat_cons (step872 p h) (sat_cons (step891 p h) (sat_cons (step869 p h) (sat_cons (step889 p h) (sat_cons (step138 p h) (sat_cons (step886 p h) (sat_cons (step418 p h) (sat_cons (step182 p h) (sat_nil p))))))))))))
def c2089 : List Lit := [(956, true), (921, false), (38, false), (2, false), (941, false), (47, true)]
theorem step2089 (p : Nat → Bool) (h : Constraints p) : clause p c2089 = true :=
  Snake9.LocalRup.prove_clause [c1276, c1284, c1310, c1340, c1334, c1315, c1287, c1278, c245, c244, c1243, c1235, c1251, c1238, c1262] c2089 (by decide) p (sat_cons (step1276 p h) (sat_cons (step1284 p h) (sat_cons (step1310 p h) (sat_cons (step1340 p h) (sat_cons (step1334 p h) (sat_cons (step1315 p h) (sat_cons (step1287 p h) (sat_cons (step1278 p h) (sat_cons (step245 p h) (sat_cons (step244 p h) (sat_cons (step1243 p h) (sat_cons (step1235 p h) (sat_cons (step1251 p h) (sat_cons (step1238 p h) (sat_cons (step1262 p h) (sat_nil p))))))))))))))))
def c2090 : List Lit := [(922, true), (913, false), (38, false), (2, false), (1, false), (341, true)]
theorem step2090 (p : Nat → Bool) (h : Constraints p) : clause p c2090 = true :=
  Snake9.LocalRup.prove_clause [c1251, c929, c918, c914, c927, c924, c920, c1258, c1262, c1254, c1252, c1238, c1246, c1247, c1235, c295, c294, c243, c1807, c1245, c1928, c265, c239, c30, c277] c2090 (by decide) p (sat_cons (step1251 p h) (sat_cons (step929 p h) (sat_cons (step918 p h) (sat_cons (step914 p h) (sat_cons (step927 p h) (sat_cons (step924 p h) (sat_cons (step920 p h) (sat_cons (step1258 p h) (sat_cons (step1262 p h) (sat_cons (step1254 p h) (sat_cons (step1252 p h) (sat_cons (step1238 p h) (sat_cons (step1246 p h) (sat_cons (step1247 p h) (sat_cons (step1235 p h) (sat_cons (step295 p h) (sat_cons (step294 p h) (sat_cons (step243 p h) (sat_cons (step1807 p h) (sat_cons (step1245 p h) (sat_cons (step1928 p h) (sat_cons (step265 p h) (sat_cons (step239 p h) (sat_cons (step30 p h) (sat_cons (step277 p h) (sat_nil p))))))))))))))))))))))))))
def c2091 : List Lit := [(930, true), (54, false), (44, false)]
theorem step2091 (p : Nat → Bool) (h : Constraints p) : clause p c2091 = true :=
  Snake9.LocalRup.prove_clause [c1279, c1280, c366] c2091 (by decide) p (sat_cons (step1279 p h) (sat_cons (step1280 p h) (sat_cons (step366 p h) (sat_nil p))))
def c2092 : List Lit := [(35, true), (16, true), (61, true), (67, true), (160, true), (33, false), (53, true)]
theorem step2092 (p : Nat → Bool) (h : Constraints p) : clause p c2092 = true :=
  Snake9.LocalRup.prove_clause [c204, c205, c1823, c1992] c2092 (by decide) p (sat_cons (step204 p h) (sat_cons (step205 p h) (sat_cons (step1823 p h) (sat_cons (step1992 p h) (sat_nil p)))))
def c2093 : List Lit := [(35, false), (15, false), (26, false), (142, true), (34, false)]
theorem step2093 (p : Nat → Bool) (h : Constraints p) : clause p c2093 = true :=
  Snake9.LocalRup.prove_clause [c216, c209, c101] c2093 (by decide) p (sat_cons (step216 p h) (sat_cons (step209 p h) (sat_cons (step101 p h) (sat_nil p))))
def c2094 : List Lit := [(1088, true), (243, true), (120, true)]
theorem step2094 (p : Nat → Bool) (h : Constraints p) : clause p c2094 = true :=
  Snake9.LocalRup.prove_clause [c1625, c1632, c1639, c1642, c1635, c1633, c1617, c1626, c1627, c1628, c1615, c768, c708] c2094 (by decide) p (sat_cons (step1625 p h) (sat_cons (step1632 p h) (sat_cons (step1639 p h) (sat_cons (step1642 p h) (sat_cons (step1635 p h) (sat_cons (step1633 p h) (sat_cons (step1617 p h) (sat_cons (step1626 p h) (sat_cons (step1627 p h) (sat_cons (step1628 p h) (sat_cons (step1615 p h) (sat_cons (step768 p h) (sat_cons (step708 p h) (sat_nil p))))))))))))))
def c2095 : List Lit := [(119, true), (127, true), (122, false), (101, true), (249, true)]
theorem step2095 (p : Nat → Bool) (h : Constraints p) : clause p c2095 = true :=
  Snake9.LocalRup.prove_clause [c747, c749, c1898] c2095 (by decide) p (sat_cons (step747 p h) (sat_cons (step749 p h) (sat_cons (step1898 p h) (sat_nil p))))
def c2096 : List Lit := [(896, true), (874, false), (25, true), (150, true)]
theorem step2096 (p : Nat → Bool) (h : Constraints p) : clause p c2096 = true :=
  Snake9.LocalRup.prove_clause [c1153, c1161, c1177, c1192, c1196, c1178, c1124, c1164, c1101, c1103, c1155, c1098, c153, c25] c2096 (by decide) p (sat_cons (step1153 p h) (sat_cons (step1161 p h) (sat_cons (step1177 p h) (sat_cons (step1192 p h) (sat_cons (step1196 p h) (sat_cons (step1178 p h) (sat_cons (step1124 p h) (sat_cons (step1164 p h) (sat_cons (step1101 p h) (sat_cons (step1103 p h) (sat_cons (step1155 p h) (sat_cons (step1098 p h) (sat_cons (step153 p h) (sat_cons (step25 p h) (sat_nil p)))))))))))))))
def c2097 : List Lit := [(862, true), (25, true), (132, true)]
theorem step2097 (p : Nat → Bool) (h : Constraints p) : clause p c2097 = true :=
  Snake9.LocalRup.prove_clause [c1120, c1124, c1112, c1114, c1101, c1103, c1109, c1107, c1098, c28, c21, c22, c1803, c1923] c2097 (by decide) p (sat_cons (step1120 p h) (sat_cons (step1124 p h) (sat_cons (step1112 p h) (sat_cons (step1114 p h) (sat_cons (step1101 p h) (sat_cons (step1103 p h) (sat_cons (step1109 p h) (sat_cons (step1107 p h) (sat_cons (step1098 p h) (sat_cons (step28 p h) (sat_cons (step21 p h) (sat_cons (step22 p h) (sat_cons (step1803 p h) (sat_cons (step1923 p h) (sat_nil p)))))))))))))))
def c2098 : List Lit := [(132, true), (6, true), (25, true), (5, false)]
theorem step2098 (p : Nat → Bool) (h : Constraints p) : clause p c2098 = true :=
  Snake9.LocalRup.prove_clause [c21, c22, c1803, c1923] c2098 (by decide) p (sat_cons (step21 p h) (sat_cons (step22 p h) (sat_cons (step1803 p h) (sat_cons (step1923 p h) (sat_nil p)))))
def c2099 : List Lit := [(1047, false), (1065, true), (124, false), (1055, false), (230, true)]
theorem step2099 (p : Nat → Bool) (h : Constraints p) : clause p c2099 = true :=
  Snake9.LocalRup.prove_clause [c1584, c1599, c1570, c1571, c1595, c1565, c1585, c658, c1580, c688] c2099 (by decide) p (sat_cons (step1584 p h) (sat_cons (step1599 p h) (sat_cons (step1570 p h) (sat_cons (step1571 p h) (sat_cons (step1595 p h) (sat_cons (step1565 p h) (sat_cons (step1585 p h) (sat_cons (step658 p h) (sat_cons (step1580 p h) (sat_cons (step688 p h) (sat_nil p)))))))))))
end B112E256
