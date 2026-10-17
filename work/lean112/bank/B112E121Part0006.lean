import B112E121Part0005
namespace B112E121
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2108 : List Lit := [(1005, false), (1151, false)]
theorem step2108 (p : Nat → Bool) (h : Constraints p) : clause p c2108 = true :=
  Snake9.LocalRup.prove_clause [c1649, c1645] c2108 (by decide) p (sat_cons (step1649 p h) (sat_cons (step1645 p h) (sat_nil p)))
def c2109 : List Lit := [(1006, false), (1150, false)]
theorem step2109 (p : Nat → Bool) (h : Constraints p) : clause p c2109 = true :=
  Snake9.LocalRup.prove_clause [c1649, c1646] c2109 (by decide) p (sat_cons (step1649 p h) (sat_cons (step1646 p h) (sat_nil p)))
def c2110 : List Lit := [(1007, false), (1149, false)]
theorem step2110 (p : Nat → Bool) (h : Constraints p) : clause p c2110 = true :=
  Snake9.LocalRup.prove_clause [c1649, c1647] c2110 (by decide) p (sat_cons (step1649 p h) (sat_cons (step1647 p h) (sat_nil p)))
def c2111 : List Lit := [(1008, false), (1148, false)]
theorem step2111 (p : Nat → Bool) (h : Constraints p) : clause p c2111 = true :=
  Snake9.LocalRup.prove_clause [c1649, c1648] c2111 (by decide) p (sat_cons (step1649 p h) (sat_cons (step1648 p h) (sat_nil p)))
def c2112 : List Lit := [(868, false), (8, false), (916, true), (9, true), (889, false), (899, false)]
theorem step2112 (p : Nat → Bool) (h : Constraints p) : clause p c2112 = true :=
  Snake9.LocalRup.prove_clause [c1144, c1171, c1208, c1101, c1108, c1124, c1125, c1202, c1111, c1109, c1176, c1102, c1104, c1147, c47, c1139] c2112 (by decide) p (sat_cons (step1144 p h) (sat_cons (step1171 p h) (sat_cons (step1208 p h) (sat_cons (step1101 p h) (sat_cons (step1108 p h) (sat_cons (step1124 p h) (sat_cons (step1125 p h) (sat_cons (step1202 p h) (sat_cons (step1111 p h) (sat_cons (step1109 p h) (sat_cons (step1176 p h) (sat_cons (step1102 p h) (sat_cons (step1104 p h) (sat_cons (step1147 p h) (sat_cons (step47 p h) (sat_cons (step1139 p h) (sat_nil p)))))))))))))))))
def c2113 : List Lit := [(887, true), (16, false), (8, false), (13, true)]
theorem step2113 (p : Nat → Bool) (h : Constraints p) : clause p c2113 = true :=
  Snake9.LocalRup.prove_clause [c1138, c1139, c181, c180, c1929] c2113 (by decide) p (sat_cons (step1138 p h) (sat_cons (step1139 p h) (sat_cons (step181 p h) (sat_cons (step180 p h) (sat_cons (step1929 p h) (sat_nil p))))))
def c2114 : List Lit := [(24, false), (900, true), (26, false), (14, false)]
theorem step2114 (p : Nat → Bool) (h : Constraints p) : clause p c2114 = true :=
  Snake9.LocalRup.prove_clause [c329, c328, c1155, c1153, c1161] c2114 (by decide) p (sat_cons (step329 p h) (sat_cons (step328 p h) (sat_cons (step1155 p h) (sat_cons (step1153 p h) (sat_cons (step1161 p h) (sat_nil p))))))
def c2115 : List Lit := [(887, false), (906, true), (26, false), (889, false), (14, false)]
theorem step2115 (p : Nat → Bool) (h : Constraints p) : clause p c2115 = true :=
  Snake9.LocalRup.prove_clause [c1879, c1181, c1147, c1148, c1177, c2114, c1143, c326, c327, c1153, c1155, c1161] c2115 (by decide) p (sat_cons (step1879 p h) (sat_cons (step1181 p h) (sat_cons (step1147 p h) (sat_cons (step1148 p h) (sat_cons (step1177 p h) (sat_cons (step2114 p h) (sat_cons (step1143 p h) (sat_cons (step326 p h) (sat_cons (step327 p h) (sat_cons (step1153 p h) (sat_cons (step1155 p h) (sat_cons (step1161 p h) (sat_nil p)))))))))))))
def c2116 : List Lit := [(947, true), (36, true), (30, false), (13, true)]
theorem step2116 (p : Nat → Bool) (h : Constraints p) : clause p c2116 = true :=
  Snake9.LocalRup.prove_clause [c1239, c1758, c1771, c1759, c1241, c1945, c1263, c1763, c1254, c1249, c1761, c399, c1949] c2116 (by decide) p (sat_cons (step1239 p h) (sat_cons (step1758 p h) (sat_cons (step1771 p h) (sat_cons (step1759 p h) (sat_cons (step1241 p h) (sat_cons (step1945 p h) (sat_cons (step1263 p h) (sat_cons (step1763 p h) (sat_cons (step1254 p h) (sat_cons (step1249 p h) (sat_cons (step1761 p h) (sat_cons (step399 p h) (sat_cons (step1949 p h) (sat_nil p))))))))))))))
def c2117 : List Lit := [(905, true), (897, false), (26, false), (891, false), (14, false)]
theorem step2117 (p : Nat → Bool) (h : Constraints p) : clause p c2117 = true :=
  Snake9.LocalRup.prove_clause [c1879, c1176, c1172, c1145, c2114, c1161, c1143, c1153, c326] c2117 (by decide) p (sat_cons (step1879 p h) (sat_cons (step1176 p h) (sat_cons (step1172 p h) (sat_cons (step1145 p h) (sat_cons (step2114 p h) (sat_cons (step1161 p h) (sat_cons (step1143 p h) (sat_cons (step1153 p h) (sat_cons (step326 p h) (sat_nil p))))))))))
def c2118 : List Lit := [(1032, true), (71, true), (87, true), (73, true)]
theorem step2118 (p : Nat → Bool) (h : Constraints p) : clause p c2118 = true :=
  Snake9.LocalRup.prove_clause [c1397, c1404, c1411, c1415, c1407, c1405, c1391, c1398, c1399, c1388, c527, c1987] c2118 (by decide) p (sat_cons (step1397 p h) (sat_cons (step1404 p h) (sat_cons (step1411 p h) (sat_cons (step1415 p h) (sat_cons (step1407 p h) (sat_cons (step1405 p h) (sat_cons (step1391 p h) (sat_cons (step1398 p h) (sat_cons (step1399 p h) (sat_cons (step1388 p h) (sat_cons (step527 p h) (sat_cons (step1987 p h) (sat_nil p)))))))))))))
def c2119 : List Lit := [(1028, true), (70, false), (69, false), (71, true)]
theorem step2119 (p : Nat → Bool) (h : Constraints p) : clause p c2119 = true :=
  Snake9.LocalRup.prove_clause [c1397, c1407, c1405, c1398, c1399, c527] c2119 (by decide) p (sat_cons (step1397 p h) (sat_cons (step1407 p h) (sat_cons (step1405 p h) (sat_cons (step1398 p h) (sat_cons (step1399 p h) (sat_cons (step527 p h) (sat_nil p)))))))
def c2120 : List Lit := [(880, true), (9, true)]
theorem step2120 (p : Nat → Bool) (h : Constraints p) : clause p c2120 = true :=
  Snake9.LocalRup.prove_clause [c1101, c1115, c1880, c1111, c1102] c2120 (by decide) p (sat_cons (step1101 p h) (sat_cons (step1115 p h) (sat_cons (step1880 p h) (sat_cons (step1111 p h) (sat_cons (step1102 p h) (sat_nil p))))))
def c2121 : List Lit := [(71, true), (77, true), (1033, true), (87, true), (73, true)]
theorem step2121 (p : Nat → Bool) (h : Constraints p) : clause p c2121 = true :=
  Snake9.LocalRup.prove_clause [c1412, c1400, c1408, c1397, c1398, c1405, c1406, c1416, c1401, c1391, c1388, c1987, c527] c2121 (by decide) p (sat_cons (step1412 p h) (sat_cons (step1400 p h) (sat_cons (step1408 p h) (sat_cons (step1397 p h) (sat_cons (step1398 p h) (sat_cons (step1405 p h) (sat_cons (step1406 p h) (sat_cons (step1416 p h) (sat_cons (step1401 p h) (sat_cons (step1391 p h) (sat_cons (step1388 p h) (sat_cons (step1987 p h) (sat_cons (step527 p h) (sat_nil p))))))))))))))
def c2122 : List Lit := [(968, false), (1001, true), (880, false), (26, false), (889, false), (14, false), (13, true)]
theorem step2122 (p : Nat → Bool) (h : Constraints p) : clause p c2122 = true :=
  Snake9.LocalRup.prove_clause [c1144, c1777, c1350, c1196, c2115, c1899, c1900, c2117, c1195, c1345, c1322, c1768, c1770, c1763, c1254, c1758, c1249, c1761, c1240, c1949, c1945, c399] c2122 (by decide) p (sat_cons (step1144 p h) (sat_cons (step1777 p h) (sat_cons (step1350 p h) (sat_cons (step1196 p h) (sat_cons (step2115 p h) (sat_cons (step1899 p h) (sat_cons (step1900 p h) (sat_cons (step2117 p h) (sat_cons (step1195 p h) (sat_cons (step1345 p h) (sat_cons (step1322 p h) (sat_cons (step1768 p h) (sat_cons (step1770 p h) (sat_cons (step1763 p h) (sat_cons (step1254 p h) (sat_cons (step1758 p h) (sat_cons (step1249 p h) (sat_cons (step1761 p h) (sat_cons (step1240 p h) (sat_cons (step1949 p h) (sat_cons (step1945 p h) (sat_cons (step399 p h) (sat_nil p)))))))))))))))))))))))
def c2123 : List Lit := [(43, false), (30, false), (15, false), (19, false), (901, true), (13, true)]
theorem step2123 (p : Nat → Bool) (h : Constraints p) : clause p c2123 = true :=
  Snake9.LocalRup.prove_clause [c1901, c357, c359, c1153, c1157, c1162] c2123 (by decide) p (sat_cons (step1901 p h) (sat_cons (step357 p h) (sat_cons (step359 p h) (sat_cons (step1153 p h) (sat_cons (step1157 p h) (sat_cons (step1162 p h) (sat_nil p)))))))
def c2124 : List Lit := [(28, false), (877, true), (887, true), (964, true), (9, true), (13, true)]
theorem step2124 (p : Nat → Bool) (h : Constraints p) : clause p c2124 = true :=
  Snake9.LocalRup.prove_clause [c1900, c1139, c1138, c197, c358, c1929, c1285, c200, c1291, c1104, c1283, c1112, c1102, c1917, c261] c2124 (by decide) p (sat_cons (step1900 p h) (sat_cons (step1139 p h) (sat_cons (step1138 p h) (sat_cons (step197 p h) (sat_cons (step358 p h) (sat_cons (step1929 p h) (sat_cons (step1285 p h) (sat_cons (step200 p h) (sat_cons (step1291 p h) (sat_cons (step1104 p h) (sat_cons (step1283 p h) (sat_cons (step1112 p h) (sat_cons (step1102 p h) (sat_cons (step1917 p h) (sat_cons (step261 p h) (sat_nil p))))))))))))))))
def c2125 : List Lit := [(895, false), (28, true), (897, false), (901, true), (906, true), (26, false), (14, false)]
theorem step2125 (p : Nat → Bool) (h : Constraints p) : clause p c2125 = true :=
  Snake9.LocalRup.prove_clause [c1162, c1161, c1177, c1145, c1157, c329, c327, c1143] c2125 (by decide) p (sat_cons (step1162 p h) (sat_cons (step1161 p h) (sat_cons (step1177 p h) (sat_cons (step1145 p h) (sat_cons (step1157 p h) (sat_cons (step329 p h) (sat_cons (step327 p h) (sat_cons (step1143 p h) (sat_nil p)))))))))
def c2126 : List Lit := [(28, true), (897, false), (14, false), (901, true), (906, true), (26, false)]
theorem step2126 (p : Nat → Bool) (h : Constraints p) : clause p c2126 = true :=
  Snake9.LocalRup.prove_clause [c2125, c1153, c328, c330, c326, c1157, c1143, c1159, c1145, c1177] c2126 (by decide) p (sat_cons (step2125 p h) (sat_cons (step1153 p h) (sat_cons (step328 p h) (sat_cons (step330 p h) (sat_cons (step326 p h) (sat_cons (step1157 p h) (sat_cons (step1143 p h) (sat_cons (step1159 p h) (sat_cons (step1145 p h) (sat_cons (step1177 p h) (sat_nil p)))))))))))
def c2127 : List Lit := [(43, false), (902, true), (907, true), (28, true), (36, false), (30, false), (15, false), (19, false), (968, true), (13, true)]
theorem step2127 (p : Nat → Bool) (h : Constraints p) : clause p c2127 = true :=
  Snake9.LocalRup.prove_clause [c1901, c359, c361, c2123, c1157, c1285, c1178, c1165, c1288, c1145, c1154, c1299, c190, c1935, c1934, c1274, c1685, c1271, c1143, c236] c2127 (by decide) p (sat_cons (step1901 p h) (sat_cons (step359 p h) (sat_cons (step361 p h) (sat_cons (step2123 p h) (sat_cons (step1157 p h) (sat_cons (step1285 p h) (sat_cons (step1178 p h) (sat_cons (step1165 p h) (sat_cons (step1288 p h) (sat_cons (step1145 p h) (sat_cons (step1154 p h) (sat_cons (step1299 p h) (sat_cons (step190 p h) (sat_cons (step1935 p h) (sat_cons (step1934 p h) (sat_cons (step1274 p h) (sat_cons (step1685 p h) (sat_cons (step1271 p h) (sat_cons (step1143 p h) (sat_cons (step236 p h) (sat_nil p)))))))))))))))))))))
def c2128 : List Lit := [(967, true)]
theorem step2128 (p : Nat → Bool) (h : Constraints p) : clause p c2128 = true :=
  Snake9.LocalRup.prove_clause [c1295, c1298, c1288, c1274, c1286, c1272, c1852] c2128 (by decide) p (sat_cons (step1295 p h) (sat_cons (step1298 p h) (sat_cons (step1288 p h) (sat_cons (step1274 p h) (sat_cons (step1286 p h) (sat_cons (step1272 p h) (sat_cons (step1852 p h) (sat_nil p))))))))
def c2129 : List Lit := [(978, true)]
theorem step2129 (p : Nat → Bool) (h : Constraints p) : clause p c2129 = true :=
  Snake9.LocalRup.prove_clause [c2128, c1776] c2129 (by decide) p (sat_cons (step2128 p h) (sat_cons (step1776 p h) (sat_nil p)))
def c2130 : List Lit := [(9, false), (881, true), (887, true), (13, true)]
theorem step2130 (p : Nat → Bool) (h : Constraints p) : clause p c2130 = true :=
  Snake9.LocalRup.prove_clause [c1139, c1138, c1836, c1895, c1087, c1100, c1094, c1120, c1902, c1109, c1103, c1104, c81, c1922, c200] c2130 (by decide) p (sat_cons (step1139 p h) (sat_cons (step1138 p h) (sat_cons (step1836 p h) (sat_cons (step1895 p h) (sat_cons (step1087 p h) (sat_cons (step1100 p h) (sat_cons (step1094 p h) (sat_cons (step1120 p h) (sat_cons (step1902 p h) (sat_cons (step1109 p h) (sat_cons (step1103 p h) (sat_cons (step1104 p h) (sat_cons (step81 p h) (sat_cons (step1922 p h) (sat_cons (step200 p h) (sat_nil p))))))))))))))))
def c2131 : List Lit := [(980, true), (43, true), (961, false), (937, false), (13, true)]
theorem step2131 (p : Nat → Bool) (h : Constraints p) : clause p c2131 = true :=
  Snake9.LocalRup.prove_clause [c2128, c1288, c1763, c1768, c1322, c1328, c1296, c1299, c1769, c1263, c1291, c1276, c1255, c1758, c1283, c1268, c1761, c1240, c1964, c1949, c1945, c466, c395, c392, c985, c984, c2059] c2131 (by decide) p (sat_cons (step2128 p h) (sat_cons (step1288 p h) (sat_cons (step1763 p h) (sat_cons (step1768 p h) (sat_cons (step1322 p h) (sat_cons (step1328 p h) (sat_cons (step1296 p h) (sat_cons (step1299 p h) (sat_cons (step1769 p h) (sat_cons (step1263 p h) (sat_cons (step1291 p h) (sat_cons (step1276 p h) (sat_cons (step1255 p h) (sat_cons (step1758 p h) (sat_cons (step1283 p h) (sat_cons (step1268 p h) (sat_cons (step1761 p h) (sat_cons (step1240 p h) (sat_cons (step1964 p h) (sat_cons (step1949 p h) (sat_cons (step1945 p h) (sat_cons (step466 p h) (sat_cons (step395 p h) (sat_cons (step392 p h) (sat_cons (step985 p h) (sat_cons (step984 p h) (sat_cons (step2059 p h) (sat_nil p))))))))))))))))))))))))))))
def c2132 : List Lit := [(947, true), (43, true), (937, false), (30, false), (13, true)]
theorem step2132 (p : Nat → Bool) (h : Constraints p) : clause p c2132 = true :=
  Snake9.LocalRup.prove_clause [c1763, c1769, c1263, c1255, c1758, c1761, c1240, c1949, c1945, c1946, c395, c985, c986, c2059, c989, c984, c2060, c392, c982, c302, c978, c1909, c977, c1943] c2132 (by decide) p (sat_cons (step1763 p h) (sat_cons (step1769 p h) (sat_cons (step1263 p h) (sat_cons (step1255 p h) (sat_cons (step1758 p h) (sat_cons (step1761 p h) (sat_cons (step1240 p h) (sat_cons (step1949 p h) (sat_cons (step1945 p h) (sat_cons (step1946 p h) (sat_cons (step395 p h) (sat_cons (step985 p h) (sat_cons (step986 p h) (sat_cons (step2059 p h) (sat_cons (step989 p h) (sat_cons (step984 p h) (sat_cons (step2060 p h) (sat_cons (step392 p h) (sat_cons (step982 p h) (sat_cons (step302 p h) (sat_cons (step978 p h) (sat_cons (step1909 p h) (sat_cons (step977 p h) (sat_cons (step1943 p h) (sat_nil p)))))))))))))))))))))))))
def c2133 : List Lit := [(947, true), (937, false), (30, false), (13, true)]
theorem step2133 (p : Nat → Bool) (h : Constraints p) : clause p c2133 = true :=
  Snake9.LocalRup.prove_clause [c1763, c1769, c1263, c2132, c1255, c1758, c1761, c1240, c1949, c1945, c399] c2133 (by decide) p (sat_cons (step1763 p h) (sat_cons (step1769 p h) (sat_cons (step1263 p h) (sat_cons (step2132 p h) (sat_cons (step1255 p h) (sat_cons (step1758 p h) (sat_cons (step1761 p h) (sat_cons (step1240 p h) (sat_cons (step1949 p h) (sat_cons (step1945 p h) (sat_cons (step399 p h) (sat_nil p))))))))))))
def c2134 : List Lit := [(11, false), (10, false), (1, false)]
theorem step2134 (p : Nat → Bool) (h : Constraints p) : clause p c2134 = true :=
  Snake9.LocalRup.prove_clause [c27, c1905] c2134 (by decide) p (sat_cons (step27 p h) (sat_cons (step1905 p h) (sat_nil p)))
def c2135 : List Lit := [(881, true), (9, true), (3, true)]
theorem step2135 (p : Nat → Bool) (h : Constraints p) : clause p c2135 = true :=
  Snake9.LocalRup.prove_clause [c1101, c1108, c1086, c1094, c1120, c1124, c1111, c1109, c1097, c1102, c1104, c1088, c2134] c2135 (by decide) p (sat_cons (step1101 p h) (sat_cons (step1108 p h) (sat_cons (step1086 p h) (sat_cons (step1094 p h) (sat_cons (step1120 p h) (sat_cons (step1124 p h) (sat_cons (step1111 p h) (sat_cons (step1109 p h) (sat_cons (step1097 p h) (sat_cons (step1102 p h) (sat_cons (step1104 p h) (sat_cons (step1088 p h) (sat_cons (step2134 p h) (sat_nil p))))))))))))))
def c2136 : List Lit := [(93, true), (1053, true), (88, true), (92, false), (47, false)]
theorem step2136 (p : Nat → Bool) (h : Constraints p) : clause p c2136 = true :=
  Snake9.LocalRup.prove_clause [c1438, c1447, c1440, c1442, c1449, c665, c1439] c2136 (by decide) p (sat_cons (step1438 p h) (sat_cons (step1447 p h) (sat_cons (step1440 p h) (sat_cons (step1442 p h) (sat_cons (step1449 p h) (sat_cons (step665 p h) (sat_cons (step1439 p h) (sat_nil p))))))))
def c2137 : List Lit := [(1053, true), (88, true), (47, false), (92, false)]
theorem step2137 (p : Nat → Bool) (h : Constraints p) : clause p c2137 = true :=
  Snake9.LocalRup.prove_clause [c2136, c666, c669, c1439, c1441, c1449] c2137 (by decide) p (sat_cons (step2136 p h) (sat_cons (step666 p h) (sat_cons (step669 p h) (sat_cons (step1439 p h) (sat_cons (step1441 p h) (sat_cons (step1449 p h) (sat_nil p)))))))
def c2138 : List Lit := [(876, true), (24, false), (9, false), (887, true), (13, true)]
theorem step2138 (p : Nat → Bool) (h : Constraints p) : clause p c2138 = true :=
  Snake9.LocalRup.prove_clause [c1895, c1100, c1139, c1138, c1902, c1109, c1103, c1104, c87, c200, c1922] c2138 (by decide) p (sat_cons (step1895 p h) (sat_cons (step1100 p h) (sat_cons (step1139 p h) (sat_cons (step1138 p h) (sat_cons (step1902 p h) (sat_cons (step1109 p h) (sat_cons (step1103 p h) (sat_cons (step1104 p h) (sat_cons (step87 p h) (sat_cons (step200 p h) (sat_cons (step1922 p h) (sat_nil p))))))))))))
def c2139 : List Lit := [(865, true), (22, false), (53, false), (9, false)]
theorem step2139 (p : Nat → Bool) (h : Constraints p) : clause p c2139 = true :=
  Snake9.LocalRup.prove_clause [c1089, c1090, c19, c1814] c2139 (by decide) p (sat_cons (step1089 p h) (sat_cons (step1090 p h) (sat_cons (step19 p h) (sat_cons (step1814 p h) (sat_nil p)))))
def c2140 : List Lit := [(11, false), (24, false), (9, false), (887, true), (13, true)]
theorem step2140 (p : Nat → Bool) (h : Constraints p) : clause p c2140 = true :=
  Snake9.LocalRup.prove_clause [c1139, c1138, c41, c200, c82, c1922] c2140 (by decide) p (sat_cons (step1139 p h) (sat_cons (step1138 p h) (sat_cons (step41 p h) (sat_cons (step200 p h) (sat_cons (step82 p h) (sat_cons (step1922 p h) (sat_nil p)))))))
def c2141 : List Lit := [(1053, false), (1067, true), (86, true)]
theorem step2141 (p : Nat → Bool) (h : Constraints p) : clause p c2141 = true :=
  Snake9.LocalRup.prove_clause [c1469, c2078, c1460, c1473, c1431, c1410, c1429, c1402, c1404, c2006, c1400, c1396, c554] c2141 (by decide) p (sat_cons (step1469 p h) (sat_cons (step2078 p h) (sat_cons (step1460 p h) (sat_cons (step1473 p h) (sat_cons (step1431 p h) (sat_cons (step1410 p h) (sat_cons (step1429 p h) (sat_cons (step1402 p h) (sat_cons (step1404 p h) (sat_cons (step2006 p h) (sat_cons (step1400 p h) (sat_cons (step1396 p h) (sat_cons (step554 p h) (sat_nil p))))))))))))))
def c2142 : List Lit := [(47, false), (1053, true), (88, true), (13, true)]
theorem step2142 (p : Nat → Bool) (h : Constraints p) : clause p c2142 = true :=
  Snake9.LocalRup.prove_clause [c1963, c2137] c2142 (by decide) p (sat_cons (step1963 p h) (sat_cons (step2137 p h) (sat_nil p)))
def c2143 : List Lit := [(1087, true), (100, false), (53, false)]
theorem step2143 (p : Nat → Bool) (h : Constraints p) : clause p c2143 = true :=
  Snake9.LocalRup.prove_clause [c1504, c1505, c777] c2143 (by decide) p (sat_cons (step1504 p h) (sat_cons (step1505 p h) (sat_cons (step777 p h) (sat_nil p))))
def c2144 : List Lit := [(1031, true), (70, false), (9, false)]
theorem step2144 (p : Nat → Bool) (h : Constraints p) : clause p c2144 = true :=
  Snake9.LocalRup.prove_clause [c1410, c1414, c1402, c1391, c1399, c1388, c522] c2144 (by decide) p (sat_cons (step1410 p h) (sat_cons (step1414 p h) (sat_cons (step1402 p h) (sat_cons (step1391 p h) (sat_cons (step1399 p h) (sat_cons (step1388 p h) (sat_cons (step522 p h) (sat_nil p))))))))
def c2145 : List Lit := [(78, false), (1088, true), (100, false), (53, false)]
theorem step2145 (p : Nat → Bool) (h : Constraints p) : clause p c2145 = true :=
  Snake9.LocalRup.prove_clause [c768, c767, c1506] c2145 (by decide) p (sat_cons (step768 p h) (sat_cons (step767 p h) (sat_cons (step1506 p h) (sat_nil p))))
def c2146 : List Lit := [(106, false), (1089, true), (57, false)]
theorem step2146 (p : Nat → Bool) (h : Constraints p) : clause p c2146 = true :=
  Snake9.LocalRup.prove_clause [c1508, c1507, c840, c820, c2029] c2146 (by decide) p (sat_cons (step1508 p h) (sat_cons (step1507 p h) (sat_cons (step840 p h) (sat_cons (step820 p h) (sat_cons (step2029 p h) (sat_nil p))))))
def c2147 : List Lit := [(47, false), (1053, true), (1067, true), (70, false), (9, false), (13, true)]
theorem step2147 (p : Nat → Bool) (h : Constraints p) : clause p c2147 = true :=
  Snake9.LocalRup.prove_clause [c2085, c1412, c1963, c2142, c526, c525, c1399, c1402, c1408, c1822, c1398] c2147 (by decide) p (sat_cons (step2085 p h) (sat_cons (step1412 p h) (sat_cons (step1963 p h) (sat_cons (step2142 p h) (sat_cons (step526 p h) (sat_cons (step525 p h) (sat_cons (step1399 p h) (sat_cons (step1402 p h) (sat_cons (step1408 p h) (sat_cons (step1822 p h) (sat_cons (step1398 p h) (sat_nil p))))))))))))
def c2148 : List Lit := [(78, true), (1028, true), (72, false), (14, false)]
theorem step2148 (p : Nat → Bool) (h : Constraints p) : clause p c2148 = true :=
  Snake9.LocalRup.prove_clause [c1403, c1399, c1401, c1405, c539, c1397] c2148 (by decide) p (sat_cons (step1403 p h) (sat_cons (step1399 p h) (sat_cons (step1401 p h) (sat_cons (step1405 p h) (sat_cons (step539 p h) (sat_cons (step1397 p h) (sat_nil p)))))))
def c2149 : List Lit := [(27, false), (15, false), (9, false), (20, true)]
theorem step2149 (p : Nat → Bool) (h : Constraints p) : clause p c2149 = true :=
  Snake9.LocalRup.prove_clause [c185, c1935] c2149 (by decide) p (sat_cons (step185 p h) (sat_cons (step1935 p h) (sat_nil p)))
def c2150 : List Lit := [(1120, true), (1111, false)]
theorem step2150 (p : Nat → Bool) (h : Constraints p) : clause p c2150 = true :=
  Snake9.LocalRup.prove_clause [c1560, c1566, c1569, c1561, c1545, c1556, c1864] c2150 (by decide) p (sat_cons (step1560 p h) (sat_cons (step1566 p h) (sat_cons (step1569 p h) (sat_cons (step1561 p h) (sat_cons (step1545 p h) (sat_cons (step1556 p h) (sat_cons (step1864 p h) (sat_nil p))))))))
def c2151 : List Lit := [(1052, true), (87, false), (88, true), (110, false)]
theorem step2151 (p : Nat → Bool) (h : Constraints p) : clause p c2151 = true :=
  Snake9.LocalRup.prove_clause [c1438, c1448, c1446, c1439, c1441, c622] c2151 (by decide) p (sat_cons (step1438 p h) (sat_cons (step1448 p h) (sat_cons (step1446 p h) (sat_cons (step1439 p h) (sat_cons (step1441 p h) (sat_cons (step622 p h) (sat_nil p)))))))
def c2152 : List Lit := [(1103, true), (90, false), (89, false)]
theorem step2152 (p : Nat → Bool) (h : Constraints p) : clause p c2152 = true :=
  Snake9.LocalRup.prove_clause [c1539, c1540, c687, c622, c2013] c2152 (by decide) p (sat_cons (step1539 p h) (sat_cons (step1540 p h) (sat_cons (step687 p h) (sat_cons (step622 p h) (sat_cons (step2013 p h) (sat_nil p))))))
def c2153 : List Lit := [(1032, true), (15, false), (71, true), (87, true)]
theorem step2153 (p : Nat → Bool) (h : Constraints p) : clause p c2153 = true :=
  Snake9.LocalRup.prove_clause [c1397, c1404, c1411, c2118, c1415, c1407, c1391, c1398, c1388, c546] c2153 (by decide) p (sat_cons (step1397 p h) (sat_cons (step1404 p h) (sat_cons (step1411 p h) (sat_cons (step2118 p h) (sat_cons (step1415 p h) (sat_cons (step1407 p h) (sat_cons (step1391 p h) (sat_cons (step1398 p h) (sat_cons (step1388 p h) (sat_cons (step546 p h) (sat_nil p)))))))))))
def c2154 : List Lit := [(44, false), (45, true), (9, false), (15, false), (87, true), (960, true), (53, false)]
theorem step2154 (p : Nat → Bool) (h : Constraints p) : clause p c2154 = true :=
  Snake9.LocalRup.prove_clause [c44, c1955, c437, c438, c1284] c2154 (by decide) p (sat_cons (step44 p h) (sat_cons (step1955 p h) (sat_cons (step437 p h) (sat_cons (step438 p h) (sat_cons (step1284 p h) (sat_nil p))))))
def c2155 : List Lit := [(968, true), (951, false)]
theorem step2155 (p : Nat → Bool) (h : Constraints p) : clause p c2155 = true :=
  Snake9.LocalRup.prove_clause [c1276, c1302, c1299, c1277, c1288, c1272, c1286, c1852] c2155 (by decide) p (sat_cons (step1276 p h) (sat_cons (step1302 p h) (sat_cons (step1299 p h) (sat_cons (step1277 p h) (sat_cons (step1288 p h) (sat_cons (step1272 p h) (sat_cons (step1286 p h) (sat_cons (step1852 p h) (sat_nil p)))))))))
def c2156 : List Lit := [(963, true), (51, false)]
theorem step2156 (p : Nat → Bool) (h : Constraints p) : clause p c2156 = true :=
  Snake9.LocalRup.prove_clause [c1288, c1852, c1286] c2156 (by decide) p (sat_cons (step1288 p h) (sat_cons (step1852 p h) (sat_cons (step1286 p h) (sat_nil p))))
def c2157 : List Lit := [(961, true), (952, true), (51, false), (30, false), (13, true)]
theorem step2157 (p : Nat → Bool) (h : Constraints p) : clause p c2157 = true :=
  Snake9.LocalRup.prove_clause [c1285, c1286, c491, c1979, c1978, c433, c482, c1270, c1964] c2157 (by decide) p (sat_cons (step1285 p h) (sat_cons (step1286 p h) (sat_cons (step491 p h) (sat_cons (step1979 p h) (sat_cons (step1978 p h) (sat_cons (step433 p h) (sat_cons (step482 p h) (sat_cons (step1270 p h) (sat_cons (step1964 p h) (sat_nil p))))))))))
def c2158 : List Lit := [(94, false), (1098, true), (95, false), (98, true), (89, false), (53, false)]
theorem step2158 (p : Nat → Bool) (h : Constraints p) : clause p c2158 = true :=
  Snake9.LocalRup.prove_clause [c1494, c717, c715, c1508, c1490, c1510, c1499, c1533, c1529, c1500, c1511, c1513, c1495, c1509, c1504, c2143, c2030, c838] c2158 (by decide) p (sat_cons (step1494 p h) (sat_cons (step717 p h) (sat_cons (step715 p h) (sat_cons (step1508 p h) (sat_cons (step1490 p h) (sat_cons (step1510 p h) (sat_cons (step1499 p h) (sat_cons (step1533 p h) (sat_cons (step1529 p h) (sat_cons (step1500 p h) (sat_cons (step1511 p h) (sat_cons (step1513 p h) (sat_cons (step1495 p h) (sat_cons (step1509 p h) (sat_cons (step1504 p h) (sat_cons (step2143 p h) (sat_cons (step2030 p h) (sat_cons (step838 p h) (sat_nil p)))))))))))))))))))
def c2159 : List Lit := [(1087, false), (94, true), (1098, true), (1081, false), (95, false), (89, false)]
theorem step2159 (p : Nat → Bool) (h : Constraints p) : clause p c2159 = true :=
  Snake9.LocalRup.prove_clause [c1827, c1529, c1512, c1513, c1533, c1508, c1502, c719, c1492] c2159 (by decide) p (sat_cons (step1827 p h) (sat_cons (step1529 p h) (sat_cons (step1512 p h) (sat_cons (step1513 p h) (sat_cons (step1533 p h) (sat_cons (step1508 p h) (sat_cons (step1502 p h) (sat_cons (step719 p h) (sat_cons (step1492 p h) (sat_nil p))))))))))
def c2160 : List Lit := [(1120, true), (1103, false)]
theorem step2160 (p : Nat → Bool) (h : Constraints p) : clause p c2160 = true :=
  Snake9.LocalRup.prove_clause [c1547, c1571, c1569, c1548, c1558, c1864, c1556] c2160 (by decide) p (sat_cons (step1547 p h) (sat_cons (step1571 p h) (sat_cons (step1569 p h) (sat_cons (step1548 p h) (sat_cons (step1558 p h) (sat_cons (step1864 p h) (sat_cons (step1556 p h) (sat_nil p))))))))
def c2161 : List Lit := [(946, true), (43, false), (30, false), (13, true)]
theorem step2161 (p : Nat → Bool) (h : Constraints p) : clause p c2161 = true :=
  Snake9.LocalRup.prove_clause [c1768, c1770, c1254, c1758, c1761, c1240, c1949, c1945, c399] c2161 (by decide) p (sat_cons (step1768 p h) (sat_cons (step1770 p h) (sat_cons (step1254 p h) (sat_cons (step1758 p h) (sat_cons (step1761 p h) (sat_cons (step1240 p h) (sat_cons (step1949 p h) (sat_cons (step1945 p h) (sat_cons (step399 p h) (sat_nil p))))))))))
def c2162 : List Lit := [(1096, true), (1081, false)]
theorem step2162 (p : Nat → Bool) (h : Constraints p) : clause p c2162 = true :=
  Snake9.LocalRup.prove_clause [c1496, c1527, c1523, c1499, c1510, c1512, c1490, c1491, c1508, c1504, c1866, c821] c2162 (by decide) p (sat_cons (step1496 p h) (sat_cons (step1527 p h) (sat_cons (step1523 p h) (sat_cons (step1499 p h) (sat_cons (step1510 p h) (sat_cons (step1512 p h) (sat_cons (step1490 p h) (sat_cons (step1491 p h) (sat_cons (step1508 p h) (sat_cons (step1504 p h) (sat_cons (step1866 p h) (sat_cons (step821 p h) (sat_nil p)))))))))))))
def c2163 : List Lit := [(1, false), (44, false), (15, false)]
theorem step2163 (p : Nat → Bool) (h : Constraints p) : clause p c2163 = true :=
  Snake9.LocalRup.prove_clause [c1905, c34] c2163 (by decide) p (sat_cons (step1905 p h) (sat_cons (step34 p h) (sat_nil p)))
def c2164 : List Lit := [(8, false), (877, true), (44, false), (15, false)]
theorem step2164 (p : Nat → Bool) (h : Constraints p) : clause p c2164 = true :=
  Snake9.LocalRup.prove_clause [c44, c50, c53, c1102, c1104, c1112] c2164 (by decide) p (sat_cons (step44 p h) (sat_cons (step50 p h) (sat_cons (step53 p h) (sat_cons (step1102 p h) (sat_cons (step1104 p h) (sat_cons (step1112 p h) (sat_nil p)))))))
def c2165 : List Lit := [(45, true), (87, true), (52, true), (44, false), (15, false)]
theorem step2165 (p : Nat → Bool) (h : Constraints p) : clause p c2165 = true :=
  Snake9.LocalRup.prove_clause [c1955, c1953, c1662] c2165 (by decide) p (sat_cons (step1955 p h) (sat_cons (step1953 p h) (sat_cons (step1662 p h) (sat_nil p))))
def c2166 : List Lit := [(1052, true), (87, true), (88, true)]
theorem step2166 (p : Nat → Bool) (h : Constraints p) : clause p c2166 = true :=
  Snake9.LocalRup.prove_clause [c1438, c1448, c1446, c1439, c1440, c1441, c2013, c685] c2166 (by decide) p (sat_cons (step1438 p h) (sat_cons (step1448 p h) (sat_cons (step1446 p h) (sat_cons (step1439 p h) (sat_cons (step1440 p h) (sat_cons (step1441 p h) (sat_cons (step2013 p h) (sat_cons (step685 p h) (sat_nil p)))))))))
def c2167 : List Lit := [(1098, true), (98, true), (95, false), (89, false), (53, false)]
theorem step2167 (p : Nat → Bool) (h : Constraints p) : clause p c2167 = true :=
  Snake9.LocalRup.prove_clause [c1494, c2158, c2159, c1827, c1504, c2143, c1529, c2030, c2031, c1511, c827, c1508, c1509, c1510, c835, c1533, c1492, c1502] c2167 (by decide) p (sat_cons (step1494 p h) (sat_cons (step2158 p h) (sat_cons (step2159 p h) (sat_cons (step1827 p h) (sat_cons (step1504 p h) (sat_cons (step2143 p h) (sat_cons (step1529 p h) (sat_cons (step2030 p h) (sat_cons (step2031 p h) (sat_cons (step1511 p h) (sat_cons (step827 p h) (sat_cons (step1508 p h) (sat_cons (step1509 p h) (sat_cons (step1510 p h) (sat_cons (step835 p h) (sat_cons (step1533 p h) (sat_cons (step1492 p h) (sat_cons (step1502 p h) (sat_nil p)))))))))))))))))))
def c2168 : List Lit := [(19, false), (901, true), (43, false), (30, false)]
theorem step2168 (p : Nat → Bool) (h : Constraints p) : clause p c2168 = true :=
  Snake9.LocalRup.prove_clause [c357, c359, c353, c1157, c1153, c1162] c2168 (by decide) p (sat_cons (step357 p h) (sat_cons (step359 p h) (sat_cons (step353 p h) (sat_cons (step1157 p h) (sat_cons (step1153 p h) (sat_cons (step1162 p h) (sat_nil p)))))))
def c2169 : List Lit := [(865, true), (22, false), (20, true)]
theorem step2169 (p : Nat → Bool) (h : Constraints p) : clause p c2169 = true :=
  Snake9.LocalRup.prove_clause [c1089, c1090, c19, c1910] c2169 (by decide) p (sat_cons (step1089 p h) (sat_cons (step1090 p h) (sat_cons (step19 p h) (sat_cons (step1910 p h) (sat_nil p)))))
def c2170 : List Lit := [(899, true), (43, false), (30, false)]
theorem step2170 (p : Nat → Bool) (h : Constraints p) : clause p c2170 = true :=
  Snake9.LocalRup.prove_clause [c1158, c1160, c1155, c1153, c365] c2170 (by decide) p (sat_cons (step1158 p h) (sat_cons (step1160 p h) (sat_cons (step1155 p h) (sat_cons (step1153 p h) (sat_cons (step365 p h) (sat_nil p))))))
def c2171 : List Lit := [(25, false), (898, true), (43, false), (30, false)]
theorem step2171 (p : Nat → Bool) (h : Constraints p) : clause p c2171 = true :=
  Snake9.LocalRup.prove_clause [c364, c365, c1157] c2171 (by decide) p (sat_cons (step364 p h) (sat_cons (step365 p h) (sat_cons (step1157 p h) (sat_nil p))))
end B112E121
