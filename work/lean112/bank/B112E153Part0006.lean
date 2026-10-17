import B112E153Part0005
namespace B112E153
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1931 : List Lit := [(1060, true), (111, false), (105, true), (117, false)]
theorem step1931 (p : Nat → Bool) (h : Constraints p) : clause p c1931 = true :=
  Snake9.LocalRup.prove_clause [c1212, c1223, c1221, c1214, c1215, c1216, c503, c452, c1914] c1931 (by decide) p (sat_cons (step1212 p h) (sat_cons (step1223 p h) (sat_cons (step1221 p h) (sat_cons (step1214 p h) (sat_cons (step1215 p h) (sat_cons (step1216 p h) (sat_cons (step503 p h) (sat_cons (step452 p h) (sat_cons (step1914 p h) (sat_nil p))))))))))
def c1932 : List Lit := [(921, false), (975, true), (1013, false), (94, false), (954, false), (1102, false)]
theorem step1932 (p : Nat → Bool) (h : Constraints p) : clause p c1932 = true :=
  Snake9.LocalRup.prove_clause [c1847, c1580, c1143, c1164, c1361, c1856, c1841, c1846, c1059, c1854, c1378, c1166, c1145, c1887, c1052, c1038, c1676, c1833, c1630, c298, c297, c1124, c1120, c1129] c1932 (by decide) p (sat_cons (step1847 p h) (sat_cons (step1580 p h) (sat_cons (step1143 p h) (sat_cons (step1164 p h) (sat_cons (step1361 p h) (sat_cons (step1856 p h) (sat_cons (step1841 p h) (sat_cons (step1846 p h) (sat_cons (step1059 p h) (sat_cons (step1854 p h) (sat_cons (step1378 p h) (sat_cons (step1166 p h) (sat_cons (step1145 p h) (sat_cons (step1887 p h) (sat_cons (step1052 p h) (sat_cons (step1038 p h) (sat_cons (step1676 p h) (sat_cons (step1833 p h) (sat_cons (step1630 p h) (sat_cons (step298 p h) (sat_cons (step297 p h) (sat_cons (step1124 p h) (sat_cons (step1120 p h) (sat_cons (step1129 p h) (sat_nil p)))))))))))))))))))))))))
def c1933 : List Lit := [(86, false), (109, false), (1056, true), (1061, true), (1072, true), (1079, true)]
theorem step1933 (p : Nat → Bool) (h : Constraints p) : clause p c1933 = true :=
  Snake9.LocalRup.prove_clause [c1625, c1880, c1213, c1214, c1222, c1663, c1217] c1933 (by decide) p (sat_cons (step1625 p h) (sat_cons (step1880 p h) (sat_cons (step1213 p h) (sat_cons (step1214 p h) (sat_cons (step1222 p h) (sat_cons (step1663 p h) (sat_cons (step1217 p h) (sat_nil p))))))))
def c1934 : List Lit := [(103, false), (82, false), (109, true), (1057, true), (117, false)]
theorem step1934 (p : Nat → Bool) (h : Constraints p) : clause p c1934 = true :=
  Snake9.LocalRup.prove_clause [c1216, c1215, c427, c452, c1791] c1934 (by decide) p (sat_cons (step1216 p h) (sat_cons (step1215 p h) (sat_cons (step427 p h) (sat_cons (step452 p h) (sat_cons (step1791 p h) (sat_nil p))))))
def c1935 : List Lit := [(81, false), (1091, true), (1071, false), (123, true), (124, false), (115, true), (118, false)]
theorem step1935 (p : Nat → Bool) (h : Constraints p) : clause p c1935 = true :=
  Snake9.LocalRup.prove_clause [c634, c1628, c1253, c1290, c1258] c1935 (by decide) p (sat_cons (step634 p h) (sat_cons (step1628 p h) (sat_cons (step1253 p h) (sat_cons (step1290 p h) (sat_cons (step1258 p h) (sat_nil p))))))
def c1936 : List Lit := [(1037, true), (1021, false), (1010, false), (81, true), (94, false), (109, true)]
theorem step1936 (p : Nat → Bool) (h : Constraints p) : clause p c1936 = true :=
  Snake9.LocalRup.prove_clause [c1106, c1115, c1145, c1580, c1167, c1174, c1150, c1585, c1118, c1108] c1936 (by decide) p (sat_cons (step1106 p h) (sat_cons (step1115 p h) (sat_cons (step1145 p h) (sat_cons (step1580 p h) (sat_cons (step1167 p h) (sat_cons (step1174 p h) (sat_cons (step1150 p h) (sat_cons (step1585 p h) (sat_cons (step1118 p h) (sat_cons (step1108 p h) (sat_nil p)))))))))))
def c1937 : List Lit := [(118, false), (1081, true), (107, false), (96, false)]
theorem step1937 (p : Nat → Bool) (h : Constraints p) : clause p c1937 = true :=
  Snake9.LocalRup.prove_clause [c1590, c1659] c1937 (by decide) p (sat_cons (step1590 p h) (sat_cons (step1659 p h) (sat_nil p)))
def c1938 : List Lit := [(1057, true), (1056, true), (1084, true), (115, false)]
theorem step1938 (p : Nat → Bool) (h : Constraints p) : clause p c1938 = true :=
  Snake9.LocalRup.prove_clause [c1215, c1216, c1890, c1891, c435, c434, c1214] c1938 (by decide) p (sat_cons (step1215 p h) (sat_cons (step1216 p h) (sat_cons (step1890 p h) (sat_cons (step1891 p h) (sat_cons (step435 p h) (sat_cons (step434 p h) (sat_cons (step1214 p h) (sat_nil p))))))))
def c1939 : List Lit := [(115, false), (103, false), (105, false), (1058, true), (1084, true)]
theorem step1939 (p : Nat → Bool) (h : Constraints p) : clause p c1939 = true :=
  Snake9.LocalRup.prove_clause [c1269, c433, c1638, c1271, c1663, c1603, c1217, c1800, c599, c600, c1267] c1939 (by decide) p (sat_cons (step1269 p h) (sat_cons (step433 p h) (sat_cons (step1638 p h) (sat_cons (step1271 p h) (sat_cons (step1663 p h) (sat_cons (step1603 p h) (sat_cons (step1217 p h) (sat_cons (step1800 p h) (sat_cons (step599 p h) (sat_cons (step600 p h) (sat_cons (step1267 p h) (sat_nil p))))))))))))
def c1940 : List Lit := [(944, true), (57, true), (89, true), (91, false)]
theorem step1940 (p : Nat → Bool) (h : Constraints p) : clause p c1940 = true :=
  Snake9.LocalRup.prove_clause [c992, c1000, c1833, c1861, c1012, c1003, c1001, c984, c990, c994, c996, c165, c1646, c1729] c1940 (by decide) p (sat_cons (step992 p h) (sat_cons (step1000 p h) (sat_cons (step1833 p h) (sat_cons (step1861 p h) (sat_cons (step1012 p h) (sat_cons (step1003 p h) (sat_cons (step1001 p h) (sat_cons (step984 p h) (sat_cons (step990 p h) (sat_cons (step994 p h) (sat_cons (step996 p h) (sat_cons (step165 p h) (sat_cons (step1646 p h) (sat_cons (step1729 p h) (sat_nil p)))))))))))))))
def c1941 : List Lit := [(988, true), (67, false), (105, false)]
theorem step1941 (p : Nat → Bool) (h : Constraints p) : clause p c1941 = true :=
  Snake9.LocalRup.prove_clause [c1066, c1067, c208] c1941 (by decide) p (sat_cons (step1066 p h) (sat_cons (step1067 p h) (sat_cons (step208 p h) (sat_nil p))))
def c1942 : List Lit := [(1001, true), (102, true), (105, false)]
theorem step1942 (p : Nat → Bool) (h : Constraints p) : clause p c1942 = true :=
  Snake9.LocalRup.prove_clause [c1088, c1092, c1080, c1069, c1077, c1067, c1941, c1588, c1744] c1942 (by decide) p (sat_cons (step1088 p h) (sat_cons (step1092 p h) (sat_cons (step1080 p h) (sat_cons (step1069 p h) (sat_cons (step1077 p h) (sat_cons (step1067 p h) (sat_cons (step1941 p h) (sat_cons (step1588 p h) (sat_cons (step1744 p h) (sat_nil p))))))))))
def c1943 : List Lit := [(1071, true), (109, false), (108, false)]
theorem step1943 (p : Nat → Bool) (h : Constraints p) : clause p c1943 = true :=
  Snake9.LocalRup.prove_clause [c1248, c1249, c506] c1943 (by decide) p (sat_cons (step1248 p h) (sat_cons (step1249 p h) (sat_cons (step506 p h) (sat_nil p))))
def c1944 : List Lit := [(1018, false), (1060, false), (94, true), (1001, false), (1090, false), (1013, false), (1122, true)]
theorem step1944 (p : Nat → Bool) (h : Constraints p) : clause p c1944 = true :=
  Snake9.LocalRup.prove_clause [c1199, c1206, c1232, c1317, c1377, c1166, c1145, c1126, c1144, c1165, c1369, c1325, c1237, c1209, c1207, c1200, c1201, c1202, c1129, c401, c1120, c1121, c382, c333, c1789] c1944 (by decide) p (sat_cons (step1199 p h) (sat_cons (step1206 p h) (sat_cons (step1232 p h) (sat_cons (step1317 p h) (sat_cons (step1377 p h) (sat_cons (step1166 p h) (sat_cons (step1145 p h) (sat_cons (step1126 p h) (sat_cons (step1144 p h) (sat_cons (step1165 p h) (sat_cons (step1369 p h) (sat_cons (step1325 p h) (sat_cons (step1237 p h) (sat_cons (step1209 p h) (sat_cons (step1207 p h) (sat_cons (step1200 p h) (sat_cons (step1201 p h) (sat_cons (step1202 p h) (sat_cons (step1129 p h) (sat_cons (step401 p h) (sat_cons (step1120 p h) (sat_cons (step1121 p h) (sat_cons (step382 p h) (sat_cons (step333 p h) (sat_cons (step1789 p h) (sat_nil p))))))))))))))))))))))))))
def c1945 : List Lit := [(88, false), (1049, true), (91, false)]
theorem step1945 (p : Nat → Bool) (h : Constraints p) : clause p c1945 = true :=
  Snake9.LocalRup.prove_clause [c1202, c1201, c400, c382, c326, c1784] c1945 (by decide) p (sat_cons (step1202 p h) (sat_cons (step1201 p h) (sat_cons (step400 p h) (sat_cons (step382 p h) (sat_cons (step326 p h) (sat_cons (step1784 p h) (sat_nil p)))))))
def c1946 : List Lit := [(1102, true), (91, false), (1017, true), (1060, false), (1047, false), (1077, false)]
theorem step1946 (p : Nat → Bool) (h : Constraints p) : clause p c1946 = true :=
  Snake9.LocalRup.prove_clause [c1893, c1206, c1232, c1289, c1318, c1325, c1290, c1237, c1269, c1207, c1201, c1202, c400, c1945, c1122, c335, c1787, c1789, c385, c1265, c1267, c1271, c643, c1262] c1946 (by decide) p (sat_cons (step1893 p h) (sat_cons (step1206 p h) (sat_cons (step1232 p h) (sat_cons (step1289 p h) (sat_cons (step1318 p h) (sat_cons (step1325 p h) (sat_cons (step1290 p h) (sat_cons (step1237 p h) (sat_cons (step1269 p h) (sat_cons (step1207 p h) (sat_cons (step1201 p h) (sat_cons (step1202 p h) (sat_cons (step400 p h) (sat_cons (step1945 p h) (sat_cons (step1122 p h) (sat_cons (step335 p h) (sat_cons (step1787 p h) (sat_cons (step1789 p h) (sat_cons (step385 p h) (sat_cons (step1265 p h) (sat_cons (step1267 p h) (sat_cons (step1271 p h) (sat_cons (step643 p h) (sat_cons (step1262 p h) (sat_nil p)))))))))))))))))))))))))
def c1947 : List Lit := [(124, false), (81, false), (1085, true), (100, false)]
theorem step1947 (p : Nat → Bool) (h : Constraints p) : clause p c1947 = true :=
  Snake9.LocalRup.prove_clause [c633, c1627] c1947 (by decide) p (sat_cons (step633 p h) (sat_cons (step1627 p h) (sat_nil p)))
def c1948 : List Lit := [(63, true), (64, false), (62, false), (57, true)]
theorem step1948 (p : Nat → Bool) (h : Constraints p) : clause p c1948 = true :=
  Snake9.LocalRup.prove_clause [c198, c192, c771, c757, c772, c758, c782, c760, c794, c761, c816, c763, c861, c766, c1827] c1948 (by decide) p (sat_cons (step198 p h) (sat_cons (step192 p h) (sat_cons (step771 p h) (sat_cons (step757 p h) (sat_cons (step772 p h) (sat_cons (step758 p h) (sat_cons (step782 p h) (sat_cons (step760 p h) (sat_cons (step794 p h) (sat_cons (step761 p h) (sat_cons (step816 p h) (sat_cons (step763 p h) (sat_cons (step861 p h) (sat_cons (step766 p h) (sat_cons (step1827 p h) (sat_nil p))))))))))))))))
def c1949 : List Lit := [(55, false), (47, false), (261, true), (54, false), (52, false)]
theorem step1949 (p : Nat → Bool) (h : Constraints p) : clause p c1949 = true :=
  Snake9.LocalRup.prove_clause [c1720, c153, c135, c1612] c1949 (by decide) p (sat_cons (step1720 p h) (sat_cons (step153 p h) (sat_cons (step135 p h) (sat_cons (step1612 p h) (sat_nil p)))))
def c1950 : List Lit := [(5, true), (854, true), (20, false), (261, true)]
theorem step1950 (p : Nat → Bool) (h : Constraints p) : clause p c1950 = true :=
  Snake9.LocalRup.prove_clause [c874, c1612, c882, c1548, c1602, c877] c1950 (by decide) p (sat_cons (step874 p h) (sat_cons (step1612 p h) (sat_cons (step882 p h) (sat_cons (step1548 p h) (sat_cons (step1602 p h) (sat_cons (step877 p h) (sat_nil p)))))))
def c1951 : List Lit := [(12, true), (15, false), (20, false), (890, true)]
theorem step1951 (p : Nat → Bool) (h : Constraints p) : clause p c1951 = true :=
  Snake9.LocalRup.prove_clause [c875, c1888, c878, c931, c1869, c916, c900, c912, c893, c905, c34] c1951 (by decide) p (sat_cons (step875 p h) (sat_cons (step1888 p h) (sat_cons (step878 p h) (sat_cons (step931 p h) (sat_cons (step1869 p h) (sat_cons (step916 p h) (sat_cons (step900 p h) (sat_cons (step912 p h) (sat_cons (step893 p h) (sat_cons (step905 p h) (sat_cons (step34 p h) (sat_nil p))))))))))))
def c1952 : List Lit := [(919, true), (42, false), (35, false), (164, true)]
theorem step1952 (p : Nat → Bool) (h : Constraints p) : clause p c1952 = true :=
  Snake9.LocalRup.prove_clause [c966, c1632, c963, c956, c119, c118, c954, c112, c1711] c1952 (by decide) p (sat_cons (step966 p h) (sat_cons (step1632 p h) (sat_cons (step963 p h) (sat_cons (step956 p h) (sat_cons (step119 p h) (sat_cons (step118 p h) (sat_cons (step954 p h) (sat_cons (step112 p h) (sat_cons (step1711 p h) (sat_nil p))))))))))
def c1953 : List Lit := [(45, false), (42, false), (35, false), (920, true), (164, true)]
theorem step1953 (p : Nat → Bool) (h : Constraints p) : clause p c1953 = true :=
  Snake9.LocalRup.prove_clause [c119, c118, c112, c941, c1711, c944, c954, c970, c963] c1953 (by decide) p (sat_cons (step119 p h) (sat_cons (step118 p h) (sat_cons (step112 p h) (sat_cons (step941 p h) (sat_cons (step1711 p h) (sat_cons (step944 p h) (sat_cons (step954 p h) (sat_cons (step970 p h) (sat_cons (step963 p h) (sat_nil p))))))))))
def c1954 : List Lit := [(890, true), (891, true), (19, true)]
theorem step1954 (p : Nat → Bool) (h : Constraints p) : clause p c1954 = true :=
  Snake9.LocalRup.prove_clause [c1828, c1676, c1689, c1951, c33, c31, c905, c893, c912, c900, c919] c1954 (by decide) p (sat_cons (step1828 p h) (sat_cons (step1676 p h) (sat_cons (step1689 p h) (sat_cons (step1951 p h) (sat_cons (step33 p h) (sat_cons (step31 p h) (sat_cons (step905 p h) (sat_cons (step893 p h) (sat_cons (step912 p h) (sat_cons (step900 p h) (sat_cons (step919 p h) (sat_nil p))))))))))))
def c1955 : List Lit := [(21, true), (20, true), (881, true), (150, true)]
theorem step1955 (p : Nat → Bool) (h : Constraints p) : clause p c1955 = true :=
  Snake9.LocalRup.prove_clause [c68, c897, c1662] c1955 (by decide) p (sat_cons (step68 p h) (sat_cons (step897 p h) (sat_cons (step1662 p h) (sat_nil p))))
def c1956 : List Lit := [(26, true), (18, false), (27, false)]
theorem step1956 (p : Nat → Bool) (h : Constraints p) : clause p c1956 = true :=
  Snake9.LocalRup.prove_clause [c1697, c1695, c1501] c1956 (by decide) p (sat_cons (step1697 p h) (sat_cons (step1695 p h) (sat_cons (step1501 p h) (sat_nil p))))
def c1957 : List Lit := [(1075, true), (109, true), (117, false), (107, false)]
theorem step1957 (p : Nat → Bool) (h : Constraints p) : clause p c1957 = true :=
  Snake9.LocalRup.prove_clause [c1254, c1256, c1252, c1248, c570, c1912] c1957 (by decide) p (sat_cons (step1254 p h) (sat_cons (step1256 p h) (sat_cons (step1252 p h) (sat_cons (step1248 p h) (sat_cons (step570 p h) (sat_cons (step1912 p h) (sat_nil p)))))))
def c1958 : List Lit := [(115, true), (1076, true), (117, false), (107, false), (109, true)]
theorem step1958 (p : Nat → Bool) (h : Constraints p) : clause p c1958 = true :=
  Snake9.LocalRup.prove_clause [c1255, c1251, c1253, c1257, c1248, c570, c1912] c1958 (by decide) p (sat_cons (step1255 p h) (sat_cons (step1251 p h) (sat_cons (step1253 p h) (sat_cons (step1257 p h) (sat_cons (step1248 p h) (sat_cons (step570 p h) (sat_cons (step1912 p h) (sat_nil p))))))))
def c1959 : List Lit := [(1071, true), (117, false), (107, false), (109, true)]
theorem step1959 (p : Nat → Bool) (h : Constraints p) : clause p c1959 = true :=
  Snake9.LocalRup.prove_clause [c1248, c1249, c1912, c569] c1959 (by decide) p (sat_cons (step1248 p h) (sat_cons (step1249 p h) (sat_cons (step1912 p h) (sat_cons (step569 p h) (sat_nil p)))))
def c1960 : List Lit := [(1076, true), (1084, true), (117, false), (107, false), (109, true)]
theorem step1960 (p : Nat → Bool) (h : Constraints p) : clause p c1960 = true :=
  Snake9.LocalRup.prove_clause [c1959, c1259, c1958, c1890, c1271, c1265, c1266, c602, c1257, c1252, c648, c1809, c517, c1250, c1912, c570] c1960 (by decide) p (sat_cons (step1959 p h) (sat_cons (step1259 p h) (sat_cons (step1958 p h) (sat_cons (step1890 p h) (sat_cons (step1271 p h) (sat_cons (step1265 p h) (sat_cons (step1266 p h) (sat_cons (step602 p h) (sat_cons (step1257 p h) (sat_cons (step1252 p h) (sat_cons (step648 p h) (sat_cons (step1809 p h) (sat_cons (step517 p h) (sat_cons (step1250 p h) (sat_cons (step1912 p h) (sat_cons (step570 p h) (sat_nil p)))))))))))))))))
def c1961 : List Lit := [(112, false), (113, false), (117, false), (107, false), (109, true)]
theorem step1961 (p : Nat → Bool) (h : Constraints p) : clause p c1961 = true :=
  Snake9.LocalRup.prove_clause [c1912, c570] c1961 (by decide) p (sat_cons (step1912 p h) (sat_cons (step570 p h) (sat_nil p)))
def c1962 : List Lit := [(103, true), (1051, false), (1056, true), (1027, false), (1057, false), (954, false), (102, false), (1089, false), (997, false), (115, false)]
theorem step1962 (p : Nat → Bool) (h : Constraints p) : clause p c1962 = true :=
  Snake9.LocalRup.prove_clause [c1213, c1214, c1221, c424, c414, c1232, c1067, c907, c1316, c1069, c1913, c1093, c1058, c1174, c1855, c1384] c1962 (by decide) p (sat_cons (step1213 p h) (sat_cons (step1214 p h) (sat_cons (step1221 p h) (sat_cons (step424 p h) (sat_cons (step414 p h) (sat_cons (step1232 p h) (sat_cons (step1067 p h) (sat_cons (step907 p h) (sat_cons (step1316 p h) (sat_cons (step1069 p h) (sat_cons (step1913 p h) (sat_cons (step1093 p h) (sat_cons (step1058 p h) (sat_cons (step1174 p h) (sat_cons (step1855 p h) (sat_cons (step1384 p h) (sat_nil p)))))))))))))))))
def c1963 : List Lit := [(1051, false), (1056, true), (115, false), (1027, false), (1057, false), (954, false), (102, false), (1089, false), (997, false)]
theorem step1963 (p : Nat → Bool) (h : Constraints p) : clause p c1963 = true :=
  Snake9.LocalRup.prove_clause [c1962, c433, c412, c422, c1212, c907, c1067, c1221, c1913, c1069, c1232, c1058, c1093, c1316, c1855, c1174, c1384] c1963 (by decide) p (sat_cons (step1962 p h) (sat_cons (step433 p h) (sat_cons (step412 p h) (sat_cons (step422 p h) (sat_cons (step1212 p h) (sat_cons (step907 p h) (sat_cons (step1067 p h) (sat_cons (step1221 p h) (sat_cons (step1913 p h) (sat_cons (step1069 p h) (sat_cons (step1232 p h) (sat_cons (step1058 p h) (sat_cons (step1093 p h) (sat_cons (step1316 p h) (sat_cons (step1855 p h) (sat_cons (step1174 p h) (sat_cons (step1384 p h) (sat_nil p))))))))))))))))))
def c1964 : List Lit := [(1051, true), (90, true), (124, true)]
theorem step1964 (p : Nat → Bool) (h : Constraints p) : clause p c1964 = true :=
  Snake9.LocalRup.prove_clause [c1204, c1206, c1201, c1202, c1198, c1787, c401] c1964 (by decide) p (sat_cons (step1204 p h) (sat_cons (step1206 p h) (sat_cons (step1201 p h) (sat_cons (step1202 p h) (sat_cons (step1198 p h) (sat_cons (step1787 p h) (sat_cons (step401 p h) (sat_nil p))))))))
def c1965 : List Lit := [(1027, false), (1102, false), (920, false), (73, true), (109, true)]
theorem step1965 (p : Nat → Bool) (h : Constraints p) : clause p c1965 = true :=
  Snake9.LocalRup.prove_clause [c1839, c1845, c1853, c1386, c1074, c1082, c1088, c1166, c1378, c1854, c1846, c1033, c1861, c985, c1174, c1089, c1093, c1085, c1069, c1076, c1067, c1747, c218] c1965 (by decide) p (sat_cons (step1839 p h) (sat_cons (step1845 p h) (sat_cons (step1853 p h) (sat_cons (step1386 p h) (sat_cons (step1074 p h) (sat_cons (step1082 p h) (sat_cons (step1088 p h) (sat_cons (step1166 p h) (sat_cons (step1378 p h) (sat_cons (step1854 p h) (sat_cons (step1846 p h) (sat_cons (step1033 p h) (sat_cons (step1861 p h) (sat_cons (step985 p h) (sat_cons (step1174 p h) (sat_cons (step1089 p h) (sat_cons (step1093 p h) (sat_cons (step1085 p h) (sat_cons (step1069 p h) (sat_cons (step1076 p h) (sat_cons (step1067 p h) (sat_cons (step1747 p h) (sat_cons (step218 p h) (sat_nil p))))))))))))))))))))))))
def c1966 : List Lit := [(71, false), (52, false), (65, false), (109, true)]
theorem step1966 (p : Nat → Bool) (h : Constraints p) : clause p c1966 = true :=
  Snake9.LocalRup.prove_clause [c1747, c218] c1966 (by decide) p (sat_cons (step1747 p h) (sat_cons (step218 p h) (sat_nil p)))
def c1967 : List Lit := [(1035, true), (990, false), (1002, false), (73, true), (109, true)]
theorem step1967 (p : Nat → Bool) (h : Constraints p) : clause p c1967 = true :=
  Snake9.LocalRup.prove_clause [c1074, c1915, c1178, c1172, c1094, c1905, c1085, c1083, c1107, c1076, c1078, c254, c1746] c1967 (by decide) p (sat_cons (step1074 p h) (sat_cons (step1915 p h) (sat_cons (step1178 p h) (sat_cons (step1172 p h) (sat_cons (step1094 p h) (sat_cons (step1905 p h) (sat_cons (step1085 p h) (sat_cons (step1083 p h) (sat_cons (step1107 p h) (sat_cons (step1076 p h) (sat_cons (step1078 p h) (sat_cons (step254 p h) (sat_cons (step1746 p h) (sat_nil p))))))))))))))
def c1968 : List Lit := [(88, false), (1051, true), (113, false)]
theorem step1968 (p : Nat → Bool) (h : Constraints p) : clause p c1968 = true :=
  Snake9.LocalRup.prove_clause [c1204, c1201, c1206, c1198, c1202, c401, c340, c382, c1789] c1968 (by decide) p (sat_cons (step1204 p h) (sat_cons (step1201 p h) (sat_cons (step1206 p h) (sat_cons (step1198 p h) (sat_cons (step1202 p h) (sat_cons (step401 p h) (sat_cons (step340 p h) (sat_cons (step382 p h) (sat_cons (step1789 p h) (sat_nil p))))))))))
def c1969 : List Lit := [(86, false), (99, false), (109, true)]
theorem step1969 (p : Nat → Bool) (h : Constraints p) : clause p c1969 = true :=
  Snake9.LocalRup.prove_clause [c1770, c1769, c1525] c1969 (by decide) p (sat_cons (step1770 p h) (sat_cons (step1769 p h) (sat_cons (step1525 p h) (sat_nil p))))
def c1970 : List Lit := [(81, false), (100, false), (99, false), (114, false), (113, false)]
theorem step1970 (p : Nat → Bool) (h : Constraints p) : clause p c1970 = true :=
  Snake9.LocalRup.prove_clause [c630, c1763, c535, c1787, c1788, c1533] c1970 (by decide) p (sat_cons (step630 p h) (sat_cons (step1763 p h) (sat_cons (step535 p h) (sat_cons (step1787 p h) (sat_cons (step1788 p h) (sat_cons (step1533 p h) (sat_nil p)))))))
def c1971 : List Lit := [(90, true), (124, true), (100, false), (99, false)]
theorem step1971 (p : Nat → Bool) (h : Constraints p) : clause p c1971 = true :=
  Snake9.LocalRup.prove_clause [c1787, c1788, c1533] c1971 (by decide) p (sat_cons (step1787 p h) (sat_cons (step1788 p h) (sat_cons (step1533 p h) (sat_nil p))))
def c1972 : List Lit := [(1122, true), (1049, false), (1010, false), (1021, false), (1060, false), (1090, false), (1001, false), (109, true)]
theorem step1972 (p : Nat → Bool) (h : Constraints p) : clause p c1972 = true :=
  Snake9.LocalRup.prove_clause [c1204, c1232, c1317, c1112, c1140, c1165, c1369, c1377, c1325, c1166, c1173, c1237, c1145, c1207, c1115, c1199, c1107, c1585] c1972 (by decide) p (sat_cons (step1204 p h) (sat_cons (step1232 p h) (sat_cons (step1317 p h) (sat_cons (step1112 p h) (sat_cons (step1140 p h) (sat_cons (step1165 p h) (sat_cons (step1369 p h) (sat_cons (step1377 p h) (sat_cons (step1325 p h) (sat_cons (step1166 p h) (sat_cons (step1173 p h) (sat_cons (step1237 p h) (sat_cons (step1145 p h) (sat_cons (step1207 p h) (sat_cons (step1115 p h) (sat_cons (step1199 p h) (sat_cons (step1107 p h) (sat_cons (step1585 p h) (sat_nil p)))))))))))))))))))
def c1973 : List Lit := [(1121, true), (1049, false), (1021, false), (1060, false), (1090, false), (1001, false), (109, true)]
theorem step1973 (p : Nat → Bool) (h : Constraints p) : clause p c1973 = true :=
  Snake9.LocalRup.prove_clause [c1204, c1232, c1317, c1135, c1164, c1361, c1368, c1325, c1165, c1172, c1237, c1140, c1207, c1114, c1199, c1107, c1585] c1973 (by decide) p (sat_cons (step1204 p h) (sat_cons (step1232 p h) (sat_cons (step1317 p h) (sat_cons (step1135 p h) (sat_cons (step1164 p h) (sat_cons (step1361 p h) (sat_cons (step1368 p h) (sat_cons (step1325 p h) (sat_cons (step1165 p h) (sat_cons (step1172 p h) (sat_cons (step1237 p h) (sat_cons (step1140 p h) (sat_cons (step1207 p h) (sat_cons (step1114 p h) (sat_cons (step1199 p h) (sat_cons (step1107 p h) (sat_cons (step1585 p h) (sat_nil p))))))))))))))))))
def c1974 : List Lit := [(1002, true), (108, false), (73, true), (109, true)]
theorem step1974 (p : Nat → Bool) (h : Constraints p) : clause p c1974 = true :=
  Snake9.LocalRup.prove_clause [c1074, c1082, c1089, c1093, c1085, c1069, c1076, c1067, c1919] c1974 (by decide) p (sat_cons (step1074 p h) (sat_cons (step1082 p h) (sat_cons (step1089 p h) (sat_cons (step1093 p h) (sat_cons (step1085 p h) (sat_cons (step1069 p h) (sat_cons (step1076 p h) (sat_cons (step1067 p h) (sat_cons (step1919 p h) (sat_nil p))))))))))
def c1975 : List Lit := [(1049, true), (1082, true), (90, true), (113, false)]
theorem step1975 (p : Nat → Bool) (h : Constraints p) : clause p c1975 = true :=
  Snake9.LocalRup.prove_clause [c1201, c1202, c1863, c1971] c1975 (by decide) p (sat_cons (step1201 p h) (sat_cons (step1202 p h) (sat_cons (step1863 p h) (sat_cons (step1971 p h) (sat_nil p)))))
def c1976 : List Lit := [(93, false), (1047, true), (115, false)]
theorem step1976 (p : Nat → Bool) (h : Constraints p) : clause p c1976 = true :=
  Snake9.LocalRup.prove_clause [c1199, c1604, c369] c1976 (by decide) p (sat_cons (step1199 p h) (sat_cons (step1604 p h) (sat_cons (step369 p h) (sat_nil p))))
def c1977 : List Lit := [(1055, true), (102, true), (107, false), (109, true)]
theorem step1977 (p : Nat → Bool) (h : Constraints p) : clause p c1977 = true :=
  Snake9.LocalRup.prove_clause [c1212, c1213, c448, c1791] c1977 (by decide) p (sat_cons (step1212 p h) (sat_cons (step1213 p h) (sat_cons (step448 p h) (sat_cons (step1791 p h) (sat_nil p)))))
def c1978 : List Lit := [(1037, true), (1011, false), (1021, false), (94, false), (1001, false), (109, true)]
theorem step1978 (p : Nat → Bool) (h : Constraints p) : clause p c1978 = true :=
  Snake9.LocalRup.prove_clause [c1113, c1145, c1167, c1174, c1150, c1585, c1116, c1107] c1978 (by decide) p (sat_cons (step1113 p h) (sat_cons (step1145 p h) (sat_cons (step1167 p h) (sat_cons (step1174 p h) (sat_cons (step1150 p h) (sat_cons (step1585 p h) (sat_cons (step1116 p h) (sat_cons (step1107 p h) (sat_nil p)))))))))
def c1979 : List Lit := [(103, false), (102, true), (117, false), (107, false), (109, true)]
theorem step1979 (p : Nat → Bool) (h : Constraints p) : clause p c1979 = true :=
  Snake9.LocalRup.prove_clause [c452, c1791] c1979 (by decide) p (sat_cons (step452 p h) (sat_cons (step1791 p h) (sat_nil p)))
def c1980 : List Lit := [(955, false), (954, false), (975, true)]
theorem step1980 (p : Nat → Bool) (h : Constraints p) : clause p c1980 = true :=
  Snake9.LocalRup.prove_clause [c1058, c1887, c1052, c934, c1676, c1954, c47, c1683, c875, c1888, c931, c916, c918, c912, c898, c900, c904, c895, c893, c55, c43, c1694, c874, c36, c881, c868, c888, c1573] c1980 (by decide) p (sat_cons (step1058 p h) (sat_cons (step1887 p h) (sat_cons (step1052 p h) (sat_cons (step934 p h) (sat_cons (step1676 p h) (sat_cons (step1954 p h) (sat_cons (step47 p h) (sat_cons (step1683 p h) (sat_cons (step875 p h) (sat_cons (step1888 p h) (sat_cons (step931 p h) (sat_cons (step916 p h) (sat_cons (step918 p h) (sat_cons (step912 p h) (sat_cons (step898 p h) (sat_cons (step900 p h) (sat_cons (step904 p h) (sat_cons (step895 p h) (sat_cons (step893 p h) (sat_cons (step55 p h) (sat_cons (step43 p h) (sat_cons (step1694 p h) (sat_cons (step874 p h) (sat_cons (step36 p h) (sat_cons (step881 p h) (sat_cons (step868 p h) (sat_cons (step888 p h) (sat_cons (step1573 p h) (sat_nil p)))))))))))))))))))))))))))))
def c1981 : List Lit := [(19, false), (854, true), (13, false), (14, false), (20, false), (89, false)]
theorem step1981 (p : Nat → Bool) (h : Constraints p) : clause p c1981 = true :=
  Snake9.LocalRup.prove_clause [c47, c43, c1683, c1950, c22, c709, c710, c1810, c713] c1981 (by decide) p (sat_cons (step47 p h) (sat_cons (step43 p h) (sat_cons (step1683 p h) (sat_cons (step1950 p h) (sat_cons (step22 p h) (sat_cons (step709 p h) (sat_cons (step710 p h) (sat_cons (step1810 p h) (sat_cons (step713 p h) (sat_nil p))))))))))
def c1982 : List Lit := [(4, true), (863, true), (20, false), (89, false), (891, true)]
theorem step1982 (p : Nat → Bool) (h : Constraints p) : clause p c1982 = true :=
  Snake9.LocalRup.prove_clause [c1913, c908, c892, c1956, c1870, c893, c937, c868, c1573, c889, c1981, c1689, c29, c31, c34, c870, c875, c905, c1574, c878, c912, c891, c916, c935] c1982 (by decide) p (sat_cons (step1913 p h) (sat_cons (step908 p h) (sat_cons (step892 p h) (sat_cons (step1956 p h) (sat_cons (step1870 p h) (sat_cons (step893 p h) (sat_cons (step937 p h) (sat_cons (step868 p h) (sat_cons (step1573 p h) (sat_cons (step889 p h) (sat_cons (step1981 p h) (sat_cons (step1689 p h) (sat_cons (step29 p h) (sat_cons (step31 p h) (sat_cons (step34 p h) (sat_cons (step870 p h) (sat_cons (step875 p h) (sat_cons (step905 p h) (sat_cons (step1574 p h) (sat_cons (step878 p h) (sat_cons (step912 p h) (sat_cons (step891 p h) (sat_cons (step916 p h) (sat_cons (step935 p h) (sat_nil p)))))))))))))))))))))))))
def c1983 : List Lit := [(891, true), (150, true), (863, true), (15, false), (14, false), (20, false), (89, false)]
theorem step1983 (p : Nat → Bool) (h : Constraints p) : clause p c1983 = true :=
  Snake9.LocalRup.prove_clause [c892, c31, c1888, c34, c1913, c932, c1982, c908, c917, c1956, c914, c68, c906, c55, c36, c1694] c1983 (by decide) p (sat_cons (step892 p h) (sat_cons (step31 p h) (sat_cons (step1888 p h) (sat_cons (step34 p h) (sat_cons (step1913 p h) (sat_cons (step932 p h) (sat_cons (step1982 p h) (sat_cons (step908 p h) (sat_cons (step917 p h) (sat_cons (step1956 p h) (sat_cons (step914 p h) (sat_cons (step68 p h) (sat_cons (step906 p h) (sat_cons (step55 p h) (sat_cons (step36 p h) (sat_cons (step1694 p h) (sat_nil p)))))))))))))))))
def c1984 : List Lit := [(890, true), (891, true), (879, false)]
theorem step1984 (p : Nat → Bool) (h : Constraints p) : clause p c1984 = true :=
  Snake9.LocalRup.prove_clause [c1828, c1676, c1954, c931, c1888, c1683, c33, c47, c905, c1615, c912, c919] c1984 (by decide) p (sat_cons (step1828 p h) (sat_cons (step1676 p h) (sat_cons (step1954 p h) (sat_cons (step931 p h) (sat_cons (step1888 p h) (sat_cons (step1683 p h) (sat_cons (step33 p h) (sat_cons (step47 p h) (sat_cons (step905 p h) (sat_cons (step1615 p h) (sat_cons (step912 p h) (sat_cons (step919 p h) (sat_nil p)))))))))))))
def c1985 : List Lit := [(105, false), (88, false), (82, false), (108, false), (92, true)]
theorem step1985 (p : Nat → Bool) (h : Constraints p) : clause p c1985 = true :=
  Snake9.LocalRup.prove_clause [c429, c280, c1765] c1985 (by decide) p (sat_cons (step429 p h) (sat_cons (step280 p h) (sat_cons (step1765 p h) (sat_nil p))))
def c1986 : List Lit := [(997, true), (117, false), (80, false)]
theorem step1986 (p : Nat → Bool) (h : Constraints p) : clause p c1986 = true :=
  Snake9.LocalRup.prove_clause [c1080, c1082, c1078, c1075, c254, c251, c1761] c1986 (by decide) p (sat_cons (step1080 p h) (sat_cons (step1082 p h) (sat_cons (step1078 p h) (sat_cons (step1075 p h) (sat_cons (step254 p h) (sat_cons (step251 p h) (sat_cons (step1761 p h) (sat_nil p))))))))
def c1987 : List Lit := [(1002, true), (71, true), (91, false), (997, false), (81, false), (107, false)]
theorem step1987 (p : Nat → Bool) (h : Constraints p) : clause p c1987 = true :=
  Snake9.LocalRup.prove_clause [c1089, c1093, c1085, c1069, c1076, c1066, c555, c1921] c1987 (by decide) p (sat_cons (step1089 p h) (sat_cons (step1093 p h) (sat_cons (step1085 p h) (sat_cons (step1069 p h) (sat_cons (step1076 p h) (sat_cons (step1066 p h) (sat_cons (step555 p h) (sat_cons (step1921 p h) (sat_nil p)))))))))
def c1988 : List Lit := [(1071, true), (86, false), (109, false)]
theorem step1988 (p : Nat → Bool) (h : Constraints p) : clause p c1988 = true :=
  Snake9.LocalRup.prove_clause [c1248, c1249, c502] c1988 (by decide) p (sat_cons (step1248 p h) (sat_cons (step1249 p h) (sat_cons (step502 p h) (sat_nil p))))
def c1989 : List Lit := [(1072, true), (1061, true), (86, false), (109, false), (1079, true)]
theorem step1989 (p : Nat → Bool) (h : Constraints p) : clause p c1989 = true :=
  Snake9.LocalRup.prove_clause [c1625, c1933, c1215, c1224] c1989 (by decide) p (sat_cons (step1625 p h) (sat_cons (step1933 p h) (sat_cons (step1215 p h) (sat_cons (step1224 p h) (sat_nil p)))))
def c1990 : List Lit := [(1060, true), (1079, true), (86, false), (109, false)]
theorem step1990 (p : Nat → Bool) (h : Constraints p) : clause p c1990 = true :=
  Snake9.LocalRup.prove_clause [c1666, c1658, c1663] c1990 (by decide) p (sat_cons (step1666 p h) (sat_cons (step1658 p h) (sat_cons (step1663 p h) (sat_nil p))))
def c1991 : List Lit := [(81, false), (1090, true), (124, false), (118, false), (1071, false)]
theorem step1991 (p : Nat → Bool) (h : Constraints p) : clause p c1991 = true :=
  Snake9.LocalRup.prove_clause [c634, c638, c1252, c1628, c1257, c1286] c1991 (by decide) p (sat_cons (step634 p h) (sat_cons (step638 p h) (sat_cons (step1252 p h) (sat_cons (step1628 p h) (sat_cons (step1257 p h) (sat_cons (step1286 p h) (sat_nil p)))))))
def c1992 : List Lit := [(1084, false), (1090, true), (1104, true), (1054, false), (1079, true), (86, false), (109, false)]
theorem step1992 (p : Nat → Bool) (h : Constraints p) : clause p c1992 = true :=
  Snake9.LocalRup.prove_clause [c1988, c1256, c1282, c1286, c1342, c1259, c1247, c1989] c1992 (by decide) p (sat_cons (step1988 p h) (sat_cons (step1256 p h) (sat_cons (step1282 p h) (sat_cons (step1286 p h) (sat_cons (step1342 p h) (sat_cons (step1259 p h) (sat_cons (step1247 p h) (sat_cons (step1989 p h) (sat_nil p)))))))))
def c1993 : List Lit := [(1073, false), (1077, true), (1104, true), (1054, false), (1079, true), (86, false), (109, false)]
theorem step1993 (p : Nat → Bool) (h : Constraints p) : clause p c1993 = true :=
  Snake9.LocalRup.prove_clause [c1893, c1988, c1257, c1260, c1285, c1989, c1342, c1247] c1993 (by decide) p (sat_cons (step1893 p h) (sat_cons (step1988 p h) (sat_cons (step1257 p h) (sat_cons (step1260 p h) (sat_cons (step1285 p h) (sat_cons (step1989 p h) (sat_cons (step1342 p h) (sat_cons (step1247 p h) (sat_nil p)))))))))
def c1994 : List Lit := [(1054, false), (1090, true), (1104, true), (1079, true), (86, false), (109, false)]
theorem step1994 (p : Nat → Bool) (h : Constraints p) : clause p c1994 = true :=
  Snake9.LocalRup.prove_clause [c1893, c1289, c1262, c1992, c1993, c1269, c1251, c1252, c1603, c1806, c646, c647, c1267] c1994 (by decide) p (sat_cons (step1893 p h) (sat_cons (step1289 p h) (sat_cons (step1262 p h) (sat_cons (step1992 p h) (sat_cons (step1993 p h) (sat_cons (step1269 p h) (sat_cons (step1251 p h) (sat_cons (step1252 p h) (sat_cons (step1603 p h) (sat_cons (step1806 p h) (sat_cons (step646 p h) (sat_cons (step647 p h) (sat_cons (step1267 p h) (sat_nil p))))))))))))))
end B112E153
