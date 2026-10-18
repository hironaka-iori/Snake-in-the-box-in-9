import B112E020Part0034
namespace B112E020
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c3852 : List Lit := [(45, true), (1598, true), (47, true), (46, false)]
theorem step3852 (p : Nat → Bool) (h : Constraints p) : clause p c3852 = true :=
  Snake9.LocalRup.prove_clause [c1156, c1193, c1164, c1152, c1154, c1161, c1162, c1189, c1157, c1174, c235, c1167] c3852 (by decide) p (sat_cons (step1156 p h) (sat_cons (step1193 p h) (sat_cons (step1164 p h) (sat_cons (step1152 p h) (sat_cons (step1154 p h) (sat_cons (step1161 p h) (sat_cons (step1162 p h) (sat_cons (step1189 p h) (sat_cons (step1157 p h) (sat_cons (step1174 p h) (sat_cons (step235 p h) (sat_cons (step1167 p h) (sat_nil p)))))))))))))
def c3853 : List Lit := [(1569, true), (37, false), (89, false)]
theorem step3853 (p : Nat → Bool) (h : Constraints p) : clause p c3853 = true :=
  Snake9.LocalRup.prove_clause [c1766, c2264, c2358, c190] c3853 (by decide) p (sat_cons (step1766 p h) (sat_cons (step2264 p h) (sat_cons (step2358 p h) (sat_cons (step190 p h) (sat_nil p)))))
def c3854 : List Lit := [(58, true), (1644, true), (61, true), (53, false), (1663, true), (1651, false), (86, false), (91, false), (103, false)]
theorem step3854 (p : Nat → Bool) (h : Constraints p) : clause p c3854 = true :=
  Snake9.LocalRup.prove_clause [c1263, c1264, c3258] c3854 (by decide) p (sat_cons (step1263 p h) (sat_cons (step1264 p h) (sat_cons (step3258 p h) (sat_nil p))))
def c3855 : List Lit := [(1648, true), (61, true), (53, false), (1645, false), (86, false), (210, true)]
theorem step3855 (p : Nat → Bool) (h : Constraints p) : clause p c3855 = true :=
  Snake9.LocalRup.prove_clause [c1269, c1271, c1267, c1262, c2675] c3855 (by decide) p (sat_cons (step1269 p h) (sat_cons (step1271 p h) (sat_cons (step1267 p h) (sat_cons (step1262 p h) (sat_cons (step2675 p h) (sat_nil p))))))
def c3856 : List Lit := [(1720, true), (1736, true), (121, false), (103, false), (115, true), (109, false), (116, false)]
theorem step3856 (p : Nat → Bool) (h : Constraints p) : clause p c3856 = true :=
  Snake9.LocalRup.prove_clause [c3487, c2308, c2985, c3757, c1427, c1424, c1432] c3856 (by decide) p (sat_cons (step3487 p h) (sat_cons (step2308 p h) (sat_cons (step2985 p h) (sat_cons (step3757 p h) (sat_cons (step1427 p h) (sat_cons (step1424 p h) (sat_cons (step1432 p h) (sat_nil p))))))))
def c3857 : List Lit := [(1600, false), (1632, true)]
theorem step3857 (p : Nat → Bool) (h : Constraints p) : clause p c3857 = true :=
  Snake9.LocalRup.prove_clause [c1991, c1983, c1210, c1234, c2205, c1968, c1732] c3857 (by decide) p (sat_cons (step1991 p h) (sat_cons (step1983 p h) (sat_cons (step1210 p h) (sat_cons (step1234 p h) (sat_cons (step2205 p h) (sat_cons (step1968 p h) (sat_cons (step1732 p h) (sat_nil p))))))))
def c3858 : List Lit := [(1600, true), (45, true), (1591, false), (47, true), (46, false)]
theorem step3858 (p : Nat → Bool) (h : Constraints p) : clause p c3858 = true :=
  Snake9.LocalRup.prove_clause [c1156, c1152, c1161, c1173, c1195, c1191, c1164, c1162, c1176, c1154, c1157, c1167, c235] c3858 (by decide) p (sat_cons (step1156 p h) (sat_cons (step1152 p h) (sat_cons (step1161 p h) (sat_cons (step1173 p h) (sat_cons (step1195 p h) (sat_cons (step1191 p h) (sat_cons (step1164 p h) (sat_cons (step1162 p h) (sat_cons (step1176 p h) (sat_cons (step1154 p h) (sat_cons (step1157 p h) (sat_cons (step1167 p h) (sat_cons (step235 p h) (sat_nil p))))))))))))))
def c3859 : List Lit := [(53, false), (61, true), (1652, false), (86, false), (51, true), (210, true), (1663, true), (1645, false)]
theorem step3859 (p : Nat → Bool) (h : Constraints p) : clause p c3859 = true :=
  Snake9.LocalRup.prove_clause [c1287, c1306, c3855, c3851, c1302, c1280, c1288] c3859 (by decide) p (sat_cons (step1287 p h) (sat_cons (step1306 p h) (sat_cons (step3855 p h) (sat_cons (step3851 p h) (sat_cons (step1302 p h) (sat_cons (step1280 p h) (sat_cons (step1288 p h) (sat_nil p))))))))
def c3860 : List Lit := [(1685, true), (1678, false), (115, true), (116, false)]
theorem step3860 (p : Nat → Bool) (h : Constraints p) : clause p c3860 = true :=
  Snake9.LocalRup.prove_clause [c1332, c1340, c1343, c1335, c1318, c1320, c1326, c1316, c1312, c455, c464, c1891] c3860 (by decide) p (sat_cons (step1332 p h) (sat_cons (step1340 p h) (sat_cons (step1343 p h) (sat_cons (step1335 p h) (sat_cons (step1318 p h) (sat_cons (step1320 p h) (sat_cons (step1326 p h) (sat_cons (step1316 p h) (sat_cons (step1312 p h) (sat_cons (step455 p h) (sat_cons (step464 p h) (sat_cons (step1891 p h) (sat_nil p)))))))))))))
def c3861 : List Lit := [(1569, true), (57, false), (89, false)]
theorem step3861 (p : Nat → Bool) (h : Constraints p) : clause p c3861 = true :=
  Snake9.LocalRup.prove_clause [c2314, c3853, c1123] c3861 (by decide) p (sat_cons (step2314 p h) (sat_cons (step3853 p h) (sat_cons (step1123 p h) (sat_nil p))))
def c3862 : List Lit := [(1590, false), (1600, true), (66, false), (45, true), (46, false)]
theorem step3862 (p : Nat → Bool) (h : Constraints p) : clause p c3862 = true :=
  Snake9.LocalRup.prove_clause [c1716, c1195, c1172, c1175, c1198, c1167, c237, c1762, c1154, c1165] c3862 (by decide) p (sat_cons (step1716 p h) (sat_cons (step1195 p h) (sat_cons (step1172 p h) (sat_cons (step1175 p h) (sat_cons (step1198 p h) (sat_cons (step1167 p h) (sat_cons (step237 p h) (sat_cons (step1762 p h) (sat_cons (step1154 p h) (sat_cons (step1165 p h) (sat_nil p)))))))))))
def c3863 : List Lit := [(1600, true), (1591, false), (1585, false), (66, false), (46, false)]
theorem step3863 (p : Nat → Bool) (h : Constraints p) : clause p c3863 = true :=
  Snake9.LocalRup.prove_clause [c1173, c1191, c1195, c1176, c2053, c1167] c3863 (by decide) p (sat_cons (step1173 p h) (sat_cons (step1191 p h) (sat_cons (step1195 p h) (sat_cons (step1176 p h) (sat_cons (step2053 p h) (sat_cons (step1167 p h) (sat_nil p)))))))
def c3864 : List Lit := [(1601, false), (1633, true)]
theorem step3864 (p : Nat → Bool) (h : Constraints p) : clause p c3864 = true :=
  Snake9.LocalRup.prove_clause [c1992, c1984, c1211, c1235, c2205, c1968, c1732] c3864 (by decide) p (sat_cons (step1992 p h) (sat_cons (step1984 p h) (sat_cons (step1211 p h) (sat_cons (step1235 p h) (sat_cons (step2205 p h) (sat_cons (step1968 p h) (sat_cons (step1732 p h) (sat_nil p))))))))
def c3865 : List Lit := [(1660, true), (61, true), (68, false), (1645, false)]
theorem step3865 (p : Nat → Bool) (h : Constraints p) : clause p c3865 = true :=
  Snake9.LocalRup.prove_clause [c1268, c1299, c1295, c3847, c1282, c1280] c3865 (by decide) p (sat_cons (step1268 p h) (sat_cons (step1299 p h) (sat_cons (step1295 p h) (sat_cons (step3847 p h) (sat_cons (step1282 p h) (sat_cons (step1280 p h) (sat_nil p)))))))
def c3866 : List Lit := [(53, true), (1589, true), (1600, true), (1590, false), (66, false), (46, false)]
theorem step3866 (p : Nat → Bool) (h : Constraints p) : clause p c3866 = true :=
  Snake9.LocalRup.prove_clause [c1166, c1168, c1175, c2053, c1195] c3866 (by decide) p (sat_cons (step1166 p h) (sat_cons (step1168 p h) (sat_cons (step1175 p h) (sat_cons (step2053 p h) (sat_cons (step1195 p h) (sat_nil p))))))
def c3867 : List Lit := [(1598, true), (64, false), (118, false), (47, true), (46, false)]
theorem step3867 (p : Nat → Bool) (h : Constraints p) : clause p c3867 = true :=
  Snake9.LocalRup.prove_clause [c1156, c1158, c1186, c3852, c368, c1170, c1172, c1175, c1189, c1167, c1161, c2055, c1153, c235] c3867 (by decide) p (sat_cons (step1156 p h) (sat_cons (step1158 p h) (sat_cons (step1186 p h) (sat_cons (step3852 p h) (sat_cons (step368 p h) (sat_cons (step1170 p h) (sat_cons (step1172 p h) (sat_cons (step1175 p h) (sat_cons (step1189 p h) (sat_cons (step1167 p h) (sat_cons (step1161 p h) (sat_cons (step2055 p h) (sat_cons (step1153 p h) (sat_cons (step235 p h) (sat_nil p)))))))))))))))
def c3868 : List Lit := [(68, false), (56, false), (108, true), (105, true), (109, false), (116, false)]
theorem step3868 (p : Nat → Bool) (h : Constraints p) : clause p c3868 = true :=
  Snake9.LocalRup.prove_clause [c704, c294, c1926] c3868 (by decide) p (sat_cons (step704 p h) (sat_cons (step294 p h) (sat_cons (step1926 p h) (sat_nil p))))
def c3869 : List Lit := [(1759, true), (1748, false), (121, false), (103, false), (115, true), (109, false), (116, false), (1743, false)]
theorem step3869 (p : Nat → Bool) (h : Constraints p) : clause p c3869 = true :=
  Snake9.LocalRup.prove_clause [c2188, c1663, c1412, c1487, c1493, c1461, c1413, c3856] c3869 (by decide) p (sat_cons (step2188 p h) (sat_cons (step1663 p h) (sat_cons (step1412 p h) (sat_cons (step1487 p h) (sat_cons (step1493 p h) (sat_cons (step1461 p h) (sat_cons (step1413 p h) (sat_cons (step3856 p h) (sat_nil p)))))))))
def c3870 : List Lit := [(53, false), (61, true), (1651, false), (86, false), (91, false), (54, false), (51, true), (1663, true), (103, false)]
theorem step3870 (p : Nat → Bool) (h : Constraints p) : clause p c3870 = true :=
  Snake9.LocalRup.prove_clause [c1266, c1284, c1309, c1775, c1853, c3854, c1274, c1275, c1306, c1267, c1285, c364, c1280] c3870 (by decide) p (sat_cons (step1266 p h) (sat_cons (step1284 p h) (sat_cons (step1309 p h) (sat_cons (step1775 p h) (sat_cons (step1853 p h) (sat_cons (step3854 p h) (sat_cons (step1274 p h) (sat_cons (step1275 p h) (sat_cons (step1306 p h) (sat_cons (step1267 p h) (sat_cons (step1285 p h) (sat_cons (step364 p h) (sat_cons (step1280 p h) (sat_nil p))))))))))))))
def c3871 : List Lit := [(1569, false), (1599, false), (1632, true), (34, true)]
theorem step3871 (p : Nat → Bool) (h : Constraints p) : clause p c3871 = true :=
  Snake9.LocalRup.prove_clause [c1991, c1215, c1112, c1115, c1145, c1141, c1116, c1118, c1209, c1114, c1109, c1234, c2051, c1968, c1732] c3871 (by decide) p (sat_cons (step1991 p h) (sat_cons (step1215 p h) (sat_cons (step1112 p h) (sat_cons (step1115 p h) (sat_cons (step1145 p h) (sat_cons (step1141 p h) (sat_cons (step1116 p h) (sat_cons (step1118 p h) (sat_cons (step1209 p h) (sat_cons (step1114 p h) (sat_cons (step1109 p h) (sat_cons (step1234 p h) (sat_cons (step2051 p h) (sat_cons (step1968 p h) (sat_cons (step1732 p h) (sat_nil p))))))))))))))))
def c3872 : List Lit := [(1556, false), (1599, false), (77, false), (58, false), (1632, true)]
theorem step3872 (p : Nat → Bool) (h : Constraints p) : clause p c3872 = true :=
  Snake9.LocalRup.prove_clause [c1991, c1215, c2047, c2057, c1209, c1778, c1234, c1732, c1968] c3872 (by decide) p (sat_cons (step1991 p h) (sat_cons (step1215 p h) (sat_cons (step2047 p h) (sat_cons (step2057 p h) (sat_cons (step1209 p h) (sat_cons (step1778 p h) (sat_cons (step1234 p h) (sat_cons (step1732 p h) (sat_cons (step1968 p h) (sat_nil p))))))))))
def c3873 : List Lit := [(1599, true), (45, true), (53, true), (47, true), (46, false)]
theorem step3873 (p : Nat → Bool) (h : Constraints p) : clause p c3873 = true :=
  Snake9.LocalRup.prove_clause [c1156, c1152, c1161, c1166, c1174, c1194, c1190, c1164, c1162, c1177, c1154, c1157, c1168, c235] c3873 (by decide) p (sat_cons (step1156 p h) (sat_cons (step1152 p h) (sat_cons (step1161 p h) (sat_cons (step1166 p h) (sat_cons (step1174 p h) (sat_cons (step1194 p h) (sat_cons (step1190 p h) (sat_cons (step1164 p h) (sat_cons (step1162 p h) (sat_cons (step1177 p h) (sat_cons (step1154 p h) (sat_cons (step1157 p h) (sat_cons (step1168 p h) (sat_cons (step235 p h) (sat_nil p)))))))))))))))
def c3874 : List Lit := [(61, true), (68, false), (1661, true), (1651, false)]
theorem step3874 (p : Nat → Bool) (h : Constraints p) : clause p c3874 = true :=
  Snake9.LocalRup.prove_clause [c1284, c1300, c1266, c3847, c1268, c1280, c1296, c1285] c3874 (by decide) p (sat_cons (step1284 p h) (sat_cons (step1300 p h) (sat_cons (step1266 p h) (sat_cons (step3847 p h) (sat_cons (step1268 p h) (sat_cons (step1280 p h) (sat_cons (step1296 p h) (sat_cons (step1285 p h) (sat_nil p)))))))))
def c3875 : List Lit := [(1645, true), (54, false), (64, false)]
theorem step3875 (p : Nat → Bool) (h : Constraints p) : clause p c3875 = true :=
  Snake9.LocalRup.prove_clause [c1265, c1266, c372] c3875 (by decide) p (sat_cons (step1265 p h) (sat_cons (step1266 p h) (sat_cons (step372 p h) (sat_nil p))))
def c3876 : List Lit := [(1590, false), (1594, true), (1600, true), (53, true), (66, false), (46, false)]
theorem step3876 (p : Nat → Bool) (h : Constraints p) : clause p c3876 = true :=
  Snake9.LocalRup.prove_clause [c3866, c1178] c3876 (by decide) p (sat_cons (step3866 p h) (sat_cons (step1178 p h) (sat_nil p)))
def c3877 : List Lit := [(45, true), (1600, true), (53, true), (66, false), (46, false)]
theorem step3877 (p : Nat → Bool) (h : Constraints p) : clause p c3877 = true :=
  Snake9.LocalRup.prove_clause [c1166, c1174, c1198, c1716, c1195, c1177, c1168, c237, c1762, c1154, c1165] c3877 (by decide) p (sat_cons (step1166 p h) (sat_cons (step1174 p h) (sat_cons (step1198 p h) (sat_cons (step1716 p h) (sat_cons (step1195 p h) (sat_cons (step1177 p h) (sat_cons (step1168 p h) (sat_cons (step237 p h) (sat_cons (step1762 p h) (sat_cons (step1154 p h) (sat_cons (step1165 p h) (sat_nil p))))))))))))
def c3878 : List Lit := [(1633, true), (1600, false), (26, false), (61, false)]
theorem step3878 (p : Nat → Bool) (h : Constraints p) : clause p c3878 = true :=
  Snake9.LocalRup.prove_clause [c2876, c1968, c1983, c1242, c1235, c1969, c1210, c2047, c2287, c1109, c147] c3878 (by decide) p (sat_cons (step2876 p h) (sat_cons (step1968 p h) (sat_cons (step1983 p h) (sat_cons (step1242 p h) (sat_cons (step1235 p h) (sat_cons (step1969 p h) (sat_cons (step1210 p h) (sat_cons (step2047 p h) (sat_cons (step2287 p h) (sat_cons (step1109 p h) (sat_cons (step147 p h) (sat_nil p))))))))))))
def c3879 : List Lit := [(1599, false), (1631, true)]
theorem step3879 (p : Nat → Bool) (h : Constraints p) : clause p c3879 = true :=
  Snake9.LocalRup.prove_clause [c1990, c1982, c1209, c1233, c2205, c1968, c1732] c3879 (by decide) p (sat_cons (step1990 p h) (sat_cons (step1982 p h) (sat_cons (step1209 p h) (sat_cons (step1233 p h) (sat_cons (step2205 p h) (sat_cons (step1968 p h) (sat_cons (step1732 p h) (sat_nil p))))))))
def c3880 : List Lit := [(53, true), (1599, true), (1590, false), (1582, false), (46, false)]
theorem step3880 (p : Nat → Bool) (h : Constraints p) : clause p c3880 = true :=
  Snake9.LocalRup.prove_clause [c1158, c1187, c1178, c1166, c1168, c1175, c1190, c1161, c2055, c1153, c235] c3880 (by decide) p (sat_cons (step1158 p h) (sat_cons (step1187 p h) (sat_cons (step1178 p h) (sat_cons (step1166 p h) (sat_cons (step1168 p h) (sat_cons (step1175 p h) (sat_cons (step1190 p h) (sat_cons (step1161 p h) (sat_cons (step2055 p h) (sat_cons (step1153 p h) (sat_cons (step235 p h) (sat_nil p))))))))))))
def c3881 : List Lit := [(1660, true), (66, true), (68, false)]
theorem step3881 (p : Nat → Bool) (h : Constraints p) : clause p c3881 = true :=
  Snake9.LocalRup.prove_clause [c1277, c1284, c1291, c2031, c1295, c1285, c1270, c1280, c1262, c406] c3881 (by decide) p (sat_cons (step1277 p h) (sat_cons (step1284 p h) (sat_cons (step1291 p h) (sat_cons (step2031 p h) (sat_cons (step1295 p h) (sat_cons (step1285 p h) (sat_cons (step1270 p h) (sat_cons (step1280 p h) (sat_cons (step1262 p h) (sat_cons (step406 p h) (sat_nil p)))))))))))
def c3882 : List Lit := [(1662, true), (1648, false), (61, true), (53, false), (1651, false), (51, true)]
theorem step3882 (p : Nat → Bool) (h : Constraints p) : clause p c3882 = true :=
  Snake9.LocalRup.prove_clause [c1284, c1305, c1301, c3851, c1285, c1280] c3882 (by decide) p (sat_cons (step1284 p h) (sat_cons (step1305 p h) (sat_cons (step1301 p h) (sat_cons (step3851 p h) (sat_cons (step1285 p h) (sat_cons (step1280 p h) (sat_nil p)))))))
def c3883 : List Lit := [(1599, true), (1591, false), (47, true), (46, false)]
theorem step3883 (p : Nat → Bool) (h : Constraints p) : clause p c3883 = true :=
  Snake9.LocalRup.prove_clause [c1173, c1156, c1158, c1187, c1190, c1176, c1159, c1161, c1167, c1157, c1153, c235] c3883 (by decide) p (sat_cons (step1173 p h) (sat_cons (step1156 p h) (sat_cons (step1158 p h) (sat_cons (step1187 p h) (sat_cons (step1190 p h) (sat_cons (step1176 p h) (sat_cons (step1159 p h) (sat_cons (step1161 p h) (sat_cons (step1167 p h) (sat_cons (step1157 p h) (sat_cons (step1153 p h) (sat_cons (step235 p h) (sat_nil p)))))))))))))
def c3884 : List Lit := [(1601, true), (53, true), (1585, false), (66, false), (1591, false), (46, false)]
theorem step3884 (p : Nat → Bool) (h : Constraints p) : clause p c3884 = true :=
  Snake9.LocalRup.prove_clause [c1166, c1176, c1192, c1196, c1179, c2053, c1168] c3884 (by decide) p (sat_cons (step1166 p h) (sat_cons (step1176 p h) (sat_cons (step1192 p h) (sat_cons (step1196 p h) (sat_cons (step1179 p h) (sat_cons (step2053 p h) (sat_cons (step1168 p h) (sat_nil p))))))))
def c3885 : List Lit := [(61, true), (1660, true), (68, false)]
theorem step3885 (p : Nat → Bool) (h : Constraints p) : clause p c3885 = true :=
  Snake9.LocalRup.prove_clause [c1266, c3865] c3885 (by decide) p (sat_cons (step1266 p h) (sat_cons (step3865 p h) (sat_nil p)))
def c3886 : List Lit := [(1598, true), (1590, false), (47, true), (46, false)]
theorem step3886 (p : Nat → Bool) (h : Constraints p) : clause p c3886 = true :=
  Snake9.LocalRup.prove_clause [c1172, c1156, c1158, c1186, c1189, c1175, c1159, c1161, c1167, c1157, c1153, c235] c3886 (by decide) p (sat_cons (step1172 p h) (sat_cons (step1156 p h) (sat_cons (step1158 p h) (sat_cons (step1186 p h) (sat_cons (step1189 p h) (sat_cons (step1175 p h) (sat_cons (step1159 p h) (sat_cons (step1161 p h) (sat_cons (step1167 p h) (sat_cons (step1157 p h) (sat_cons (step1153 p h) (sat_cons (step235 p h) (sat_nil p)))))))))))))
def c3887 : List Lit := [(1600, true), (53, true), (1585, false), (66, false), (1590, false), (46, false)]
theorem step3887 (p : Nat → Bool) (h : Constraints p) : clause p c3887 = true :=
  Snake9.LocalRup.prove_clause [c1191, c3876] c3887 (by decide) p (sat_cons (step1191 p h) (sat_cons (step3876 p h) (sat_nil p)))
def c3888 : List Lit := [(1599, true), (1585, false), (66, false), (1590, false), (46, false)]
theorem step3888 (p : Nat → Bool) (h : Constraints p) : clause p c3888 = true :=
  Snake9.LocalRup.prove_clause [c1172, c1194, c1190, c2053, c1175, c1167] c3888 (by decide) p (sat_cons (step1172 p h) (sat_cons (step1194 p h) (sat_cons (step1190 p h) (sat_cons (step2053 p h) (sat_cons (step1175 p h) (sat_cons (step1167 p h) (sat_nil p)))))))
def c3889 : List Lit := [(1599, true), (45, true), (1590, false), (47, true), (46, false)]
theorem step3889 (p : Nat → Bool) (h : Constraints p) : clause p c3889 = true :=
  Snake9.LocalRup.prove_clause [c1156, c1152, c1161, c1172, c1194, c1190, c1164, c1162, c1175, c1154, c1157, c1167, c235] c3889 (by decide) p (sat_cons (step1156 p h) (sat_cons (step1152 p h) (sat_cons (step1161 p h) (sat_cons (step1172 p h) (sat_cons (step1194 p h) (sat_cons (step1190 p h) (sat_cons (step1164 p h) (sat_cons (step1162 p h) (sat_cons (step1175 p h) (sat_cons (step1154 p h) (sat_cons (step1157 p h) (sat_cons (step1167 p h) (sat_cons (step235 p h) (sat_nil p))))))))))))))
def c3890 : List Lit := [(1662, true), (61, true), (1651, false), (58, true), (64, true), (116, false)]
theorem step3890 (p : Nat → Bool) (h : Constraints p) : clause p c3890 = true :=
  Snake9.LocalRup.prove_clause [c1263, c1266, c1271, c1284, c1305, c1301, c2168, c1285, c1280] c3890 (by decide) p (sat_cons (step1263 p h) (sat_cons (step1266 p h) (sat_cons (step1271 p h) (sat_cons (step1284 p h) (sat_cons (step1305 p h) (sat_cons (step1301 p h) (sat_cons (step2168 p h) (sat_cons (step1285 p h) (sat_cons (step1280 p h) (sat_nil p))))))))))
def c3891 : List Lit := [(61, false), (68, false), (64, true), (115, true), (116, false)]
theorem step3891 (p : Nat → Bool) (h : Constraints p) : clause p c3891 = true :=
  Snake9.LocalRup.prove_clause [c1863, c357] c3891 (by decide) p (sat_cons (step1863 p h) (sat_cons (step357 p h) (sat_nil p)))
def c3892 : List Lit := [(1661, true), (66, false), (61, true), (1651, false), (122, true)]
theorem step3892 (p : Nat → Bool) (h : Constraints p) : clause p c3892 = true :=
  Snake9.LocalRup.prove_clause [c1266, c1268, c1284, c1296, c1300, c1285, c1269, c1271, c1280, c1267, c1262, c405, c365, c1881] c3892 (by decide) p (sat_cons (step1266 p h) (sat_cons (step1268 p h) (sat_cons (step1284 p h) (sat_cons (step1296 p h) (sat_cons (step1300 p h) (sat_cons (step1285 p h) (sat_cons (step1269 p h) (sat_cons (step1271 p h) (sat_cons (step1280 p h) (sat_cons (step1267 p h) (sat_cons (step1262 p h) (sat_cons (step405 p h) (sat_cons (step365 p h) (sat_cons (step1881 p h) (sat_nil p)))))))))))))))
def c3893 : List Lit := [(54, false), (58, false), (64, true)]
theorem step3893 (p : Nat → Bool) (h : Constraints p) : clause p c3893 = true :=
  Snake9.LocalRup.prove_clause [c1855, c1856, c1579] c3893 (by decide) p (sat_cons (step1855 p h) (sat_cons (step1856 p h) (sat_cons (step1579 p h) (sat_nil p))))
def c3894 : List Lit := [(1652, false), (61, true), (58, true), (64, true), (1663, true), (116, false)]
theorem step3894 (p : Nat → Bool) (h : Constraints p) : clause p c3894 = true :=
  Snake9.LocalRup.prove_clause [c1263, c1266, c1271, c1302, c1287, c1288, c1306, c1280, c2168] c3894 (by decide) p (sat_cons (step1263 p h) (sat_cons (step1266 p h) (sat_cons (step1271 p h) (sat_cons (step1302 p h) (sat_cons (step1287 p h) (sat_cons (step1288 p h) (sat_cons (step1306 p h) (sat_cons (step1280 p h) (sat_cons (step2168 p h) (sat_nil p))))))))))
def c3895 : List Lit := [(113, true), (1736, true), (1760, true), (121, true), (115, true), (116, false)]
theorem step3895 (p : Nat → Bool) (h : Constraints p) : clause p c3895 = true :=
  Snake9.LocalRup.prove_clause [c3510, c1663, c1426, c3473, c1432] c3895 (by decide) p (sat_cons (step3510 p h) (sat_cons (step1663 p h) (sat_cons (step1426 p h) (sat_cons (step3473 p h) (sat_cons (step1432 p h) (sat_nil p))))))
def c3896 : List Lit := [(1731, false), (1736, true), (1760, true), (1744, false), (104, true), (109, false), (1711, false)]
theorem step3896 (p : Nat → Bool) (h : Constraints p) : clause p c3896 = true :=
  Snake9.LocalRup.prove_clause [c1431, c1432, c1457, c1427, c1494, c2985, c1413] c3896 (by decide) p (sat_cons (step1431 p h) (sat_cons (step1432 p h) (sat_cons (step1457 p h) (sat_cons (step1427 p h) (sat_cons (step1494 p h) (sat_cons (step2985 p h) (sat_cons (step1413 p h) (sat_nil p))))))))
def c3897 : List Lit := [(1760, true), (121, true), (103, false), (115, true), (109, false), (116, false), (124, true)]
theorem step3897 (p : Nat → Bool) (h : Constraints p) : clause p c3897 = true :=
  Snake9.LocalRup.prove_clause [c1442, c1444, c2188, c1663, c1412, c3487, c1488, c1462, c3895, c624, c3760, c3896, c1424, c525, c688, c1934] c3897 (by decide) p (sat_cons (step1442 p h) (sat_cons (step1444 p h) (sat_cons (step2188 p h) (sat_cons (step1663 p h) (sat_cons (step1412 p h) (sat_cons (step3487 p h) (sat_cons (step1488 p h) (sat_cons (step1462 p h) (sat_cons (step3895 p h) (sat_cons (step624 p h) (sat_cons (step3760 p h) (sat_cons (step3896 p h) (sat_cons (step1424 p h) (sat_cons (step525 p h) (sat_cons (step688 p h) (sat_cons (step1934 p h) (sat_nil p)))))))))))))))))
def c3898 : List Lit := [(1601, false), (26, false), (61, false), (1634, true)]
theorem step3898 (p : Nat → Bool) (h : Constraints p) : clause p c3898 = true :=
  Snake9.LocalRup.prove_clause [c2876, c1968, c1236, c1984, c1211, c1243, c2047, c2361, c1969, c1109, c2288, c147] c3898 (by decide) p (sat_cons (step2876 p h) (sat_cons (step1968 p h) (sat_cons (step1236 p h) (sat_cons (step1984 p h) (sat_cons (step1211 p h) (sat_cons (step1243 p h) (sat_cons (step2047 p h) (sat_cons (step2361 p h) (sat_cons (step1969 p h) (sat_cons (step1109 p h) (sat_cons (step2288 p h) (sat_cons (step147 p h) (sat_nil p)))))))))))))
def c3899 : List Lit := [(56, false), (58, false), (68, false), (57, true), (109, false)]
theorem step3899 (p : Nat → Bool) (h : Constraints p) : clause p c3899 = true :=
  Snake9.LocalRup.prove_clause [c2333, c1858, c1580] c3899 (by decide) p (sat_cons (step2333 p h) (sat_cons (step1858 p h) (sat_cons (step1580 p h) (sat_nil p))))
def c3900 : List Lit := [(1685, true), (1677, false), (75, true), (115, true), (116, false)]
theorem step3900 (p : Nat → Bool) (h : Constraints p) : clause p c3900 = true :=
  Snake9.LocalRup.prove_clause [c1331, c1313, c1320, c1343, c1346, c1334, c1323, c1321, c1326, c1314, c1316, c455, c464, c1891] c3900 (by decide) p (sat_cons (step1331 p h) (sat_cons (step1313 p h) (sat_cons (step1320 p h) (sat_cons (step1343 p h) (sat_cons (step1346 p h) (sat_cons (step1334 p h) (sat_cons (step1323 p h) (sat_cons (step1321 p h) (sat_cons (step1326 p h) (sat_cons (step1314 p h) (sat_cons (step1316 p h) (sat_cons (step455 p h) (sat_cons (step464 p h) (sat_cons (step1891 p h) (sat_nil p)))))))))))))))
def c3901 : List Lit := [(1761, true), (1731, false), (1744, false), (1725, false), (1715, false), (104, true), (109, false), (116, false)]
theorem step3901 (p : Nat → Bool) (h : Constraints p) : clause p c3901 = true :=
  Snake9.LocalRup.prove_clause [c2188, c1495, c3776, c1462] c3901 (by decide) p (sat_cons (step2188 p h) (sat_cons (step1495 p h) (sat_cons (step3776 p h) (sat_cons (step1462 p h) (sat_nil p)))))
def c3902 : List Lit := [(1761, true), (1739, false), (91, false), (108, true), (1715, false), (115, true), (109, false), (116, false), (122, true), (124, true)]
theorem step3902 (p : Nat → Bool) (h : Constraints p) : clause p c3902 = true :=
  Snake9.LocalRup.prove_clause [c1440, c1446, c2188, c3510, c1402, c1413, c3487, c1495, c3901, c1424, c2043, c3554, c3607, c1418, c3811, c1500, c1447, c1457, c1442, c3783] c3902 (by decide) p (sat_cons (step1440 p h) (sat_cons (step1446 p h) (sat_cons (step2188 p h) (sat_cons (step3510 p h) (sat_cons (step1402 p h) (sat_cons (step1413 p h) (sat_cons (step3487 p h) (sat_cons (step1495 p h) (sat_cons (step3901 p h) (sat_cons (step1424 p h) (sat_cons (step2043 p h) (sat_cons (step3554 p h) (sat_cons (step3607 p h) (sat_cons (step1418 p h) (sat_cons (step3811 p h) (sat_cons (step1500 p h) (sat_cons (step1447 p h) (sat_cons (step1457 p h) (sat_cons (step1442 p h) (sat_cons (step3783 p h) (sat_nil p)))))))))))))))))))))
def c3903 : List Lit := [(1643, true), (53, false), (54, false), (51, false)]
theorem step3903 (p : Nat → Bool) (h : Constraints p) : clause p c3903 = true :=
  Snake9.LocalRup.prove_clause [c1262, c1263, c1578, c270, c1852] c3903 (by decide) p (sat_cons (step1262 p h) (sat_cons (step1263 p h) (sat_cons (step1578 p h) (sat_cons (step270 p h) (sat_cons (step1852 p h) (sat_nil p))))))
def c3904 : List Lit := [(1662, true), (58, true), (61, true), (68, false), (1645, false), (66, true)]
theorem step3904 (p : Nat → Bool) (h : Constraints p) : clause p c3904 = true :=
  Snake9.LocalRup.prove_clause [c1263, c1271, c1277, c1284, c1305, c1301, c1274, c1285, c1264, c1280, c3347, c406] c3904 (by decide) p (sat_cons (step1263 p h) (sat_cons (step1271 p h) (sat_cons (step1277 p h) (sat_cons (step1284 p h) (sat_cons (step1305 p h) (sat_cons (step1301 p h) (sat_cons (step1274 p h) (sat_cons (step1285 p h) (sat_cons (step1264 p h) (sat_cons (step1280 p h) (sat_cons (step3347 p h) (sat_cons (step406 p h) (sat_nil p)))))))))))))
def c3905 : List Lit := [(56, false), (58, false), (68, false), (109, false)]
theorem step3905 (p : Nat → Bool) (h : Constraints p) : clause p c3905 = true :=
  Snake9.LocalRup.prove_clause [c294, c3899] c3905 (by decide) p (sat_cons (step294 p h) (sat_cons (step3899 p h) (sat_nil p)))
def c3906 : List Lit := [(1632, true), (1599, false), (26, false), (61, false)]
theorem step3906 (p : Nat → Bool) (h : Constraints p) : clause p c3906 = true :=
  Snake9.LocalRup.prove_clause [c1982, c2876, c1968, c1234, c1241, c1209, c1969, c2047, c2287, c1109, c147] c3906 (by decide) p (sat_cons (step1982 p h) (sat_cons (step2876 p h) (sat_cons (step1968 p h) (sat_cons (step1234 p h) (sat_cons (step1241 p h) (sat_cons (step1209 p h) (sat_cons (step1969 p h) (sat_cons (step2047 p h) (sat_cons (step2287 p h) (sat_cons (step1109 p h) (sat_cons (step147 p h) (sat_nil p))))))))))))
def c3907 : List Lit := [(47, false), (42, false), (1598, true), (1663, true), (10, true), (60, false), (43, true)]
theorem step3907 (p : Nat → Bool) (h : Constraints p) : clause p c3907 = true :=
  Snake9.LocalRup.prove_clause [c1844, c1843, c232, c1734, c400, c1155, c1280, c1158, c1288, c1186, c3243, c1302, c1177, c3232, c1263, c3224, c1170, c2623] c3907 (by decide) p (sat_cons (step1844 p h) (sat_cons (step1843 p h) (sat_cons (step232 p h) (sat_cons (step1734 p h) (sat_cons (step400 p h) (sat_cons (step1155 p h) (sat_cons (step1280 p h) (sat_cons (step1158 p h) (sat_cons (step1288 p h) (sat_cons (step1186 p h) (sat_cons (step3243 p h) (sat_cons (step1302 p h) (sat_cons (step1177 p h) (sat_cons (step3232 p h) (sat_cons (step1263 p h) (sat_cons (step3224 p h) (sat_cons (step1170 p h) (sat_cons (step2623 p h) (sat_nil p)))))))))))))))))))
def c3908 : List Lit := [(54, false), (58, true), (1648, true), (1598, true), (1582, false)]
theorem step3908 (p : Nat → Bool) (h : Constraints p) : clause p c3908 = true :=
  Snake9.LocalRup.prove_clause [c1263, c1271, c1158, c1186, c1177, c2623, c3875, c1166, c1168, c1174, c1765, c1189, c1152, c1161] c3908 (by decide) p (sat_cons (step1263 p h) (sat_cons (step1271 p h) (sat_cons (step1158 p h) (sat_cons (step1186 p h) (sat_cons (step1177 p h) (sat_cons (step2623 p h) (sat_cons (step3875 p h) (sat_cons (step1166 p h) (sat_cons (step1168 p h) (sat_cons (step1174 p h) (sat_cons (step1765 p h) (sat_cons (step1189 p h) (sat_cons (step1152 p h) (sat_cons (step1161 p h) (sat_nil p)))))))))))))))
def c3909 : List Lit := [(58, true), (1648, true), (1598, true), (1582, false)]
theorem step3909 (p : Nat → Bool) (h : Constraints p) : clause p c3909 = true :=
  Snake9.LocalRup.prove_clause [c1158, c1186, c1263, c3908, c1170, c1172, c1175, c1189, c1166, c1161, c2483, c1152] c3909 (by decide) p (sat_cons (step1158 p h) (sat_cons (step1186 p h) (sat_cons (step1263 p h) (sat_cons (step3908 p h) (sat_cons (step1170 p h) (sat_cons (step1172 p h) (sat_cons (step1175 p h) (sat_cons (step1189 p h) (sat_cons (step1166 p h) (sat_cons (step1161 p h) (sat_cons (step2483 p h) (sat_cons (step1152 p h) (sat_nil p)))))))))))))
def c3910 : List Lit := [(1590, false), (1598, true), (47, true), (11, true)]
theorem step3910 (p : Nat → Bool) (h : Constraints p) : clause p c3910 = true :=
  Snake9.LocalRup.prove_clause [c1156, c1158, c1186, c1172, c3886, c1175, c1189, c1167, c1159, c1161, c1157, c1152, c262, c1847] c3910 (by decide) p (sat_cons (step1156 p h) (sat_cons (step1158 p h) (sat_cons (step1186 p h) (sat_cons (step1172 p h) (sat_cons (step3886 p h) (sat_cons (step1175 p h) (sat_cons (step1189 p h) (sat_cons (step1167 p h) (sat_cons (step1159 p h) (sat_cons (step1161 p h) (sat_cons (step1157 p h) (sat_cons (step1152 p h) (sat_cons (step262 p h) (sat_cons (step1847 p h) (sat_nil p)))))))))))))))
def c3911 : List Lit := [(1648, true), (1590, true), (1598, true), (1582, false)]
theorem step3911 (p : Nat → Bool) (h : Constraints p) : clause p c3911 = true :=
  Snake9.LocalRup.prove_clause [c1170, c1269, c3909, c2211, c3893, c1166, c2493, c1174, c1152, c1189, c1161] c3911 (by decide) p (sat_cons (step1170 p h) (sat_cons (step1269 p h) (sat_cons (step3909 p h) (sat_cons (step2211 p h) (sat_cons (step3893 p h) (sat_cons (step1166 p h) (sat_cons (step2493 p h) (sat_cons (step1174 p h) (sat_cons (step1152 p h) (sat_cons (step1189 p h) (sat_cons (step1161 p h) (sat_nil p))))))))))))
def c3912 : List Lit := [(49, false), (46, true), (42, false), (45, false), (48, false)]
theorem step3912 (p : Nat → Bool) (h : Constraints p) : clause p c3912 = true :=
  Snake9.LocalRup.prove_clause [c262, c223, c1848] c3912 (by decide) p (sat_cons (step262 p h) (sat_cons (step223 p h) (sat_cons (step1848 p h) (sat_nil p))))
def c3913 : List Lit := [(1645, true), (64, false), (45, false)]
theorem step3913 (p : Nat → Bool) (h : Constraints p) : clause p c3913 = true :=
  Snake9.LocalRup.prove_clause [c1265, c1266, c369] c3913 (by decide) p (sat_cons (step1265 p h) (sat_cons (step1266 p h) (sat_cons (step369 p h) (sat_nil p))))
def c3914 : List Lit := [(43, true), (1548, true), (11, false), (46, true), (48, false), (9, true), (47, false), (1575, true)]
theorem step3914 (p : Nat → Bool) (h : Constraints p) : clause p c3914 = true :=
  Snake9.LocalRup.prove_clause [c2309, c2265, c1844, c1110, c1111, c2057, c43, c44, c2051, c1022, c1026, c1732, c1101, c1037, c2024, c1034, c29, c1023] c3914 (by decide) p (sat_cons (step2309 p h) (sat_cons (step2265 p h) (sat_cons (step1844 p h) (sat_cons (step1110 p h) (sat_cons (step1111 p h) (sat_cons (step2057 p h) (sat_cons (step43 p h) (sat_cons (step44 p h) (sat_cons (step2051 p h) (sat_cons (step1022 p h) (sat_cons (step1026 p h) (sat_cons (step1732 p h) (sat_cons (step1101 p h) (sat_cons (step1037 p h) (sat_cons (step2024 p h) (sat_cons (step1034 p h) (sat_cons (step29 p h) (sat_cons (step1023 p h) (sat_nil p)))))))))))))))))))
def c3915 : List Lit := [(1548, true), (11, false), (48, false), (9, true), (44, false), (42, false), (47, false), (1575, true)]
theorem step3915 (p : Nat → Bool) (h : Constraints p) : clause p c3915 = true :=
  Snake9.LocalRup.prove_clause [c232, c3914, c211, c214, c203, c1112, c1832, c2264, c1145, c1116, c1118, c1114, c1109, c2051, c43, c44, c1732, c1023, c1026, c1101, c1034, c1037] c3915 (by decide) p (sat_cons (step232 p h) (sat_cons (step3914 p h) (sat_cons (step211 p h) (sat_cons (step214 p h) (sat_cons (step203 p h) (sat_cons (step1112 p h) (sat_cons (step1832 p h) (sat_cons (step2264 p h) (sat_cons (step1145 p h) (sat_cons (step1116 p h) (sat_cons (step1118 p h) (sat_cons (step1114 p h) (sat_cons (step1109 p h) (sat_cons (step2051 p h) (sat_cons (step43 p h) (sat_cons (step44 p h) (sat_cons (step1732 p h) (sat_cons (step1023 p h) (sat_cons (step1026 p h) (sat_cons (step1101 p h) (sat_cons (step1034 p h) (sat_cons (step1037 p h) (sat_nil p)))))))))))))))))))))))
end B112E020
