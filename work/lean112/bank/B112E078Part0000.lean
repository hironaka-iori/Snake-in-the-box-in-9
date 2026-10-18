import B112E078Inputs
namespace B112E078
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1212 : List Lit := [(68, true)]
theorem step1212 (p : Nat → Bool) (h : Constraints p) : clause p c1212 = true :=
  Snake9.LocalRup.prove_clause [c409, c408] c1212 (by decide) p (sat_cons (step409 p h) (sat_cons (step408 p h) (sat_nil p)))
def c1213 : List Lit := [(187, true), (66, true)]
theorem step1213 (p : Nat → Bool) (h : Constraints p) : clause p c1213 = true :=
  Snake9.LocalRup.prove_clause [c1212, c410] c1213 (by decide) p (sat_cons (step1212 p h) (sat_cons (step410 p h) (sat_nil p)))
def c1214 : List Lit := [(470, false)]
theorem step1214 (p : Nat → Bool) (h : Constraints p) : clause p c1214 = true :=
  Snake9.LocalRup.prove_clause [c731, c728] c1214 (by decide) p (sat_cons (step731 p h) (sat_cons (step728 p h) (sat_nil p)))
def c1215 : List Lit := [(354, false)]
theorem step1215 (p : Nat → Bool) (h : Constraints p) : clause p c1215 = true :=
  Snake9.LocalRup.prove_clause [c731, c730] c1215 (by decide) p (sat_cons (step731 p h) (sat_cons (step730 p h) (sat_nil p)))
def c1216 : List Lit := [(468, false)]
theorem step1216 (p : Nat → Bool) (h : Constraints p) : clause p c1216 = true :=
  Snake9.LocalRup.prove_clause [c1214, c724] c1216 (by decide) p (sat_cons (step1214 p h) (sat_cons (step724 p h) (sat_nil p)))
def c1217 : List Lit := [(410, false)]
theorem step1217 (p : Nat → Bool) (h : Constraints p) : clause p c1217 = true :=
  Snake9.LocalRup.prove_clause [c1214, c727] c1217 (by decide) p (sat_cons (step1214 p h) (sat_cons (step727 p h) (sat_nil p)))
def c1218 : List Lit := [(294, false)]
theorem step1218 (p : Nat → Bool) (h : Constraints p) : clause p c1218 = true :=
  Snake9.LocalRup.prove_clause [c1215, c667] c1218 (by decide) p (sat_cons (step1215 p h) (sat_cons (step667 p h) (sat_nil p)))
def c1219 : List Lit := [(466, false)]
theorem step1219 (p : Nat → Bool) (h : Constraints p) : clause p c1219 = true :=
  Snake9.LocalRup.prove_clause [c1216, c720] c1219 (by decide) p (sat_cons (step1216 p h) (sat_cons (step720 p h) (sat_nil p)))
def c1220 : List Lit := [(380, false)]
theorem step1220 (p : Nat → Bool) (h : Constraints p) : clause p c1220 = true :=
  Snake9.LocalRup.prove_clause [c1217, c697] c1220 (by decide) p (sat_cons (step1217 p h) (sat_cons (step697 p h) (sat_nil p)))
def c1221 : List Lit := [(292, false)]
theorem step1221 (p : Nat → Bool) (h : Constraints p) : clause p c1221 = true :=
  Snake9.LocalRup.prove_clause [c1218, c626] c1221 (by decide) p (sat_cons (step1218 p h) (sat_cons (step626 p h) (sat_nil p)))
def c1222 : List Lit := [(264, false)]
theorem step1222 (p : Nat → Bool) (h : Constraints p) : clause p c1222 = true :=
  Snake9.LocalRup.prove_clause [c1218, c629] c1222 (by decide) p (sat_cons (step1218 p h) (sat_cons (step629 p h) (sat_nil p)))
def c1223 : List Lit := [(366, false)]
theorem step1223 (p : Nat → Bool) (h : Constraints p) : clause p c1223 = true :=
  Snake9.LocalRup.prove_clause [c1220, c680] c1223 (by decide) p (sat_cons (step1220 p h) (sat_cons (step680 p h) (sat_nil p)))
def c1224 : List Lit := [(276, false)]
theorem step1224 (p : Nat → Bool) (h : Constraints p) : clause p c1224 = true :=
  Snake9.LocalRup.prove_clause [c1221, c624] c1224 (by decide) p (sat_cons (step1221 p h) (sat_cons (step624 p h) (sat_nil p)))
def c1225 : List Lit := [(262, false)]
theorem step1225 (p : Nat → Bool) (h : Constraints p) : clause p c1225 = true :=
  Snake9.LocalRup.prove_clause [c1222, c600] c1225 (by decide) p (sat_cons (step1222 p h) (sat_cons (step600 p h) (sat_nil p)))
def c1226 : List Lit := [(250, false)]
theorem step1226 (p : Nat → Bool) (h : Constraints p) : clause p c1226 = true :=
  Snake9.LocalRup.prove_clause [c1222, c603] c1226 (by decide) p (sat_cons (step1222 p h) (sat_cons (step603 p h) (sat_nil p)))
def c1227 : List Lit := [(364, false)]
theorem step1227 (p : Nat → Bool) (h : Constraints p) : clause p c1227 = true :=
  Snake9.LocalRup.prove_clause [c1223, c673] c1227 (by decide) p (sat_cons (step1223 p h) (sat_cons (step673 p h) (sat_nil p)))
def c1228 : List Lit := [(274, false)]
theorem step1228 (p : Nat → Bool) (h : Constraints p) : clause p c1228 = true :=
  Snake9.LocalRup.prove_clause [c1224, c614] c1228 (by decide) p (sat_cons (step1224 p h) (sat_cons (step614 p h) (sat_nil p)))
def c1229 : List Lit := [(254, false)]
theorem step1229 (p : Nat → Bool) (h : Constraints p) : clause p c1229 = true :=
  Snake9.LocalRup.prove_clause [c1225, c598] c1229 (by decide) p (sat_cons (step1225 p h) (sat_cons (step598 p h) (sat_nil p)))
def c1230 : List Lit := [(242, false)]
theorem step1230 (p : Nat → Bool) (h : Constraints p) : clause p c1230 = true :=
  Snake9.LocalRup.prove_clause [c1226, c587] c1230 (by decide) p (sat_cons (step1226 p h) (sat_cons (step587 p h) (sat_nil p)))
def c1231 : List Lit := [(270, false)]
theorem step1231 (p : Nat → Bool) (h : Constraints p) : clause p c1231 = true :=
  Snake9.LocalRup.prove_clause [c1228, c612] c1231 (by decide) p (sat_cons (step1228 p h) (sat_cons (step612 p h) (sat_nil p)))
def c1232 : List Lit := [(252, false)]
theorem step1232 (p : Nat → Bool) (h : Constraints p) : clause p c1232 = true :=
  Snake9.LocalRup.prove_clause [c1229, c592] c1232 (by decide) p (sat_cons (step1229 p h) (sat_cons (step592 p h) (sat_nil p)))
def c1233 : List Lit := [(1591, true)]
theorem step1233 (p : Nat → Bool) (h : Constraints p) : clause p c1233 = true :=
  Snake9.LocalRup.prove_clause [c562, c560, c559, c1019, c1022, c1014, c1006, c1008, c1012, c1003, c1004, c416, c407, c403, c398] c1233 (by decide) p (sat_cons (step562 p h) (sat_cons (step560 p h) (sat_cons (step559 p h) (sat_cons (step1019 p h) (sat_cons (step1022 p h) (sat_cons (step1014 p h) (sat_cons (step1006 p h) (sat_cons (step1008 p h) (sat_cons (step1012 p h) (sat_cons (step1003 p h) (sat_cons (step1004 p h) (sat_cons (step416 p h) (sat_cons (step407 p h) (sat_cons (step403 p h) (sat_cons (step398 p h) (sat_nil p))))))))))))))))
def c1234 : List Lit := [(1618, true)]
theorem step1234 (p : Nat → Bool) (h : Constraints p) : clause p c1234 = true :=
  Snake9.LocalRup.prove_clause [c1233, c1048] c1234 (by decide) p (sat_cons (step1233 p h) (sat_cons (step1048 p h) (sat_nil p)))
def c1235 : List Lit := [(1611, true)]
theorem step1235 (p : Nat → Bool) (h : Constraints p) : clause p c1235 = true :=
  Snake9.LocalRup.prove_clause [c566, c1042, c1044, c1040, c1029, c1033, c1034, c1026, c432, c435] c1235 (by decide) p (sat_cons (step566 p h) (sat_cons (step1042 p h) (sat_cons (step1044 p h) (sat_cons (step1040 p h) (sat_cons (step1029 p h) (sat_cons (step1033 p h) (sat_cons (step1034 p h) (sat_cons (step1026 p h) (sat_cons (step432 p h) (sat_cons (step435 p h) (sat_nil p)))))))))))
def c1236 : List Lit := [(1619, true)]
theorem step1236 (p : Nat → Bool) (h : Constraints p) : clause p c1236 = true :=
  Snake9.LocalRup.prove_clause [c1235, c1233, c1049] c1236 (by decide) p (sat_cons (step1235 p h) (sat_cons (step1233 p h) (sat_cons (step1049 p h) (sat_nil p))))
def c1237 : List Lit := [(1537, true)]
theorem step1237 (p : Nat → Bool) (h : Constraints p) : clause p c1237 = true :=
  Snake9.LocalRup.prove_clause [c555, c906, c910, c898, c900, c884, c896, c892, c893, c881, c882, c337, c340, c326] c1237 (by decide) p (sat_cons (step555 p h) (sat_cons (step906 p h) (sat_cons (step910 p h) (sat_cons (step898 p h) (sat_cons (step900 p h) (sat_cons (step884 p h) (sat_cons (step896 p h) (sat_cons (step892 p h) (sat_cons (step893 p h) (sat_cons (step881 p h) (sat_cons (step882 p h) (sat_cons (step337 p h) (sat_cons (step340 p h) (sat_cons (step326 p h) (sat_nil p)))))))))))))))
def c1238 : List Lit := [(1493, true), (7, true), (1473, false), (1455, false), (38, false), (1449, false)]
theorem step1238 (p : Nat → Bool) (h : Constraints p) : clause p c1238 = true :=
  Snake9.LocalRup.prove_clause [c537, c740, c750, c761, c789, c793, c831, c836, c794, c798, c762, c790, c773, c753, c782, c770, c771, c742, c241, c65, c27] c1238 (by decide) p (sat_cons (step537 p h) (sat_cons (step740 p h) (sat_cons (step750 p h) (sat_cons (step761 p h) (sat_cons (step789 p h) (sat_cons (step793 p h) (sat_cons (step831 p h) (sat_cons (step836 p h) (sat_cons (step794 p h) (sat_cons (step798 p h) (sat_cons (step762 p h) (sat_cons (step790 p h) (sat_cons (step773 p h) (sat_cons (step753 p h) (sat_cons (step782 p h) (sat_cons (step770 p h) (sat_cons (step771 p h) (sat_cons (step742 p h) (sat_cons (step241 p h) (sat_cons (step65 p h) (sat_cons (step27 p h) (sat_nil p))))))))))))))))))))))
def c1239 : List Lit := [(6, false), (14, false), (17, false), (25, false), (38, false)]
theorem step1239 (p : Nat → Bool) (h : Constraints p) : clause p c1239 = true :=
  Snake9.LocalRup.prove_clause [c537, c241, c65, c27] c1239 (by decide) p (sat_cons (step537 p h) (sat_cons (step241 p h) (sat_cons (step65 p h) (sat_cons (step27 p h) (sat_nil p)))))
def c1240 : List Lit := [(1665, false), (1679, true), (1652, false), (40, true)]
theorem step1240 (p : Nat → Bool) (h : Constraints p) : clause p c1240 = true :=
  Snake9.LocalRup.prove_clause [c573, c1128, c1095, c1119, c1123, c1131, c1096, c1077, c1091, c1070, c1067, c481, c482, c1208] c1240 (by decide) p (sat_cons (step573 p h) (sat_cons (step1128 p h) (sat_cons (step1095 p h) (sat_cons (step1119 p h) (sat_cons (step1123 p h) (sat_cons (step1131 p h) (sat_cons (step1096 p h) (sat_cons (step1077 p h) (sat_cons (step1091 p h) (sat_cons (step1070 p h) (sat_cons (step1067 p h) (sat_cons (step481 p h) (sat_cons (step482 p h) (sat_cons (step1208 p h) (sat_nil p)))))))))))))))
def c1241 : List Lit := [(103, false), (107, false), (40, true)]
theorem step1241 (p : Nat → Bool) (h : Constraints p) : clause p c1241 = true :=
  Snake9.LocalRup.prove_clause [c573, c481, c482, c1208] c1241 (by decide) p (sat_cons (step573 p h) (sat_cons (step481 p h) (sat_cons (step482 p h) (sat_cons (step1208 p h) (sat_nil p)))))
def c1242 : List Lit := [(103, true), (1642, true)]
theorem step1242 (p : Nat → Bool) (h : Constraints p) : clause p c1242 = true :=
  Snake9.LocalRup.prove_clause [c572, c1071, c1067, c1069, c1073, c470, c1064, c1065, c474] c1242 (by decide) p (sat_cons (step572 p h) (sat_cons (step1071 p h) (sat_cons (step1067 p h) (sat_cons (step1069 p h) (sat_cons (step1073 p h) (sat_cons (step470 p h) (sat_cons (step1064 p h) (sat_cons (step1065 p h) (sat_cons (step474 p h) (sat_nil p))))))))))
def c1243 : List Lit := [(1660, true), (105, false), (109, false), (41, true)]
theorem step1243 (p : Nat → Bool) (h : Constraints p) : clause p c1243 = true :=
  Snake9.LocalRup.prove_clause [c574, c1101, c1102, c513, c483, c485] c1243 (by decide) p (sat_cons (step574 p h) (sat_cons (step1101 p h) (sat_cons (step1102 p h) (sat_cons (step513 p h) (sat_cons (step483 p h) (sat_cons (step485 p h) (sat_nil p)))))))
def c1244 : List Lit := [(1523, true), (38, false), (40, true)]
theorem step1244 (p : Nat → Bool) (h : Constraints p) : clause p c1244 = true :=
  Snake9.LocalRup.prove_clause [c555, c881, c882, c342, c323] c1244 (by decide) p (sat_cons (step555 p h) (sat_cons (step881 p h) (sat_cons (step882 p h) (sat_cons (step342 p h) (sat_cons (step323 p h) (sat_nil p))))))
def c1245 : List Lit := [(1534, true), (55, true), (39, false)]
theorem step1245 (p : Nat → Bool) (h : Constraints p) : clause p c1245 = true :=
  Snake9.LocalRup.prove_clause [c556, c892, c903, c901, c894, c895, c896, c394, c334, c345] c1245 (by decide) p (sat_cons (step556 p h) (sat_cons (step892 p h) (sat_cons (step903 p h) (sat_cons (step901 p h) (sat_cons (step894 p h) (sat_cons (step895 p h) (sat_cons (step896 p h) (sat_cons (step394 p h) (sat_cons (step334 p h) (sat_cons (step345 p h) (sat_nil p)))))))))))
def c1246 : List Lit := [(57, true), (1535, true), (47, false), (55, true), (39, false)]
theorem step1246 (p : Nat → Bool) (h : Constraints p) : clause p c1246 = true :=
  Snake9.LocalRup.prove_clause [c556, c892, c902, c895, c897, c904, c894, c334, c391, c345] c1246 (by decide) p (sat_cons (step556 p h) (sat_cons (step892 p h) (sat_cons (step902 p h) (sat_cons (step895 p h) (sat_cons (step897 p h) (sat_cons (step904 p h) (sat_cons (step894 p h) (sat_cons (step334 p h) (sat_cons (step391 p h) (sat_cons (step345 p h) (sat_nil p)))))))))))
def c1247 : List Lit := [(56, false), (45, true), (57, false), (1524, true), (47, false), (39, false), (40, true)]
theorem step1247 (p : Nat → Bool) (h : Constraints p) : clause p c1247 = true :=
  Snake9.LocalRup.prove_clause [c558, c555, c393, c386, c359, c883, c341, c333] c1247 (by decide) p (sat_cons (step558 p h) (sat_cons (step555 p h) (sat_cons (step393 p h) (sat_cons (step386 p h) (sat_cons (step359 p h) (sat_cons (step883 p h) (sat_cons (step341 p h) (sat_cons (step333 p h) (sat_nil p)))))))))
def c1248 : List Lit := [(1535, true), (1524, true), (47, false), (55, true), (27, false), (39, false), (40, true)]
theorem step1248 (p : Nat → Bool) (h : Constraints p) : clause p c1248 = true :=
  Snake9.LocalRup.prove_clause [c556, c1246, c286, c1247, c896, c904, c894, c392, c345, c330, c332, c883] c1248 (by decide) p (sat_cons (step556 p h) (sat_cons (step1246 p h) (sat_cons (step286 p h) (sat_cons (step1247 p h) (sat_cons (step896 p h) (sat_cons (step904 p h) (sat_cons (step894 p h) (sat_cons (step392 p h) (sat_cons (step345 p h) (sat_cons (step330 p h) (sat_cons (step332 p h) (sat_cons (step883 p h) (sat_nil p)))))))))))))
def c1249 : List Lit := [(1521, true), (48, false), (42, false)]
theorem step1249 (p : Nat → Bool) (h : Constraints p) : clause p c1249 = true :=
  Snake9.LocalRup.prove_clause [c878, c879, c311] c1249 (by decide) p (sat_cons (step878 p h) (sat_cons (step879 p h) (sat_cons (step311 p h) (sat_nil p))))
def c1250 : List Lit := [(1641, true)]
theorem step1250 (p : Nat → Bool) (h : Constraints p) : clause p c1250 = true :=
  Snake9.LocalRup.prove_clause [c572, c1070, c1072, c1068, c1064, c1065, c470, c474] c1250 (by decide) p (sat_cons (step572 p h) (sat_cons (step1070 p h) (sat_cons (step1072 p h) (sat_cons (step1068 p h) (sat_cons (step1064 p h) (sat_cons (step1065 p h) (sat_cons (step470 p h) (sat_cons (step474 p h) (sat_nil p)))))))))
def c1251 : List Lit := [(1645, true)]
theorem step1251 (p : Nat → Bool) (h : Constraints p) : clause p c1251 = true :=
  Snake9.LocalRup.prove_clause [c1250, c1077] c1251 (by decide) p (sat_cons (step1250 p h) (sat_cons (step1077 p h) (sat_nil p)))
def c1252 : List Lit := [(1654, false), (106, true), (1679, true), (41, true), (40, true)]
theorem step1252 (p : Nat → Bool) (h : Constraints p) : clause p c1252 = true :=
  Snake9.LocalRup.prove_clause [c1251, c1131, c1124, c1087, c1097, c1096, c1099, c1121, c1122, c1089, c1135, c1109, c1078, c1243, c1242, c1092, c1241] c1252 (by decide) p (sat_cons (step1251 p h) (sat_cons (step1131 p h) (sat_cons (step1124 p h) (sat_cons (step1087 p h) (sat_cons (step1097 p h) (sat_cons (step1096 p h) (sat_cons (step1099 p h) (sat_cons (step1121 p h) (sat_cons (step1122 p h) (sat_cons (step1089 p h) (sat_cons (step1135 p h) (sat_cons (step1109 p h) (sat_cons (step1078 p h) (sat_cons (step1243 p h) (sat_cons (step1242 p h) (sat_cons (step1092 p h) (sat_cons (step1241 p h) (sat_nil p))))))))))))))))))
def c1253 : List Lit := [(1654, true), (47, false), (27, false)]
theorem step1253 (p : Nat → Bool) (h : Constraints p) : clause p c1253 = true :=
  Snake9.LocalRup.prove_clause [c577, c1090, c1091, c504, c287, c501] c1253 (by decide) p (sat_cons (step577 p h) (sat_cons (step1090 p h) (sat_cons (step1091 p h) (sat_cons (step504 p h) (sat_cons (step287 p h) (sat_cons (step501 p h) (sat_nil p)))))))
def c1254 : List Lit := [(1669, true), (109, false), (106, true), (41, true)]
theorem step1254 (p : Nat → Bool) (h : Constraints p) : clause p c1254 = true :=
  Snake9.LocalRup.prove_clause [c1087, c1095, c1121, c1118, c1098, c1109, c1089, c1243] c1254 (by decide) p (sat_cons (step1087 p h) (sat_cons (step1095 p h) (sat_cons (step1121 p h) (sat_cons (step1118 p h) (sat_cons (step1098 p h) (sat_cons (step1109 p h) (sat_cons (step1089 p h) (sat_cons (step1243 p h) (sat_nil p)))))))))
def c1255 : List Lit := [(1662, true), (55, false), (1532, true)]
theorem step1255 (p : Nat → Bool) (h : Constraints p) : clause p c1255 = true :=
  Snake9.LocalRup.prove_clause [c580, c1104, c1105, c528, c524, c363, c364, c897] c1255 (by decide) p (sat_cons (step580 p h) (sat_cons (step1104 p h) (sat_cons (step1105 p h) (sat_cons (step528 p h) (sat_cons (step524 p h) (sat_cons (step363 p h) (sat_cons (step364 p h) (sat_cons (step897 p h) (sat_nil p)))))))))
def c1256 : List Lit := [(1670, true), (1662, false), (109, false), (106, true), (41, true)]
theorem step1256 (p : Nat → Bool) (h : Constraints p) : clause p c1256 = true :=
  Snake9.LocalRup.prove_clause [c1107, c1087, c1095, c1119, c1122, c1110, c1098, c1243, c1089] c1256 (by decide) p (sat_cons (step1107 p h) (sat_cons (step1087 p h) (sat_cons (step1095 p h) (sat_cons (step1119 p h) (sat_cons (step1122 p h) (sat_cons (step1110 p h) (sat_cons (step1098 p h) (sat_cons (step1243 p h) (sat_cons (step1089 p h) (sat_nil p))))))))))
def c1257 : List Lit := [(1612, true), (1605, false)]
theorem step1257 (p : Nat → Bool) (h : Constraints p) : clause p c1257 = true :=
  Snake9.LocalRup.prove_clause [c566, c1038, c1043, c1045, c1041, c1029, c1033, c1034, c1026, c432, c435] c1257 (by decide) p (sat_cons (step566 p h) (sat_cons (step1038 p h) (sat_cons (step1043 p h) (sat_cons (step1045 p h) (sat_cons (step1041 p h) (sat_cons (step1029 p h) (sat_cons (step1033 p h) (sat_cons (step1034 p h) (sat_cons (step1026 p h) (sat_cons (step432 p h) (sat_cons (step435 p h) (sat_nil p))))))))))))
def c1258 : List Lit := [(1662, true), (1678, true), (106, false)]
theorem step1258 (p : Nat → Bool) (h : Constraints p) : clause p c1258 = true :=
  Snake9.LocalRup.prove_clause [c581, c1104, c1105, c529, c532, c496, c498, c1242, c1091, c1078, c1093, c1134, c1117] c1258 (by decide) p (sat_cons (step581 p h) (sat_cons (step1104 p h) (sat_cons (step1105 p h) (sat_cons (step529 p h) (sat_cons (step532 p h) (sat_cons (step496 p h) (sat_cons (step498 p h) (sat_cons (step1242 p h) (sat_cons (step1091 p h) (sat_cons (step1078 p h) (sat_cons (step1093 p h) (sat_cons (step1134 p h) (sat_cons (step1117 p h) (sat_nil p))))))))))))))
def c1259 : List Lit := [(1678, true), (106, false), (41, true)]
theorem step1259 (p : Nat → Bool) (h : Constraints p) : clause p c1259 = true :=
  Snake9.LocalRup.prove_clause [c1251, c1130, c1115, c1258, c1107, c1110, c1118, c1093, c1095, c1090, c1088, c1243] c1259 (by decide) p (sat_cons (step1251 p h) (sat_cons (step1130 p h) (sat_cons (step1115 p h) (sat_cons (step1258 p h) (sat_cons (step1107 p h) (sat_cons (step1110 p h) (sat_cons (step1118 p h) (sat_cons (step1093 p h) (sat_cons (step1095 p h) (sat_cons (step1090 p h) (sat_cons (step1088 p h) (sat_cons (step1243 p h) (sat_nil p)))))))))))))
def c1260 : List Lit := [(116, false), (55, false), (1532, true), (106, false)]
theorem step1260 (p : Nat → Bool) (h : Constraints p) : clause p c1260 = true :=
  Snake9.LocalRup.prove_clause [c580, c526, c524, c363, c364, c897] c1260 (by decide) p (sat_cons (step580 p h) (sat_cons (step526 p h) (sat_cons (step524 p h) (sat_cons (step363 p h) (sat_cons (step364 p h) (sat_cons (step897 p h) (sat_nil p)))))))
def c1261 : List Lit := [(1654, true), (116, true), (1670, true), (102, true), (44, true), (106, false), (41, true)]
theorem step1261 (p : Nat → Bool) (h : Constraints p) : clause p c1261 = true :=
  Snake9.LocalRup.prove_clause [c576, c1116, c1090, c1091, c494, c498, c1106, c1108, c1111, c1119, c1243, c1095, c1088] c1261 (by decide) p (sat_cons (step576 p h) (sat_cons (step1116 p h) (sat_cons (step1090 p h) (sat_cons (step1091 p h) (sat_cons (step494 p h) (sat_cons (step498 p h) (sat_cons (step1106 p h) (sat_cons (step1108 p h) (sat_cons (step1111 p h) (sat_cons (step1119 p h) (sat_cons (step1243 p h) (sat_cons (step1095 p h) (sat_cons (step1088 p h) (sat_nil p))))))))))))))
def c1262 : List Lit := [(118, false), (1662, false), (55, false), (1680, true), (106, false), (41, true)]
theorem step1262 (p : Nat → Bool) (h : Constraints p) : clause p c1262 = true :=
  Snake9.LocalRup.prove_clause [c581, c1107, c527, c532, c496, c498, c1242, c1091, c1078, c1093, c1136, c1119, c1122, c1110, c1094, c1096, c1092, c1088, c1243] c1262 (by decide) p (sat_cons (step581 p h) (sat_cons (step1107 p h) (sat_cons (step527 p h) (sat_cons (step532 p h) (sat_cons (step496 p h) (sat_cons (step498 p h) (sat_cons (step1242 p h) (sat_cons (step1091 p h) (sat_cons (step1078 p h) (sat_cons (step1093 p h) (sat_cons (step1136 p h) (sat_cons (step1119 p h) (sat_cons (step1122 p h) (sat_cons (step1110 p h) (sat_cons (step1094 p h) (sat_cons (step1096 p h) (sat_cons (step1092 p h) (sat_cons (step1088 p h) (sat_cons (step1243 p h) (sat_nil p))))))))))))))))))))
def c1263 : List Lit := [(1654, false), (1663, false), (1680, true), (41, true), (40, true)]
theorem step1263 (p : Nat → Bool) (h : Constraints p) : clause p c1263 = true :=
  Snake9.LocalRup.prove_clause [c1251, c1132, c1108, c1123, c1094, c1093, c1096, c1120, c1119, c1088, c1111, c1136, c1243, c1078, c1092, c1242, c1241] c1263 (by decide) p (sat_cons (step1251 p h) (sat_cons (step1132 p h) (sat_cons (step1108 p h) (sat_cons (step1123 p h) (sat_cons (step1094 p h) (sat_cons (step1093 p h) (sat_cons (step1096 p h) (sat_cons (step1120 p h) (sat_cons (step1119 p h) (sat_cons (step1088 p h) (sat_cons (step1111 p h) (sat_cons (step1136 p h) (sat_cons (step1243 p h) (sat_cons (step1078 p h) (sat_cons (step1092 p h) (sat_cons (step1242 p h) (sat_cons (step1241 p h) (sat_nil p))))))))))))))))))
def c1264 : List Lit := [(1493, false), (106, false), (1527, false), (1620, false), (41, true), (39, false), (40, true)]
theorem step1264 (p : Nat → Bool) (h : Constraints p) : clause p c1264 = true :=
  Snake9.LocalRup.prove_clause [c1171, c1259, c1156, c1168, c920, c929, c992, c994, c1166, c931, c1158, c922, c899, c1245, c1255, c1260, c1262, c1106, c1108, c1263, c1090, c1091, c1241, c1242, c1078, c1136, c1116, c1119, c1111, c1095, c1243, c1088] c1264 (by decide) p (sat_cons (step1171 p h) (sat_cons (step1259 p h) (sat_cons (step1156 p h) (sat_cons (step1168 p h) (sat_cons (step920 p h) (sat_cons (step929 p h) (sat_cons (step992 p h) (sat_cons (step994 p h) (sat_cons (step1166 p h) (sat_cons (step931 p h) (sat_cons (step1158 p h) (sat_cons (step922 p h) (sat_cons (step899 p h) (sat_cons (step1245 p h) (sat_cons (step1255 p h) (sat_cons (step1260 p h) (sat_cons (step1262 p h) (sat_cons (step1106 p h) (sat_cons (step1108 p h) (sat_cons (step1263 p h) (sat_cons (step1090 p h) (sat_cons (step1091 p h) (sat_cons (step1241 p h) (sat_cons (step1242 p h) (sat_cons (step1078 p h) (sat_cons (step1136 p h) (sat_cons (step1116 p h) (sat_cons (step1119 p h) (sat_cons (step1111 p h) (sat_cons (step1095 p h) (sat_cons (step1243 p h) (sat_cons (step1088 p h) (sat_nil p)))))))))))))))))))))))))))))))))
def c1265 : List Lit := [(1592, true), (90, false), (72, true)]
theorem step1265 (p : Nat → Bool) (h : Constraints p) : clause p c1265 = true :=
  Snake9.LocalRup.prove_clause [c559, c1012, c1014, c1020, c1023, c1015, c1006, c1013, c1004, c404, c402] c1265 (by decide) p (sat_cons (step559 p h) (sat_cons (step1012 p h) (sat_cons (step1014 p h) (sat_cons (step1020 p h) (sat_cons (step1023 p h) (sat_cons (step1015 p h) (sat_cons (step1006 p h) (sat_cons (step1013 p h) (sat_cons (step1004 p h) (sat_cons (step404 p h) (sat_cons (step402 p h) (sat_nil p))))))))))))
def c1266 : List Lit := [(1534, true), (116, false), (106, false), (39, false)]
theorem step1266 (p : Nat → Bool) (h : Constraints p) : clause p c1266 = true :=
  Snake9.LocalRup.prove_clause [c899, c1245, c1260] c1266 (by decide) p (sat_cons (step899 p h) (sat_cons (step1245 p h) (sat_cons (step1260 p h) (sat_nil p))))
def c1267 : List Lit := [(1698, true), (1669, false), (72, true), (1642, false), (1612, false)]
theorem step1267 (p : Nat → Bool) (h : Constraints p) : clause p c1267 = true :=
  Snake9.LocalRup.prove_clause [c1233, c1078, c1135, c1050, c1158, c1162, c1139, c1053, c1081, c1265, c1061] c1267 (by decide) p (sat_cons (step1233 p h) (sat_cons (step1078 p h) (sat_cons (step1135 p h) (sat_cons (step1050 p h) (sat_cons (step1158 p h) (sat_cons (step1162 p h) (sat_cons (step1139 p h) (sat_cons (step1053 p h) (sat_cons (step1081 p h) (sat_cons (step1265 p h) (sat_cons (step1061 p h) (sat_nil p))))))))))))
def c1268 : List Lit := [(90, false), (1592, true), (5, false)]
theorem step1268 (p : Nat → Bool) (h : Constraints p) : clause p c1268 = true :=
  Snake9.LocalRup.prove_clause [c562, c559, c1024, c1265, c416, c413, c1008, c1009, c1023, c1004, c1014, c404, c1011, c402] c1268 (by decide) p (sat_cons (step562 p h) (sat_cons (step559 p h) (sat_cons (step1024 p h) (sat_cons (step1265 p h) (sat_cons (step416 p h) (sat_cons (step413 p h) (sat_cons (step1008 p h) (sat_cons (step1009 p h) (sat_cons (step1023 p h) (sat_cons (step1004 p h) (sat_cons (step1014 p h) (sat_cons (step404 p h) (sat_cons (step1011 p h) (sat_cons (step402 p h) (sat_nil p)))))))))))))))
def c1269 : List Lit := [(1533, true), (39, false)]
theorem step1269 (p : Nat → Bool) (h : Constraints p) : clause p c1269 = true :=
  Snake9.LocalRup.prove_clause [c556, c898, c900, c895, c896, c893, c394, c334, c345] c1269 (by decide) p (sat_cons (step556 p h) (sat_cons (step898 p h) (sat_cons (step900 p h) (sat_cons (step895 p h) (sat_cons (step896 p h) (sat_cons (step893 p h) (sat_cons (step394 p h) (sat_cons (step334 p h) (sat_cons (step345 p h) (sat_nil p))))))))))
def c1270 : List Lit := [(53, false), (51, true), (56, false), (57, false)]
theorem step1270 (p : Nat → Bool) (h : Constraints p) : clause p c1270 = true :=
  Snake9.LocalRup.prove_clause [c556, c394, c345] c1270 (by decide) p (sat_cons (step556 p h) (sat_cons (step394 p h) (sat_cons (step345 p h) (sat_nil p))))
def c1271 : List Lit := [(7, false), (17, false), (56, false), (1, true), (39, false)]
theorem step1271 (p : Nat → Bool) (h : Constraints p) : clause p c1271 = true :=
  Snake9.LocalRup.prove_clause [c538, c263, c75, c31] c1271 (by decide) p (sat_cons (step538 p h) (sat_cons (step263 p h) (sat_cons (step75 p h) (sat_cons (step31 p h) (sat_nil p)))))
def c1272 : List Lit := [(1679, true), (106, true), (40, true), (41, true)]
theorem step1272 (p : Nat → Bool) (h : Constraints p) : clause p c1272 = true :=
  Snake9.LocalRup.prove_clause [c1252, c1090, c1091, c1254, c1241, c1135, c1242, c1078] c1272 (by decide) p (sat_cons (step1252 p h) (sat_cons (step1090 p h) (sat_cons (step1091 p h) (sat_cons (step1254 p h) (sat_cons (step1241 p h) (sat_cons (step1135 p h) (sat_cons (step1242 p h) (sat_cons (step1078 p h) (sat_nil p)))))))))
def c1273 : List Lit := [(1493, false), (1527, false), (1620, false), (41, true), (39, false), (40, true)]
theorem step1273 (p : Nat → Bool) (h : Constraints p) : clause p c1273 = true :=
  Snake9.LocalRup.prove_clause [c1171, c1269, c921, c930, c1264, c993, c1167, c1157, c1272] c1273 (by decide) p (sat_cons (step1171 p h) (sat_cons (step1269 p h) (sat_cons (step921 p h) (sat_cons (step930 p h) (sat_cons (step1264 p h) (sat_cons (step993 p h) (sat_cons (step1167 p h) (sat_cons (step1157 p h) (sat_cons (step1272 p h) (sat_nil p))))))))))
def c1274 : List Lit := [(26, true), (1493, true), (1473, false), (1455, false), (38, false), (1449, false)]
theorem step1274 (p : Nat → Bool) (h : Constraints p) : clause p c1274 = true :=
  Snake9.LocalRup.prove_clause [c747, c760, c826, c795, c791, c781, c783, c790, c794, c799, c831, c773, c761, c770, c771, c750, c1239, c741] c1274 (by decide) p (sat_cons (step747 p h) (sat_cons (step760 p h) (sat_cons (step826 p h) (sat_cons (step795 p h) (sat_cons (step791 p h) (sat_cons (step781 p h) (sat_cons (step783 p h) (sat_cons (step790 p h) (sat_cons (step794 p h) (sat_cons (step799 p h) (sat_cons (step831 p h) (sat_cons (step773 p h) (sat_cons (step761 p h) (sat_cons (step770 p h) (sat_cons (step771 p h) (sat_cons (step750 p h) (sat_cons (step1239 p h) (sat_cons (step741 p h) (sat_nil p)))))))))))))))))))
def c1275 : List Lit := [(17, false), (16, false), (1493, true), (1473, false), (1455, false), (38, false), (1449, false)]
theorem step1275 (p : Nat → Bool) (h : Constraints p) : clause p c1275 = true :=
  Snake9.LocalRup.prove_clause [c541, c537, c789, c747, c760, c826, c803, c1238, c73, c771, c773, c776, c798, c799, c58, c831, c790, c79, c761, c782, c750, c741, c27, c241] c1275 (by decide) p (sat_cons (step541 p h) (sat_cons (step537 p h) (sat_cons (step789 p h) (sat_cons (step747 p h) (sat_cons (step760 p h) (sat_cons (step826 p h) (sat_cons (step803 p h) (sat_cons (step1238 p h) (sat_cons (step73 p h) (sat_cons (step771 p h) (sat_cons (step773 p h) (sat_cons (step776 p h) (sat_cons (step798 p h) (sat_cons (step799 p h) (sat_cons (step58 p h) (sat_cons (step831 p h) (sat_cons (step790 p h) (sat_cons (step79 p h) (sat_cons (step761 p h) (sat_cons (step782 p h) (sat_cons (step750 p h) (sat_cons (step741 p h) (sat_cons (step27 p h) (sat_cons (step241 p h) (sat_nil p)))))))))))))))))))))))))
end B112E078
