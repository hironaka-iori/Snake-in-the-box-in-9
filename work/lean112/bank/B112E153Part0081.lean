import B112E153Part0080
namespace B112E153
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c6731 : List Lit := [(1002, false), (86, true), (1060, false), (1085, false), (113, false)]
theorem step6731 (p : Nat → Bool) (h : Constraints p) : clause p c6731 = true :=
  Snake9.LocalRup.prove_clause [c6719, c6730] c6731 (by decide) p (sat_cons (step6719 p h) (sat_cons (step6730 p h) (sat_nil p)))
def c6732 : List Lit := [(944, true), (1002, true), (113, false)]
theorem step6732 (p : Nat → Bool) (h : Constraints p) : clause p c6732 = true :=
  Snake9.LocalRup.prove_clause [c6364, c1833, c3994, c1074, c228, c6527] c6732 (by decide) p (sat_cons (step6364 p h) (sat_cons (step1833 p h) (sat_cons (step3994 p h) (sat_cons (step1074 p h) (sat_cons (step228 p h) (sat_cons (step6527 p h) (sat_nil p)))))))
def c6733 : List Lit := [(46, false), (100, false), (920, true), (113, false)]
theorem step6733 (p : Nat → Bool) (h : Constraints p) : clause p c6733 = true :=
  Snake9.LocalRup.prove_clause [c2791, c620, c1718] c6733 (by decide) p (sat_cons (step2791 p h) (sat_cons (step620 p h) (sat_cons (step1718 p h) (sat_nil p))))
def c6734 : List Lit := [(100, false), (975, true), (1051, false), (920, true), (944, false), (1010, false), (1085, false), (113, false)]
theorem step6734 (p : Nat → Bool) (h : Constraints p) : clause p c6734 = true :=
  Snake9.LocalRup.prove_clause [c6716, c1112, c6724, c1139, c6457, c6722, c1106, c1854, c1115, c1378, c1179, c6733, c955, c6135, c1632, c6108, c1619, c1910, c5412, c2380, c1027, c2237, c1259, c938, c551, c2143, c1287, c6396, c6072, c1233, c1326] c6734 (by decide) p (sat_cons (step6716 p h) (sat_cons (step1112 p h) (sat_cons (step6724 p h) (sat_cons (step1139 p h) (sat_cons (step6457 p h) (sat_cons (step6722 p h) (sat_cons (step1106 p h) (sat_cons (step1854 p h) (sat_cons (step1115 p h) (sat_cons (step1378 p h) (sat_cons (step1179 p h) (sat_cons (step6733 p h) (sat_cons (step955 p h) (sat_cons (step6135 p h) (sat_cons (step1632 p h) (sat_cons (step6108 p h) (sat_cons (step1619 p h) (sat_cons (step1910 p h) (sat_cons (step5412 p h) (sat_cons (step2380 p h) (sat_cons (step1027 p h) (sat_cons (step2237 p h) (sat_cons (step1259 p h) (sat_cons (step938 p h) (sat_cons (step551 p h) (sat_cons (step2143 p h) (sat_cons (step1287 p h) (sat_cons (step6396 p h) (sat_cons (step6072 p h) (sat_cons (step1233 p h) (sat_cons (step1326 p h) (sat_nil p))))))))))))))))))))))))))))))))
def c6735 : List Lit := [(81, false), (1049, false), (1025, false), (975, true), (1051, false), (920, true), (1002, true), (1024, false), (1085, false), (113, false)]
theorem step6735 (p : Nat → Bool) (h : Constraints p) : clause p c6735 = true :=
  Snake9.LocalRup.prove_clause [c6364, c1089, c1085, c2236, c6240, c2204, c6726, c4258, c6260, c6242, c2237, c1854, c955, c1178, c1074, c1076, c938, c2143, c1910, c5412, c2057, c6132, c1164, c551, c1199, c1287, c1363, c6396, c1207, c1333, c1238] c6735 (by decide) p (sat_cons (step6364 p h) (sat_cons (step1089 p h) (sat_cons (step1085 p h) (sat_cons (step2236 p h) (sat_cons (step6240 p h) (sat_cons (step2204 p h) (sat_cons (step6726 p h) (sat_cons (step4258 p h) (sat_cons (step6260 p h) (sat_cons (step6242 p h) (sat_cons (step2237 p h) (sat_cons (step1854 p h) (sat_cons (step955 p h) (sat_cons (step1178 p h) (sat_cons (step1074 p h) (sat_cons (step1076 p h) (sat_cons (step938 p h) (sat_cons (step2143 p h) (sat_cons (step1910 p h) (sat_cons (step5412 p h) (sat_cons (step2057 p h) (sat_cons (step6132 p h) (sat_cons (step1164 p h) (sat_cons (step551 p h) (sat_cons (step1199 p h) (sat_cons (step1287 p h) (sat_cons (step1363 p h) (sat_cons (step6396 p h) (sat_cons (step1207 p h) (sat_cons (step1333 p h) (sat_cons (step1238 p h) (sat_nil p))))))))))))))))))))))))))))))))
def c6736 : List Lit := [(1076, true), (1068, true), (1049, false), (920, true), (1002, true), (113, false)]
theorem step6736 (p : Nat → Bool) (h : Constraints p) : clause p c6736 = true :=
  Snake9.LocalRup.prove_clause [c6364, c1089, c1085, c6132, c1076, c1889, c6309, c6416] c6736 (by decide) p (sat_cons (step6364 p h) (sat_cons (step1089 p h) (sat_cons (step1085 p h) (sat_cons (step6132 p h) (sat_cons (step1076 p h) (sat_cons (step1889 p h) (sat_cons (step6309 p h) (sat_cons (step6416 p h) (sat_nil p)))))))))
def c6737 : List Lit := [(974, true), (1067, true), (1091, false), (1021, true), (1008, false), (100, true), (953, false), (86, true), (1060, false), (113, false)]
theorem step6737 (p : Nat → Bool) (h : Constraints p) : clause p c6737 = true :=
  Snake9.LocalRup.prove_clause [c1201, c4507, c4774, c1057, c5734, c626, c5365, c1632, c4468, c1207, c1238] c6737 (by decide) p (sat_cons (step1201 p h) (sat_cons (step4507 p h) (sat_cons (step4774 p h) (sat_cons (step1057 p h) (sat_cons (step5734 p h) (sat_cons (step626 p h) (sat_cons (step5365 p h) (sat_cons (step1632 p h) (sat_cons (step4468 p h) (sat_cons (step1207 p h) (sat_cons (step1238 p h) (sat_nil p))))))))))))
def c6738 : List Lit := [(46, true), (1067, true), (1003, true), (1008, false), (1049, false), (1027, true), (920, true), (86, true), (113, false)]
theorem step6738 (p : Nat → Bool) (h : Constraints p) : clause p c6738 = true :=
  Snake9.LocalRup.prove_clause [c955, c6135, c1619, c1910, c5412, c2380, c4046, c938, c551, c3866, c6396, c1207, c1238] c6738 (by decide) p (sat_cons (step955 p h) (sat_cons (step6135 p h) (sat_cons (step1619 p h) (sat_cons (step1910 p h) (sat_cons (step5412 p h) (sat_cons (step2380 p h) (sat_cons (step4046 p h) (sat_cons (step938 p h) (sat_cons (step551 p h) (sat_cons (step3866 p h) (sat_cons (step6396 p h) (sat_cons (step1207 p h) (sat_cons (step1238 p h) (sat_nil p))))))))))))))
def c6739 : List Lit := [(919, false), (1091, false), (1123, true), (1021, true), (1013, false), (1049, false), (975, true), (944, false), (1060, false)]
theorem step6739 (p : Nat → Bool) (h : Constraints p) : clause p c6739 = true :=
  Snake9.LocalRup.prove_clause [c1027, c2237, c1058, c2143, c5365, c6072, c1207, c1326, c1237] c6739 (by decide) p (sat_cons (step1027 p h) (sat_cons (step2237 p h) (sat_cons (step1058 p h) (sat_cons (step2143 p h) (sat_cons (step5365 p h) (sat_cons (step6072 p h) (sat_cons (step1207 p h) (sat_cons (step1326 p h) (sat_cons (step1237 p h) (sat_nil p))))))))))
def c6740 : List Lit := [(1123, true), (975, true), (1027, true), (920, true), (86, true), (1060, false), (1085, false), (113, false)]
theorem step6740 (p : Nat → Bool) (h : Constraints p) : clause p c6740 = true :=
  Snake9.LocalRup.prove_clause [c6716, c6731, c6732, c2117, c1853, c1386, c6724, c1109, c1112, c1138, c6409, c1139, c6734, c1201, c6735, c1106, c1115, c1144, c1180, c1158, c1145, c6109, c1256, c1283, c1089, c1085, c1363, c1338, c6736, c1287, c1333, c6738, c2791, c6739, c1605, c3995, c938, c1706, c4180, c551, c548, c1076, c3866, c4450, c1207, c1238] c6740 (by decide) p (sat_cons (step6716 p h) (sat_cons (step6731 p h) (sat_cons (step6732 p h) (sat_cons (step2117 p h) (sat_cons (step1853 p h) (sat_cons (step1386 p h) (sat_cons (step6724 p h) (sat_cons (step1109 p h) (sat_cons (step1112 p h) (sat_cons (step1138 p h) (sat_cons (step6409 p h) (sat_cons (step1139 p h) (sat_cons (step6734 p h) (sat_cons (step1201 p h) (sat_cons (step6735 p h) (sat_cons (step1106 p h) (sat_cons (step1115 p h) (sat_cons (step1144 p h) (sat_cons (step1180 p h) (sat_cons (step1158 p h) (sat_cons (step1145 p h) (sat_cons (step6109 p h) (sat_cons (step1256 p h) (sat_cons (step1283 p h) (sat_cons (step1089 p h) (sat_cons (step1085 p h) (sat_cons (step1363 p h) (sat_cons (step1338 p h) (sat_cons (step6736 p h) (sat_cons (step1287 p h) (sat_cons (step1333 p h) (sat_cons (step6738 p h) (sat_cons (step2791 p h) (sat_cons (step6739 p h) (sat_cons (step1605 p h) (sat_cons (step3995 p h) (sat_cons (step938 p h) (sat_cons (step1706 p h) (sat_cons (step4180 p h) (sat_cons (step551 p h) (sat_cons (step548 p h) (sat_cons (step1076 p h) (sat_cons (step3866 p h) (sat_cons (step4450 p h) (sat_cons (step1207 p h) (sat_cons (step1238 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))
def c6741 : List Lit := [(975, true), (1027, true), (920, true), (86, true), (1060, false), (1085, false), (113, false)]
theorem step6741 (p : Nat → Bool) (h : Constraints p) : clause p c6741 = true :=
  Snake9.LocalRup.prove_clause [c6409, c6109, c1256, c1283, c6731, c6732, c2117, c1853, c2183, c1109, c1112, c1138, c6724, c1139, c6734, c1201, c6735, c1106, c1115, c1145, c1144, c6740, c1854, c4507, c4774, c6342, c2381, c1057, c2791, c626, c2187, c1027, c5365, c2143, c1632, c3995, c1207, c1165, c4468, c1706, c1371, c1238, c551, c1338, c1333, c6416, c1287] c6741 (by decide) p (sat_cons (step6409 p h) (sat_cons (step6109 p h) (sat_cons (step1256 p h) (sat_cons (step1283 p h) (sat_cons (step6731 p h) (sat_cons (step6732 p h) (sat_cons (step2117 p h) (sat_cons (step1853 p h) (sat_cons (step2183 p h) (sat_cons (step1109 p h) (sat_cons (step1112 p h) (sat_cons (step1138 p h) (sat_cons (step6724 p h) (sat_cons (step1139 p h) (sat_cons (step6734 p h) (sat_cons (step1201 p h) (sat_cons (step6735 p h) (sat_cons (step1106 p h) (sat_cons (step1115 p h) (sat_cons (step1145 p h) (sat_cons (step1144 p h) (sat_cons (step6740 p h) (sat_cons (step1854 p h) (sat_cons (step4507 p h) (sat_cons (step4774 p h) (sat_cons (step6342 p h) (sat_cons (step2381 p h) (sat_cons (step1057 p h) (sat_cons (step2791 p h) (sat_cons (step626 p h) (sat_cons (step2187 p h) (sat_cons (step1027 p h) (sat_cons (step5365 p h) (sat_cons (step2143 p h) (sat_cons (step1632 p h) (sat_cons (step3995 p h) (sat_cons (step1207 p h) (sat_cons (step1165 p h) (sat_cons (step4468 p h) (sat_cons (step1706 p h) (sat_cons (step1371 p h) (sat_cons (step1238 p h) (sat_cons (step551 p h) (sat_cons (step1338 p h) (sat_cons (step1333 p h) (sat_cons (step6416 p h) (sat_cons (step1287 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))
def c6742 : List Lit := [(100, false), (1122, true), (1090, false), (920, true), (1002, true), (1010, false), (1060, false), (113, false)]
theorem step6742 (p : Nat → Bool) (h : Constraints p) : clause p c6742 = true :=
  Snake9.LocalRup.prove_clause [c6457, c6733, c1106, c955, c1115, c2380, c4046, c1074, c1124, c1082, c2057, c1088, c1944] c6742 (by decide) p (sat_cons (step6457 p h) (sat_cons (step6733 p h) (sat_cons (step1106 p h) (sat_cons (step955 p h) (sat_cons (step1115 p h) (sat_cons (step2380 p h) (sat_cons (step4046 p h) (sat_cons (step1074 p h) (sat_cons (step1124 p h) (sat_cons (step1082 p h) (sat_cons (step2057 p h) (sat_cons (step1088 p h) (sat_cons (step1944 p h) (sat_nil p))))))))))))))
def c6743 : List Lit := [(1008, true), (1122, true), (1022, true), (920, true), (1002, true), (1012, false), (113, false)]
theorem step6743 (p : Nat → Bool) (h : Constraints p) : clause p c6743 = true :=
  Snake9.LocalRup.prove_clause [c6716, c6364, c1138, c1369, c1178, c1106, c2205, c2206, c2204, c4258, c6260, c6242, c4058, c955, c1074, c938, c1124, c6108, c1910, c5412, c1082, c2057, c1126, c1132, c551, c1088, c1199, c1139, c6396, c1164, c2212, c1362] c6743 (by decide) p (sat_cons (step6716 p h) (sat_cons (step6364 p h) (sat_cons (step1138 p h) (sat_cons (step1369 p h) (sat_cons (step1178 p h) (sat_cons (step1106 p h) (sat_cons (step2205 p h) (sat_cons (step2206 p h) (sat_cons (step2204 p h) (sat_cons (step4258 p h) (sat_cons (step6260 p h) (sat_cons (step6242 p h) (sat_cons (step4058 p h) (sat_cons (step955 p h) (sat_cons (step1074 p h) (sat_cons (step938 p h) (sat_cons (step1124 p h) (sat_cons (step6108 p h) (sat_cons (step1910 p h) (sat_cons (step5412 p h) (sat_cons (step1082 p h) (sat_cons (step2057 p h) (sat_cons (step1126 p h) (sat_cons (step1132 p h) (sat_cons (step551 p h) (sat_cons (step1088 p h) (sat_cons (step1199 p h) (sat_cons (step1139 p h) (sat_cons (step6396 p h) (sat_cons (step1164 p h) (sat_cons (step2212 p h) (sat_cons (step1362 p h) (sat_nil p)))))))))))))))))))))))))))))))))
def c6744 : List Lit := [(1052, false), (954, false), (35, false), (107, true), (1123, true), (1067, true), (1091, false), (1013, false), (1060, false)]
theorem step6744 (p : Nat → Bool) (h : Constraints p) : clause p c6744 = true :=
  Snake9.LocalRup.prove_clause [c1237, c1238, c1326, c4450, c6072, c1075, c1088, c1082] c6744 (by decide) p (sat_cons (step1237 p h) (sat_cons (step1238 p h) (sat_cons (step1326 p h) (sat_cons (step4450 p h) (sat_cons (step6072 p h) (sat_cons (step1075 p h) (sat_cons (step1088 p h) (sat_cons (step1082 p h) (sat_nil p)))))))))
def c6745 : List Lit := [(73, false), (1123, true), (46, false), (1067, true), (1091, false), (1021, true), (1008, false), (1049, false), (1035, true), (920, true), (944, false), (86, true), (1060, false), (113, false)]
theorem step6745 (p : Nat → Bool) (h : Constraints p) : clause p c6745 = true :=
  Snake9.LocalRup.prove_clause [c6364, c6716, c1109, c1115, c1889, c4180, c6309, c3995, c1027, c6744, c1207, c6055, c5365, c4116] c6745 (by decide) p (sat_cons (step6364 p h) (sat_cons (step6716 p h) (sat_cons (step1109 p h) (sat_cons (step1115 p h) (sat_cons (step1889 p h) (sat_cons (step4180 p h) (sat_cons (step6309 p h) (sat_cons (step3995 p h) (sat_cons (step1027 p h) (sat_cons (step6744 p h) (sat_cons (step1207 p h) (sat_cons (step6055 p h) (sat_cons (step5365 p h) (sat_cons (step4116 p h) (sat_nil p)))))))))))))))
def c6746 : List Lit := [(1027, true), (920, true), (86, true), (1060, false), (1085, false), (113, false)]
theorem step6746 (p : Nat → Bool) (h : Constraints p) : clause p c6746 = true :=
  Snake9.LocalRup.prove_clause [c6716, c6109, c1256, c1283, c6731, c6732, c2183, c1109, c1112, c1138, c1141, c6741, c1855, c1369, c1178, c6742, c1201, c6743, c1115, c1143, c1145, c1157, c1356, c1338, c6736, c1287, c1333, c6737, c6738, c1854, c6745, c1074, c1082, c2057, c1088, c1199, c1164, c1207, c1362, c1237, c1326] c6746 (by decide) p (sat_cons (step6716 p h) (sat_cons (step6109 p h) (sat_cons (step1256 p h) (sat_cons (step1283 p h) (sat_cons (step6731 p h) (sat_cons (step6732 p h) (sat_cons (step2183 p h) (sat_cons (step1109 p h) (sat_cons (step1112 p h) (sat_cons (step1138 p h) (sat_cons (step1141 p h) (sat_cons (step6741 p h) (sat_cons (step1855 p h) (sat_cons (step1369 p h) (sat_cons (step1178 p h) (sat_cons (step6742 p h) (sat_cons (step1201 p h) (sat_cons (step6743 p h) (sat_cons (step1115 p h) (sat_cons (step1143 p h) (sat_cons (step1145 p h) (sat_cons (step1157 p h) (sat_cons (step1356 p h) (sat_cons (step1338 p h) (sat_cons (step6736 p h) (sat_cons (step1287 p h) (sat_cons (step1333 p h) (sat_cons (step6737 p h) (sat_cons (step6738 p h) (sat_cons (step1854 p h) (sat_cons (step6745 p h) (sat_cons (step1074 p h) (sat_cons (step1082 p h) (sat_cons (step2057 p h) (sat_cons (step1088 p h) (sat_cons (step1199 p h) (sat_cons (step1164 p h) (sat_cons (step1207 p h) (sat_cons (step1362 p h) (sat_cons (step1237 p h) (sat_cons (step1326 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))
def c6747 : List Lit := [(81, false), (1025, false), (1035, false), (920, true), (1085, false), (113, false)]
theorem step6747 (p : Nat → Bool) (h : Constraints p) : clause p c6747 = true :=
  Snake9.LocalRup.prove_clause [c6457, c6726, c1201, c1204] c6747 (by decide) p (sat_cons (step6457 p h) (sat_cons (step6726 p h) (sat_cons (step1201 p h) (sat_cons (step1204 p h) (sat_nil p)))))
def c6748 : List Lit := [(100, false), (1008, false), (975, true), (920, true), (944, false), (86, true), (1085, false), (113, false)]
theorem step6748 (p : Nat → Bool) (h : Constraints p) : clause p c6748 = true :=
  Snake9.LocalRup.prove_clause [c6716, c1109, c6722, c6733, c6734, c1854, c955, c1206, c1968, c1378, c4046, c1120, c1160, c2892] c6748 (by decide) p (sat_cons (step6716 p h) (sat_cons (step1109 p h) (sat_cons (step6722 p h) (sat_cons (step6733 p h) (sat_cons (step6734 p h) (sat_cons (step1854 p h) (sat_cons (step955 p h) (sat_cons (step1206 p h) (sat_cons (step1968 p h) (sat_cons (step1378 p h) (sat_cons (step4046 p h) (sat_cons (step1120 p h) (sat_cons (step1160 p h) (sat_cons (step2892 p h) (sat_nil p)))))))))))))))
def c6749 : List Lit := [(1123, true), (1091, false), (1049, false), (1027, false), (1060, false)]
theorem step6749 (p : Nat → Bool) (h : Constraints p) : clause p c6749 = true :=
  Snake9.LocalRup.prove_clause [c6716, c1159, c1378, c1370, c1166, c1326, c1580, c1237, c1199, c1207] c6749 (by decide) p (sat_cons (step6716 p h) (sat_cons (step1159 p h) (sat_cons (step1378 p h) (sat_cons (step1370 p h) (sat_cons (step1166 p h) (sat_cons (step1326 p h) (sat_cons (step1580 p h) (sat_cons (step1237 p h) (sat_cons (step1199 p h) (sat_cons (step1207 p h) (sat_nil p)))))))))))
def c6750 : List Lit := [(920, true), (86, true), (1060, false), (1085, false), (113, false)]
theorem step6750 (p : Nat → Bool) (h : Constraints p) : clause p c6750 = true :=
  Snake9.LocalRup.prove_clause [c6716, c6731, c6732, c2117, c1853, c2183, c1109, c1112, c6109, c1256, c1283, c6746, c1159, c1369, c1371, c1855, c1338, c6724, c1139, c6747, c1106, c6748, c1201, c1204, c6736, c1287, c6749, c1854, c4507, c4766, c4774, c2381, c5734, c624, c626, c2187, c1632, c2143, c4468, c1166, c1233, c6127] c6750 (by decide) p (sat_cons (step6716 p h) (sat_cons (step6731 p h) (sat_cons (step6732 p h) (sat_cons (step2117 p h) (sat_cons (step1853 p h) (sat_cons (step2183 p h) (sat_cons (step1109 p h) (sat_cons (step1112 p h) (sat_cons (step6109 p h) (sat_cons (step1256 p h) (sat_cons (step1283 p h) (sat_cons (step6746 p h) (sat_cons (step1159 p h) (sat_cons (step1369 p h) (sat_cons (step1371 p h) (sat_cons (step1855 p h) (sat_cons (step1338 p h) (sat_cons (step6724 p h) (sat_cons (step1139 p h) (sat_cons (step6747 p h) (sat_cons (step1106 p h) (sat_cons (step6748 p h) (sat_cons (step1201 p h) (sat_cons (step1204 p h) (sat_cons (step6736 p h) (sat_cons (step1287 p h) (sat_cons (step6749 p h) (sat_cons (step1854 p h) (sat_cons (step4507 p h) (sat_cons (step4766 p h) (sat_cons (step4774 p h) (sat_cons (step2381 p h) (sat_cons (step5734 p h) (sat_cons (step624 p h) (sat_cons (step626 p h) (sat_cons (step2187 p h) (sat_cons (step1632 p h) (sat_cons (step2143 p h) (sat_cons (step4468 p h) (sat_cons (step1166 p h) (sat_cons (step1233 p h) (sat_cons (step6127 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))
def c6751 : List Lit := [(1001, false), (1025, false), (73, false), (1076, true), (81, false), (1122, true), (1002, true), (86, true), (1089, false), (113, false)]
theorem step6751 (p : Nat → Bool) (h : Constraints p) : clause p c6751 = true :=
  Snake9.LocalRup.prove_clause [c6364, c6716, c1889, c6457, c1201, c2204, c955, c6732, c6236, c1164, c1038, c1362, c4107, c1337, c6416] c6751 (by decide) p (sat_cons (step6364 p h) (sat_cons (step6716 p h) (sat_cons (step1889 p h) (sat_cons (step6457 p h) (sat_cons (step1201 p h) (sat_cons (step2204 p h) (sat_cons (step955 p h) (sat_cons (step6732 p h) (sat_cons (step6236 p h) (sat_cons (step1164 p h) (sat_cons (step1038 p h) (sat_cons (step1362 p h) (sat_cons (step4107 p h) (sat_cons (step1337 p h) (sat_cons (step6416 p h) (sat_nil p))))))))))))))))
def c6752 : List Lit := [(1025, false), (73, false), (1076, true), (81, false), (1122, true), (1002, true), (86, true), (1089, false), (113, false)]
theorem step6752 (p : Nat → Bool) (h : Constraints p) : clause p c6752 = true :=
  Snake9.LocalRup.prove_clause [c6364, c6716, c1259, c2204, c955, c1109, c1112, c1138, c1156, c1348, c1858, c1157, c1354, c1857, c3914, c6751, c1088, c2143, c1082, c1039, c1075, c4512] c6752 (by decide) p (sat_cons (step6364 p h) (sat_cons (step6716 p h) (sat_cons (step1259 p h) (sat_cons (step2204 p h) (sat_cons (step955 p h) (sat_cons (step1109 p h) (sat_cons (step1112 p h) (sat_cons (step1138 p h) (sat_cons (step1156 p h) (sat_cons (step1348 p h) (sat_cons (step1858 p h) (sat_cons (step1157 p h) (sat_cons (step1354 p h) (sat_cons (step1857 p h) (sat_cons (step3914 p h) (sat_cons (step6751 p h) (sat_cons (step1088 p h) (sat_cons (step2143 p h) (sat_cons (step1082 p h) (sat_cons (step1039 p h) (sat_cons (step1075 p h) (sat_cons (step4512 p h) (sat_nil p)))))))))))))))))))))))
def c6753 : List Lit := [(73, false), (1047, false), (1076, true), (1008, true), (86, true), (1060, false), (1085, false), (113, false)]
theorem step6753 (p : Nat → Bool) (h : Constraints p) : clause p c6753 = true :=
  Snake9.LocalRup.prove_clause [c6364, c6363, c1106, c6457, c1201, c1207, c1237, c229, c1763, c636, c2206, c2205, c6750, c1839, c6731, c6732, c1033, c1980, c1855, c1109, c1112, c1138, c1156, c1278, c6752, c1139, c1126, c1128, c5889, c1124, c1120, c1059, c558, c1856, c4030, c4203, c167, c166, c2872, c326, c2235, c984, c1248, c2716, c1831, c1349, c1013, c1857, c1034, c1060] c6753 (by decide) p (sat_cons (step6364 p h) (sat_cons (step6363 p h) (sat_cons (step1106 p h) (sat_cons (step6457 p h) (sat_cons (step1201 p h) (sat_cons (step1207 p h) (sat_cons (step1237 p h) (sat_cons (step229 p h) (sat_cons (step1763 p h) (sat_cons (step636 p h) (sat_cons (step2206 p h) (sat_cons (step2205 p h) (sat_cons (step6750 p h) (sat_cons (step1839 p h) (sat_cons (step6731 p h) (sat_cons (step6732 p h) (sat_cons (step1033 p h) (sat_cons (step1980 p h) (sat_cons (step1855 p h) (sat_cons (step1109 p h) (sat_cons (step1112 p h) (sat_cons (step1138 p h) (sat_cons (step1156 p h) (sat_cons (step1278 p h) (sat_cons (step6752 p h) (sat_cons (step1139 p h) (sat_cons (step1126 p h) (sat_cons (step1128 p h) (sat_cons (step5889 p h) (sat_cons (step1124 p h) (sat_cons (step1120 p h) (sat_cons (step1059 p h) (sat_cons (step558 p h) (sat_cons (step1856 p h) (sat_cons (step4030 p h) (sat_cons (step4203 p h) (sat_cons (step167 p h) (sat_cons (step166 p h) (sat_cons (step2872 p h) (sat_cons (step326 p h) (sat_cons (step2235 p h) (sat_cons (step984 p h) (sat_cons (step1248 p h) (sat_cons (step2716 p h) (sat_cons (step1831 p h) (sat_cons (step1349 p h) (sat_cons (step1013 p h) (sat_cons (step1857 p h) (sat_cons (step1034 p h) (sat_cons (step1060 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))
def c6754 : List Lit := [(73, true), (1072, true), (912, false), (944, false), (994, true), (86, true), (113, false)]
theorem step6754 (p : Nat → Bool) (h : Constraints p) : clause p c6754 = true :=
  Snake9.LocalRup.prove_clause [c6716, c1074, c1076, c1082, c4218, c1088, c3679, c6236, c1038] c6754 (by decide) p (sat_cons (step6716 p h) (sat_cons (step1074 p h) (sat_cons (step1076 p h) (sat_cons (step1082 p h) (sat_cons (step4218 p h) (sat_cons (step1088 p h) (sat_cons (step3679 p h) (sat_cons (step6236 p h) (sat_cons (step1038 p h) (sat_nil p))))))))))
def c6755 : List Lit := [(1076, true), (1008, true), (86, true), (1060, false), (1085, false), (113, false)]
theorem step6755 (p : Nat → Bool) (h : Constraints p) : clause p c6755 = true :=
  Snake9.LocalRup.prove_clause [c6364, c1106, c2204, c955, c6750, c1839, c6731, c6732, c1033, c1980, c1855, c1089, c1085, c1278, c1259, c6754, c6752, c6753, c5329] c6755 (by decide) p (sat_cons (step6364 p h) (sat_cons (step1106 p h) (sat_cons (step2204 p h) (sat_cons (step955 p h) (sat_cons (step6750 p h) (sat_cons (step1839 p h) (sat_cons (step6731 p h) (sat_cons (step6732 p h) (sat_cons (step1033 p h) (sat_cons (step1980 p h) (sat_cons (step1855 p h) (sat_cons (step1089 p h) (sat_cons (step1085 p h) (sat_cons (step1278 p h) (sat_cons (step1259 p h) (sat_cons (step6754 p h) (sat_cons (step6752 p h) (sat_cons (step6753 p h) (sat_cons (step5329 p h) (sat_nil p))))))))))))))))))))
def c6756 : List Lit := [(1025, false), (1034, true), (1103, false), (919, false), (920, false)]
theorem step6756 (p : Nat → Bool) (h : Constraints p) : clause p c6756 = true :=
  Snake9.LocalRup.prove_clause [c1157, c1164, c1355, c2143, c1856, c3283] c6756 (by decide) p (sat_cons (step1157 p h) (sat_cons (step1164 p h) (sat_cons (step1355 p h) (sat_cons (step2143 p h) (sat_cons (step1856 p h) (sat_cons (step3283 p h) (sat_nil p)))))))
def c6757 : List Lit := [(1103, false), (919, false), (955, false), (920, false), (86, true)]
theorem step6757 (p : Nat → Bool) (h : Constraints p) : clause p c6757 = true :=
  Snake9.LocalRup.prove_clause [c1839, c1980, c1855, c1109, c1112, c1138, c1156, c1349, c1362, c1857, c6756, c1139, c5889, c1059, c1060, c1856, c1034, c1355, c2143, c1163] c6757 (by decide) p (sat_cons (step1839 p h) (sat_cons (step1980 p h) (sat_cons (step1855 p h) (sat_cons (step1109 p h) (sat_cons (step1112 p h) (sat_cons (step1138 p h) (sat_cons (step1156 p h) (sat_cons (step1349 p h) (sat_cons (step1362 p h) (sat_cons (step1857 p h) (sat_cons (step6756 p h) (sat_cons (step1139 p h) (sat_cons (step5889 p h) (sat_cons (step1059 p h) (sat_cons (step1060 p h) (sat_cons (step1856 p h) (sat_cons (step1034 p h) (sat_cons (step1355 p h) (sat_cons (step2143 p h) (sat_cons (step1163 p h) (sat_nil p)))))))))))))))))))))
def c6758 : List Lit := [(1008, true), (86, true), (1060, false), (1085, false), (113, false)]
theorem step6758 (p : Nat → Bool) (h : Constraints p) : clause p c6758 = true :=
  Snake9.LocalRup.prove_clause [c6716, c6750, c1839, c6731, c6732, c1033, c1980, c1855, c1369, c1109, c1112, c1106, c2236, c6457, c1201, c6755, c1287, c6757, c1326, c1237, c1207, c1199, c5329, c1580, c1165, c1164, c1140, c6191] c6758 (by decide) p (sat_cons (step6716 p h) (sat_cons (step6750 p h) (sat_cons (step1839 p h) (sat_cons (step6731 p h) (sat_cons (step6732 p h) (sat_cons (step1033 p h) (sat_cons (step1980 p h) (sat_cons (step1855 p h) (sat_cons (step1369 p h) (sat_cons (step1109 p h) (sat_cons (step1112 p h) (sat_cons (step1106 p h) (sat_cons (step2236 p h) (sat_cons (step6457 p h) (sat_cons (step1201 p h) (sat_cons (step6755 p h) (sat_cons (step1287 p h) (sat_cons (step6757 p h) (sat_cons (step1326 p h) (sat_cons (step1237 p h) (sat_cons (step1207 p h) (sat_cons (step1199 p h) (sat_cons (step5329 p h) (sat_cons (step1580 p h) (sat_cons (step1165 p h) (sat_cons (step1164 p h) (sat_cons (step1140 p h) (sat_cons (step6191 p h) (sat_nil p)))))))))))))))))))))))))))))
def c6759 : List Lit := [(1001, false), (1008, false), (1035, true), (955, false), (86, true)]
theorem step6759 (p : Nat → Bool) (h : Constraints p) : clause p c6759 = true :=
  Snake9.LocalRup.prove_clause [c6716, c1109, c1115, c1143, c1165, c1164, c1148, c1144, c1361, c1116, c1856, c1111, c1059, c6203] c6759 (by decide) p (sat_cons (step6716 p h) (sat_cons (step1109 p h) (sat_cons (step1115 p h) (sat_cons (step1143 p h) (sat_cons (step1165 p h) (sat_cons (step1164 p h) (sat_cons (step1148 p h) (sat_cons (step1144 p h) (sat_cons (step1361 p h) (sat_cons (step1116 p h) (sat_cons (step1856 p h) (sat_cons (step1111 p h) (sat_cons (step1059 p h) (sat_cons (step6203 p h) (sat_nil p)))))))))))))))
def c6760 : List Lit := [(1091, true), (1103, true), (921, true), (1001, true), (1022, true), (1085, false), (113, false)]
theorem step6760 (p : Nat → Bool) (h : Constraints p) : clause p c6760 = true :=
  Snake9.LocalRup.prove_clause [c1088, c1082, c1075, c1074, c1580, c1199, c1287, c1259, c5055, c4201, c4218, c1269, c2009, c5117, c6160, c6165, c1332, c1207, c1238] c6760 (by decide) p (sat_cons (step1088 p h) (sat_cons (step1082 p h) (sat_cons (step1075 p h) (sat_cons (step1074 p h) (sat_cons (step1580 p h) (sat_cons (step1199 p h) (sat_cons (step1287 p h) (sat_cons (step1259 p h) (sat_cons (step5055 p h) (sat_cons (step4201 p h) (sat_cons (step4218 p h) (sat_cons (step1269 p h) (sat_cons (step2009 p h) (sat_cons (step5117 p h) (sat_cons (step6160 p h) (sat_cons (step6165 p h) (sat_cons (step1332 p h) (sat_cons (step1207 p h) (sat_cons (step1238 p h) (sat_nil p))))))))))))))))))))
def c6761 : List Lit := [(86, true), (1060, false), (1085, false), (113, false)]
theorem step6761 (p : Nat → Bool) (h : Constraints p) : clause p c6761 = true :=
  Snake9.LocalRup.prove_clause [c6716, c1109, c1112, c1138, c1156, c1348, c1858, c6731, c6732, c6750, c1839, c1033, c1980, c1855, c1369, c1159, c1141, c6758, c1115, c1143, c1157, c1354, c1857, c3914, c6759, c2143, c1034, c1039, c3284, c1856, c1361, c1355, c1158, c6760, c1326, c6055, c1237] c6761 (by decide) p (sat_cons (step6716 p h) (sat_cons (step1109 p h) (sat_cons (step1112 p h) (sat_cons (step1138 p h) (sat_cons (step1156 p h) (sat_cons (step1348 p h) (sat_cons (step1858 p h) (sat_cons (step6731 p h) (sat_cons (step6732 p h) (sat_cons (step6750 p h) (sat_cons (step1839 p h) (sat_cons (step1033 p h) (sat_cons (step1980 p h) (sat_cons (step1855 p h) (sat_cons (step1369 p h) (sat_cons (step1159 p h) (sat_cons (step1141 p h) (sat_cons (step6758 p h) (sat_cons (step1115 p h) (sat_cons (step1143 p h) (sat_cons (step1157 p h) (sat_cons (step1354 p h) (sat_cons (step1857 p h) (sat_cons (step3914 p h) (sat_cons (step6759 p h) (sat_cons (step2143 p h) (sat_cons (step1034 p h) (sat_cons (step1039 p h) (sat_cons (step3284 p h) (sat_cons (step1856 p h) (sat_cons (step1361 p h) (sat_cons (step1355 p h) (sat_cons (step1158 p h) (sat_cons (step6760 p h) (sat_cons (step1326 p h) (sat_cons (step6055 p h) (sat_cons (step1237 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))
def c6762 : List Lit := [(1121, true), (1034, false)]
theorem step6762 (p : Nat → Bool) (h : Constraints p) : clause p c6762 = true :=
  Snake9.LocalRup.prove_clause [c6716, c1361] c6762 (by decide) p (sat_cons (step6716 p h) (sat_cons (step1361 p h) (sat_nil p)))
def c6763 : List Lit := [(102, false), (82, false), (115, false)]
theorem step6763 (p : Nat → Bool) (h : Constraints p) : clause p c6763 = true :=
  Snake9.LocalRup.prove_clause [c6365, c419] c6763 (by decide) p (sat_cons (step6365 p h) (sat_cons (step419 p h) (sat_nil p)))
def c6764 : List Lit := [(102, false), (115, false), (29, false)]
theorem step6764 (p : Nat → Bool) (h : Constraints p) : clause p c6764 = true :=
  Snake9.LocalRup.prove_clause [c6365, c406] c6764 (by decide) p (sat_cons (step6365 p h) (sat_cons (step406 p h) (sat_nil p)))
def c6765 : List Lit := [(102, false), (82, false), (29, false)]
theorem step6765 (p : Nat → Bool) (h : Constraints p) : clause p c6765 = true :=
  Snake9.LocalRup.prove_clause [c6365, c402] c6765 (by decide) p (sat_cons (step6365 p h) (sat_cons (step402 p h) (sat_nil p)))
def c6766 : List Lit := [(1036, false), (1123, true)]
theorem step6766 (p : Nat → Bool) (h : Constraints p) : clause p c6766 = true :=
  Snake9.LocalRup.prove_clause [c6716, c1378] c6766 (by decide) p (sat_cons (step6716 p h) (sat_cons (step1378 p h) (sat_nil p)))
def c6767 : List Lit := [(1037, false), (1124, true)]
theorem step6767 (p : Nat → Bool) (h : Constraints p) : clause p c6767 = true :=
  Snake9.LocalRup.prove_clause [c6716, c1386] c6767 (by decide) p (sat_cons (step6716 p h) (sat_cons (step1386 p h) (sat_nil p)))
def c6768 : List Lit := [(1119, true), (1032, false)]
theorem step6768 (p : Nat → Bool) (h : Constraints p) : clause p c6768 = true :=
  Snake9.LocalRup.prove_clause [c6716, c1348] c6768 (by decide) p (sat_cons (step6716 p h) (sat_cons (step1348 p h) (sat_nil p)))
def c6769 : List Lit := [(1120, true), (1033, false)]
theorem step6769 (p : Nat → Bool) (h : Constraints p) : clause p c6769 = true :=
  Snake9.LocalRup.prove_clause [c6716, c1354] c6769 (by decide) p (sat_cons (step6716 p h) (sat_cons (step1354 p h) (sat_nil p)))
def c6770 : List Lit := [(73, false), (107, false), (113, false)]
theorem step6770 (p : Nat → Bool) (h : Constraints p) : clause p c6770 = true :=
  Snake9.LocalRup.prove_clause [c6364, c1889] c6770 (by decide) p (sat_cons (step6364 p h) (sat_cons (step1889 p h) (sat_nil p)))
def c6771 : List Lit := [(72, false), (73, false), (113, false)]
theorem step6771 (p : Nat → Bool) (h : Constraints p) : clause p c6771 = true :=
  Snake9.LocalRup.prove_clause [c6364, c228] c6771 (by decide) p (sat_cons (step6364 p h) (sat_cons (step228 p h) (sat_nil p)))
def c6772 : List Lit := [(114, true), (73, false), (107, false), (81, false)]
theorem step6772 (p : Nat → Bool) (h : Constraints p) : clause p c6772 = true :=
  Snake9.LocalRup.prove_clause [c6364, c1921] c6772 (by decide) p (sat_cons (step6364 p h) (sat_cons (step1921 p h) (sat_nil p)))
def c6773 : List Lit := [(66, false), (75, false)]
theorem step6773 (p : Nat → Bool) (h : Constraints p) : clause p c6773 = true :=
  Snake9.LocalRup.prove_clause [c6362, c1588] c6773 (by decide) p (sat_cons (step6362 p h) (sat_cons (step1588 p h) (sat_nil p)))
def c6774 : List Lit := [(66, false), (75, false)]
theorem step6774 (p : Nat → Bool) (h : Constraints p) : clause p c6774 = true :=
  Snake9.LocalRup.prove_clause [c6364, c6365, c205] c6774 (by decide) p (sat_cons (step6364 p h) (sat_cons (step6365 p h) (sat_cons (step205 p h) (sat_nil p))))
def c6775 : List Lit := [(58, false), (61, false), (75, false)]
theorem step6775 (p : Nat → Bool) (h : Constraints p) : clause p c6775 = true :=
  Snake9.LocalRup.prove_clause [c6363, c178] c6775 (by decide) p (sat_cons (step6363 p h) (sat_cons (step178 p h) (sat_nil p)))
def c6776 : List Lit := [(58, false), (57, false), (75, false)]
theorem step6776 (p : Nat → Bool) (h : Constraints p) : clause p c6776 = true :=
  Snake9.LocalRup.prove_clause [c6363, c176] c6776 (by decide) p (sat_cons (step6363 p h) (sat_cons (step176 p h) (sat_nil p)))
def c6777 : List Lit := [(70, false), (52, false), (71, false)]
theorem step6777 (p : Nat → Bool) (h : Constraints p) : clause p c6777 = true :=
  Snake9.LocalRup.prove_clause [c6365, c218] c6777 (by decide) p (sat_cons (step6365 p h) (sat_cons (step218 p h) (sat_nil p)))
def c6778 : List Lit := [(67, false), (105, false)]
theorem step6778 (p : Nat → Bool) (h : Constraints p) : clause p c6778 = true :=
  Snake9.LocalRup.prove_clause [c6365, c6364, c208] c6778 (by decide) p (sat_cons (step6365 p h) (sat_cons (step6364 p h) (sat_cons (step208 p h) (sat_nil p))))
def c6779 : List Lit := [(67, false), (105, false)]
theorem step6779 (p : Nat → Bool) (h : Constraints p) : clause p c6779 = true :=
  Snake9.LocalRup.prove_clause [c6362, c1941] c6779 (by decide) p (sat_cons (step6362 p h) (sat_cons (step1941 p h) (sat_nil p)))
def c6780 : List Lit := [(931, false), (944, true)]
theorem step6780 (p : Nat → Bool) (h : Constraints p) : clause p c6780 = true :=
  Snake9.LocalRup.prove_clause [c6366, c1012] c6780 (by decide) p (sat_cons (step6366 p h) (sat_cons (step1012 p h) (sat_nil p)))
def c6781 : List Lit := [(1122, true), (1035, false)]
theorem step6781 (p : Nat → Bool) (h : Constraints p) : clause p c6781 = true :=
  Snake9.LocalRup.prove_clause [c6716, c1369] c6781 (by decide) p (sat_cons (step6716 p h) (sat_cons (step1369 p h) (sat_nil p)))
def c6782 : List Lit := [(67, true), (108, false), (66, true)]
theorem step6782 (p : Nat → Bool) (h : Constraints p) : clause p c6782 = true :=
  Snake9.LocalRup.prove_clause [c6365, c1626] c6782 (by decide) p (sat_cons (step6365 p h) (sat_cons (step1626 p h) (sat_nil p)))
def c6783 : List Lit := [(102, false), (115, false), (108, false)]
theorem step6783 (p : Nat → Bool) (h : Constraints p) : clause p c6783 = true :=
  Snake9.LocalRup.prove_clause [c6365, c425] c6783 (by decide) p (sat_cons (step6365 p h) (sat_cons (step425 p h) (sat_nil p)))
def c6784 : List Lit := [(102, false), (105, false), (115, false)]
theorem step6784 (p : Nat → Bool) (h : Constraints p) : clause p c6784 = true :=
  Snake9.LocalRup.prove_clause [c6365, c424] c6784 (by decide) p (sat_cons (step6365 p h) (sat_cons (step424 p h) (sat_nil p)))
def c6785 : List Lit := [(72, false), (73, false), (81, false)]
theorem step6785 (p : Nat → Bool) (h : Constraints p) : clause p c6785 = true :=
  Snake9.LocalRup.prove_clause [c6364, c227] c6785 (by decide) p (sat_cons (step6364 p h) (sat_cons (step227 p h) (sat_nil p)))
def c6786 : List Lit := [(81, false), (72, false), (113, false)]
theorem step6786 (p : Nat → Bool) (h : Constraints p) : clause p c6786 = true :=
  Snake9.LocalRup.prove_clause [c6364, c229] c6786 (by decide) p (sat_cons (step6364 p h) (sat_cons (step229 p h) (sat_nil p)))
def c6787 : List Lit := [(1003, false), (1028, false)]
theorem step6787 (p : Nat → Bool) (h : Constraints p) : clause p c6787 = true :=
  Snake9.LocalRup.prove_clause [c6717, c1182] c6787 (by decide) p (sat_cons (step6717 p h) (sat_cons (step1182 p h) (sat_nil p)))
def c6788 : List Lit := [(102, false), (1072, false), (1034, false), (956, false), (1066, false)]
theorem step6788 (p : Nat → Bool) (h : Constraints p) : clause p c6788 = true :=
  Snake9.LocalRup.prove_clause [c6365, c2146] c6788 (by decide) p (sat_cons (step6365 p h) (sat_cons (step2146 p h) (sat_nil p)))
def c6789 : List Lit := [(1084, true), (81, false), (73, false)]
theorem step6789 (p : Nat → Bool) (h : Constraints p) : clause p c6789 = true :=
  Snake9.LocalRup.prove_clause [c6364, c2563] c6789 (by decide) p (sat_cons (step6364 p h) (sat_cons (step2563 p h) (sat_nil p)))
def c6790 : List Lit := [(919, false), (73, false), (99, false), (974, true)]
theorem step6790 (p : Nat → Bool) (h : Constraints p) : clause p c6790 = true :=
  Snake9.LocalRup.prove_clause [c6363, c2567] c6790 (by decide) p (sat_cons (step6363 p h) (sat_cons (step2567 p h) (sat_nil p)))
def c6791 : List Lit := [(939, true), (75, false)]
theorem step6791 (p : Nat → Bool) (h : Constraints p) : clause p c6791 = true :=
  Snake9.LocalRup.prove_clause [c6362, c6363, c2906] c6791 (by decide) p (sat_cons (step6362 p h) (sat_cons (step6363 p h) (sat_cons (step2906 p h) (sat_nil p))))
def c6792 : List Lit := [(75, false), (82, false), (86, false), (108, true), (1061, true), (1072, true)]
theorem step6792 (p : Nat → Bool) (h : Constraints p) : clause p c6792 = true :=
  Snake9.LocalRup.prove_clause [c6362, c2327] c6792 (by decide) p (sat_cons (step6362 p h) (sat_cons (step2327 p h) (sat_nil p)))
def c6793 : List Lit := [(55, true), (939, true)]
theorem step6793 (p : Nat → Bool) (h : Constraints p) : clause p c6793 = true :=
  Snake9.LocalRup.prove_clause [c6363, c2235] c6793 (by decide) p (sat_cons (step6363 p h) (sat_cons (step2235 p h) (sat_nil p)))
def c6794 : List Lit := [(52, false), (108, false), (75, false), (82, false)]
theorem step6794 (p : Nat → Bool) (h : Constraints p) : clause p c6794 = true :=
  Snake9.LocalRup.prove_clause [c6362, c2331] c6794 (by decide) p (sat_cons (step6362 p h) (sat_cons (step2331 p h) (sat_nil p)))
end B112E153
