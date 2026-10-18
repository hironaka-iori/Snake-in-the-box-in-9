import B112E088Inputs
namespace B112E088
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1160 : List Lit := [(11, true)]
theorem step1160 (p : Nat → Bool) (h : Constraints p) : clause p c1160 = true :=
  Snake9.LocalRup.prove_clause [c35, c34] c1160 (by decide) p (sat_cons (step35 p h) (sat_cons (step34 p h) (sat_nil p)))
def c1161 : List Lit := [(127, true), (9, true)]
theorem step1161 (p : Nat → Bool) (h : Constraints p) : clause p c1161 = true :=
  Snake9.LocalRup.prove_clause [c1160, c38] c1161 (by decide) p (sat_cons (step1160 p h) (sat_cons (step38 p h) (sat_nil p)))
def c1162 : List Lit := [(55, false)]
theorem step1162 (p : Nat → Bool) (h : Constraints p) : clause p c1162 = true :=
  Snake9.LocalRup.prove_clause [c497, c367] c1162 (by decide) p (sat_cons (step497 p h) (sat_cons (step367 p h) (sat_nil p)))
def c1163 : List Lit := [(64, false)]
theorem step1163 (p : Nat → Bool) (h : Constraints p) : clause p c1163 = true :=
  Snake9.LocalRup.prove_clause [c503, c385] c1163 (by decide) p (sat_cons (step503 p h) (sat_cons (step385 p h) (sat_nil p)))
def c1164 : List Lit := [(458, false)]
theorem step1164 (p : Nat → Bool) (h : Constraints p) : clause p c1164 = true :=
  Snake9.LocalRup.prove_clause [c682, c679] c1164 (by decide) p (sat_cons (step682 p h) (sat_cons (step679 p h) (sat_nil p)))
def c1165 : List Lit := [(344, false)]
theorem step1165 (p : Nat → Bool) (h : Constraints p) : clause p c1165 = true :=
  Snake9.LocalRup.prove_clause [c682, c681] c1165 (by decide) p (sat_cons (step682 p h) (sat_cons (step681 p h) (sat_nil p)))
def c1166 : List Lit := [(456, false)]
theorem step1166 (p : Nat → Bool) (h : Constraints p) : clause p c1166 = true :=
  Snake9.LocalRup.prove_clause [c1164, c675] c1166 (by decide) p (sat_cons (step1164 p h) (sat_cons (step675 p h) (sat_nil p)))
def c1167 : List Lit := [(400, false)]
theorem step1167 (p : Nat → Bool) (h : Constraints p) : clause p c1167 = true :=
  Snake9.LocalRup.prove_clause [c1164, c678] c1167 (by decide) p (sat_cons (step1164 p h) (sat_cons (step678 p h) (sat_nil p)))
def c1168 : List Lit := [(342, false)]
theorem step1168 (p : Nat → Bool) (h : Constraints p) : clause p c1168 = true :=
  Snake9.LocalRup.prove_clause [c1165, c616] c1168 (by decide) p (sat_cons (step1165 p h) (sat_cons (step616 p h) (sat_nil p)))
def c1169 : List Lit := [(286, false)]
theorem step1169 (p : Nat → Bool) (h : Constraints p) : clause p c1169 = true :=
  Snake9.LocalRup.prove_clause [c1165, c619] c1169 (by decide) p (sat_cons (step1165 p h) (sat_cons (step619 p h) (sat_nil p)))
def c1170 : List Lit := [(426, false)]
theorem step1170 (p : Nat → Bool) (h : Constraints p) : clause p c1170 = true :=
  Snake9.LocalRup.prove_clause [c1166, c673] c1170 (by decide) p (sat_cons (step1166 p h) (sat_cons (step673 p h) (sat_nil p)))
def c1171 : List Lit := [(370, false)]
theorem step1171 (p : Nat → Bool) (h : Constraints p) : clause p c1171 = true :=
  Snake9.LocalRup.prove_clause [c1167, c645] c1171 (by decide) p (sat_cons (step1167 p h) (sat_cons (step645 p h) (sat_nil p)))
def c1172 : List Lit := [(340, false)]
theorem step1172 (p : Nat → Bool) (h : Constraints p) : clause p c1172 = true :=
  Snake9.LocalRup.prove_clause [c1168, c611] c1172 (by decide) p (sat_cons (step1168 p h) (sat_cons (step611 p h) (sat_nil p)))
def c1173 : List Lit := [(312, false)]
theorem step1173 (p : Nat → Bool) (h : Constraints p) : clause p c1173 = true :=
  Snake9.LocalRup.prove_clause [c1168, c614] c1173 (by decide) p (sat_cons (step1168 p h) (sat_cons (step614 p h) (sat_nil p)))
def c1174 : List Lit := [(258, false)]
theorem step1174 (p : Nat → Bool) (h : Constraints p) : clause p c1174 = true :=
  Snake9.LocalRup.prove_clause [c1169, c566] c1174 (by decide) p (sat_cons (step1169 p h) (sat_cons (step566 p h) (sat_nil p)))
def c1175 : List Lit := [(338, false)]
theorem step1175 (p : Nat → Bool) (h : Constraints p) : clause p c1175 = true :=
  Snake9.LocalRup.prove_clause [c1172, c607] c1175 (by decide) p (sat_cons (step1172 p h) (sat_cons (step607 p h) (sat_nil p)))
def c1176 : List Lit := [(298, false)]
theorem step1176 (p : Nat → Bool) (h : Constraints p) : clause p c1176 = true :=
  Snake9.LocalRup.prove_clause [c1173, c586] c1176 (by decide) p (sat_cons (step1173 p h) (sat_cons (step586 p h) (sat_nil p)))
def c1177 : List Lit := [(256, false)]
theorem step1177 (p : Nat → Bool) (h : Constraints p) : clause p c1177 = true :=
  Snake9.LocalRup.prove_clause [c1174, c545] c1177 (by decide) p (sat_cons (step1174 p h) (sat_cons (step545 p h) (sat_nil p)))
def c1178 : List Lit := [(244, false)]
theorem step1178 (p : Nat → Bool) (h : Constraints p) : clause p c1178 = true :=
  Snake9.LocalRup.prove_clause [c1174, c548] c1178 (by decide) p (sat_cons (step1174 p h) (sat_cons (step548 p h) (sat_nil p)))
def c1179 : List Lit := [(330, false)]
theorem step1179 (p : Nat → Bool) (h : Constraints p) : clause p c1179 = true :=
  Snake9.LocalRup.prove_clause [c1175, c605] c1179 (by decide) p (sat_cons (step1175 p h) (sat_cons (step605 p h) (sat_nil p)))
def c1180 : List Lit := [(290, false)]
theorem step1180 (p : Nat → Bool) (h : Constraints p) : clause p c1180 = true :=
  Snake9.LocalRup.prove_clause [c1176, c575] c1180 (by decide) p (sat_cons (step1176 p h) (sat_cons (step575 p h) (sat_nil p)))
def c1181 : List Lit := [(254, false)]
theorem step1181 (p : Nat → Bool) (h : Constraints p) : clause p c1181 = true :=
  Snake9.LocalRup.prove_clause [c1177, c542] c1181 (by decide) p (sat_cons (step1177 p h) (sat_cons (step542 p h) (sat_nil p)))
def c1182 : List Lit := [(236, false)]
theorem step1182 (p : Nat → Bool) (h : Constraints p) : clause p c1182 = true :=
  Snake9.LocalRup.prove_clause [c1178, c531] c1182 (by decide) p (sat_cons (step1178 p h) (sat_cons (step531 p h) (sat_nil p)))
def c1183 : List Lit := [(328, false)]
theorem step1183 (p : Nat → Bool) (h : Constraints p) : clause p c1183 = true :=
  Snake9.LocalRup.prove_clause [c1179, c599] c1183 (by decide) p (sat_cons (step1179 p h) (sat_cons (step599 p h) (sat_nil p)))
def c1184 : List Lit := [(1467, true)]
theorem step1184 (p : Nat → Bool) (h : Constraints p) : clause p c1184 = true :=
  Snake9.LocalRup.prove_clause [c1162, c830] c1184 (by decide) p (sat_cons (step1162 p h) (sat_cons (step830 p h) (sat_nil p)))
def c1185 : List Lit := [(51, true), (1468, true)]
theorem step1185 (p : Nat → Bool) (h : Constraints p) : clause p c1185 = true :=
  Snake9.LocalRup.prove_clause [c1162, c831] c1185 (by decide) p (sat_cons (step1162 p h) (sat_cons (step831 p h) (sat_nil p)))
def c1186 : List Lit := [(1471, true)]
theorem step1186 (p : Nat → Bool) (h : Constraints p) : clause p c1186 = true :=
  Snake9.LocalRup.prove_clause [c1184, c836] c1186 (by decide) p (sat_cons (step1184 p h) (sat_cons (step836 p h) (sat_nil p)))
def c1187 : List Lit := [(1469, false), (1472, true)]
theorem step1187 (p : Nat → Bool) (h : Constraints p) : clause p c1187 = true :=
  Snake9.LocalRup.prove_clause [c1184, c837] c1187 (by decide) p (sat_cons (step1184 p h) (sat_cons (step837 p h) (sat_nil p)))
def c1188 : List Lit := [(1470, false), (1473, true)]
theorem step1188 (p : Nat → Bool) (h : Constraints p) : clause p c1188 = true :=
  Snake9.LocalRup.prove_clause [c1184, c838] c1188 (by decide) p (sat_cons (step1184 p h) (sat_cons (step838 p h) (sat_nil p)))
def c1189 : List Lit := [(1475, true)]
theorem step1189 (p : Nat → Bool) (h : Constraints p) : clause p c1189 = true :=
  Snake9.LocalRup.prove_clause [c1186, c842] c1189 (by decide) p (sat_cons (step1186 p h) (sat_cons (step842 p h) (sat_nil p)))
def c1190 : List Lit := [(1463, false), (1476, true)]
theorem step1190 (p : Nat → Bool) (h : Constraints p) : clause p c1190 = true :=
  Snake9.LocalRup.prove_clause [c1186, c846] c1190 (by decide) p (sat_cons (step1186 p h) (sat_cons (step846 p h) (sat_nil p)))
def c1191 : List Lit := [(1464, false), (1477, true)]
theorem step1191 (p : Nat → Bool) (h : Constraints p) : clause p c1191 = true :=
  Snake9.LocalRup.prove_clause [c1186, c850] c1191 (by decide) p (sat_cons (step1186 p h) (sat_cons (step850 p h) (sat_nil p)))
def c1192 : List Lit := [(1465, false), (1478, true)]
theorem step1192 (p : Nat → Bool) (h : Constraints p) : clause p c1192 = true :=
  Snake9.LocalRup.prove_clause [c1186, c854] c1192 (by decide) p (sat_cons (step1186 p h) (sat_cons (step854 p h) (sat_nil p)))
def c1193 : List Lit := [(1466, false), (1479, true)]
theorem step1193 (p : Nat → Bool) (h : Constraints p) : clause p c1193 = true :=
  Snake9.LocalRup.prove_clause [c1186, c858] c1193 (by decide) p (sat_cons (step1186 p h) (sat_cons (step858 p h) (sat_nil p)))
def c1194 : List Lit := [(1454, false), (1486, true)]
theorem step1194 (p : Nat → Bool) (h : Constraints p) : clause p c1194 = true :=
  Snake9.LocalRup.prove_clause [c1189, c875] c1194 (by decide) p (sat_cons (step1189 p h) (sat_cons (step875 p h) (sat_nil p)))
def c1195 : List Lit := [(1455, false), (1487, true)]
theorem step1195 (p : Nat → Bool) (h : Constraints p) : clause p c1195 = true :=
  Snake9.LocalRup.prove_clause [c1189, c882] c1195 (by decide) p (sat_cons (step1189 p h) (sat_cons (step882 p h) (sat_nil p)))
def c1196 : List Lit := [(1456, false), (1488, true)]
theorem step1196 (p : Nat → Bool) (h : Constraints p) : clause p c1196 = true :=
  Snake9.LocalRup.prove_clause [c1189, c888] c1196 (by decide) p (sat_cons (step1189 p h) (sat_cons (step888 p h) (sat_nil p)))
def c1197 : List Lit := [(1457, false), (1489, true)]
theorem step1197 (p : Nat → Bool) (h : Constraints p) : clause p c1197 = true :=
  Snake9.LocalRup.prove_clause [c1189, c894] c1197 (by decide) p (sat_cons (step1189 p h) (sat_cons (step894 p h) (sat_nil p)))
def c1198 : List Lit := [(1458, false), (1490, true)]
theorem step1198 (p : Nat → Bool) (h : Constraints p) : clause p c1198 = true :=
  Snake9.LocalRup.prove_clause [c1189, c899] c1198 (by decide) p (sat_cons (step1189 p h) (sat_cons (step899 p h) (sat_nil p)))
def c1199 : List Lit := [(1522, true)]
theorem step1199 (p : Nat → Bool) (h : Constraints p) : clause p c1199 = true :=
  Snake9.LocalRup.prove_clause [c1163, c950] c1199 (by decide) p (sat_cons (step1163 p h) (sat_cons (step950 p h) (sat_nil p)))
def c1200 : List Lit := [(66, true), (1523, true)]
theorem step1200 (p : Nat → Bool) (h : Constraints p) : clause p c1200 = true :=
  Snake9.LocalRup.prove_clause [c1163, c951] c1200 (by decide) p (sat_cons (step1163 p h) (sat_cons (step951 p h) (sat_nil p)))
def c1201 : List Lit := [(1526, true)]
theorem step1201 (p : Nat → Bool) (h : Constraints p) : clause p c1201 = true :=
  Snake9.LocalRup.prove_clause [c1199, c955] c1201 (by decide) p (sat_cons (step1199 p h) (sat_cons (step955 p h) (sat_nil p)))
def c1202 : List Lit := [(1524, false), (1527, true)]
theorem step1202 (p : Nat → Bool) (h : Constraints p) : clause p c1202 = true :=
  Snake9.LocalRup.prove_clause [c1199, c956] c1202 (by decide) p (sat_cons (step1199 p h) (sat_cons (step956 p h) (sat_nil p)))
def c1203 : List Lit := [(1525, false), (1528, true)]
theorem step1203 (p : Nat → Bool) (h : Constraints p) : clause p c1203 = true :=
  Snake9.LocalRup.prove_clause [c1199, c957] c1203 (by decide) p (sat_cons (step1199 p h) (sat_cons (step957 p h) (sat_nil p)))
def c1204 : List Lit := [(1530, true)]
theorem step1204 (p : Nat → Bool) (h : Constraints p) : clause p c1204 = true :=
  Snake9.LocalRup.prove_clause [c1201, c960] c1204 (by decide) p (sat_cons (step1201 p h) (sat_cons (step960 p h) (sat_nil p)))
def c1205 : List Lit := [(1519, false), (1531, true)]
theorem step1205 (p : Nat → Bool) (h : Constraints p) : clause p c1205 = true :=
  Snake9.LocalRup.prove_clause [c1201, c963] c1205 (by decide) p (sat_cons (step1201 p h) (sat_cons (step963 p h) (sat_nil p)))
def c1206 : List Lit := [(1553, false), (1562, true)]
theorem step1206 (p : Nat → Bool) (h : Constraints p) : clause p c1206 = true :=
  Snake9.LocalRup.prove_clause [c1204, c992] c1206 (by decide) p (sat_cons (step1204 p h) (sat_cons (step992 p h) (sat_nil p)))
def c1207 : List Lit := [(1554, false), (1563, true)]
theorem step1207 (p : Nat → Bool) (h : Constraints p) : clause p c1207 = true :=
  Snake9.LocalRup.prove_clause [c1204, c993] c1207 (by decide) p (sat_cons (step1204 p h) (sat_cons (step993 p h) (sat_nil p)))
def c1208 : List Lit := [(1562, true)]
theorem step1208 (p : Nat → Bool) (h : Constraints p) : clause p c1208 = true :=
  Snake9.LocalRup.prove_clause [c507, c506, c505, c1206, c994, c987, c961, c972, c973, c1202, c958, c971, c968, c952, c1200, c403, c402, c399, c390] c1208 (by decide) p (sat_cons (step507 p h) (sat_cons (step506 p h) (sat_cons (step505 p h) (sat_cons (step1206 p h) (sat_cons (step994 p h) (sat_cons (step987 p h) (sat_cons (step961 p h) (sat_cons (step972 p h) (sat_cons (step973 p h) (sat_cons (step1202 p h) (sat_cons (step958 p h) (sat_cons (step971 p h) (sat_cons (step968 p h) (sat_cons (step952 p h) (sat_cons (step1200 p h) (sat_cons (step403 p h) (sat_cons (step402 p h) (sat_cons (step399 p h) (sat_cons (step390 p h) (sat_nil p))))))))))))))))))))
def c1209 : List Lit := [(85, false), (88, false)]
theorem step1209 (p : Nat → Bool) (h : Constraints p) : clause p c1209 = true :=
  Snake9.LocalRup.prove_clause [c508, c415, c416, c1157] c1209 (by decide) p (sat_cons (step508 p h) (sat_cons (step415 p h) (sat_cons (step416 p h) (sat_cons (step1157 p h) (sat_nil p)))))
def c1210 : List Lit := [(88, false), (1563, true)]
theorem step1210 (p : Nat → Bool) (h : Constraints p) : clause p c1210 = true :=
  Snake9.LocalRup.prove_clause [c509, c1207, c985, c980, c1209, c977, c978, c979, c982, c984, c975, c995, c417, c1205, c422, c946, c410, c944] c1210 (by decide) p (sat_cons (step509 p h) (sat_cons (step1207 p h) (sat_cons (step985 p h) (sat_cons (step980 p h) (sat_cons (step1209 p h) (sat_cons (step977 p h) (sat_cons (step978 p h) (sat_cons (step979 p h) (sat_cons (step982 p h) (sat_cons (step984 p h) (sat_cons (step975 p h) (sat_cons (step995 p h) (sat_cons (step417 p h) (sat_cons (step1205 p h) (sat_cons (step422 p h) (sat_cons (step946 p h) (sat_cons (step410 p h) (sat_cons (step944 p h) (sat_nil p)))))))))))))))))))
def c1211 : List Lit := [(1549, false), (1563, true)]
theorem step1211 (p : Nat → Bool) (h : Constraints p) : clause p c1211 = true :=
  Snake9.LocalRup.prove_clause [c507, c1207, c984, c988, c995, c972, c961, c971, c1202, c958, c403, c952, c1200, c396] c1211 (by decide) p (sat_cons (step507 p h) (sat_cons (step1207 p h) (sat_cons (step984 p h) (sat_cons (step988 p h) (sat_cons (step995 p h) (sat_cons (step972 p h) (sat_cons (step961 p h) (sat_cons (step971 p h) (sat_cons (step1202 p h) (sat_cons (step958 p h) (sat_cons (step403 p h) (sat_cons (step952 p h) (sat_cons (step1200 p h) (sat_cons (step396 p h) (sat_nil p)))))))))))))))
def c1212 : List Lit := [(17, true), (1549, true)]
theorem step1212 (p : Nat → Bool) (h : Constraints p) : clause p c1212 = true :=
  Snake9.LocalRup.prove_clause [c508, c509, c979, c977, c416, c981, c975, c976, c423, c424, c406] c1212 (by decide) p (sat_cons (step508 p h) (sat_cons (step509 p h) (sat_cons (step979 p h) (sat_cons (step977 p h) (sat_cons (step416 p h) (sat_cons (step981 p h) (sat_cons (step975 p h) (sat_cons (step976 p h) (sat_cons (step423 p h) (sat_cons (step424 p h) (sat_cons (step406 p h) (sat_nil p))))))))))))
def c1213 : List Lit := [(20, false), (1549, true), (1419, true)]
theorem step1213 (p : Nat → Bool) (h : Constraints p) : clause p c1213 = true :=
  Snake9.LocalRup.prove_clause [c1212, c979, c976, c92, c87, c719, c713, c722, c735] c1213 (by decide) p (sat_cons (step1212 p h) (sat_cons (step979 p h) (sat_cons (step976 p h) (sat_cons (step92 p h) (sat_cons (step87 p h) (sat_cons (step719 p h) (sat_cons (step713 p h) (sat_cons (step722 p h) (sat_cons (step735 p h) (sat_nil p))))))))))
def c1214 : List Lit := [(1549, true), (1419, true)]
theorem step1214 (p : Nat → Bool) (h : Constraints p) : clause p c1214 = true :=
  Snake9.LocalRup.prove_clause [c739, c979, c976, c1212, c1213, c709, c711, c714, c735, c89, c722, c719] c1214 (by decide) p (sat_cons (step739 p h) (sat_cons (step979 p h) (sat_cons (step976 p h) (sat_cons (step1212 p h) (sat_cons (step1213 p h) (sat_cons (step709 p h) (sat_cons (step711 p h) (sat_cons (step714 p h) (sat_cons (step735 p h) (sat_cons (step89 p h) (sat_cons (step722 p h) (sat_cons (step719 p h) (sat_nil p)))))))))))))
def c1215 : List Lit := [(1608, true)]
theorem step1215 (p : Nat → Bool) (h : Constraints p) : clause p c1215 = true :=
  Snake9.LocalRup.prove_clause [c518, c1053, c1055, c1050, c1051, c1048, c470, c475] c1215 (by decide) p (sat_cons (step518 p h) (sat_cons (step1053 p h) (sat_cons (step1055 p h) (sat_cons (step1050 p h) (sat_cons (step1051 p h) (sat_cons (step1048 p h) (sat_cons (step470 p h) (sat_cons (step475 p h) (sat_nil p)))))))))
def c1216 : List Lit := [(1612, true)]
theorem step1216 (p : Nat → Bool) (h : Constraints p) : clause p c1216 = true :=
  Snake9.LocalRup.prove_clause [c1215, c1058] c1216 (by decide) p (sat_cons (step1215 p h) (sat_cons (step1058 p h) (sat_nil p)))
def c1217 : List Lit := [(1620, true)]
theorem step1217 (p : Nat → Bool) (h : Constraints p) : clause p c1217 = true :=
  Snake9.LocalRup.prove_clause [c1216, c1065] c1217 (by decide) p (sat_cons (step1216 p h) (sat_cons (step1065 p h) (sat_nil p)))
def c1218 : List Lit := [(1527, false), (1566, true), (65, false), (1550, false), (59, true), (90, false)]
theorem step1218 (p : Nat → Bool) (h : Constraints p) : clause p c1218 = true :=
  Snake9.LocalRup.prove_clause [c985, c1004, c948, c964, c966, c1000, c949, c989, c943, c973, c389, c969] c1218 (by decide) p (sat_cons (step985 p h) (sat_cons (step1004 p h) (sat_cons (step948 p h) (sat_cons (step964 p h) (sat_cons (step966 p h) (sat_cons (step1000 p h) (sat_cons (step949 p h) (sat_cons (step989 p h) (sat_cons (step943 p h) (sat_cons (step973 p h) (sat_cons (step389 p h) (sat_cons (step969 p h) (sat_nil p)))))))))))))
def c1219 : List Lit := [(1527, true)]
theorem step1219 (p : Nat → Bool) (h : Constraints p) : clause p c1219 = true :=
  Snake9.LocalRup.prove_clause [c505, c504, c1202, c958, c952, c953, c1200, c398, c399, c395, c390] c1219 (by decide) p (sat_cons (step505 p h) (sat_cons (step504 p h) (sat_cons (step1202 p h) (sat_cons (step958 p h) (sat_cons (step952 p h) (sat_cons (step953 p h) (sat_cons (step1200 p h) (sat_cons (step398 p h) (sat_cons (step399 p h) (sat_cons (step395 p h) (sat_cons (step390 p h) (sat_nil p))))))))))))
def c1220 : List Lit := [(1531, true)]
theorem step1220 (p : Nat → Bool) (h : Constraints p) : clause p c1220 = true :=
  Snake9.LocalRup.prove_clause [c1219, c961] c1220 (by decide) p (sat_cons (step1219 p h) (sat_cons (step961 p h) (sat_nil p)))
def c1221 : List Lit := [(90, false), (1525, true), (1538, true), (1520, true), (1585, true), (92, true)]
theorem step1221 (p : Nat → Bool) (h : Constraints p) : clause p c1221 = true :=
  Snake9.LocalRup.prove_clause [c511, c1164, c682, c1162, c499, c500, c502, c506, c504, c505, c1024, c1017, c1022, c1020, c441, c433, c432, c648, c649, c650, c659, c671, c674, c677, c680, c643, c615, c635, c610, c633, c634, c606, c631, c628, c602, c603, c630, c626, c601, c598, c600, c595, c366, c371, c374, c376, c949, c943, c383, c389, c970, c400, c402, c394, c954, c393, c398, c399, c390] c1221 (by decide) p (sat_cons (step511 p h) (sat_cons (step1164 p h) (sat_cons (step682 p h) (sat_cons (step1162 p h) (sat_cons (step499 p h) (sat_cons (step500 p h) (sat_cons (step502 p h) (sat_cons (step506 p h) (sat_cons (step504 p h) (sat_cons (step505 p h) (sat_cons (step1024 p h) (sat_cons (step1017 p h) (sat_cons (step1022 p h) (sat_cons (step1020 p h) (sat_cons (step441 p h) (sat_cons (step433 p h) (sat_cons (step432 p h) (sat_cons (step648 p h) (sat_cons (step649 p h) (sat_cons (step650 p h) (sat_cons (step659 p h) (sat_cons (step671 p h) (sat_cons (step674 p h) (sat_cons (step677 p h) (sat_cons (step680 p h) (sat_cons (step643 p h) (sat_cons (step615 p h) (sat_cons (step635 p h) (sat_cons (step610 p h) (sat_cons (step633 p h) (sat_cons (step634 p h) (sat_cons (step606 p h) (sat_cons (step631 p h) (sat_cons (step628 p h) (sat_cons (step602 p h) (sat_cons (step603 p h) (sat_cons (step630 p h) (sat_cons (step626 p h) (sat_cons (step601 p h) (sat_cons (step598 p h) (sat_cons (step600 p h) (sat_cons (step595 p h) (sat_cons (step366 p h) (sat_cons (step371 p h) (sat_cons (step374 p h) (sat_cons (step376 p h) (sat_cons (step949 p h) (sat_cons (step943 p h) (sat_cons (step383 p h) (sat_cons (step389 p h) (sat_cons (step970 p h) (sat_cons (step400 p h) (sat_cons (step402 p h) (sat_cons (step394 p h) (sat_cons (step954 p h) (sat_cons (step393 p h) (sat_cons (step398 p h) (sat_cons (step399 p h) (sat_cons (step390 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1222 : List Lit := [(33, false), (1398, true)]
theorem step1222 (p : Nat → Bool) (h : Constraints p) : clause p c1222 = true :=
  Snake9.LocalRup.prove_clause [c476, c701, c686, c683, c688, c684, c30, c699, c694, c691, c208, c2, c15] c1222 (by decide) p (sat_cons (step476 p h) (sat_cons (step701 p h) (sat_cons (step686 p h) (sat_cons (step683 p h) (sat_cons (step688 p h) (sat_cons (step684 p h) (sat_cons (step30 p h) (sat_cons (step699 p h) (sat_cons (step694 p h) (sat_cons (step691 p h) (sat_cons (step208 p h) (sat_cons (step2 p h) (sat_cons (step15 p h) (sat_nil p))))))))))))))
def c1223 : List Lit := [(1488, true), (1470, false), (1398, true)]
theorem step1223 (p : Nat → Bool) (h : Constraints p) : clause p c1223 = true :=
  Snake9.LocalRup.prove_clause [c478, c495, c1188, c844, c701, c688, c686, c683, c684, c30, c29, c7, c784, c791, c1222, c775, c778, c802, c877, c807, c779, c777, c803, c871, c792, c845, c848, c786, c787, c841, c822, c241, c1185, c819, c342, c355] c1223 (by decide) p (sat_cons (step478 p h) (sat_cons (step495 p h) (sat_cons (step1188 p h) (sat_cons (step844 p h) (sat_cons (step701 p h) (sat_cons (step688 p h) (sat_cons (step686 p h) (sat_cons (step683 p h) (sat_cons (step684 p h) (sat_cons (step30 p h) (sat_cons (step29 p h) (sat_cons (step7 p h) (sat_cons (step784 p h) (sat_cons (step791 p h) (sat_cons (step1222 p h) (sat_cons (step775 p h) (sat_cons (step778 p h) (sat_cons (step802 p h) (sat_cons (step877 p h) (sat_cons (step807 p h) (sat_cons (step779 p h) (sat_cons (step777 p h) (sat_cons (step803 p h) (sat_cons (step871 p h) (sat_cons (step792 p h) (sat_cons (step845 p h) (sat_cons (step848 p h) (sat_cons (step786 p h) (sat_cons (step787 p h) (sat_cons (step841 p h) (sat_cons (step822 p h) (sat_cons (step241 p h) (sat_cons (step1185 p h) (sat_cons (step819 p h) (sat_cons (step342 p h) (sat_cons (step355 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))
end B112E088
