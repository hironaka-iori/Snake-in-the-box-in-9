import B112E120Part0004
namespace B112E120
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1158 : List Lit := [(1490, false), (1498, true)]
theorem step1158 (p : Nat → Bool) (h : Constraints p) : clause p c1158 = true :=
  Snake9.LocalRup.prove_clause [c887, c580] c1158 (by decide) p (sat_cons (step887 p h) (sat_cons (step580 p h) (sat_nil p)))
def c1159 : List Lit := [(1491, false), (1499, true)]
theorem step1159 (p : Nat → Bool) (h : Constraints p) : clause p c1159 = true :=
  Snake9.LocalRup.prove_clause [c887, c581] c1159 (by decide) p (sat_cons (step887 p h) (sat_cons (step581 p h) (sat_nil p)))
def c1160 : List Lit := [(1469, false), (1497, true)]
theorem step1160 (p : Nat → Bool) (h : Constraints p) : clause p c1160 = true :=
  Snake9.LocalRup.prove_clause [c885, c582] c1160 (by decide) p (sat_cons (step885 p h) (sat_cons (step582 p h) (sat_nil p)))
def c1161 : List Lit := [(1470, false), (1498, true)]
theorem step1161 (p : Nat → Bool) (h : Constraints p) : clause p c1161 = true :=
  Snake9.LocalRup.prove_clause [c885, c585] c1161 (by decide) p (sat_cons (step885 p h) (sat_cons (step585 p h) (sat_nil p)))
def c1162 : List Lit := [(1471, false), (1499, true)]
theorem step1162 (p : Nat → Bool) (h : Constraints p) : clause p c1162 = true :=
  Snake9.LocalRup.prove_clause [c885, c589] c1162 (by decide) p (sat_cons (step885 p h) (sat_cons (step589 p h) (sat_nil p)))
def c1163 : List Lit := [(1514, true), (1497, false)]
theorem step1163 (p : Nat → Bool) (h : Constraints p) : clause p c1163 = true :=
  Snake9.LocalRup.prove_clause [c966, c597] c1163 (by decide) p (sat_cons (step966 p h) (sat_cons (step597 p h) (sat_nil p)))
def c1164 : List Lit := [(1515, true), (1498, false)]
theorem step1164 (p : Nat → Bool) (h : Constraints p) : clause p c1164 = true :=
  Snake9.LocalRup.prove_clause [c966, c598] c1164 (by decide) p (sat_cons (step966 p h) (sat_cons (step598 p h) (sat_nil p)))
def c1165 : List Lit := [(1499, false), (1516, true)]
theorem step1165 (p : Nat → Bool) (h : Constraints p) : clause p c1165 = true :=
  Snake9.LocalRup.prove_clause [c966, c599] c1165 (by decide) p (sat_cons (step966 p h) (sat_cons (step599 p h) (sat_nil p)))
def c1166 : List Lit := [(1500, false), (1517, true)]
theorem step1166 (p : Nat → Bool) (h : Constraints p) : clause p c1166 = true :=
  Snake9.LocalRup.prove_clause [c966, c600] c1166 (by decide) p (sat_cons (step966 p h) (sat_cons (step600 p h) (sat_nil p)))
def c1167 : List Lit := [(1444, false), (1514, true)]
theorem step1167 (p : Nat → Bool) (h : Constraints p) : clause p c1167 = true :=
  Snake9.LocalRup.prove_clause [c888, c601] c1167 (by decide) p (sat_cons (step888 p h) (sat_cons (step601 p h) (sat_nil p)))
def c1168 : List Lit := [(1569, true), (1541, false)]
theorem step1168 (p : Nat → Bool) (h : Constraints p) : clause p c1168 = true :=
  Snake9.LocalRup.prove_clause [c1040, c686] c1168 (by decide) p (sat_cons (step1040 p h) (sat_cons (step686 p h) (sat_nil p)))
def c1169 : List Lit := [(1595, false), (1627, true)]
theorem step1169 (p : Nat → Bool) (h : Constraints p) : clause p c1169 = true :=
  Snake9.LocalRup.prove_clause [c983, c783] c1169 (by decide) p (sat_cons (step983 p h) (sat_cons (step783 p h) (sat_nil p)))
def c1170 : List Lit := [(1596, false), (1628, true)]
theorem step1170 (p : Nat → Bool) (h : Constraints p) : clause p c1170 = true :=
  Snake9.LocalRup.prove_clause [c983, c787] c1170 (by decide) p (sat_cons (step983 p h) (sat_cons (step787 p h) (sat_nil p)))
def c1171 : List Lit := [(1597, false), (1629, true)]
theorem step1171 (p : Nat → Bool) (h : Constraints p) : clause p c1171 = true :=
  Snake9.LocalRup.prove_clause [c983, c790] c1171 (by decide) p (sat_cons (step983 p h) (sat_cons (step790 p h) (sat_nil p)))
def c1172 : List Lit := [(1628, false), (1646, true)]
theorem step1172 (p : Nat → Bool) (h : Constraints p) : clause p c1172 = true :=
  Snake9.LocalRup.prove_clause [c893, c792] c1172 (by decide) p (sat_cons (step893 p h) (sat_cons (step792 p h) (sat_nil p)))
def c1173 : List Lit := [(1629, false), (1647, true)]
theorem step1173 (p : Nat → Bool) (h : Constraints p) : clause p c1173 = true :=
  Snake9.LocalRup.prove_clause [c893, c793] c1173 (by decide) p (sat_cons (step893 p h) (sat_cons (step793 p h) (sat_nil p)))
def c1174 : List Lit := [(1630, false), (1648, true)]
theorem step1174 (p : Nat → Bool) (h : Constraints p) : clause p c1174 = true :=
  Snake9.LocalRup.prove_clause [c893, c794] c1174 (by decide) p (sat_cons (step893 p h) (sat_cons (step794 p h) (sat_nil p)))
def c1175 : List Lit := [(1647, true), (1571, false)]
theorem step1175 (p : Nat → Bool) (h : Constraints p) : clause p c1175 = true :=
  Snake9.LocalRup.prove_clause [c1031, c803] c1175 (by decide) p (sat_cons (step1031 p h) (sat_cons (step803 p h) (sat_nil p)))
def c1176 : List Lit := [(1571, false), (1629, false)]
theorem step1176 (p : Nat → Bool) (h : Constraints p) : clause p c1176 = true :=
  Snake9.LocalRup.prove_clause [c910, c806] c1176 (by decide) p (sat_cons (step910 p h) (sat_cons (step806 p h) (sat_nil p)))
def c1177 : List Lit := [(1572, false), (1628, false)]
theorem step1177 (p : Nat → Bool) (h : Constraints p) : clause p c1177 = true :=
  Snake9.LocalRup.prove_clause [c910, c810] c1177 (by decide) p (sat_cons (step910 p h) (sat_cons (step810 p h) (sat_nil p)))
def c1178 : List Lit := [(1573, false), (1649, true)]
theorem step1178 (p : Nat → Bool) (h : Constraints p) : clause p c1178 = true :=
  Snake9.LocalRup.prove_clause [c1031, c812] c1178 (by decide) p (sat_cons (step1031 p h) (sat_cons (step812 p h) (sat_nil p)))
def c1179 : List Lit := [(1514, false), (1649, false)]
theorem step1179 (p : Nat → Bool) (h : Constraints p) : clause p c1179 = true :=
  Snake9.LocalRup.prove_clause [c821, c817] c1179 (by decide) p (sat_cons (step821 p h) (sat_cons (step817 p h) (sat_nil p)))
def c1180 : List Lit := [(1515, false), (1648, false)]
theorem step1180 (p : Nat → Bool) (h : Constraints p) : clause p c1180 = true :=
  Snake9.LocalRup.prove_clause [c821, c818] c1180 (by decide) p (sat_cons (step821 p h) (sat_cons (step818 p h) (sat_nil p)))
def c1181 : List Lit := [(1516, false), (1647, false)]
theorem step1181 (p : Nat → Bool) (h : Constraints p) : clause p c1181 = true :=
  Snake9.LocalRup.prove_clause [c821, c819] c1181 (by decide) p (sat_cons (step821 p h) (sat_cons (step819 p h) (sat_nil p)))
def c1182 : List Lit := [(1517, false), (1646, false)]
theorem step1182 (p : Nat → Bool) (h : Constraints p) : clause p c1182 = true :=
  Snake9.LocalRup.prove_clause [c821, c820] c1182 (by decide) p (sat_cons (step821 p h) (sat_cons (step820 p h) (sat_nil p)))
def c1183 : List Lit := [(1401, true), (25, false)]
theorem step1183 (p : Nat → Bool) (h : Constraints p) : clause p c1183 = true :=
  Snake9.LocalRup.prove_clause [c468, c469, c1088, c11] c1183 (by decide) p (sat_cons (step468 p h) (sat_cons (step469 p h) (sat_cons (step1088 p h) (sat_cons (step11 p h) (sat_nil p)))))
def c1184 : List Lit := [(1591, false), (1628, true)]
theorem step1184 (p : Nat → Bool) (h : Constraints p) : clause p c1184 = true :=
  Snake9.LocalRup.prove_clause [c1170, c725, c730, c784, c704, c1019, c701] c1184 (by decide) p (sat_cons (step1170 p h) (sat_cons (step725 p h) (sat_cons (step730 p h) (sat_cons (step784 p h) (sat_cons (step704 p h) (sat_cons (step1019 p h) (sat_cons (step701 p h) (sat_nil p))))))))
def c1185 : List Lit := [(1428, true), (32, false), (78, false), (1517, true), (1430, false), (1445, true), (14, false), (12, false), (1411, false), (81, false)]
theorem step1185 (p : Nat → Bool) (h : Constraints p) : clause p c1185 = true :=
  Snake9.LocalRup.prove_clause [c482, c495, c496, c20, c52, c53, c487, c525, c489, c530, c508, c523, c520, c485, c604, c470, c1162, c469, c546, c1087, c903, c1086, c1074] c1185 (by decide) p (sat_cons (step482 p h) (sat_cons (step495 p h) (sat_cons (step496 p h) (sat_cons (step20 p h) (sat_cons (step52 p h) (sat_cons (step53 p h) (sat_cons (step487 p h) (sat_cons (step525 p h) (sat_cons (step489 p h) (sat_cons (step530 p h) (sat_cons (step508 p h) (sat_cons (step523 p h) (sat_cons (step520 p h) (sat_cons (step485 p h) (sat_cons (step604 p h) (sat_cons (step470 p h) (sat_cons (step1162 p h) (sat_cons (step469 p h) (sat_cons (step546 p h) (sat_cons (step1087 p h) (sat_cons (step903 p h) (sat_cons (step1086 p h) (sat_cons (step1074 p h) (sat_nil p))))))))))))))))))))))))
def c1186 : List Lit := [(32, false), (78, false), (1517, true), (1426, false), (1445, true), (14, false), (12, false), (1411, false), (81, false)]
theorem step1186 (p : Nat → Bool) (h : Constraints p) : clause p c1186 = true :=
  Snake9.LocalRup.prove_clause [c482, c521, c506, c501, c499, c1185, c500, c505, c509, c523, c520, c489, c485, c604, c487, c470, c1162, c20, c469, c497, c1087, c52, c53, c1086, c525, c1074, c530, c903, c546] c1186 (by decide) p (sat_cons (step482 p h) (sat_cons (step521 p h) (sat_cons (step506 p h) (sat_cons (step501 p h) (sat_cons (step499 p h) (sat_cons (step1185 p h) (sat_cons (step500 p h) (sat_cons (step505 p h) (sat_cons (step509 p h) (sat_cons (step523 p h) (sat_cons (step520 p h) (sat_cons (step489 p h) (sat_cons (step485 p h) (sat_cons (step604 p h) (sat_cons (step487 p h) (sat_cons (step470 p h) (sat_cons (step1162 p h) (sat_cons (step20 p h) (sat_cons (step469 p h) (sat_cons (step497 p h) (sat_cons (step1087 p h) (sat_cons (step52 p h) (sat_cons (step53 p h) (sat_cons (step1086 p h) (sat_cons (step525 p h) (sat_cons (step1074 p h) (sat_cons (step530 p h) (sat_cons (step903 p h) (sat_cons (step546 p h) (sat_nil p))))))))))))))))))))))))))))))
def c1187 : List Lit := [(16, true), (1426, false), (1436, true), (12, false), (81, false)]
theorem step1187 (p : Nat → Bool) (h : Constraints p) : clause p c1187 = true :=
  Snake9.LocalRup.prove_clause [c499, c512, c490, c491, c509, c487, c500, c20, c495] c1187 (by decide) p (sat_cons (step499 p h) (sat_cons (step512 p h) (sat_cons (step490 p h) (sat_cons (step491 p h) (sat_cons (step509 p h) (sat_cons (step487 p h) (sat_cons (step500 p h) (sat_cons (step20 p h) (sat_cons (step495 p h) (sat_nil p))))))))))
def c1188 : List Lit := [(1489, true), (49, true), (1649, true), (1556, true), (77, true)]
theorem step1188 (p : Nat → Bool) (h : Constraints p) : clause p c1188 = true :=
  Snake9.LocalRup.prove_clause [c986, c988, c1072, c987, c876, c1029] c1188 (by decide) p (sat_cons (step986 p h) (sat_cons (step988 p h) (sat_cons (step1072 p h) (sat_cons (step987 p h) (sat_cons (step876 p h) (sat_cons (step1029 p h) (sat_nil p)))))))
def c1189 : List Lit := [(1556, true), (77, false), (1517, true), (24, false), (1426, false), (1445, true), (1408, true), (12, false), (1411, false), (1553, false), (81, false)]
theorem step1189 (p : Nat → Bool) (h : Constraints p) : clause p c1189 = true :=
  Snake9.LocalRup.prove_clause [c474, c473, c482, c521, c1187, c21, c655, c984, c657, c649, c1009, c1186, c902, c1092, c195, c191, c197, c196, c653, c548, c739, c31, c210, c1096, c1095, c220, c221, c215, c37, c713, c742, c1058, c711, c748, c1158, c721, c1164, c730, c1180, c1174, c791, c789, c731, c773, c771, c722, c749, c758, c714, c744, c755, c1137, c297] c1189 (by decide) p (sat_cons (step474 p h) (sat_cons (step473 p h) (sat_cons (step482 p h) (sat_cons (step521 p h) (sat_cons (step1187 p h) (sat_cons (step21 p h) (sat_cons (step655 p h) (sat_cons (step984 p h) (sat_cons (step657 p h) (sat_cons (step649 p h) (sat_cons (step1009 p h) (sat_cons (step1186 p h) (sat_cons (step902 p h) (sat_cons (step1092 p h) (sat_cons (step195 p h) (sat_cons (step191 p h) (sat_cons (step197 p h) (sat_cons (step196 p h) (sat_cons (step653 p h) (sat_cons (step548 p h) (sat_cons (step739 p h) (sat_cons (step31 p h) (sat_cons (step210 p h) (sat_cons (step1096 p h) (sat_cons (step1095 p h) (sat_cons (step220 p h) (sat_cons (step221 p h) (sat_cons (step215 p h) (sat_cons (step37 p h) (sat_cons (step713 p h) (sat_cons (step742 p h) (sat_cons (step1058 p h) (sat_cons (step711 p h) (sat_cons (step748 p h) (sat_cons (step1158 p h) (sat_cons (step721 p h) (sat_cons (step1164 p h) (sat_cons (step730 p h) (sat_cons (step1180 p h) (sat_cons (step1174 p h) (sat_cons (step791 p h) (sat_cons (step789 p h) (sat_cons (step731 p h) (sat_cons (step773 p h) (sat_cons (step771 p h) (sat_cons (step722 p h) (sat_cons (step749 p h) (sat_cons (step758 p h) (sat_cons (step714 p h) (sat_cons (step744 p h) (sat_cons (step755 p h) (sat_cons (step1137 p h) (sat_cons (step297 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1190 : List Lit := [(86, false), (1588, true), (1603, true), (16, false), (79, true), (15, false), (13, true)]
theorem step1190 (p : Nat → Bool) (h : Constraints p) : clause p c1190 = true :=
  Snake9.LocalRup.prove_clause [c31, c1096, c220, c221, c714, c744, c1137, c1138, c837] c1190 (by decide) p (sat_cons (step31 p h) (sat_cons (step1096 p h) (sat_cons (step220 p h) (sat_cons (step221 p h) (sat_cons (step714 p h) (sat_cons (step744 p h) (sat_cons (step1137 p h) (sat_cons (step1138 p h) (sat_cons (step837 p h) (sat_nil p))))))))))
def c1191 : List Lit := [(104, true), (86, true), (1618, true), (223, true), (103, true)]
theorem step1191 (p : Nat → Bool) (h : Constraints p) : clause p c1191 = true :=
  Snake9.LocalRup.prove_clause [c739, c773, c749, c743, c744, c303, c748, c751, c1141, c771, c741, c289, c760, c753] c1191 (by decide) p (sat_cons (step739 p h) (sat_cons (step773 p h) (sat_cons (step749 p h) (sat_cons (step743 p h) (sat_cons (step744 p h) (sat_cons (step303 p h) (sat_cons (step748 p h) (sat_cons (step751 p h) (sat_cons (step1141 p h) (sat_cons (step771 p h) (sat_cons (step741 p h) (sat_cons (step289 p h) (sat_cons (step760 p h) (sat_cons (step753 p h) (sat_nil p)))))))))))))))
def c1192 : List Lit := [(100, false), (104, false), (79, true), (78, false)]
theorem step1192 (p : Nat → Bool) (h : Constraints p) : clause p c1192 = true :=
  Snake9.LocalRup.prove_clause [c1138, c283] c1192 (by decide) p (sat_cons (step1138 p h) (sat_cons (step283 p h) (sat_nil p)))
def c1193 : List Lit := [(1602, false), (101, false), (106, false), (1618, true), (103, true)]
theorem step1193 (p : Nat → Bool) (h : Constraints p) : clause p c1193 = true :=
  Snake9.LocalRup.prove_clause [c773, c739, c748, c751, c771, c741, c760, c289, c753] c1193 (by decide) p (sat_cons (step773 p h) (sat_cons (step739 p h) (sat_cons (step748 p h) (sat_cons (step751 p h) (sat_cons (step771 p h) (sat_cons (step741 p h) (sat_cons (step760 p h) (sat_cons (step289 p h) (sat_cons (step753 p h) (sat_nil p))))))))))
def c1194 : List Lit := [(1498, true), (1628, false), (1617, false)]
theorem step1194 (p : Nat → Bool) (h : Constraints p) : clause p c1194 = true :=
  Snake9.LocalRup.prove_clause [c1044, c1063] c1194 (by decide) p (sat_cons (step1044 p h) (sat_cons (step1063 p h) (sat_nil p)))
def c1195 : List Lit := [(90, true), (1581, true), (79, true), (1608, true)]
theorem step1195 (p : Nat → Bool) (h : Constraints p) : clause p c1195 = true :=
  Snake9.LocalRup.prove_clause [c753, c752, c1126, c703, c1129, c314] c1195 (by decide) p (sat_cons (step753 p h) (sat_cons (step752 p h) (sat_cons (step1126 p h) (sat_cons (step703 p h) (sat_cons (step1129 p h) (sat_cons (step314 p h) (sat_nil p)))))))
def c1196 : List Lit := [(91, true), (90, false), (1583, true), (78, false)]
theorem step1196 (p : Nat → Bool) (h : Constraints p) : clause p c1196 = true :=
  Snake9.LocalRup.prove_clause [c705, c702, c703, c707, c241] c1196 (by decide) p (sat_cons (step705 p h) (sat_cons (step702 p h) (sat_cons (step703 p h) (sat_cons (step707 p h) (sat_cons (step241 p h) (sat_nil p))))))
def c1197 : List Lit := [(90, false), (1583, true), (78, false)]
theorem step1197 (p : Nat → Bool) (h : Constraints p) : clause p c1197 = true :=
  Snake9.LocalRup.prove_clause [c1196, c243, c240, c701, c707] c1197 (by decide) p (sat_cons (step1196 p h) (sat_cons (step243 p h) (sat_cons (step240 p h) (sat_cons (step701 p h) (sat_cons (step707 p h) (sat_nil p))))))
def c1198 : List Lit := [(1583, true), (78, false), (79, true), (1608, true)]
theorem step1198 (p : Nat → Bool) (h : Constraints p) : clause p c1198 = true :=
  Snake9.LocalRup.prove_clause [c705, c1195, c1197] c1198 (by decide) p (sat_cons (step705 p h) (sat_cons (step1195 p h) (sat_cons (step1197 p h) (sat_nil p))))
def c1199 : List Lit := [(78, true), (77, false), (1557, true), (80, false), (86, true)]
theorem step1199 (p : Nat → Bool) (h : Constraints p) : clause p c1199 = true :=
  Snake9.LocalRup.prove_clause [c651, c660, c649, c650, c658, c183, c653] c1199 (by decide) p (sat_cons (step651 p h) (sat_cons (step660 p h) (sat_cons (step649 p h) (sat_cons (step650 p h) (sat_cons (step658 p h) (sat_cons (step183 p h) (sat_cons (step653 p h) (sat_nil p))))))))
def c1200 : List Lit := [(1595, true), (1587, false), (1608, true), (78, false)]
theorem step1200 (p : Nat → Bool) (h : Constraints p) : clause p c1200 = true :=
  Snake9.LocalRup.prove_clause [c715, c753, c752, c982, c733, c314, c1197, c1129] c1200 (by decide) p (sat_cons (step715 p h) (sat_cons (step753 p h) (sat_cons (step752 p h) (sat_cons (step982 p h) (sat_cons (step733 p h) (sat_cons (step314 p h) (sat_cons (step1197 p h) (sat_cons (step1129 p h) (sat_nil p)))))))))
def c1201 : List Lit := [(92, false), (90, true), (1608, true)]
theorem step1201 (p : Nat → Bool) (h : Constraints p) : clause p c1201 = true :=
  Snake9.LocalRup.prove_clause [c753, c752, c314, c1129] c1201 (by decide) p (sat_cons (step753 p h) (sat_cons (step752 p h) (sat_cons (step314 p h) (sat_cons (step1129 p h) (sat_nil p)))))
def c1202 : List Lit := [(91, false), (1498, false), (1628, false), (79, false), (78, false)]
theorem step1202 (p : Nat → Bool) (h : Constraints p) : clause p c1202 = true :=
  Snake9.LocalRup.prove_clause [c1164, c1180, c800, c153, c169, c174, c861, c640, c648, c911, c656, c657, c1064, c1065, c796, c603, c1181] c1202 (by decide) p (sat_cons (step1164 p h) (sat_cons (step1180 p h) (sat_cons (step800 p h) (sat_cons (step153 p h) (sat_cons (step169 p h) (sat_cons (step174 p h) (sat_cons (step861 p h) (sat_cons (step640 p h) (sat_cons (step648 p h) (sat_cons (step911 p h) (sat_cons (step656 p h) (sat_cons (step657 p h) (sat_cons (step1064 p h) (sat_cons (step1065 p h) (sat_cons (step796 p h) (sat_cons (step603 p h) (sat_cons (step1181 p h) (sat_nil p))))))))))))))))))
def c1203 : List Lit := [(1553, true), (93, true), (95, false), (96, false)]
theorem step1203 (p : Nat → Bool) (h : Constraints p) : clause p c1203 = true :=
  Snake9.LocalRup.prove_clause [c651, c652, c281, c227, c1134] c1203 (by decide) p (sat_cons (step651 p h) (sat_cons (step652 p h) (sat_cons (step281 p h) (sat_cons (step227 p h) (sat_cons (step1134 p h) (sat_nil p))))))
def c1204 : List Lit := [(81, false), (1553, false), (94, false), (95, false), (1444, true), (1570, true), (1445, true), (79, false), (78, false)]
theorem step1204 (p : Nat → Bool) (h : Constraints p) : clause p c1204 = true :=
  Snake9.LocalRup.prove_clause [c1154, c483, c152, c1082, c861, c473, c474, c479, c482, c485, c520, c470, c505, c1183, c502, c494, c37, c36, c1099] c1204 (by decide) p (sat_cons (step1154 p h) (sat_cons (step483 p h) (sat_cons (step152 p h) (sat_cons (step1082 p h) (sat_cons (step861 p h) (sat_cons (step473 p h) (sat_cons (step474 p h) (sat_cons (step479 p h) (sat_cons (step482 p h) (sat_cons (step485 p h) (sat_cons (step520 p h) (sat_cons (step470 p h) (sat_cons (step505 p h) (sat_cons (step1183 p h) (sat_cons (step502 p h) (sat_cons (step494 p h) (sat_cons (step37 p h) (sat_cons (step36 p h) (sat_cons (step1099 p h) (sat_nil p))))))))))))))))))))
def c1205 : List Lit := [(1569, false), (1581, false), (1628, false), (1617, false), (100, true), (79, false), (78, false)]
theorem step1205 (p : Nat → Bool) (h : Constraints p) : clause p c1205 = true :=
  Snake9.LocalRup.prove_clause [c705, c1194, c1164, c1180, c800, c1172, c1182, c606, c712, c715, c796, c797, c1181, c788, c603, c737, c734, c1154, c708, c716, c718, c483, c714, c709, c710, c266, c1203, c1204, c648, c657, c911, c640, c148, c861, c479, c480, c482, c485, c473, c474, c520, c470, c505, c1183, c502, c494, c37, c36, c1099] c1205 (by decide) p (sat_cons (step705 p h) (sat_cons (step1194 p h) (sat_cons (step1164 p h) (sat_cons (step1180 p h) (sat_cons (step800 p h) (sat_cons (step1172 p h) (sat_cons (step1182 p h) (sat_cons (step606 p h) (sat_cons (step712 p h) (sat_cons (step715 p h) (sat_cons (step796 p h) (sat_cons (step797 p h) (sat_cons (step1181 p h) (sat_cons (step788 p h) (sat_cons (step603 p h) (sat_cons (step737 p h) (sat_cons (step734 p h) (sat_cons (step1154 p h) (sat_cons (step708 p h) (sat_cons (step716 p h) (sat_cons (step718 p h) (sat_cons (step483 p h) (sat_cons (step714 p h) (sat_cons (step709 p h) (sat_cons (step710 p h) (sat_cons (step266 p h) (sat_cons (step1203 p h) (sat_cons (step1204 p h) (sat_cons (step648 p h) (sat_cons (step657 p h) (sat_cons (step911 p h) (sat_cons (step640 p h) (sat_cons (step148 p h) (sat_cons (step861 p h) (sat_cons (step479 p h) (sat_cons (step480 p h) (sat_cons (step482 p h) (sat_cons (step485 p h) (sat_cons (step473 p h) (sat_cons (step474 p h) (sat_cons (step520 p h) (sat_cons (step470 p h) (sat_cons (step505 p h) (sat_cons (step1183 p h) (sat_cons (step502 p h) (sat_cons (step494 p h) (sat_cons (step37 p h) (sat_cons (step36 p h) (sat_cons (step1099 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))
def c1206 : List Lit := [(1556, false), (1569, true), (1570, true)]
theorem step1206 (p : Nat → Bool) (h : Constraints p) : clause p c1206 = true :=
  Snake9.LocalRup.prove_clause [c881, c663, c911, c668, c682, c641, c645, c878, c1118, c136, c619, c616] c1206 (by decide) p (sat_cons (step881 p h) (sat_cons (step663 p h) (sat_cons (step911 p h) (sat_cons (step668 p h) (sat_cons (step682 p h) (sat_cons (step641 p h) (sat_cons (step645 p h) (sat_cons (step878 p h) (sat_cons (step1118 p h) (sat_cons (step136 p h) (sat_cons (step619 p h) (sat_cons (step616 p h) (sat_nil p)))))))))))))
def c1207 : List Lit := [(1553, false), (1556, true), (1569, true), (79, false)]
theorem step1207 (p : Nat → Bool) (h : Constraints p) : clause p c1207 = true :=
  Snake9.LocalRup.prove_clause [c654, c657, c1064, c1009] c1207 (by decide) p (sat_cons (step654 p h) (sat_cons (step657 p h) (sat_cons (step1064 p h) (sat_cons (step1009 p h) (sat_nil p)))))
def c1208 : List Lit := [(1596, true), (1553, true), (1581, false), (100, true)]
theorem step1208 (p : Nat → Bool) (h : Constraints p) : clause p c1208 = true :=
  Snake9.LocalRup.prove_clause [c705, c712, c715, c737, c734, c708, c716, c718, c714, c709, c266, c1203] c1208 (by decide) p (sat_cons (step705 p h) (sat_cons (step712 p h) (sat_cons (step715 p h) (sat_cons (step737 p h) (sat_cons (step734 p h) (sat_cons (step708 p h) (sat_cons (step716 p h) (sat_cons (step718 p h) (sat_cons (step714 p h) (sat_cons (step709 p h) (sat_cons (step266 p h) (sat_cons (step1203 p h) (sat_nil p)))))))))))))
def c1209 : List Lit := [(1581, false), (1628, false), (1617, false), (100, true), (79, false), (78, false)]
theorem step1209 (p : Nat → Bool) (h : Constraints p) : clause p c1209 = true :=
  Snake9.LocalRup.prove_clause [c1194, c1164, c1180, c800, c1205, c1206, c1207, c1208, c788, c1173, c1181, c603, c1069, c1065, c648, c861, c656, c148, c1064] c1209 (by decide) p (sat_cons (step1194 p h) (sat_cons (step1164 p h) (sat_cons (step1180 p h) (sat_cons (step800 p h) (sat_cons (step1205 p h) (sat_cons (step1206 p h) (sat_cons (step1207 p h) (sat_cons (step1208 p h) (sat_cons (step788 p h) (sat_cons (step1173 p h) (sat_cons (step1181 p h) (sat_cons (step603 p h) (sat_cons (step1069 p h) (sat_cons (step1065 p h) (sat_cons (step648 p h) (sat_cons (step861 p h) (sat_cons (step656 p h) (sat_cons (step148 p h) (sat_cons (step1064 p h) (sat_nil p))))))))))))))))))))
def c1210 : List Lit := [(1617, false), (100, true), (1608, true), (79, false), (78, false)]
theorem step1210 (p : Nat → Bool) (h : Constraints p) : clause p c1210 = true :=
  Snake9.LocalRup.prove_clause [c712, c1200, c753, c752, c784, c1194, c1164, c1180, c1174, c800, c791, c1202, c1209, c703, c314, c1201, c1128, c1197, c245, c735, c709, c718, c719, c734, c714, c788, c280, c797, c651, c1206, c1207] c1210 (by decide) p (sat_cons (step712 p h) (sat_cons (step1200 p h) (sat_cons (step753 p h) (sat_cons (step752 p h) (sat_cons (step784 p h) (sat_cons (step1194 p h) (sat_cons (step1164 p h) (sat_cons (step1180 p h) (sat_cons (step1174 p h) (sat_cons (step800 p h) (sat_cons (step791 p h) (sat_cons (step1202 p h) (sat_cons (step1209 p h) (sat_cons (step703 p h) (sat_cons (step314 p h) (sat_cons (step1201 p h) (sat_cons (step1128 p h) (sat_cons (step1197 p h) (sat_cons (step245 p h) (sat_cons (step735 p h) (sat_cons (step709 p h) (sat_cons (step718 p h) (sat_cons (step719 p h) (sat_cons (step734 p h) (sat_cons (step714 p h) (sat_cons (step788 p h) (sat_cons (step280 p h) (sat_cons (step797 p h) (sat_cons (step651 p h) (sat_cons (step1206 p h) (sat_cons (step1207 p h) (sat_nil p))))))))))))))))))))))))))))))))
def c1211 : List Lit := [(1628, false), (91, false), (79, false), (78, false)]
theorem step1211 (p : Nat → Bool) (h : Constraints p) : clause p c1211 = true :=
  Snake9.LocalRup.prove_clause [c163, c903, c542, c1202, c1044, c1047] c1211 (by decide) p (sat_cons (step163 p h) (sat_cons (step903 p h) (sat_cons (step542 p h) (sat_cons (step1202 p h) (sat_cons (step1044 p h) (sat_cons (step1047 p h) (sat_nil p)))))))
def c1212 : List Lit := [(1498, true), (1572, true), (1469, false), (1548, false), (1551, false), (86, true), (1535, false), (84, false), (106, false)]
theorem step1212 (p : Nat → Bool) (h : Constraints p) : clause p c1212 = true :=
  Snake9.LocalRup.prove_clause [c1044, c583, c986, c988, c991, c987, c224, c876, c653, c631, c658, c689, c669] c1212 (by decide) p (sat_cons (step1044 p h) (sat_cons (step583 p h) (sat_cons (step986 p h) (sat_cons (step988 p h) (sat_cons (step991 p h) (sat_cons (step987 p h) (sat_cons (step224 p h) (sat_cons (step876 p h) (sat_cons (step653 p h) (sat_cons (step631 p h) (sat_cons (step658 p h) (sat_cons (step689 p h) (sat_cons (step669 p h) (sat_nil p))))))))))))))
def c1213 : List Lit := [(91, false), (86, true), (1535, false), (84, false), (1556, false), (106, false), (1627, false), (79, false), (78, false)]
theorem step1213 (p : Nat → Bool) (h : Constraints p) : clause p c1213 = true :=
  Snake9.LocalRup.prove_clause [c153, c169, c174, c163, c861, c640, c648, c903, c479, c643, c911, c542, c482, c799, c1160, c1181, c1163, c1179, c809, c1212, c1164, c603, c1180, c1154, c520, c804, c485, c949, c470, c658, c1183, c653, c492, c219, c499, c490, c508] c1213 (by decide) p (sat_cons (step153 p h) (sat_cons (step169 p h) (sat_cons (step174 p h) (sat_cons (step163 p h) (sat_cons (step861 p h) (sat_cons (step640 p h) (sat_cons (step648 p h) (sat_cons (step903 p h) (sat_cons (step479 p h) (sat_cons (step643 p h) (sat_cons (step911 p h) (sat_cons (step542 p h) (sat_cons (step482 p h) (sat_cons (step799 p h) (sat_cons (step1160 p h) (sat_cons (step1181 p h) (sat_cons (step1163 p h) (sat_cons (step1179 p h) (sat_cons (step809 p h) (sat_cons (step1212 p h) (sat_cons (step1164 p h) (sat_cons (step603 p h) (sat_cons (step1180 p h) (sat_cons (step1154 p h) (sat_cons (step520 p h) (sat_cons (step804 p h) (sat_cons (step485 p h) (sat_cons (step949 p h) (sat_cons (step470 p h) (sat_cons (step658 p h) (sat_cons (step1183 p h) (sat_cons (step653 p h) (sat_cons (step492 p h) (sat_cons (step219 p h) (sat_cons (step499 p h) (sat_cons (step490 p h) (sat_cons (step508 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))
def c1214 : List Lit := [(1546, false), (1551, false), (1571, true), (1648, true), (1583, false), (86, true), (84, false), (1556, false), (106, false), (100, true)]
theorem step1214 (p : Nat → Bool) (h : Constraints p) : clause p c1214 = true :=
  Snake9.LocalRup.prove_clause [c911, c949, c800, c658, c1170, c653, c734, c229, c716, c714] c1214 (by decide) p (sat_cons (step911 p h) (sat_cons (step949 p h) (sat_cons (step800 p h) (sat_cons (step658 p h) (sat_cons (step1170 p h) (sat_cons (step653 p h) (sat_cons (step734 p h) (sat_cons (step229 p h) (sat_cons (step716 p h) (sat_cons (step714 p h) (sat_nil p)))))))))))
def c1215 : List Lit := [(1551, false), (1469, false), (1648, true), (1583, false), (86, true), (1535, false), (84, false), (80, false), (1556, false), (106, false), (102, false), (1595, false), (100, true), (79, false), (78, false)]
theorem step1215 (p : Nat → Bool) (h : Constraints p) : clause p c1215 = true :=
  Snake9.LocalRup.prove_clause [c1160, c1169, c804, c1213, c712, c1214, c640, c641, c158, c148, c185, c903, c861, c653, c658, c664, c950, c688, c799, c1014, c631, c1181, c716, c718, c876, c1165, c714, c584, c226, c979, c1058, c547] c1215 (by decide) p (sat_cons (step1160 p h) (sat_cons (step1169 p h) (sat_cons (step804 p h) (sat_cons (step1213 p h) (sat_cons (step712 p h) (sat_cons (step1214 p h) (sat_cons (step640 p h) (sat_cons (step641 p h) (sat_cons (step158 p h) (sat_cons (step148 p h) (sat_cons (step185 p h) (sat_cons (step903 p h) (sat_cons (step861 p h) (sat_cons (step653 p h) (sat_cons (step658 p h) (sat_cons (step664 p h) (sat_cons (step950 p h) (sat_cons (step688 p h) (sat_cons (step799 p h) (sat_cons (step1014 p h) (sat_cons (step631 p h) (sat_cons (step1181 p h) (sat_cons (step716 p h) (sat_cons (step718 p h) (sat_cons (step876 p h) (sat_cons (step1165 p h) (sat_cons (step714 p h) (sat_cons (step584 p h) (sat_cons (step226 p h) (sat_cons (step979 p h) (sat_cons (step1058 p h) (sat_cons (step547 p h) (sat_nil p)))))))))))))))))))))))))))))))))
def c1216 : List Lit := [(1469, false), (1648, true), (1583, false), (86, true), (1535, false), (84, false), (80, false), (1556, false), (106, false), (102, false), (1595, false), (100, true), (79, false), (78, false)]
theorem step1216 (p : Nat → Bool) (h : Constraints p) : clause p c1216 = true :=
  Snake9.LocalRup.prove_clause [c1169, c804, c712, c1215, c1009, c640, c1021, c911, c876, c799, c800, c1181, c1170, c1165, c734, c584, c716, c718, c979, c714, c547, c226, c1058] c1216 (by decide) p (sat_cons (step1169 p h) (sat_cons (step804 p h) (sat_cons (step712 p h) (sat_cons (step1215 p h) (sat_cons (step1009 p h) (sat_cons (step640 p h) (sat_cons (step1021 p h) (sat_cons (step911 p h) (sat_cons (step876 p h) (sat_cons (step799 p h) (sat_cons (step800 p h) (sat_cons (step1181 p h) (sat_cons (step1170 p h) (sat_cons (step1165 p h) (sat_cons (step734 p h) (sat_cons (step584 p h) (sat_cons (step716 p h) (sat_cons (step718 p h) (sat_cons (step979 p h) (sat_cons (step714 p h) (sat_cons (step547 p h) (sat_cons (step226 p h) (sat_cons (step1058 p h) (sat_nil p))))))))))))))))))))))))
def c1217 : List Lit := [(1648, true), (1583, false), (86, true), (1535, false), (84, false), (80, false), (1556, false), (106, false), (102, false), (1595, false), (100, true), (79, false), (78, false)]
theorem step1217 (p : Nat → Bool) (h : Constraints p) : clause p c1217 = true :=
  Snake9.LocalRup.prove_clause [c1169, c804, c1216, c542, c903, c162, c158, c648, c640, c1214] c1217 (by decide) p (sat_cons (step1169 p h) (sat_cons (step804 p h) (sat_cons (step1216 p h) (sat_cons (step542 p h) (sat_cons (step903 p h) (sat_cons (step162 p h) (sat_cons (step158 p h) (sat_cons (step648 p h) (sat_cons (step640 p h) (sat_cons (step1214 p h) (sat_nil p)))))))))))
def c1218 : List Lit := [(1571, true), (1561, false), (1546, false), (1551, false), (49, true), (1490, true), (86, true), (1535, false), (84, false), (106, false)]
theorem step1218 (p : Nat → Bool) (h : Constraints p) : clause p c1218 = true :=
  Snake9.LocalRup.prove_clause [c949, c688, c658, c631, c653, c876, c224, c1058, c1052, c987] c1218 (by decide) p (sat_cons (step949 p h) (sat_cons (step688 p h) (sat_cons (step658 p h) (sat_cons (step631 p h) (sat_cons (step653 p h) (sat_cons (step876 p h) (sat_cons (step224 p h) (sat_cons (step1058 p h) (sat_cons (step1052 p h) (sat_cons (step987 p h) (sat_nil p)))))))))))
def c1219 : List Lit := [(50, true), (59, false), (1498, true)]
theorem step1219 (p : Nat → Bool) (h : Constraints p) : clause p c1219 = true :=
  Snake9.LocalRup.prove_clause [c1044, c1158, c1058, c1052, c987] c1219 (by decide) p (sat_cons (step1044 p h) (sat_cons (step1158 p h) (sat_cons (step1058 p h) (sat_cons (step1052 p h) (sat_cons (step987 p h) (sat_nil p))))))
def c1220 : List Lit := [(59, false), (1591, true), (1498, true), (84, false), (106, false), (100, true)]
theorem step1220 (p : Nat → Bool) (h : Constraints p) : clause p c1220 = true :=
  Snake9.LocalRup.prove_clause [c1158, c1043, c1044, c1219, c226, c714, c719, c709, c979, c547, c549, c976, c95, c105, c1113] c1220 (by decide) p (sat_cons (step1158 p h) (sat_cons (step1043 p h) (sat_cons (step1044 p h) (sat_cons (step1219 p h) (sat_cons (step226 p h) (sat_cons (step714 p h) (sat_cons (step719 p h) (sat_cons (step709 p h) (sat_cons (step979 p h) (sat_cons (step547 p h) (sat_cons (step549 p h) (sat_cons (step976 p h) (sat_cons (step95 p h) (sat_cons (step105 p h) (sat_cons (step1113 p h) (sat_nil p))))))))))))))))
def c1221 : List Lit := [(1489, false), (1552, true), (1515, true)]
theorem step1221 (p : Nat → Bool) (h : Constraints p) : clause p c1221 = true :=
  Snake9.LocalRup.prove_clause [c1164, c1044, c1157, c583, c602, c1038] c1221 (by decide) p (sat_cons (step1164 p h) (sat_cons (step1044 p h) (sat_cons (step1157 p h) (sat_cons (step583 p h) (sat_cons (step602 p h) (sat_cons (step1038 p h) (sat_nil p)))))))
end B112E120
