import B112E120Part0003
namespace B112E120
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1094 : List Lit := [(22, true), (32, true), (14, false), (13, true)]
theorem step1094 (p : Nat → Bool) (h : Constraints p) : clause p c1094 = true :=
  Snake9.LocalRup.prove_clause [c332, c27] c1094 (by decide) p (sat_cons (step332 p h) (sat_cons (step27 p h) (sat_nil p)))
def c1095 : List Lit := [(23, true), (17, true), (15, false), (13, true), (83, true)]
theorem step1095 (p : Nat → Bool) (h : Constraints p) : clause p c1095 = true :=
  Snake9.LocalRup.prove_clause [c333, c29] c1095 (by decide) p (sat_cons (step333 p h) (sat_cons (step29 p h) (sat_nil p)))
def c1096 : List Lit := [(17, true), (84, true), (13, true), (16, false)]
theorem step1096 (p : Nat → Bool) (h : Constraints p) : clause p c1096 = true :=
  Snake9.LocalRup.prove_clause [c334, c30] c1096 (by decide) p (sat_cons (step334 p h) (sat_cons (step30 p h) (sat_nil p)))
def c1097 : List Lit := [(26, true), (21, false), (12, true)]
theorem step1097 (p : Nat → Bool) (h : Constraints p) : clause p c1097 = true :=
  Snake9.LocalRup.prove_clause [c335, c34] c1097 (by decide) p (sat_cons (step335 p h) (sat_cons (step34 p h) (sat_nil p)))
def c1098 : List Lit := [(26, true), (22, true), (24, false)]
theorem step1098 (p : Nat → Bool) (h : Constraints p) : clause p c1098 = true :=
  Snake9.LocalRup.prove_clause [c336, c40] c1098 (by decide) p (sat_cons (step336 p h) (sat_cons (step40 p h) (sat_nil p)))
def c1099 : List Lit := [(22, true), (23, true), (24, false)]
theorem step1099 (p : Nat → Bool) (h : Constraints p) : clause p c1099 = true :=
  Snake9.LocalRup.prove_clause [c336, c41] c1099 (by decide) p (sat_cons (step336 p h) (sat_cons (step41 p h) (sat_nil p)))
def c1100 : List Lit := [(34, true), (30, false), (12, true)]
theorem step1100 (p : Nat → Bool) (h : Constraints p) : clause p c1100 = true :=
  Snake9.LocalRup.prove_clause [c337, c49] c1100 (by decide) p (sat_cons (step337 p h) (sat_cons (step49 p h) (sat_nil p)))
def c1101 : List Lit := [(29, true), (30, false), (12, true)]
theorem step1101 (p : Nat → Bool) (h : Constraints p) : clause p c1101 = true :=
  Snake9.LocalRup.prove_clause [c337, c50] c1101 (by decide) p (sat_cons (step337 p h) (sat_cons (step50 p h) (sat_nil p)))
def c1102 : List Lit := [(40, false), (41, true)]
theorem step1102 (p : Nat → Bool) (h : Constraints p) : clause p c1102 = true :=
  Snake9.LocalRup.prove_clause [c340, c62] c1102 (by decide) p (sat_cons (step340 p h) (sat_cons (step62 p h) (sat_nil p)))
def c1103 : List Lit := [(79, true), (44, false), (49, true)]
theorem step1103 (p : Nat → Bool) (h : Constraints p) : clause p c1103 = true :=
  Snake9.LocalRup.prove_clause [c341, c68] c1103 (by decide) p (sat_cons (step341 p h) (sat_cons (step68 p h) (sat_nil p)))
def c1104 : List Lit := [(43, true), (79, true), (44, false)]
theorem step1104 (p : Nat → Bool) (h : Constraints p) : clause p c1104 = true :=
  Snake9.LocalRup.prove_clause [c341, c69] c1104 (by decide) p (sat_cons (step341 p h) (sat_cons (step69 p h) (sat_nil p)))
def c1105 : List Lit := [(43, true), (44, false), (49, true)]
theorem step1105 (p : Nat → Bool) (h : Constraints p) : clause p c1105 = true :=
  Snake9.LocalRup.prove_clause [c341, c70] c1105 (by decide) p (sat_cons (step341 p h) (sat_cons (step70 p h) (sat_nil p)))
def c1106 : List Lit := [(65, true), (47, false), (82, true), (49, true)]
theorem step1106 (p : Nat → Bool) (h : Constraints p) : clause p c1106 = true :=
  Snake9.LocalRup.prove_clause [c343, c74] c1106 (by decide) p (sat_cons (step343 p h) (sat_cons (step74 p h) (sat_nil p)))
def c1107 : List Lit := [(57, true), (47, false), (82, true), (49, true)]
theorem step1107 (p : Nat → Bool) (h : Constraints p) : clause p c1107 = true :=
  Snake9.LocalRup.prove_clause [c343, c75] c1107 (by decide) p (sat_cons (step343 p h) (sat_cons (step75 p h) (sat_nil p)))
def c1108 : List Lit := [(57, true), (65, true), (47, false), (49, true)]
theorem step1108 (p : Nat → Bool) (h : Constraints p) : clause p c1108 = true :=
  Snake9.LocalRup.prove_clause [c343, c76] c1108 (by decide) p (sat_cons (step343 p h) (sat_cons (step76 p h) (sat_nil p)))
def c1109 : List Lit := [(51, true), (48, false), (49, true), (83, true), (58, true)]
theorem step1109 (p : Nat → Bool) (h : Constraints p) : clause p c1109 = true :=
  Snake9.LocalRup.prove_clause [c344, c77] c1109 (by decide) p (sat_cons (step344 p h) (sat_cons (step77 p h) (sat_nil p)))
def c1110 : List Lit := [(58, true), (83, true), (43, true), (49, true), (48, false)]
theorem step1110 (p : Nat → Bool) (h : Constraints p) : clause p c1110 = true :=
  Snake9.LocalRup.prove_clause [c344, c78] c1110 (by decide) p (sat_cons (step344 p h) (sat_cons (step78 p h) (sat_nil p)))
def c1111 : List Lit := [(51, true), (50, false), (84, true)]
theorem step1111 (p : Nat → Bool) (h : Constraints p) : clause p c1111 = true :=
  Snake9.LocalRup.prove_clause [c345, c85] c1111 (by decide) p (sat_cons (step345 p h) (sat_cons (step85 p h) (sat_nil p)))
def c1112 : List Lit := [(55, false), (60, true)]
theorem step1112 (p : Nat → Bool) (h : Constraints p) : clause p c1112 = true :=
  Snake9.LocalRup.prove_clause [c347, c92] c1112 (by decide) p (sat_cons (step347 p h) (sat_cons (step92 p h) (sat_nil p)))
def c1113 : List Lit := [(57, true), (58, true), (59, false), (49, true)]
theorem step1113 (p : Nat → Bool) (h : Constraints p) : clause p c1113 = true :=
  Snake9.LocalRup.prove_clause [c348, c106] c1113 (by decide) p (sat_cons (step348 p h) (sat_cons (step106 p h) (sat_nil p)))
def c1114 : List Lit := [(68, true), (65, true), (62, false)]
theorem step1114 (p : Nat → Bool) (h : Constraints p) : clause p c1114 = true :=
  Snake9.LocalRup.prove_clause [c349, c109] c1114 (by decide) p (sat_cons (step349 p h) (sat_cons (step109 p h) (sat_nil p)))
def c1115 : List Lit := [(61, true), (64, false), (65, true)]
theorem step1115 (p : Nat → Bool) (h : Constraints p) : clause p c1115 = true :=
  Snake9.LocalRup.prove_clause [c351, c111] c1115 (by decide) p (sat_cons (step351 p h) (sat_cons (step111 p h) (sat_nil p)))
def c1116 : List Lit := [(67, false), (183, true)]
theorem step1116 (p : Nat → Bool) (h : Constraints p) : clause p c1116 = true :=
  Snake9.LocalRup.prove_clause [c845, c122] c1116 (by decide) p (sat_cons (step845 p h) (sat_cons (step122 p h) (sat_nil p)))
def c1117 : List Lit := [(70, false), (69, true)]
theorem step1117 (p : Nat → Bool) (h : Constraints p) : clause p c1117 = true :=
  Snake9.LocalRup.prove_clause [c353, c128] c1117 (by decide) p (sat_cons (step353 p h) (sat_cons (step128 p h) (sat_nil p)))
def c1118 : List Lit := [(73, false), (75, true)]
theorem step1118 (p : Nat → Bool) (h : Constraints p) : clause p c1118 = true :=
  Snake9.LocalRup.prove_clause [c355, c132] c1118 (by decide) p (sat_cons (step355 p h) (sat_cons (step132 p h) (sat_nil p)))
def c1119 : List Lit := [(89, true), (82, true), (77, false), (76, true), (79, true)]
theorem step1119 (p : Nat → Bool) (h : Constraints p) : clause p c1119 = true :=
  Snake9.LocalRup.prove_clause [c356, c141] c1119 (by decide) p (sat_cons (step356 p h) (sat_cons (step141 p h) (sat_nil p)))
def c1120 : List Lit := [(80, true), (87, true), (79, true), (81, false)]
theorem step1120 (p : Nat → Bool) (h : Constraints p) : clause p c1120 = true :=
  Snake9.LocalRup.prove_clause [c357, c187] c1120 (by decide) p (sat_cons (step357 p h) (sat_cons (step187 p h) (sat_nil p)))
def c1121 : List Lit := [(87, true), (12, true), (79, true), (81, false)]
theorem step1121 (p : Nat → Bool) (h : Constraints p) : clause p c1121 = true :=
  Snake9.LocalRup.prove_clause [c357, c189] c1121 (by decide) p (sat_cons (step357 p h) (sat_cons (step189 p h) (sat_nil p)))
def c1122 : List Lit := [(80, true), (12, true), (81, false), (79, true)]
theorem step1122 (p : Nat → Bool) (h : Constraints p) : clause p c1122 = true :=
  Snake9.LocalRup.prove_clause [c357, c190] c1122 (by decide) p (sat_cons (step357 p h) (sat_cons (step190 p h) (sat_nil p)))
def c1123 : List Lit := [(97, true), (82, true), (85, false), (84, true), (87, true)]
theorem step1123 (p : Nat → Bool) (h : Constraints p) : clause p c1123 = true :=
  Snake9.LocalRup.prove_clause [c358, c232] c1123 (by decide) p (sat_cons (step358 p h) (sat_cons (step232 p h) (sat_nil p)))
def c1124 : List Lit := [(97, true), (82, true), (85, false), (80, true), (84, true)]
theorem step1124 (p : Nat → Bool) (h : Constraints p) : clause p c1124 = true :=
  Snake9.LocalRup.prove_clause [c358, c233] c1124 (by decide) p (sat_cons (step358 p h) (sat_cons (step233 p h) (sat_nil p)))
def c1125 : List Lit := [(90, true), (91, false), (89, true)]
theorem step1125 (p : Nat → Bool) (h : Constraints p) : clause p c1125 = true :=
  Snake9.LocalRup.prove_clause [c359, c252] c1125 (by decide) p (sat_cons (step359 p h) (sat_cons (step252 p h) (sat_nil p)))
def c1126 : List Lit := [(90, true), (91, false), (79, true)]
theorem step1126 (p : Nat → Bool) (h : Constraints p) : clause p c1126 = true :=
  Snake9.LocalRup.prove_clause [c359, c253] c1126 (by decide) p (sat_cons (step359 p h) (sat_cons (step253 p h) (sat_nil p)))
def c1127 : List Lit := [(91, false), (89, true), (79, true)]
theorem step1127 (p : Nat → Bool) (h : Constraints p) : clause p c1127 = true :=
  Snake9.LocalRup.prove_clause [c359, c254] c1127 (by decide) p (sat_cons (step359 p h) (sat_cons (step254 p h) (sat_nil p)))
def c1128 : List Lit := [(98, true), (111, true), (92, false)]
theorem step1128 (p : Nat → Bool) (h : Constraints p) : clause p c1128 = true :=
  Snake9.LocalRup.prove_clause [c360, c255] c1128 (by decide) p (sat_cons (step360 p h) (sat_cons (step255 p h) (sat_nil p)))
def c1129 : List Lit := [(90, true), (111, true), (92, false)]
theorem step1129 (p : Nat → Bool) (h : Constraints p) : clause p c1129 = true :=
  Snake9.LocalRup.prove_clause [c360, c256] c1129 (by decide) p (sat_cons (step360 p h) (sat_cons (step256 p h) (sat_nil p)))
def c1130 : List Lit := [(98, true), (90, true), (92, false)]
theorem step1130 (p : Nat → Bool) (h : Constraints p) : clause p c1130 = true :=
  Snake9.LocalRup.prove_clause [c360, c257] c1130 (by decide) p (sat_cons (step360 p h) (sat_cons (step257 p h) (sat_nil p)))
def c1131 : List Lit := [(23, true), (90, true), (83, true), (93, true), (58, true), (95, false)]
theorem step1131 (p : Nat → Bool) (h : Constraints p) : clause p c1131 = true :=
  Snake9.LocalRup.prove_clause [c361, c272] c1131 (by decide) p (sat_cons (step361 p h) (sat_cons (step272 p h) (sat_nil p)))
def c1132 : List Lit := [(98, true), (96, false), (97, true), (93, true)]
theorem step1132 (p : Nat → Bool) (h : Constraints p) : clause p c1132 = true :=
  Snake9.LocalRup.prove_clause [c362, c273] c1132 (by decide) p (sat_cons (step362 p h) (sat_cons (step273 p h) (sat_nil p)))
def c1133 : List Lit := [(98, true), (84, true), (97, true), (96, false)]
theorem step1133 (p : Nat → Bool) (h : Constraints p) : clause p c1133 = true :=
  Snake9.LocalRup.prove_clause [c362, c274] c1133 (by decide) p (sat_cons (step362 p h) (sat_cons (step274 p h) (sat_nil p)))
def c1134 : List Lit := [(98, true), (93, true), (96, false), (84, true)]
theorem step1134 (p : Nat → Bool) (h : Constraints p) : clause p c1134 = true :=
  Snake9.LocalRup.prove_clause [c362, c275] c1134 (by decide) p (sat_cons (step362 p h) (sat_cons (step275 p h) (sat_nil p)))
def c1135 : List Lit := [(93, true), (84, true), (97, true), (96, false)]
theorem step1135 (p : Nat → Bool) (h : Constraints p) : clause p c1135 = true :=
  Snake9.LocalRup.prove_clause [c362, c276] c1135 (by decide) p (sat_cons (step362 p h) (sat_cons (step276 p h) (sat_nil p)))
def c1136 : List Lit := [(99, true), (105, true), (100, false)]
theorem step1136 (p : Nat → Bool) (h : Constraints p) : clause p c1136 = true :=
  Snake9.LocalRup.prove_clause [c363, c286] c1136 (by decide) p (sat_cons (step363 p h) (sat_cons (step286 p h) (sat_nil p)))
def c1137 : List Lit := [(105, true), (100, false), (79, true)]
theorem step1137 (p : Nat → Bool) (h : Constraints p) : clause p c1137 = true :=
  Snake9.LocalRup.prove_clause [c363, c287] c1137 (by decide) p (sat_cons (step363 p h) (sat_cons (step287 p h) (sat_nil p)))
def c1138 : List Lit := [(99, true), (100, false), (79, true)]
theorem step1138 (p : Nat → Bool) (h : Constraints p) : clause p c1138 = true :=
  Snake9.LocalRup.prove_clause [c363, c288] c1138 (by decide) p (sat_cons (step363 p h) (sat_cons (step288 p h) (sat_nil p)))
def c1139 : List Lit := [(101, true), (110, true), (80, true), (102, false)]
theorem step1139 (p : Nat → Bool) (h : Constraints p) : clause p c1139 = true :=
  Snake9.LocalRup.prove_clause [c364, c291] c1139 (by decide) p (sat_cons (step364 p h) (sat_cons (step291 p h) (sat_nil p)))
def c1140 : List Lit := [(101, true), (29, true), (110, true), (102, false)]
theorem step1140 (p : Nat → Bool) (h : Constraints p) : clause p c1140 = true :=
  Snake9.LocalRup.prove_clause [c364, c292] c1140 (by decide) p (sat_cons (step364 p h) (sat_cons (step292 p h) (sat_nil p)))
def c1141 : List Lit := [(107, true), (101, true), (106, false)]
theorem step1141 (p : Nat → Bool) (h : Constraints p) : clause p c1141 = true :=
  Snake9.LocalRup.prove_clause [c366, c299] c1141 (by decide) p (sat_cons (step366 p h) (sat_cons (step299 p h) (sat_nil p)))
def c1142 : List Lit := [(101, true), (106, false), (84, true)]
theorem step1142 (p : Nat → Bool) (h : Constraints p) : clause p c1142 = true :=
  Snake9.LocalRup.prove_clause [c366, c301] c1142 (by decide) p (sat_cons (step366 p h) (sat_cons (step301 p h) (sat_nil p)))
def c1143 : List Lit := [(108, true), (101, true), (109, false), (110, true)]
theorem step1143 (p : Nat → Bool) (h : Constraints p) : clause p c1143 = true :=
  Snake9.LocalRup.prove_clause [c367, c309] c1143 (by decide) p (sat_cons (step367 p h) (sat_cons (step309 p h) (sat_nil p)))
def c1144 : List Lit := [(116, true), (110, true), (112, false)]
theorem step1144 (p : Nat → Bool) (h : Constraints p) : clause p c1144 = true :=
  Snake9.LocalRup.prove_clause [c368, c316] c1144 (by decide) p (sat_cons (step368 p h) (sat_cons (step316 p h) (sat_nil p)))
def c1145 : List Lit := [(110, true), (112, false), (111, true)]
theorem step1145 (p : Nat → Bool) (h : Constraints p) : clause p c1145 = true :=
  Snake9.LocalRup.prove_clause [c368, c317] c1145 (by decide) p (sat_cons (step368 p h) (sat_cons (step317 p h) (sat_nil p)))
def c1146 : List Lit := [(114, true), (113, false), (108, true)]
theorem step1146 (p : Nat → Bool) (h : Constraints p) : clause p c1146 = true :=
  Snake9.LocalRup.prove_clause [c369, c318] c1146 (by decide) p (sat_cons (step369 p h) (sat_cons (step318 p h) (sat_nil p)))
def c1147 : List Lit := [(114, true), (113, false), (93, true)]
theorem step1147 (p : Nat → Bool) (h : Constraints p) : clause p c1147 = true :=
  Snake9.LocalRup.prove_clause [c369, c319] c1147 (by decide) p (sat_cons (step369 p h) (sat_cons (step319 p h) (sat_nil p)))
def c1148 : List Lit := [(114, true), (105, true), (115, false)]
theorem step1148 (p : Nat → Bool) (h : Constraints p) : clause p c1148 = true :=
  Snake9.LocalRup.prove_clause [c370, c326] c1148 (by decide) p (sat_cons (step370 p h) (sat_cons (step326 p h) (sat_nil p)))
def c1149 : List Lit := [(183, false), (184, false)]
theorem step1149 (p : Nat → Bool) (h : Constraints p) : clause p c1149 = true :=
  Snake9.LocalRup.prove_clause [c859, c405] c1149 (by decide) p (sat_cons (step859 p h) (sat_cons (step405 p h) (sat_nil p)))
def c1150 : List Lit := [(223, false), (224, false)]
theorem step1150 (p : Nat → Bool) (h : Constraints p) : clause p c1150 = true :=
  Snake9.LocalRup.prove_clause [c858, c441] c1150 (by decide) p (sat_cons (step858 p h) (sat_cons (step441 p h) (sat_nil p)))
def c1151 : List Lit := [(425, false), (453, false)]
theorem step1151 (p : Nat → Bool) (h : Constraints p) : clause p c1151 = true :=
  Snake9.LocalRup.prove_clause [c848, c458] c1151 (by decide) p (sat_cons (step848 p h) (sat_cons (step458 p h) (sat_nil p)))
def c1152 : List Lit := [(399, false), (455, false)]
theorem step1152 (p : Nat → Bool) (h : Constraints p) : clause p c1152 = true :=
  Snake9.LocalRup.prove_clause [c846, c462] c1152 (by decide) p (sat_cons (step846 p h) (sat_cons (step462 p h) (sat_nil p)))
def c1153 : List Lit := [(343, false), (457, false)]
theorem step1153 (p : Nat → Bool) (h : Constraints p) : clause p c1153 = true :=
  Snake9.LocalRup.prove_clause [c467, c465] c1153 (by decide) p (sat_cons (step467 p h) (sat_cons (step465 p h) (sat_nil p)))
def c1154 : List Lit := [(1416, false), (1444, true)]
theorem step1154 (p : Nat → Bool) (h : Constraints p) : clause p c1154 = true :=
  Snake9.LocalRup.prove_clause [c894, c522] c1154 (by decide) p (sat_cons (step894 p h) (sat_cons (step522 p h) (sat_nil p)))
def c1155 : List Lit := [(1417, false), (1445, true)]
theorem step1155 (p : Nat → Bool) (h : Constraints p) : clause p c1155 = true :=
  Snake9.LocalRup.prove_clause [c894, c524] c1155 (by decide) p (sat_cons (step894 p h) (sat_cons (step524 p h) (sat_nil p)))
def c1156 : List Lit := [(1457, false), (1469, true)]
theorem step1156 (p : Nat → Bool) (h : Constraints p) : clause p c1156 = true :=
  Snake9.LocalRup.prove_clause [c886, c543] c1156 (by decide) p (sat_cons (step886 p h) (sat_cons (step543 p h) (sat_nil p)))
def c1157 : List Lit := [(1489, false), (1497, true)]
theorem step1157 (p : Nat → Bool) (h : Constraints p) : clause p c1157 = true :=
  Snake9.LocalRup.prove_clause [c887, c579] c1157 (by decide) p (sat_cons (step887 p h) (sat_cons (step579 p h) (sat_nil p)))
end B112E120
