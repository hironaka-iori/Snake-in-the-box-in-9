import B112E168Inputs
namespace B112E168
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1138 : List Lit := [(73, true)]
theorem step1138 (p : Nat → Bool) (h : Constraints p) : clause p c1138 = true :=
  Snake9.LocalRup.prove_clause [c343, c342] c1138 (by decide) p (sat_cons (step343 p h) (sat_cons (step342 p h) (sat_nil p)))
def c1139 : List Lit := [(72, false), (71, false), (79, false)]
theorem step1139 (p : Nat → Bool) (h : Constraints p) : clause p c1139 = true :=
  Snake9.LocalRup.prove_clause [c1138, c351] c1139 (by decide) p (sat_cons (step1138 p h) (sat_cons (step351 p h) (sat_nil p)))
def c1140 : List Lit := [(187, true), (72, true)]
theorem step1140 (p : Nat → Bool) (h : Constraints p) : clause p c1140 = true :=
  Snake9.LocalRup.prove_clause [c1138, c353] c1140 (by decide) p (sat_cons (step1138 p h) (sat_cons (step353 p h) (sat_nil p)))
def c1141 : List Lit := [(2, false)]
theorem step1141 (p : Nat → Bool) (h : Constraints p) : clause p c1141 = true :=
  Snake9.LocalRup.prove_clause [c448, c4] c1141 (by decide) p (sat_cons (step448 p h) (sat_cons (step4 p h) (sat_nil p)))
def c1142 : List Lit := [(66, false)]
theorem step1142 (p : Nat → Bool) (h : Constraints p) : clause p c1142 = true :=
  Snake9.LocalRup.prove_clause [c479, c336] c1142 (by decide) p (sat_cons (step479 p h) (sat_cons (step336 p h) (sat_nil p)))
def c1143 : List Lit := [(450, false)]
theorem step1143 (p : Nat → Bool) (h : Constraints p) : clause p c1143 = true :=
  Snake9.LocalRup.prove_clause [c677, c674] c1143 (by decide) p (sat_cons (step677 p h) (sat_cons (step674 p h) (sat_nil p)))
def c1144 : List Lit := [(338, false)]
theorem step1144 (p : Nat → Bool) (h : Constraints p) : clause p c1144 = true :=
  Snake9.LocalRup.prove_clause [c677, c676] c1144 (by decide) p (sat_cons (step677 p h) (sat_cons (step676 p h) (sat_nil p)))
def c1145 : List Lit := [(448, false)]
theorem step1145 (p : Nat → Bool) (h : Constraints p) : clause p c1145 = true :=
  Snake9.LocalRup.prove_clause [c1143, c671] c1145 (by decide) p (sat_cons (step1143 p h) (sat_cons (step671 p h) (sat_nil p)))
def c1146 : List Lit := [(392, false)]
theorem step1146 (p : Nat → Bool) (h : Constraints p) : clause p c1146 = true :=
  Snake9.LocalRup.prove_clause [c1143, c673] c1146 (by decide) p (sat_cons (step1143 p h) (sat_cons (step673 p h) (sat_nil p)))
def c1147 : List Lit := [(282, false)]
theorem step1147 (p : Nat → Bool) (h : Constraints p) : clause p c1147 = true :=
  Snake9.LocalRup.prove_clause [c1144, c586] c1147 (by decide) p (sat_cons (step1144 p h) (sat_cons (step586 p h) (sat_nil p)))
def c1148 : List Lit := [(418, false)]
theorem step1148 (p : Nat → Bool) (h : Constraints p) : clause p c1148 = true :=
  Snake9.LocalRup.prove_clause [c1145, c669] c1148 (by decide) p (sat_cons (step1145 p h) (sat_cons (step669 p h) (sat_nil p)))
def c1149 : List Lit := [(390, false)]
theorem step1149 (p : Nat → Bool) (h : Constraints p) : clause p c1149 = true :=
  Snake9.LocalRup.prove_clause [c1146, c626] c1149 (by decide) p (sat_cons (step1146 p h) (sat_cons (step626 p h) (sat_nil p)))
def c1150 : List Lit := [(254, false)]
theorem step1150 (p : Nat → Bool) (h : Constraints p) : clause p c1150 = true :=
  Snake9.LocalRup.prove_clause [c1147, c546] c1150 (by decide) p (sat_cons (step1147 p h) (sat_cons (step546 p h) (sat_nil p)))
def c1151 : List Lit := [(388, false)]
theorem step1151 (p : Nat → Bool) (h : Constraints p) : clause p c1151 = true :=
  Snake9.LocalRup.prove_clause [c1149, c622] c1151 (by decide) p (sat_cons (step1149 p h) (sat_cons (step622 p h) (sat_nil p)))
def c1152 : List Lit := [(240, false)]
theorem step1152 (p : Nat → Bool) (h : Constraints p) : clause p c1152 = true :=
  Snake9.LocalRup.prove_clause [c1150, c525] c1152 (by decide) p (sat_cons (step1150 p h) (sat_cons (step525 p h) (sat_nil p)))
def c1153 : List Lit := [(380, false)]
theorem step1153 (p : Nat → Bool) (h : Constraints p) : clause p c1153 = true :=
  Snake9.LocalRup.prove_clause [c1151, c620] c1153 (by decide) p (sat_cons (step1151 p h) (sat_cons (step620 p h) (sat_nil p)))
def c1154 : List Lit := [(238, false)]
theorem step1154 (p : Nat → Bool) (h : Constraints p) : clause p c1154 = true :=
  Snake9.LocalRup.prove_clause [c1152, c513] c1154 (by decide) p (sat_cons (step1152 p h) (sat_cons (step513 p h) (sat_nil p)))
def c1155 : List Lit := [(236, false)]
theorem step1155 (p : Nat → Bool) (h : Constraints p) : clause p c1155 = true :=
  Snake9.LocalRup.prove_clause [c1154, c509] c1155 (by decide) p (sat_cons (step1154 p h) (sat_cons (step509 p h) (sat_nil p)))
def c1156 : List Lit := [(115, true), (118, true), (120, true), (121, true), (123, true), (127, true), (128, true), (130, true), (133, true), (134, true), (136, true), (137, true), (139, true), (141, true), (142, true), (146, true), (147, true), (149, true), (151, true), (152, true), (155, true), (156, true), (159, true), (160, true), (162, true), (163, true), (164, true), (167, true), (169, true), (170, true), (173, true), (177, true), (178, true), (179, true), (181, true), (185, true), (187, true), (188, true), (189, true), (193, true), (194, true), (195, true), (197, true), (200, true), (202, true), (203, true), (204, true), (209, true), (210, true), (211, true), (213, true), (217, true), (219, true), (220, true), (222, true), (223, true), (226, true), (228, true)]
theorem step1156 (p : Nat → Bool) (h : Constraints p) : clause p c1156 = true :=
  Snake9.LocalRup.prove_clause [c448, c449, c450, c451, c452, c453, c454, c455, c456, c457, c458, c459, c460, c461, c462, c463, c464, c465, c466, c467, c468, c469, c470, c471, c472, c473, c474, c475, c476, c477, c478, c479, c480, c481, c482, c483, c484, c485, c486, c487, c488, c489, c490, c491, c492, c493, c494, c495, c496, c497, c498, c499, c500, c501, c502, c678] c1156 (by decide) p (sat_cons (step448 p h) (sat_cons (step449 p h) (sat_cons (step450 p h) (sat_cons (step451 p h) (sat_cons (step452 p h) (sat_cons (step453 p h) (sat_cons (step454 p h) (sat_cons (step455 p h) (sat_cons (step456 p h) (sat_cons (step457 p h) (sat_cons (step458 p h) (sat_cons (step459 p h) (sat_cons (step460 p h) (sat_cons (step461 p h) (sat_cons (step462 p h) (sat_cons (step463 p h) (sat_cons (step464 p h) (sat_cons (step465 p h) (sat_cons (step466 p h) (sat_cons (step467 p h) (sat_cons (step468 p h) (sat_cons (step469 p h) (sat_cons (step470 p h) (sat_cons (step471 p h) (sat_cons (step472 p h) (sat_cons (step473 p h) (sat_cons (step474 p h) (sat_cons (step475 p h) (sat_cons (step476 p h) (sat_cons (step477 p h) (sat_cons (step478 p h) (sat_cons (step479 p h) (sat_cons (step480 p h) (sat_cons (step481 p h) (sat_cons (step482 p h) (sat_cons (step483 p h) (sat_cons (step484 p h) (sat_cons (step485 p h) (sat_cons (step486 p h) (sat_cons (step487 p h) (sat_cons (step488 p h) (sat_cons (step489 p h) (sat_cons (step490 p h) (sat_cons (step491 p h) (sat_cons (step492 p h) (sat_cons (step493 p h) (sat_cons (step494 p h) (sat_cons (step495 p h) (sat_cons (step496 p h) (sat_cons (step497 p h) (sat_cons (step498 p h) (sat_cons (step499 p h) (sat_cons (step500 p h) (sat_cons (step501 p h) (sat_cons (step502 p h) (sat_cons (step678 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1157 : List Lit := [(1375, true)]
theorem step1157 (p : Nat → Bool) (h : Constraints p) : clause p c1157 = true :=
  Snake9.LocalRup.prove_clause [c1141, c683] c1157 (by decide) p (sat_cons (step1141 p h) (sat_cons (step683 p h) (sat_nil p)))
def c1158 : List Lit := [(1373, false), (1376, true)]
theorem step1158 (p : Nat → Bool) (h : Constraints p) : clause p c1158 = true :=
  Snake9.LocalRup.prove_clause [c1141, c684] c1158 (by decide) p (sat_cons (step1141 p h) (sat_cons (step684 p h) (sat_nil p)))
def c1159 : List Lit := [(1374, false), (1377, true)]
theorem step1159 (p : Nat → Bool) (h : Constraints p) : clause p c1159 = true :=
  Snake9.LocalRup.prove_clause [c1141, c685] c1159 (by decide) p (sat_cons (step1141 p h) (sat_cons (step685 p h) (sat_nil p)))
def c1160 : List Lit := [(1386, true)]
theorem step1160 (p : Nat → Bool) (h : Constraints p) : clause p c1160 = true :=
  Snake9.LocalRup.prove_clause [c1157, c700] c1160 (by decide) p (sat_cons (step1157 p h) (sat_cons (step700 p h) (sat_nil p)))
def c1161 : List Lit := [(1382, false), (1387, true)]
theorem step1161 (p : Nat → Bool) (h : Constraints p) : clause p c1161 = true :=
  Snake9.LocalRup.prove_clause [c1157, c701] c1161 (by decide) p (sat_cons (step1157 p h) (sat_cons (step701 p h) (sat_nil p)))
def c1162 : List Lit := [(1383, false), (1388, true)]
theorem step1162 (p : Nat → Bool) (h : Constraints p) : clause p c1162 = true :=
  Snake9.LocalRup.prove_clause [c1157, c702] c1162 (by decide) p (sat_cons (step1157 p h) (sat_cons (step702 p h) (sat_nil p)))
def c1163 : List Lit := [(1384, false), (1389, true)]
theorem step1163 (p : Nat → Bool) (h : Constraints p) : clause p c1163 = true :=
  Snake9.LocalRup.prove_clause [c1157, c703] c1163 (by decide) p (sat_cons (step1157 p h) (sat_cons (step703 p h) (sat_nil p)))
def c1164 : List Lit := [(1385, false), (1390, true)]
theorem step1164 (p : Nat → Bool) (h : Constraints p) : clause p c1164 = true :=
  Snake9.LocalRup.prove_clause [c1157, c704] c1164 (by decide) p (sat_cons (step1157 p h) (sat_cons (step704 p h) (sat_nil p)))
def c1165 : List Lit := [(1413, true)]
theorem step1165 (p : Nat → Bool) (h : Constraints p) : clause p c1165 = true :=
  Snake9.LocalRup.prove_clause [c1160, c748] c1165 (by decide) p (sat_cons (step1160 p h) (sat_cons (step748 p h) (sat_nil p)))
def c1166 : List Lit := [(1406, false), (1414, true)]
theorem step1166 (p : Nat → Bool) (h : Constraints p) : clause p c1166 = true :=
  Snake9.LocalRup.prove_clause [c1160, c749] c1166 (by decide) p (sat_cons (step1160 p h) (sat_cons (step749 p h) (sat_nil p)))
def c1167 : List Lit := [(1407, false), (1415, true)]
theorem step1167 (p : Nat → Bool) (h : Constraints p) : clause p c1167 = true :=
  Snake9.LocalRup.prove_clause [c1160, c750] c1167 (by decide) p (sat_cons (step1160 p h) (sat_cons (step750 p h) (sat_nil p)))
def c1168 : List Lit := [(1408, false), (1416, true)]
theorem step1168 (p : Nat → Bool) (h : Constraints p) : clause p c1168 = true :=
  Snake9.LocalRup.prove_clause [c1160, c751] c1168 (by decide) p (sat_cons (step1160 p h) (sat_cons (step751 p h) (sat_nil p)))
def c1169 : List Lit := [(1409, false), (1417, true)]
theorem step1169 (p : Nat → Bool) (h : Constraints p) : clause p c1169 = true :=
  Snake9.LocalRup.prove_clause [c1160, c752] c1169 (by decide) p (sat_cons (step1160 p h) (sat_cons (step752 p h) (sat_nil p)))
def c1170 : List Lit := [(1410, false), (1418, true)]
theorem step1170 (p : Nat → Bool) (h : Constraints p) : clause p c1170 = true :=
  Snake9.LocalRup.prove_clause [c1160, c753] c1170 (by decide) p (sat_cons (step1160 p h) (sat_cons (step753 p h) (sat_nil p)))
def c1171 : List Lit := [(1474, false), (1489, true)]
theorem step1171 (p : Nat → Bool) (h : Constraints p) : clause p c1171 = true :=
  Snake9.LocalRup.prove_clause [c1165, c879] c1171 (by decide) p (sat_cons (step1165 p h) (sat_cons (step879 p h) (sat_nil p)))
def c1172 : List Lit := [(1475, false), (1490, true)]
theorem step1172 (p : Nat → Bool) (h : Constraints p) : clause p c1172 = true :=
  Snake9.LocalRup.prove_clause [c1165, c880] c1172 (by decide) p (sat_cons (step1165 p h) (sat_cons (step880 p h) (sat_nil p)))
def c1173 : List Lit := [(1502, true)]
theorem step1173 (p : Nat → Bool) (h : Constraints p) : clause p c1173 = true :=
  Snake9.LocalRup.prove_clause [c1142, c937] c1173 (by decide) p (sat_cons (step1142 p h) (sat_cons (step937 p h) (sat_nil p)))
def c1174 : List Lit := [(68, true), (1503, true)]
theorem step1174 (p : Nat → Bool) (h : Constraints p) : clause p c1174 = true :=
  Snake9.LocalRup.prove_clause [c1142, c938] c1174 (by decide) p (sat_cons (step1142 p h) (sat_cons (step938 p h) (sat_nil p)))
def c1175 : List Lit := [(1506, true)]
theorem step1175 (p : Nat → Bool) (h : Constraints p) : clause p c1175 = true :=
  Snake9.LocalRup.prove_clause [c1173, c940] c1175 (by decide) p (sat_cons (step1173 p h) (sat_cons (step940 p h) (sat_nil p)))
def c1176 : List Lit := [(1504, false), (1507, true)]
theorem step1176 (p : Nat → Bool) (h : Constraints p) : clause p c1176 = true :=
  Snake9.LocalRup.prove_clause [c1173, c941] c1176 (by decide) p (sat_cons (step1173 p h) (sat_cons (step941 p h) (sat_nil p)))
def c1177 : List Lit := [(1510, true)]
theorem step1177 (p : Nat → Bool) (h : Constraints p) : clause p c1177 = true :=
  Snake9.LocalRup.prove_clause [c1175, c944] c1177 (by decide) p (sat_cons (step1175 p h) (sat_cons (step944 p h) (sat_nil p)))
def c1178 : List Lit := [(1499, false), (1511, true)]
theorem step1178 (p : Nat → Bool) (h : Constraints p) : clause p c1178 = true :=
  Snake9.LocalRup.prove_clause [c1175, c947] c1178 (by decide) p (sat_cons (step1175 p h) (sat_cons (step947 p h) (sat_nil p)))
def c1179 : List Lit := [(1500, false), (1512, true)]
theorem step1179 (p : Nat → Bool) (h : Constraints p) : clause p c1179 = true :=
  Snake9.LocalRup.prove_clause [c1175, c951] c1179 (by decide) p (sat_cons (step1175 p h) (sat_cons (step951 p h) (sat_nil p)))
def c1180 : List Lit := [(1501, false), (1513, true)]
theorem step1180 (p : Nat → Bool) (h : Constraints p) : clause p c1180 = true :=
  Snake9.LocalRup.prove_clause [c1175, c955] c1180 (by decide) p (sat_cons (step1175 p h) (sat_cons (step955 p h) (sat_nil p)))
def c1181 : List Lit := [(1537, true)]
theorem step1181 (p : Nat → Bool) (h : Constraints p) : clause p c1181 = true :=
  Snake9.LocalRup.prove_clause [c1177, c984] c1181 (by decide) p (sat_cons (step1177 p h) (sat_cons (step984 p h) (sat_nil p)))
def c1182 : List Lit := [(1530, false), (1538, true)]
theorem step1182 (p : Nat → Bool) (h : Constraints p) : clause p c1182 = true :=
  Snake9.LocalRup.prove_clause [c1177, c985] c1182 (by decide) p (sat_cons (step1177 p h) (sat_cons (step985 p h) (sat_nil p)))
def c1183 : List Lit := [(1531, false), (1539, true)]
theorem step1183 (p : Nat → Bool) (h : Constraints p) : clause p c1183 = true :=
  Snake9.LocalRup.prove_clause [c1177, c986] c1183 (by decide) p (sat_cons (step1177 p h) (sat_cons (step986 p h) (sat_nil p)))
def c1184 : List Lit := [(1532, false), (1540, true)]
theorem step1184 (p : Nat → Bool) (h : Constraints p) : clause p c1184 = true :=
  Snake9.LocalRup.prove_clause [c1177, c987] c1184 (by decide) p (sat_cons (step1177 p h) (sat_cons (step987 p h) (sat_nil p)))
def c1185 : List Lit := [(1533, false), (1541, true)]
theorem step1185 (p : Nat → Bool) (h : Constraints p) : clause p c1185 = true :=
  Snake9.LocalRup.prove_clause [c1177, c988] c1185 (by decide) p (sat_cons (step1177 p h) (sat_cons (step988 p h) (sat_nil p)))
def c1186 : List Lit := [(1592, false), (1607, true)]
theorem step1186 (p : Nat → Bool) (h : Constraints p) : clause p c1186 = true :=
  Snake9.LocalRup.prove_clause [c1181, c1073] c1186 (by decide) p (sat_cons (step1181 p h) (sat_cons (step1073 p h) (sat_nil p)))
def c1187 : List Lit := [(1593, false), (1608, true)]
theorem step1187 (p : Nat → Bool) (h : Constraints p) : clause p c1187 = true :=
  Snake9.LocalRup.prove_clause [c1181, c1074] c1187 (by decide) p (sat_cons (step1181 p h) (sat_cons (step1074 p h) (sat_nil p)))
def c1188 : List Lit := [(1594, false), (1609, true)]
theorem step1188 (p : Nat → Bool) (h : Constraints p) : clause p c1188 = true :=
  Snake9.LocalRup.prove_clause [c1181, c1075] c1188 (by decide) p (sat_cons (step1181 p h) (sat_cons (step1075 p h) (sat_nil p)))
def c1189 : List Lit := [(1595, false), (1610, true)]
theorem step1189 (p : Nat → Bool) (h : Constraints p) : clause p c1189 = true :=
  Snake9.LocalRup.prove_clause [c1181, c1076] c1189 (by decide) p (sat_cons (step1181 p h) (sat_cons (step1076 p h) (sat_nil p)))
def c1190 : List Lit := [(1440, true)]
theorem step1190 (p : Nat → Bool) (h : Constraints p) : clause p c1190 = true :=
  Snake9.LocalRup.prove_clause [c465, c803, c807, c795, c797, c784, c793, c789, c790, c781, c154, c135, c137] c1190 (by decide) p (sat_cons (step465 p h) (sat_cons (step803 p h) (sat_cons (step807 p h) (sat_cons (step795 p h) (sat_cons (step797 p h) (sat_cons (step784 p h) (sat_cons (step793 p h) (sat_cons (step789 p h) (sat_cons (step790 p h) (sat_cons (step781 p h) (sat_cons (step154 p h) (sat_cons (step135 p h) (sat_cons (step137 p h) (sat_nil p))))))))))))))
def c1191 : List Lit := [(1460, true)]
theorem step1191 (p : Nat → Bool) (h : Constraints p) : clause p c1191 = true :=
  Snake9.LocalRup.prove_clause [c474, c838, c842, c830, c832, c819, c821, c828, c824, c817, c279, c289, c191] c1191 (by decide) p (sat_cons (step474 p h) (sat_cons (step838 p h) (sat_cons (step842 p h) (sat_cons (step830 p h) (sat_cons (step832 p h) (sat_cons (step819 p h) (sat_cons (step821 p h) (sat_cons (step828 p h) (sat_cons (step824 p h) (sat_cons (step817 p h) (sat_cons (step279 p h) (sat_cons (step289 p h) (sat_cons (step191 p h) (sat_nil p))))))))))))))
def c1192 : List Lit := [(1468, true)]
theorem step1192 (p : Nat → Bool) (h : Constraints p) : clause p c1192 = true :=
  Snake9.LocalRup.prove_clause [c1191, c1190, c856] c1192 (by decide) p (sat_cons (step1191 p h) (sat_cons (step1190 p h) (sat_cons (step856 p h) (sat_nil p))))
def c1193 : List Lit := [(1454, true), (1497, true)]
theorem step1193 (p : Nat → Bool) (h : Constraints p) : clause p c1193 = true :=
  Snake9.LocalRup.prove_clause [c475, c930, c929, c827, c828, c331, c287, c292] c1193 (by decide) p (sat_cons (step475 p h) (sat_cons (step930 p h) (sat_cons (step929 p h) (sat_cons (step827 p h) (sat_cons (step828 p h) (sat_cons (step331 p h) (sat_cons (step287 p h) (sat_cons (step292 p h) (sat_nil p)))))))))
def c1194 : List Lit := [(56, true), (57, false), (43, false)]
theorem step1194 (p : Nat → Bool) (h : Constraints p) : clause p c1194 = true :=
  Snake9.LocalRup.prove_clause [c474, c288, c289, c1125] c1194 (by decide) p (sat_cons (step474 p h) (sat_cons (step288 p h) (sat_cons (step289 p h) (sat_cons (step1125 p h) (sat_nil p)))))
def c1195 : List Lit := [(56, false), (1436, true), (1497, true)]
theorem step1195 (p : Nat → Bool) (h : Constraints p) : clause p c1195 = true :=
  Snake9.LocalRup.prove_clause [c465, c466, c478, c797, c789, c795, c793, c790, c154, c148, c137, c150, c147, c930, c929, c314, c315, c319] c1195 (by decide) p (sat_cons (step465 p h) (sat_cons (step466 p h) (sat_cons (step478 p h) (sat_cons (step797 p h) (sat_cons (step789 p h) (sat_cons (step795 p h) (sat_cons (step793 p h) (sat_cons (step790 p h) (sat_cons (step154 p h) (sat_cons (step148 p h) (sat_cons (step137 p h) (sat_cons (step150 p h) (sat_cons (step147 p h) (sat_cons (step930 p h) (sat_cons (step929 p h) (sat_cons (step314 p h) (sat_cons (step315 p h) (sat_cons (step319 p h) (sat_nil p)))))))))))))))))))
def c1196 : List Lit := [(1403, true), (1436, true)]
theorem step1196 (p : Nat → Bool) (h : Constraints p) : clause p c1196 = true :=
  Snake9.LocalRup.prove_clause [c465, c466, c795, c793, c797, c789, c790, c154, c148, c140, c724, c138, c728, c730, c726, c721, c98] c1196 (by decide) p (sat_cons (step465 p h) (sat_cons (step466 p h) (sat_cons (step795 p h) (sat_cons (step793 p h) (sat_cons (step797 p h) (sat_cons (step789 p h) (sat_cons (step790 p h) (sat_cons (step154 p h) (sat_cons (step148 p h) (sat_cons (step140 p h) (sat_cons (step724 p h) (sat_cons (step138 p h) (sat_cons (step728 p h) (sat_cons (step730 p h) (sat_cons (step726 p h) (sat_cons (step721 p h) (sat_cons (step98 p h) (sat_nil p))))))))))))))))))
def c1197 : List Lit := [(47, true), (1464, true), (54, true), (1455, false), (50, false), (62, false)]
theorem step1197 (p : Nat → Bool) (h : Constraints p) : clause p c1197 = true :=
  Snake9.LocalRup.prove_clause [c824, c834, c850, c820, c817, c818, c819, c254, c846, c826, c837] c1197 (by decide) p (sat_cons (step824 p h) (sat_cons (step834 p h) (sat_cons (step850 p h) (sat_cons (step820 p h) (sat_cons (step817 p h) (sat_cons (step818 p h) (sat_cons (step819 p h) (sat_cons (step254 p h) (sat_cons (step846 p h) (sat_cons (step826 p h) (sat_cons (step837 p h) (sat_nil p))))))))))))
def c1198 : List Lit := [(64, true), (1436, true), (1497, true), (1511, false)]
theorem step1198 (p : Nat → Bool) (h : Constraints p) : clause p c1198 = true :=
  Snake9.TreeRup.prove_clause [c465, c493, c466, c475, c478, c1110, c1196, c795, c792, c1195, c1194, c797, c789, c930, c793, c790, c154, c147, c146, c148, c137, c151, c406, c1016, c1025, c1028, c144, c135, c781, c787, c811, c150, c140, c138, c929, c989, c292, c319, c320, c829, c299, c302, c306, c714, c824, c1048, c717, c834, c1050, c840, c1054, c864, c1067, c1078, c1107, c741, c1168, c901, c866, c1197, c107, c101, c104, c968, c721, c726, c970, c731, c975, c742, c990, c1169, c1083, c906, c1106] c1198 (by decide) p (sat_cons (step465 p h) (sat_cons (step493 p h) (sat_cons (step466 p h) (sat_cons (step475 p h) (sat_cons (step478 p h) (sat_cons (step1110 p h) (sat_cons (step1196 p h) (sat_cons (step795 p h) (sat_cons (step792 p h) (sat_cons (step1195 p h) (sat_cons (step1194 p h) (sat_cons (step797 p h) (sat_cons (step789 p h) (sat_cons (step930 p h) (sat_cons (step793 p h) (sat_cons (step790 p h) (sat_cons (step154 p h) (sat_cons (step147 p h) (sat_cons (step146 p h) (sat_cons (step148 p h) (sat_cons (step137 p h) (sat_cons (step151 p h) (sat_cons (step406 p h) (sat_cons (step1016 p h) (sat_cons (step1025 p h) (sat_cons (step1028 p h) (sat_cons (step144 p h) (sat_cons (step135 p h) (sat_cons (step781 p h) (sat_cons (step787 p h) (sat_cons (step811 p h) (sat_cons (step150 p h) (sat_cons (step140 p h) (sat_cons (step138 p h) (sat_cons (step929 p h) (sat_cons (step989 p h) (sat_cons (step292 p h) (sat_cons (step319 p h) (sat_cons (step320 p h) (sat_cons (step829 p h) (sat_cons (step299 p h) (sat_cons (step302 p h) (sat_cons (step306 p h) (sat_cons (step714 p h) (sat_cons (step824 p h) (sat_cons (step1048 p h) (sat_cons (step717 p h) (sat_cons (step834 p h) (sat_cons (step1050 p h) (sat_cons (step840 p h) (sat_cons (step1054 p h) (sat_cons (step864 p h) (sat_cons (step1067 p h) (sat_cons (step1078 p h) (sat_cons (step1107 p h) (sat_cons (step741 p h) (sat_cons (step1168 p h) (sat_cons (step901 p h) (sat_cons (step866 p h) (sat_cons (step1197 p h) (sat_cons (step107 p h) (sat_cons (step101 p h) (sat_cons (step104 p h) (sat_cons (step968 p h) (sat_cons (step721 p h) (sat_cons (step726 p h) (sat_cons (step970 p h) (sat_cons (step731 p h) (sat_cons (step975 p h) (sat_cons (step742 p h) (sat_cons (step990 p h) (sat_cons (step1169 p h) (sat_cons (step1083 p h) (sat_cons (step906 p h) (sat_cons (step1106 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1199 : List Lit := [(1447, true), (1417, true), (1401, false), (50, false), (27, false), (36, false), (62, false)]
theorem step1199 (p : Nat → Bool) (h : Constraints p) : clause p c1199 = true :=
  Snake9.LocalRup.prove_clause [c816, c817, c244, c101, c689, c721, c692, c731, c1161, c737, c757] c1199 (by decide) p (sat_cons (step816 p h) (sat_cons (step817 p h) (sat_cons (step244 p h) (sat_cons (step101 p h) (sat_cons (step689 p h) (sat_cons (step721 p h) (sat_cons (step692 p h) (sat_cons (step731 p h) (sat_cons (step1161 p h) (sat_cons (step737 p h) (sat_cons (step757 p h) (sat_nil p))))))))))))
def c1200 : List Lit := [(51, false), (1464, false), (50, false), (1407, false), (1492, true), (34, true), (30, true), (62, false)]
theorem step1200 (p : Nat → Bool) (h : Constraints p) : clause p c1200 = true :=
  Snake9.LocalRup.prove_clause [c244, c250, c689, c783, c692, c788, c1161, c814, c756, c872, c902] c1200 (by decide) p (sat_cons (step244 p h) (sat_cons (step250 p h) (sat_cons (step689 p h) (sat_cons (step783 p h) (sat_cons (step692 p h) (sat_cons (step788 p h) (sat_cons (step1161 p h) (sat_cons (step814 p h) (sat_cons (step756 p h) (sat_cons (step872 p h) (sat_cons (step902 p h) (sat_nil p))))))))))))
def c1201 : List Lit := [(8, false), (51, true), (1451, true), (43, false)]
theorem step1201 (p : Nat → Bool) (h : Constraints p) : clause p c1201 = true :=
  Snake9.LocalRup.prove_clause [c451, c19, c20, c1111, c170, c823, c818] c1201 (by decide) p (sat_cons (step451 p h) (sat_cons (step19 p h) (sat_cons (step20 p h) (sat_cons (step1111 p h) (sat_cons (step170 p h) (sat_cons (step823 p h) (sat_cons (step818 p h) (sat_nil p))))))))
end B112E168
