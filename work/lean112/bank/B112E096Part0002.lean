import B112E096Part0001
namespace B112E096
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1164 : List Lit := [(1461, true), (5, false), (62, false)]
theorem step1164 (p : Nat → Bool) (h : Constraints p) : clause p c1164 = true :=
  Snake9.LocalRup.prove_clause [c1066, c1065, c1162, c652, c609, c1163, c10, c13, c1049, c593, c610, c611, c649, c600, c635, c1110, c620, c614] c1164 (by decide) p (sat_cons (step1066 p h) (sat_cons (step1065 p h) (sat_cons (step1162 p h) (sat_cons (step652 p h) (sat_cons (step609 p h) (sat_cons (step1163 p h) (sat_cons (step10 p h) (sat_cons (step13 p h) (sat_cons (step1049 p h) (sat_cons (step593 p h) (sat_cons (step610 p h) (sat_cons (step611 p h) (sat_cons (step649 p h) (sat_cons (step600 p h) (sat_cons (step635 p h) (sat_cons (step1110 p h) (sat_cons (step620 p h) (sat_cons (step614 p h) (sat_nil p)))))))))))))))))))
def c1165 : List Lit := [(5, false), (1509, false), (62, false), (1538, true)]
theorem step1165 (p : Nat → Bool) (h : Constraints p) : clause p c1165 = true :=
  Snake9.LocalRup.prove_clause [c1066, c715, c744, c654, c1164, c740, c719, c676, c671, c664, c11, c14, c15, c1049, c1163, c593, c612] c1165 (by decide) p (sat_cons (step1066 p h) (sat_cons (step715 p h) (sat_cons (step744 p h) (sat_cons (step654 p h) (sat_cons (step1164 p h) (sat_cons (step740 p h) (sat_cons (step719 p h) (sat_cons (step676 p h) (sat_cons (step671 p h) (sat_cons (step664 p h) (sat_cons (step11 p h) (sat_cons (step14 p h) (sat_cons (step15 p h) (sat_cons (step1049 p h) (sat_cons (step1163 p h) (sat_cons (step593 p h) (sat_cons (step612 p h) (sat_nil p))))))))))))))))))
def c1166 : List Lit := [(1429, false), (1509, false), (1538, true)]
theorem step1166 (p : Nat → Bool) (h : Constraints p) : clause p c1166 = true :=
  Snake9.LocalRup.prove_clause [c1066, c1065, c1058, c465, c715, c744, c652, c653, c740, c635, c716, c719, c711, c676, c679, c697, c671, c1071, c659, c663, c687, c688, c657, c1125, c695, c690, c88, c122, c93] c1166 (by decide) p (sat_cons (step1066 p h) (sat_cons (step1065 p h) (sat_cons (step1058 p h) (sat_cons (step465 p h) (sat_cons (step715 p h) (sat_cons (step744 p h) (sat_cons (step652 p h) (sat_cons (step653 p h) (sat_cons (step740 p h) (sat_cons (step635 p h) (sat_cons (step716 p h) (sat_cons (step719 p h) (sat_cons (step711 p h) (sat_cons (step676 p h) (sat_cons (step679 p h) (sat_cons (step697 p h) (sat_cons (step671 p h) (sat_cons (step1071 p h) (sat_cons (step659 p h) (sat_cons (step663 p h) (sat_cons (step687 p h) (sat_cons (step688 p h) (sat_cons (step657 p h) (sat_cons (step1125 p h) (sat_cons (step695 p h) (sat_cons (step690 p h) (sat_cons (step88 p h) (sat_cons (step122 p h) (sat_cons (step93 p h) (sat_nil p))))))))))))))))))))))))))))))
def c1167 : List Lit := [(4, true), (1429, true), (5, true)]
theorem step1167 (p : Nat → Bool) (h : Constraints p) : clause p c1167 = true :=
  Snake9.LocalRup.prove_clause [c451, c1047, c1045, c1037, c448, c452, c1049, c591, c609, c1163, c19, c17, c497, c498, c499, c501, c507, c496, c504, c495, c503, c3, c502, c4, c23, c593, c21, c611, c594, c602] c1167 (by decide) p (sat_cons (step451 p h) (sat_cons (step1047 p h) (sat_cons (step1045 p h) (sat_cons (step1037 p h) (sat_cons (step448 p h) (sat_cons (step452 p h) (sat_cons (step1049 p h) (sat_cons (step591 p h) (sat_cons (step609 p h) (sat_cons (step1163 p h) (sat_cons (step19 p h) (sat_cons (step17 p h) (sat_cons (step497 p h) (sat_cons (step498 p h) (sat_cons (step499 p h) (sat_cons (step501 p h) (sat_cons (step507 p h) (sat_cons (step496 p h) (sat_cons (step504 p h) (sat_cons (step495 p h) (sat_cons (step503 p h) (sat_cons (step3 p h) (sat_cons (step502 p h) (sat_cons (step4 p h) (sat_cons (step23 p h) (sat_cons (step593 p h) (sat_cons (step21 p h) (sat_cons (step611 p h) (sat_cons (step594 p h) (sat_cons (step602 p h) (sat_nil p)))))))))))))))))))))))))))))))
def c1168 : List Lit := [(13, false), (10, false), (12, false)]
theorem step1168 (p : Nat → Bool) (h : Constraints p) : clause p c1168 = true :=
  Snake9.LocalRup.prove_clause [c452, c20, c22] c1168 (by decide) p (sat_cons (step452 p h) (sat_cons (step20 p h) (sat_cons (step22 p h) (sat_nil p))))
def c1169 : List Lit := [(1422, true)]
theorem step1169 (p : Nat → Bool) (h : Constraints p) : clause p c1169 = true :=
  Snake9.LocalRup.prove_clause [c600, c602, c597, c598, c594, c1168] c1169 (by decide) p (sat_cons (step600 p h) (sat_cons (step602 p h) (sat_cons (step597 p h) (sat_cons (step598 p h) (sat_cons (step594 p h) (sat_cons (step1168 p h) (sat_nil p)))))))
def c1170 : List Lit := [(1518, true), (150, true), (1438, true), (1509, false)]
theorem step1170 (p : Nat → Bool) (h : Constraints p) : clause p c1170 = true :=
  Snake9.LocalRup.prove_clause [c1058, c461, c465, c716, c1137, c719, c711, c67, c676, c679, c697, c69, c671, c1071, c659, c663, c687, c688, c657, c1124, c695, c690, c88, c122, c93] c1170 (by decide) p (sat_cons (step1058 p h) (sat_cons (step461 p h) (sat_cons (step465 p h) (sat_cons (step716 p h) (sat_cons (step1137 p h) (sat_cons (step719 p h) (sat_cons (step711 p h) (sat_cons (step67 p h) (sat_cons (step676 p h) (sat_cons (step679 p h) (sat_cons (step697 p h) (sat_cons (step69 p h) (sat_cons (step671 p h) (sat_cons (step1071 p h) (sat_cons (step659 p h) (sat_cons (step663 p h) (sat_cons (step687 p h) (sat_cons (step688 p h) (sat_cons (step657 p h) (sat_cons (step1124 p h) (sat_cons (step695 p h) (sat_cons (step690 p h) (sat_cons (step88 p h) (sat_cons (step122 p h) (sat_cons (step93 p h) (sat_nil p))))))))))))))))))))))))))
def c1171 : List Lit := [(291, true), (1423, true), (5, true)]
theorem step1171 (p : Nat → Bool) (h : Constraints p) : clause p c1171 = true :=
  Snake9.LocalRup.prove_clause [c451, c1037, c448, c452, c1163, c18, c518, c519, c517, c505, c506, c512, c504, c500, c511, c503, c496, c510, c502, c495, c30, c3, c1110, c4, c603, c23, c594, c21] c1171 (by decide) p (sat_cons (step451 p h) (sat_cons (step1037 p h) (sat_cons (step448 p h) (sat_cons (step452 p h) (sat_cons (step1163 p h) (sat_cons (step18 p h) (sat_cons (step518 p h) (sat_cons (step519 p h) (sat_cons (step517 p h) (sat_cons (step505 p h) (sat_cons (step506 p h) (sat_cons (step512 p h) (sat_cons (step504 p h) (sat_cons (step500 p h) (sat_cons (step511 p h) (sat_cons (step503 p h) (sat_cons (step496 p h) (sat_cons (step510 p h) (sat_cons (step502 p h) (sat_cons (step495 p h) (sat_cons (step30 p h) (sat_cons (step3 p h) (sat_cons (step1110 p h) (sat_cons (step4 p h) (sat_cons (step603 p h) (sat_cons (step23 p h) (sat_cons (step594 p h) (sat_cons (step21 p h) (sat_nil p)))))))))))))))))))))))))))))
def c1172 : List Lit := [(1427, true)]
theorem step1172 (p : Nat → Bool) (h : Constraints p) : clause p c1172 = true :=
  Snake9.LocalRup.prove_clause [c1169, c1053] c1172 (by decide) p (sat_cons (step1169 p h) (sat_cons (step1053 p h) (sat_nil p)))
def c1173 : List Lit := [(22, false), (1443, false), (39, false), (1451, true)]
theorem step1173 (p : Nat → Bool) (h : Constraints p) : clause p c1173 = true :=
  Snake9.LocalRup.prove_clause [c1065, c638, c1125, c1124, c636, c624, c630] c1173 (by decide) p (sat_cons (step1065 p h) (sat_cons (step638 p h) (sat_cons (step1125 p h) (sat_cons (step1124 p h) (sat_cons (step636 p h) (sat_cons (step624 p h) (sat_cons (step630 p h) (sat_nil p))))))))
def c1174 : List Lit := [(22, false), (39, false), (1451, true)]
theorem step1174 (p : Nat → Bool) (h : Constraints p) : clause p c1174 = true :=
  Snake9.LocalRup.prove_clause [c1065, c638, c1125, c1124, c1173, c636, c626, c627, c631, c1064, c625] c1174 (by decide) p (sat_cons (step1065 p h) (sat_cons (step638 p h) (sat_cons (step1125 p h) (sat_cons (step1124 p h) (sat_cons (step1173 p h) (sat_cons (step636 p h) (sat_cons (step626 p h) (sat_cons (step627 p h) (sat_cons (step631 p h) (sat_cons (step1064 p h) (sat_cons (step625 p h) (sat_nil p))))))))))))
def c1175 : List Lit := [(1486, false), (48, true), (1, false), (4, false), (1509, false), (1538, true)]
theorem step1175 (p : Nat → Bool) (h : Constraints p) : clause p c1175 = true :=
  Snake9.LocalRup.prove_clause [c1067, c1058, c1172, c1065, c733, c724, c723, c711, c737, c693, c645, c691, c635, c1, c618, c616] c1175 (by decide) p (sat_cons (step1067 p h) (sat_cons (step1058 p h) (sat_cons (step1172 p h) (sat_cons (step1065 p h) (sat_cons (step733 p h) (sat_cons (step724 p h) (sat_cons (step723 p h) (sat_cons (step711 p h) (sat_cons (step737 p h) (sat_cons (step693 p h) (sat_cons (step645 p h) (sat_cons (step691 p h) (sat_cons (step635 p h) (sat_cons (step1 p h) (sat_cons (step618 p h) (sat_cons (step616 p h) (sat_nil p)))))))))))))))))
def c1176 : List Lit := [(21, true), (24, false), (22, true), (1461, true), (135, true)]
theorem step1176 (p : Nat → Bool) (h : Constraints p) : clause p c1176 = true :=
  Snake9.LocalRup.prove_clause [c1172, c1065, c455, c646, c638, c1109, c615, c617, c32, c621, c613, c35, c40] c1176 (by decide) p (sat_cons (step1172 p h) (sat_cons (step1065 p h) (sat_cons (step455 p h) (sat_cons (step646 p h) (sat_cons (step638 p h) (sat_cons (step1109 p h) (sat_cons (step615 p h) (sat_cons (step617 p h) (sat_cons (step32 p h) (sat_cons (step621 p h) (sat_cons (step613 p h) (sat_cons (step35 p h) (sat_cons (step40 p h) (sat_nil p))))))))))))))
def c1177 : List Lit := [(38, true), (82, false), (34, false), (105, false), (22, true), (39, false), (221, true), (101, false)]
theorem step1177 (p : Nat → Bool) (h : Constraints p) : clause p c1177 = true :=
  Snake9.LocalRup.prove_clause [c465, c462, c92, c379, c73, c326, c287, c337] c1177 (by decide) p (sat_cons (step465 p h) (sat_cons (step462 p h) (sat_cons (step92 p h) (sat_cons (step379 p h) (sat_cons (step73 p h) (sat_cons (step326 p h) (sat_cons (step287 p h) (sat_cons (step337 p h) (sat_nil p)))))))))
def c1178 : List Lit := [(103, false), (99, true), (107, true), (82, false), (105, false), (221, true)]
theorem step1178 (p : Nat → Bool) (h : Constraints p) : clause p c1178 = true :=
  Snake9.LocalRup.prove_clause [c326, c337] c1178 (by decide) p (sat_cons (step326 p h) (sat_cons (step337 p h) (sat_nil p)))
def c1179 : List Lit := [(1443, true), (31, false)]
theorem step1179 (p : Nat → Bool) (h : Constraints p) : clause p c1179 = true :=
  Snake9.LocalRup.prove_clause [c461, c68, c626, c627, c66] c1179 (by decide) p (sat_cons (step461 p h) (sat_cons (step68 p h) (sat_cons (step626 p h) (sat_cons (step627 p h) (sat_cons (step66 p h) (sat_nil p))))))
def c1180 : List Lit := [(1565, true), (1560, false)]
theorem step1180 (p : Nat → Bool) (h : Constraints p) : clause p c1180 = true :=
  Snake9.LocalRup.prove_clause [c477, c1155, c776, c757, c758, c752, c152, c148, c750] c1180 (by decide) p (sat_cons (step477 p h) (sat_cons (step1155 p h) (sat_cons (step776 p h) (sat_cons (step757 p h) (sat_cons (step758 p h) (sat_cons (step752 p h) (sat_cons (step152 p h) (sat_cons (step148 p h) (sat_cons (step750 p h) (sat_nil p))))))))))
def c1181 : List Lit := [(2, false), (120, true)]
theorem step1181 (p : Nat → Bool) (h : Constraints p) : clause p c1181 = true :=
  Snake9.LocalRup.prove_clause [c1037, c3] c1181 (by decide) p (sat_cons (step1037 p h) (sat_cons (step3 p h) (sat_nil p)))
def c1182 : List Lit := [(3, false), (2, true), (5, true)]
theorem step1182 (p : Nat → Bool) (h : Constraints p) : clause p c1182 = true :=
  Snake9.LocalRup.prove_clause [c448, c4] c1182 (by decide) p (sat_cons (step448 p h) (sat_cons (step4 p h) (sat_nil p)))
def c1183 : List Lit := [(4, false), (1, true), (5, true)]
theorem step1183 (p : Nat → Bool) (h : Constraints p) : clause p c1183 = true :=
  Snake9.LocalRup.prove_clause [c449, c5] c1183 (by decide) p (sat_cons (step449 p h) (sat_cons (step5 p h) (sat_nil p)))
def c1184 : List Lit := [(15, false), (16, true)]
theorem step1184 (p : Nat → Bool) (h : Constraints p) : clause p c1184 = true :=
  Snake9.LocalRup.prove_clause [c454, c27] c1184 (by decide) p (sat_cons (step454 p h) (sat_cons (step27 p h) (sat_nil p)))
def c1185 : List Lit := [(27, true), (20, true), (22, true), (18, false)]
theorem step1185 (p : Nat → Bool) (h : Constraints p) : clause p c1185 = true :=
  Snake9.LocalRup.prove_clause [c455, c34] c1185 (by decide) p (sat_cons (step455 p h) (sat_cons (step34 p h) (sat_nil p)))
def c1186 : List Lit := [(23, true), (79, true), (20, true), (19, false)]
theorem step1186 (p : Nat → Bool) (h : Constraints p) : clause p c1186 = true :=
  Snake9.LocalRup.prove_clause [c456, c38] c1186 (by decide) p (sat_cons (step456 p h) (sat_cons (step38 p h) (sat_nil p)))
def c1187 : List Lit := [(1, true), (23, true), (19, false), (20, true)]
theorem step1187 (p : Nat → Bool) (h : Constraints p) : clause p c1187 = true :=
  Snake9.LocalRup.prove_clause [c456, c39] c1187 (by decide) p (sat_cons (step456 p h) (sat_cons (step39 p h) (sat_nil p)))
def c1188 : List Lit := [(82, true), (21, false), (22, true)]
theorem step1188 (p : Nat → Bool) (h : Constraints p) : clause p c1188 = true :=
  Snake9.LocalRup.prove_clause [c457, c48] c1188 (by decide) p (sat_cons (step457 p h) (sat_cons (step48 p h) (sat_nil p)))
def c1189 : List Lit := [(17, true), (82, true), (21, false)]
theorem step1189 (p : Nat → Bool) (h : Constraints p) : clause p c1189 = true :=
  Snake9.LocalRup.prove_clause [c457, c49] c1189 (by decide) p (sat_cons (step457 p h) (sat_cons (step49 p h) (sat_nil p)))
def c1190 : List Lit := [(17, true), (21, false), (22, true)]
theorem step1190 (p : Nat → Bool) (h : Constraints p) : clause p c1190 = true :=
  Snake9.LocalRup.prove_clause [c457, c50] c1190 (by decide) p (sat_cons (step457 p h) (sat_cons (step50 p h) (sat_nil p)))
def c1191 : List Lit := [(23, true), (20, true), (24, false), (22, true)]
theorem step1191 (p : Nat → Bool) (h : Constraints p) : clause p c1191 = true :=
  Snake9.LocalRup.prove_clause [c458, c59] c1191 (by decide) p (sat_cons (step458 p h) (sat_cons (step59 p h) (sat_nil p)))
def c1192 : List Lit := [(26, false), (27, true)]
theorem step1192 (p : Nat → Bool) (h : Constraints p) : clause p c1192 = true :=
  Snake9.LocalRup.prove_clause [c459, c61] c1192 (by decide) p (sat_cons (step459 p h) (sat_cons (step61 p h) (sat_nil p)))
def c1193 : List Lit := [(30, true), (29, false), (46, true)]
theorem step1193 (p : Nat → Bool) (h : Constraints p) : clause p c1193 = true :=
  Snake9.LocalRup.prove_clause [c460, c64] c1193 (by decide) p (sat_cons (step460 p h) (sat_cons (step64 p h) (sat_nil p)))
def c1194 : List Lit := [(25, true), (29, false), (46, true)]
theorem step1194 (p : Nat → Bool) (h : Constraints p) : clause p c1194 = true :=
  Snake9.LocalRup.prove_clause [c460, c65] c1194 (by decide) p (sat_cons (step460 p h) (sat_cons (step65 p h) (sat_nil p)))
def c1195 : List Lit := [(31, false), (32, true)]
theorem step1195 (p : Nat → Bool) (h : Constraints p) : clause p c1195 = true :=
  Snake9.LocalRup.prove_clause [c461, c67] c1195 (by decide) p (sat_cons (step461 p h) (sat_cons (step67 p h) (sat_nil p)))
def c1196 : List Lit := [(98, true), (34, false), (38, true)]
theorem step1196 (p : Nat → Bool) (h : Constraints p) : clause p c1196 = true :=
  Snake9.LocalRup.prove_clause [c462, c73] c1196 (by decide) p (sat_cons (step462 p h) (sat_cons (step73 p h) (sat_nil p)))
def c1197 : List Lit := [(33, true), (98, true), (34, false)]
theorem step1197 (p : Nat → Bool) (h : Constraints p) : clause p c1197 = true :=
  Snake9.LocalRup.prove_clause [c462, c74] c1197 (by decide) p (sat_cons (step462 p h) (sat_cons (step74 p h) (sat_nil p)))
def c1198 : List Lit := [(33, true), (34, false), (38, true)]
theorem step1198 (p : Nat → Bool) (h : Constraints p) : clause p c1198 = true :=
  Snake9.LocalRup.prove_clause [c462, c75] c1198 (by decide) p (sat_cons (step462 p h) (sat_cons (step75 p h) (sat_nil p)))
def c1199 : List Lit := [(100, true), (33, true), (35, false), (36, true)]
theorem step1199 (p : Nat → Bool) (h : Constraints p) : clause p c1199 = true :=
  Snake9.LocalRup.prove_clause [c463, c77] c1199 (by decide) p (sat_cons (step463 p h) (sat_cons (step77 p h) (sat_nil p)))
def c1200 : List Lit := [(36, true), (45, true), (37, false), (20, true), (101, true)]
theorem step1200 (p : Nat → Bool) (h : Constraints p) : clause p c1200 = true :=
  Snake9.LocalRup.prove_clause [c464, c85] c1200 (by decide) p (sat_cons (step464 p h) (sat_cons (step85 p h) (sat_nil p)))
def c1201 : List Lit := [(20, true), (36, true), (5, true), (37, false), (101, true)]
theorem step1201 (p : Nat → Bool) (h : Constraints p) : clause p c1201 = true :=
  Snake9.LocalRup.prove_clause [c464, c86] c1201 (by decide) p (sat_cons (step464 p h) (sat_cons (step86 p h) (sat_nil p)))
def c1202 : List Lit := [(45, true), (36, true), (20, true), (37, false), (5, true)]
theorem step1202 (p : Nat → Bool) (h : Constraints p) : clause p c1202 = true :=
  Snake9.LocalRup.prove_clause [c464, c87] c1202 (by decide) p (sat_cons (step464 p h) (sat_cons (step87 p h) (sat_nil p)))
def c1203 : List Lit := [(103, true), (49, true), (38, true), (39, false)]
theorem step1203 (p : Nat → Bool) (h : Constraints p) : clause p c1203 = true :=
  Snake9.LocalRup.prove_clause [c465, c90] c1203 (by decide) p (sat_cons (step465 p h) (sat_cons (step90 p h) (sat_nil p)))
def c1204 : List Lit := [(103, true), (49, true), (39, false), (22, true)]
theorem step1204 (p : Nat → Bool) (h : Constraints p) : clause p c1204 = true :=
  Snake9.LocalRup.prove_clause [c465, c91] c1204 (by decide) p (sat_cons (step465 p h) (sat_cons (step91 p h) (sat_nil p)))
def c1205 : List Lit := [(103, true), (38, true), (39, false), (22, true)]
theorem step1205 (p : Nat → Bool) (h : Constraints p) : clause p c1205 = true :=
  Snake9.LocalRup.prove_clause [c465, c92] c1205 (by decide) p (sat_cons (step465 p h) (sat_cons (step92 p h) (sat_nil p)))
def c1206 : List Lit := [(49, true), (38, true), (39, false), (22, true)]
theorem step1206 (p : Nat → Bool) (h : Constraints p) : clause p c1206 = true :=
  Snake9.LocalRup.prove_clause [c465, c93] c1206 (by decide) p (sat_cons (step465 p h) (sat_cons (step93 p h) (sat_nil p)))
def c1207 : List Lit := [(40, true), (105, true), (41, false)]
theorem step1207 (p : Nat → Bool) (h : Constraints p) : clause p c1207 = true :=
  Snake9.LocalRup.prove_clause [c466, c97] c1207 (by decide) p (sat_cons (step466 p h) (sat_cons (step97 p h) (sat_nil p)))
def c1208 : List Lit := [(105, true), (41, false), (36, true)]
theorem step1208 (p : Nat → Bool) (h : Constraints p) : clause p c1208 = true :=
  Snake9.LocalRup.prove_clause [c466, c98] c1208 (by decide) p (sat_cons (step466 p h) (sat_cons (step98 p h) (sat_nil p)))
def c1209 : List Lit := [(40, true), (41, false), (36, true)]
theorem step1209 (p : Nat → Bool) (h : Constraints p) : clause p c1209 = true :=
  Snake9.LocalRup.prove_clause [c466, c99] c1209 (by decide) p (sat_cons (step466 p h) (sat_cons (step99 p h) (sat_nil p)))
def c1210 : List Lit := [(36, true), (42, true), (43, false)]
theorem step1210 (p : Nat → Bool) (h : Constraints p) : clause p c1210 = true :=
  Snake9.LocalRup.prove_clause [c467, c104] c1210 (by decide) p (sat_cons (step467 p h) (sat_cons (step104 p h) (sat_nil p)))
def c1211 : List Lit := [(50, true), (112, true), (44, false)]
theorem step1211 (p : Nat → Bool) (h : Constraints p) : clause p c1211 = true :=
  Snake9.LocalRup.prove_clause [c468, c105] c1211 (by decide) p (sat_cons (step468 p h) (sat_cons (step105 p h) (sat_nil p)))
def c1212 : List Lit := [(45, true), (112, true), (44, false)]
theorem step1212 (p : Nat → Bool) (h : Constraints p) : clause p c1212 = true :=
  Snake9.LocalRup.prove_clause [c468, c106] c1212 (by decide) p (sat_cons (step468 p h) (sat_cons (step106 p h) (sat_nil p)))
def c1213 : List Lit := [(50, true), (45, true), (44, false)]
theorem step1213 (p : Nat → Bool) (h : Constraints p) : clause p c1213 = true :=
  Snake9.LocalRup.prove_clause [c468, c107] c1213 (by decide) p (sat_cons (step468 p h) (sat_cons (step107 p h) (sat_nil p)))
def c1214 : List Lit := [(49, true), (46, true), (47, false)]
theorem step1214 (p : Nat → Bool) (h : Constraints p) : clause p c1214 = true :=
  Snake9.LocalRup.prove_clause [c469, c115] c1214 (by decide) p (sat_cons (step469 p h) (sat_cons (step115 p h) (sat_nil p)))
def c1215 : List Lit := [(42, true), (49, true), (47, false)]
theorem step1215 (p : Nat → Bool) (h : Constraints p) : clause p c1215 = true :=
  Snake9.LocalRup.prove_clause [c469, c116] c1215 (by decide) p (sat_cons (step469 p h) (sat_cons (step116 p h) (sat_nil p)))
def c1216 : List Lit := [(42, true), (46, true), (47, false)]
theorem step1216 (p : Nat → Bool) (h : Constraints p) : clause p c1216 = true :=
  Snake9.LocalRup.prove_clause [c469, c117] c1216 (by decide) p (sat_cons (step469 p h) (sat_cons (step117 p h) (sat_nil p)))
def c1217 : List Lit := [(50, true), (49, true), (48, false), (38, true)]
theorem step1217 (p : Nat → Bool) (h : Constraints p) : clause p c1217 = true :=
  Snake9.LocalRup.prove_clause [c470, c121] c1217 (by decide) p (sat_cons (step470 p h) (sat_cons (step121 p h) (sat_nil p)))
def c1218 : List Lit := [(1, true), (79, true), (51, false)]
theorem step1218 (p : Nat → Bool) (h : Constraints p) : clause p c1218 = true :=
  Snake9.LocalRup.prove_clause [c471, c125] c1218 (by decide) p (sat_cons (step471 p h) (sat_cons (step125 p h) (sat_nil p)))
def c1219 : List Lit := [(54, false), (55, true)]
theorem step1219 (p : Nat → Bool) (h : Constraints p) : clause p c1219 = true :=
  Snake9.LocalRup.prove_clause [c472, c126] c1219 (by decide) p (sat_cons (step472 p h) (sat_cons (step126 p h) (sat_nil p)))
def c1220 : List Lit := [(64, true), (98, true), (60, false)]
theorem step1220 (p : Nat → Bool) (h : Constraints p) : clause p c1220 = true :=
  Snake9.LocalRup.prove_clause [c473, c135] c1220 (by decide) p (sat_cons (step473 p h) (sat_cons (step135 p h) (sat_nil p)))
def c1221 : List Lit := [(59, true), (98, true), (60, false)]
theorem step1221 (p : Nat → Bool) (h : Constraints p) : clause p c1221 = true :=
  Snake9.LocalRup.prove_clause [c473, c136] c1221 (by decide) p (sat_cons (step473 p h) (sat_cons (step136 p h) (sat_nil p)))
def c1222 : List Lit := [(59, true), (64, true), (60, false)]
theorem step1222 (p : Nat → Bool) (h : Constraints p) : clause p c1222 = true :=
  Snake9.LocalRup.prove_clause [c473, c137] c1222 (by decide) p (sat_cons (step473 p h) (sat_cons (step137 p h) (sat_nil p)))
def c1223 : List Lit := [(65, true), (68, true), (61, false), (100, true)]
theorem step1223 (p : Nat → Bool) (h : Constraints p) : clause p c1223 = true :=
  Snake9.LocalRup.prove_clause [c474, c138] c1223 (by decide) p (sat_cons (step474 p h) (sat_cons (step138 p h) (sat_nil p)))
def c1224 : List Lit := [(59, true), (68, true), (61, false), (100, true)]
theorem step1224 (p : Nat → Bool) (h : Constraints p) : clause p c1224 = true :=
  Snake9.LocalRup.prove_clause [c474, c139] c1224 (by decide) p (sat_cons (step474 p h) (sat_cons (step139 p h) (sat_nil p)))
def c1225 : List Lit := [(101, true), (71, true), (62, false)]
theorem step1225 (p : Nat → Bool) (h : Constraints p) : clause p c1225 = true :=
  Snake9.LocalRup.prove_clause [c475, c140] c1225 (by decide) p (sat_cons (step475 p h) (sat_cons (step140 p h) (sat_nil p)))
def c1226 : List Lit := [(5, true), (101, true), (62, false)]
theorem step1226 (p : Nat → Bool) (h : Constraints p) : clause p c1226 = true :=
  Snake9.LocalRup.prove_clause [c475, c141] c1226 (by decide) p (sat_cons (step475 p h) (sat_cons (step141 p h) (sat_nil p)))
def c1227 : List Lit := [(5, true), (71, true), (62, false)]
theorem step1227 (p : Nat → Bool) (h : Constraints p) : clause p c1227 = true :=
  Snake9.LocalRup.prove_clause [c475, c142] c1227 (by decide) p (sat_cons (step475 p h) (sat_cons (step142 p h) (sat_nil p)))
end B112E096
