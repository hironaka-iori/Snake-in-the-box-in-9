import B112E169Inputs
namespace B112E169
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1134 : List Lit := [(42, false), (22, false), (44, false)]
theorem step1134 (p : Nat → Bool) (h : Constraints p) : clause p c1134 = true :=
  Snake9.LocalRup.prove_clause [c27, c226] c1134 (by decide) p (sat_cons (step27 p h) (sat_cons (step226 p h) (sat_nil p)))
def c1135 : List Lit := [(42, false), (32, false), (44, false)]
theorem step1135 (p : Nat → Bool) (h : Constraints p) : clause p c1135 = true :=
  Snake9.LocalRup.prove_clause [c27, c227] c1135 (by decide) p (sat_cons (step27 p h) (sat_cons (step227 p h) (sat_nil p)))
def c1136 : List Lit := [(42, false), (44, false), (47, false)]
theorem step1136 (p : Nat → Bool) (h : Constraints p) : clause p c1136 = true :=
  Snake9.LocalRup.prove_clause [c27, c228] c1136 (by decide) p (sat_cons (step27 p h) (sat_cons (step228 p h) (sat_nil p)))
def c1137 : List Lit := [(42, false), (44, false), (108, false)]
theorem step1137 (p : Nat → Bool) (h : Constraints p) : clause p c1137 = true :=
  Snake9.LocalRup.prove_clause [c27, c229] c1137 (by decide) p (sat_cons (step27 p h) (sat_cons (step229 p h) (sat_nil p)))
def c1138 : List Lit := [(42, false), (47, false), (108, false)]
theorem step1138 (p : Nat → Bool) (h : Constraints p) : clause p c1138 = true :=
  Snake9.LocalRup.prove_clause [c27, c230] c1138 (by decide) p (sat_cons (step27 p h) (sat_cons (step230 p h) (sat_nil p)))
def c1139 : List Lit := [(1, false)]
theorem step1139 (p : Nat → Bool) (h : Constraints p) : clause p c1139 = true :=
  Snake9.LocalRup.prove_clause [c434, c1] c1139 (by decide) p (sat_cons (step434 p h) (sat_cons (step1 p h) (sat_nil p)))
def c1140 : List Lit := [(58, false)]
theorem step1140 (p : Nat → Bool) (h : Constraints p) : clause p c1140 = true :=
  Snake9.LocalRup.prove_clause [c457, c291] c1140 (by decide) p (sat_cons (step457 p h) (sat_cons (step291 p h) (sat_nil p)))
def c1141 : List Lit := [(61, false)]
theorem step1141 (p : Nat → Bool) (h : Constraints p) : clause p c1141 = true :=
  Snake9.LocalRup.prove_clause [c459, c298] c1141 (by decide) p (sat_cons (step459 p h) (sat_cons (step298 p h) (sat_nil p)))
def c1142 : List Lit := [(458, false)]
theorem step1142 (p : Nat → Bool) (h : Constraints p) : clause p c1142 = true :=
  Snake9.LocalRup.prove_clause [c689, c686] c1142 (by decide) p (sat_cons (step689 p h) (sat_cons (step686 p h) (sat_nil p)))
def c1143 : List Lit := [(344, false)]
theorem step1143 (p : Nat → Bool) (h : Constraints p) : clause p c1143 = true :=
  Snake9.LocalRup.prove_clause [c689, c688] c1143 (by decide) p (sat_cons (step689 p h) (sat_cons (step688 p h) (sat_nil p)))
def c1144 : List Lit := [(456, false)]
theorem step1144 (p : Nat → Bool) (h : Constraints p) : clause p c1144 = true :=
  Snake9.LocalRup.prove_clause [c1142, c682] c1144 (by decide) p (sat_cons (step1142 p h) (sat_cons (step682 p h) (sat_nil p)))
def c1145 : List Lit := [(400, false)]
theorem step1145 (p : Nat → Bool) (h : Constraints p) : clause p c1145 = true :=
  Snake9.LocalRup.prove_clause [c1142, c685] c1145 (by decide) p (sat_cons (step1142 p h) (sat_cons (step685 p h) (sat_nil p)))
def c1146 : List Lit := [(342, false)]
theorem step1146 (p : Nat → Bool) (h : Constraints p) : clause p c1146 = true :=
  Snake9.LocalRup.prove_clause [c1143, c588] c1146 (by decide) p (sat_cons (step1143 p h) (sat_cons (step588 p h) (sat_nil p)))
def c1147 : List Lit := [(286, false)]
theorem step1147 (p : Nat → Bool) (h : Constraints p) : clause p c1147 = true :=
  Snake9.LocalRup.prove_clause [c1143, c591] c1147 (by decide) p (sat_cons (step1143 p h) (sat_cons (step591 p h) (sat_nil p)))
def c1148 : List Lit := [(454, false)]
theorem step1148 (p : Nat → Bool) (h : Constraints p) : clause p c1148 = true :=
  Snake9.LocalRup.prove_clause [c1144, c677] c1148 (by decide) p (sat_cons (step1144 p h) (sat_cons (step677 p h) (sat_nil p)))
def c1149 : List Lit := [(426, false)]
theorem step1149 (p : Nat → Bool) (h : Constraints p) : clause p c1149 = true :=
  Snake9.LocalRup.prove_clause [c1144, c680] c1149 (by decide) p (sat_cons (step1144 p h) (sat_cons (step680 p h) (sat_nil p)))
def c1150 : List Lit := [(370, false)]
theorem step1150 (p : Nat → Bool) (h : Constraints p) : clause p c1150 = true :=
  Snake9.LocalRup.prove_clause [c1145, c626] c1150 (by decide) p (sat_cons (step1145 p h) (sat_cons (step626 p h) (sat_nil p)))
def c1151 : List Lit := [(340, false)]
theorem step1151 (p : Nat → Bool) (h : Constraints p) : clause p c1151 = true :=
  Snake9.LocalRup.prove_clause [c1146, c583] c1151 (by decide) p (sat_cons (step1146 p h) (sat_cons (step583 p h) (sat_nil p)))
def c1152 : List Lit := [(312, false)]
theorem step1152 (p : Nat → Bool) (h : Constraints p) : clause p c1152 = true :=
  Snake9.LocalRup.prove_clause [c1146, c586] c1152 (by decide) p (sat_cons (step1146 p h) (sat_cons (step586 p h) (sat_nil p)))
def c1153 : List Lit := [(284, false)]
theorem step1153 (p : Nat → Bool) (h : Constraints p) : clause p c1153 = true :=
  Snake9.LocalRup.prove_clause [c1147, c532] c1153 (by decide) p (sat_cons (step1147 p h) (sat_cons (step532 p h) (sat_nil p)))
def c1154 : List Lit := [(258, false)]
theorem step1154 (p : Nat → Bool) (h : Constraints p) : clause p c1154 = true :=
  Snake9.LocalRup.prove_clause [c1147, c535] c1154 (by decide) p (sat_cons (step1147 p h) (sat_cons (step535 p h) (sat_nil p)))
def c1155 : List Lit := [(452, false)]
theorem step1155 (p : Nat → Bool) (h : Constraints p) : clause p c1155 = true :=
  Snake9.LocalRup.prove_clause [c1148, c672] c1155 (by decide) p (sat_cons (step1148 p h) (sat_cons (step672 p h) (sat_nil p)))
def c1156 : List Lit := [(438, false)]
theorem step1156 (p : Nat → Bool) (h : Constraints p) : clause p c1156 = true :=
  Snake9.LocalRup.prove_clause [c1148, c675] c1156 (by decide) p (sat_cons (step1148 p h) (sat_cons (step675 p h) (sat_nil p)))
def c1157 : List Lit := [(412, false)]
theorem step1157 (p : Nat → Bool) (h : Constraints p) : clause p c1157 = true :=
  Snake9.LocalRup.prove_clause [c1149, c648] c1157 (by decide) p (sat_cons (step1149 p h) (sat_cons (step648 p h) (sat_nil p)))
def c1158 : List Lit := [(338, false)]
theorem step1158 (p : Nat → Bool) (h : Constraints p) : clause p c1158 = true :=
  Snake9.LocalRup.prove_clause [c1151, c578] c1158 (by decide) p (sat_cons (step1151 p h) (sat_cons (step578 p h) (sat_nil p)))
def c1159 : List Lit := [(324, false)]
theorem step1159 (p : Nat → Bool) (h : Constraints p) : clause p c1159 = true :=
  Snake9.LocalRup.prove_clause [c1151, c581] c1159 (by decide) p (sat_cons (step1151 p h) (sat_cons (step581 p h) (sat_nil p)))
def c1160 : List Lit := [(310, false)]
theorem step1160 (p : Nat → Bool) (h : Constraints p) : clause p c1160 = true :=
  Snake9.LocalRup.prove_clause [c1152, c551] c1160 (by decide) p (sat_cons (step1152 p h) (sat_cons (step551 p h) (sat_nil p)))
def c1161 : List Lit := [(282, false)]
theorem step1161 (p : Nat → Bool) (h : Constraints p) : clause p c1161 = true :=
  Snake9.LocalRup.prove_clause [c1153, c527] c1161 (by decide) p (sat_cons (step1153 p h) (sat_cons (step527 p h) (sat_nil p)))
def c1162 : List Lit := [(270, false)]
theorem step1162 (p : Nat → Bool) (h : Constraints p) : clause p c1162 = true :=
  Snake9.LocalRup.prove_clause [c1153, c530] c1162 (by decide) p (sat_cons (step1153 p h) (sat_cons (step530 p h) (sat_nil p)))
def c1163 : List Lit := [(256, false)]
theorem step1163 (p : Nat → Bool) (h : Constraints p) : clause p c1163 = true :=
  Snake9.LocalRup.prove_clause [c1154, c498] c1163 (by decide) p (sat_cons (step1154 p h) (sat_cons (step498 p h) (sat_nil p)))
def c1164 : List Lit := [(244, false)]
theorem step1164 (p : Nat → Bool) (h : Constraints p) : clause p c1164 = true :=
  Snake9.LocalRup.prove_clause [c1154, c501] c1164 (by decide) p (sat_cons (step1154 p h) (sat_cons (step501 p h) (sat_nil p)))
def c1165 : List Lit := [(444, false)]
theorem step1165 (p : Nat → Bool) (h : Constraints p) : clause p c1165 = true :=
  Snake9.LocalRup.prove_clause [c1155, c670] c1165 (by decide) p (sat_cons (step1155 p h) (sat_cons (step670 p h) (sat_nil p)))
def c1166 : List Lit := [(430, false)]
theorem step1166 (p : Nat → Bool) (h : Constraints p) : clause p c1166 = true :=
  Snake9.LocalRup.prove_clause [c1156, c658] c1166 (by decide) p (sat_cons (step1156 p h) (sat_cons (step658 p h) (sat_nil p)))
def c1167 : List Lit := [(410, false)]
theorem step1167 (p : Nat → Bool) (h : Constraints p) : clause p c1167 = true :=
  Snake9.LocalRup.prove_clause [c1157, c636] c1167 (by decide) p (sat_cons (step1157 p h) (sat_cons (step636 p h) (sat_nil p)))
def c1168 : List Lit := [(336, false)]
theorem step1168 (p : Nat → Bool) (h : Constraints p) : clause p c1168 = true :=
  Snake9.LocalRup.prove_clause [c1158, c574] c1168 (by decide) p (sat_cons (step1158 p h) (sat_cons (step574 p h) (sat_nil p)))
def c1169 : List Lit := [(316, false)]
theorem step1169 (p : Nat → Bool) (h : Constraints p) : clause p c1169 = true :=
  Snake9.LocalRup.prove_clause [c1159, c564] c1169 (by decide) p (sat_cons (step1159 p h) (sat_cons (step564 p h) (sat_nil p)))
def c1170 : List Lit := [(308, false)]
theorem step1170 (p : Nat → Bool) (h : Constraints p) : clause p c1170 = true :=
  Snake9.LocalRup.prove_clause [c1160, c548] c1170 (by decide) p (sat_cons (step1160 p h) (sat_cons (step548 p h) (sat_nil p)))
def c1171 : List Lit := [(274, false)]
theorem step1171 (p : Nat → Bool) (h : Constraints p) : clause p c1171 = true :=
  Snake9.LocalRup.prove_clause [c1161, c525] c1171 (by decide) p (sat_cons (step1161 p h) (sat_cons (step525 p h) (sat_nil p)))
def c1172 : List Lit := [(262, false)]
theorem step1172 (p : Nat → Bool) (h : Constraints p) : clause p c1172 = true :=
  Snake9.LocalRup.prove_clause [c1162, c514] c1172 (by decide) p (sat_cons (step1162 p h) (sat_cons (step514 p h) (sat_nil p)))
def c1173 : List Lit := [(248, false)]
theorem step1173 (p : Nat → Bool) (h : Constraints p) : clause p c1173 = true :=
  Snake9.LocalRup.prove_clause [c1163, c496] c1173 (by decide) p (sat_cons (step1163 p h) (sat_cons (step496 p h) (sat_nil p)))
def c1174 : List Lit := [(242, false)]
theorem step1174 (p : Nat → Bool) (h : Constraints p) : clause p c1174 = true :=
  Snake9.LocalRup.prove_clause [c1164, c484] c1174 (by decide) p (sat_cons (step1164 p h) (sat_cons (step484 p h) (sat_nil p)))
def c1175 : List Lit := [(408, false)]
theorem step1175 (p : Nat → Bool) (h : Constraints p) : clause p c1175 = true :=
  Snake9.LocalRup.prove_clause [c1167, c633] c1175 (by decide) p (sat_cons (step1167 p h) (sat_cons (step633 p h) (sat_nil p)))
def c1176 : List Lit := [(314, false)]
theorem step1176 (p : Nat → Bool) (h : Constraints p) : clause p c1176 = true :=
  Snake9.LocalRup.prove_clause [c1169, c558] c1176 (by decide) p (sat_cons (step1169 p h) (sat_cons (step558 p h) (sat_nil p)))
def c1177 : List Lit := [(272, false)]
theorem step1177 (p : Nat → Bool) (h : Constraints p) : clause p c1177 = true :=
  Snake9.LocalRup.prove_clause [c1171, c519] c1177 (by decide) p (sat_cons (step1171 p h) (sat_cons (step519 p h) (sat_nil p)))
def c1178 : List Lit := [(260, false)]
theorem step1178 (p : Nat → Bool) (h : Constraints p) : clause p c1178 = true :=
  Snake9.LocalRup.prove_clause [c1172, c506] c1178 (by decide) p (sat_cons (step1172 p h) (sat_cons (step506 p h) (sat_nil p)))
def c1179 : List Lit := [(238, false)]
theorem step1179 (p : Nat → Bool) (h : Constraints p) : clause p c1179 = true :=
  Snake9.LocalRup.prove_clause [c1174, c482] c1179 (by decide) p (sat_cons (step1174 p h) (sat_cons (step482 p h) (sat_nil p)))
def c1180 : List Lit := [(1566, true)]
theorem step1180 (p : Nat → Bool) (h : Constraints p) : clause p c1180 = true :=
  Snake9.LocalRup.prove_clause [c992, c995, c988, c963, c974, c976, c958, c971, c972, c956, c308, c313, c309] c1180 (by decide) p (sat_cons (step992 p h) (sat_cons (step995 p h) (sat_cons (step988 p h) (sat_cons (step963 p h) (sat_cons (step974 p h) (sat_cons (step976 p h) (sat_cons (step958 p h) (sat_cons (step971 p h) (sat_cons (step972 p h) (sat_cons (step956 p h) (sat_cons (step308 p h) (sat_cons (step313 p h) (sat_cons (step309 p h) (sat_nil p))))))))))))))
def c1181 : List Lit := [(69, false), (1548, true)]
theorem step1181 (p : Nat → Bool) (h : Constraints p) : clause p c1181 = true :=
  Snake9.LocalRup.prove_clause [c974, c972, c971, c976, c308, c313, c309] c1181 (by decide) p (sat_cons (step974 p h) (sat_cons (step972 p h) (sat_cons (step971 p h) (sat_cons (step976 p h) (sat_cons (step308 p h) (sat_cons (step313 p h) (sat_cons (step309 p h) (sat_nil p))))))))
def c1182 : List Lit := [(1559, true), (1536, true)]
theorem step1182 (p : Nat → Bool) (h : Constraints p) : clause p c1182 = true :=
  Snake9.LocalRup.prove_clause [c1150, c959, c986, c988, c982, c984, c980, c977, c1181, c956, c957, c961, c952, c953, c311, c302, c307, c305, c599, c594, c600, c595, c604, c597, c607] c1182 (by decide) p (sat_cons (step1150 p h) (sat_cons (step959 p h) (sat_cons (step986 p h) (sat_cons (step988 p h) (sat_cons (step982 p h) (sat_cons (step984 p h) (sat_cons (step980 p h) (sat_cons (step977 p h) (sat_cons (step1181 p h) (sat_cons (step956 p h) (sat_cons (step957 p h) (sat_cons (step961 p h) (sat_cons (step952 p h) (sat_cons (step953 p h) (sat_cons (step311 p h) (sat_cons (step302 p h) (sat_cons (step307 p h) (sat_cons (step305 p h) (sat_cons (step599 p h) (sat_cons (step594 p h) (sat_cons (step600 p h) (sat_cons (step595 p h) (sat_cons (step604 p h) (sat_cons (step597 p h) (sat_cons (step607 p h) (sat_nil p))))))))))))))))))))))))))
def c1183 : List Lit := [(1567, true)]
theorem step1183 (p : Nat → Bool) (h : Constraints p) : clause p c1183 = true :=
  Snake9.LocalRup.prove_clause [c1150, c993, c998, c964, c1182, c996, c963, c958, c960, c955, c956, c952, c953, c1181, c989, c982, c984, c980, c977, c302, c311, c307, c305, c599, c594, c600, c595, c604, c597, c607] c1183 (by decide) p (sat_cons (step1150 p h) (sat_cons (step993 p h) (sat_cons (step998 p h) (sat_cons (step964 p h) (sat_cons (step1182 p h) (sat_cons (step996 p h) (sat_cons (step963 p h) (sat_cons (step958 p h) (sat_cons (step960 p h) (sat_cons (step955 p h) (sat_cons (step956 p h) (sat_cons (step952 p h) (sat_cons (step953 p h) (sat_cons (step1181 p h) (sat_cons (step989 p h) (sat_cons (step982 p h) (sat_cons (step984 p h) (sat_cons (step980 p h) (sat_cons (step977 p h) (sat_cons (step302 p h) (sat_cons (step311 p h) (sat_cons (step307 p h) (sat_cons (step305 p h) (sat_cons (step599 p h) (sat_cons (step594 p h) (sat_cons (step600 p h) (sat_cons (step595 p h) (sat_cons (step604 p h) (sat_cons (step597 p h) (sat_cons (step607 p h) (sat_nil p)))))))))))))))))))))))))))))))
def c1184 : List Lit := [(1531, true), (1555, true), (70, false)]
theorem step1184 (p : Nat → Bool) (h : Constraints p) : clause p c1184 = true :=
  Snake9.LocalRup.prove_clause [c1150, c984, c977, c982, c980, c952, c953, c311, c302, c307, c305, c599, c594, c600, c595, c604, c597, c607] c1184 (by decide) p (sat_cons (step1150 p h) (sat_cons (step984 p h) (sat_cons (step977 p h) (sat_cons (step982 p h) (sat_cons (step980 p h) (sat_cons (step952 p h) (sat_cons (step953 p h) (sat_cons (step311 p h) (sat_cons (step302 p h) (sat_cons (step307 p h) (sat_cons (step305 p h) (sat_cons (step599 p h) (sat_cons (step594 p h) (sat_cons (step600 p h) (sat_cons (step595 p h) (sat_cons (step604 p h) (sat_cons (step597 p h) (sat_cons (step607 p h) (sat_nil p)))))))))))))))))))
def c1185 : List Lit := [(1441, true)]
theorem step1185 (p : Nat → Bool) (h : Constraints p) : clause p c1185 = true :=
  Snake9.LocalRup.prove_clause [c766, c769, c752, c712, c745, c747, c704, c743, c739, c740, c701, c702, c94, c86, c96, c51] c1185 (by decide) p (sat_cons (step766 p h) (sat_cons (step769 p h) (sat_cons (step752 p h) (sat_cons (step712 p h) (sat_cons (step745 p h) (sat_cons (step747 p h) (sat_cons (step704 p h) (sat_cons (step743 p h) (sat_cons (step739 p h) (sat_cons (step740 p h) (sat_cons (step701 p h) (sat_cons (step702 p h) (sat_cons (step94 p h) (sat_cons (step86 p h) (sat_cons (step96 p h) (sat_cons (step51 p h) (sat_nil p)))))))))))))))))
def c1186 : List Lit := [(52, false), (55, false), (57, false)]
theorem step1186 (p : Nat → Bool) (h : Constraints p) : clause p c1186 = true :=
  Snake9.LocalRup.prove_clause [c1168, c284, c290, c282, c569, c568, c572] c1186 (by decide) p (sat_cons (step1168 p h) (sat_cons (step284 p h) (sat_cons (step290 p h) (sat_cons (step282 p h) (sat_cons (step569 p h) (sat_cons (step568 p h) (sat_cons (step572 p h) (sat_nil p))))))))
def c1187 : List Lit := [(1482, true), (57, false)]
theorem step1187 (p : Nat → Bool) (h : Constraints p) : clause p c1187 = true :=
  Snake9.LocalRup.prove_clause [c851, c852, c1186] c1187 (by decide) p (sat_cons (step851 p h) (sat_cons (step852 p h) (sat_cons (step1186 p h) (sat_nil p))))
def c1188 : List Lit := [(71, true), (70, false), (62, true), (367, true)]
theorem step1188 (p : Nat → Bool) (h : Constraints p) : clause p c1188 = true :=
  Snake9.LocalRup.prove_clause [c461, c604, c600, c599, c603, c602, c601, c310, c307, c306] c1188 (by decide) p (sat_cons (step461 p h) (sat_cons (step604 p h) (sat_cons (step600 p h) (sat_cons (step599 p h) (sat_cons (step603 p h) (sat_cons (step602 p h) (sat_cons (step601 p h) (sat_cons (step310 p h) (sat_cons (step307 p h) (sat_cons (step306 p h) (sat_nil p)))))))))))
def c1189 : List Lit := [(1444, true), (46, false), (1405, false), (125, true)]
theorem step1189 (p : Nat → Bool) (h : Constraints p) : clause p c1189 = true :=
  Snake9.LocalRup.prove_clause [c726, c787, c782, c727, c755, c706, c736, c698, c173, c23] c1189 (by decide) p (sat_cons (step726 p h) (sat_cons (step787 p h) (sat_cons (step782 p h) (sat_cons (step727 p h) (sat_cons (step755 p h) (sat_cons (step706 p h) (sat_cons (step736 p h) (sat_cons (step698 p h) (sat_cons (step173 p h) (sat_cons (step23 p h) (sat_nil p)))))))))))
def c1190 : List Lit := [(1434, true), (83, false), (140, true)]
theorem step1190 (p : Nat → Bool) (h : Constraints p) : clause p c1190 = true :=
  Snake9.LocalRup.prove_clause [c752, c755, c745, c747, c734, c743, c739, c740, c732, c95, c57, c98] c1190 (by decide) p (sat_cons (step752 p h) (sat_cons (step755 p h) (sat_cons (step745 p h) (sat_cons (step747 p h) (sat_cons (step734 p h) (sat_cons (step743 p h) (sat_cons (step739 p h) (sat_cons (step740 p h) (sat_cons (step732 p h) (sat_cons (step95 p h) (sat_cons (step57 p h) (sat_cons (step98 p h) (sat_nil p)))))))))))))
def c1191 : List Lit := [(1430, true), (18, false), (83, false), (140, true)]
theorem step1191 (p : Nat → Bool) (h : Constraints p) : clause p c1191 = true :=
  Snake9.LocalRup.prove_clause [c745, c747, c743, c739, c740, c57, c95, c98] c1191 (by decide) p (sat_cons (step745 p h) (sat_cons (step747 p h) (sat_cons (step743 p h) (sat_cons (step739 p h) (sat_cons (step740 p h) (sat_cons (step57 p h) (sat_cons (step95 p h) (sat_cons (step98 p h) (sat_nil p)))))))))
def c1192 : List Lit := [(43, false), (44, false), (1471, true), (30, true), (37, true), (45, false)]
theorem step1192 (p : Nat → Bool) (h : Constraints p) : clause p c1192 = true :=
  Snake9.LocalRup.prove_clause [c238, c239, c800, c811, c806, c832, c815, c817, c813, c808, c809, c163, c222, c218] c1192 (by decide) p (sat_cons (step238 p h) (sat_cons (step239 p h) (sat_cons (step800 p h) (sat_cons (step811 p h) (sat_cons (step806 p h) (sat_cons (step832 p h) (sat_cons (step815 p h) (sat_cons (step817 p h) (sat_cons (step813 p h) (sat_cons (step808 p h) (sat_cons (step809 p h) (sat_cons (step163 p h) (sat_cons (step222 p h) (sat_cons (step218 p h) (sat_nil p)))))))))))))))
def c1193 : List Lit := [(42, true), (1465, true), (43, true), (44, false), (37, true)]
theorem step1193 (p : Nat → Bool) (h : Constraints p) : clause p c1193 = true :=
  Snake9.LocalRup.prove_clause [c450, c815, c811, c242, c813, c817, c808, c809, c222, c160, c218] c1193 (by decide) p (sat_cons (step450 p h) (sat_cons (step815 p h) (sat_cons (step811 p h) (sat_cons (step242 p h) (sat_cons (step813 p h) (sat_cons (step817 p h) (sat_cons (step808 p h) (sat_cons (step809 p h) (sat_cons (step222 p h) (sat_cons (step160 p h) (sat_cons (step218 p h) (sat_nil p))))))))))))
def c1194 : List Lit := [(1464, true), (156, true), (37, true)]
theorem step1194 (p : Nat → Bool) (h : Constraints p) : clause p c1194 = true :=
  Snake9.LocalRup.prove_clause [c814, c816, c812, c808, c809, c219, c222] c1194 (by decide) p (sat_cons (step814 p h) (sat_cons (step816 p h) (sat_cons (step812 p h) (sat_cons (step808 p h) (sat_cons (step809 p h) (sat_cons (step219 p h) (sat_cons (step222 p h) (sat_nil p))))))))
def c1195 : List Lit := [(40, false), (1460, true), (156, true), (37, true)]
theorem step1195 (p : Nat → Bool) (h : Constraints p) : clause p c1195 = true :=
  Snake9.LocalRup.prove_clause [c809, c808, c219, c222] c1195 (by decide) p (sat_cons (step809 p h) (sat_cons (step808 p h) (sat_cons (step219 p h) (sat_cons (step222 p h) (sat_nil p)))))
def c1196 : List Lit := [(46, false), (38, false), (42, false), (162, true), (49, false), (37, true)]
theorem step1196 (p : Nat → Bool) (h : Constraints p) : clause p c1196 = true :=
  Snake9.LocalRup.prove_clause [c257, c260, c253] c1196 (by decide) p (sat_cons (step257 p h) (sat_cons (step260 p h) (sat_cons (step253 p h) (sat_nil p))))
def c1197 : List Lit := [(1600, true), (1602, true)]
theorem step1197 (p : Nat → Bool) (h : Constraints p) : clause p c1197 = true :=
  Snake9.LocalRup.prove_clause [c1156, c1046, c1045, c1042, c1043, c397, c402, c387, c401, c651, c653, c657, c654] c1197 (by decide) p (sat_cons (step1156 p h) (sat_cons (step1046 p h) (sat_cons (step1045 p h) (sat_cons (step1042 p h) (sat_cons (step1043 p h) (sat_cons (step397 p h) (sat_cons (step402 p h) (sat_cons (step387 p h) (sat_cons (step401 p h) (sat_cons (step651 p h) (sat_cons (step653 p h) (sat_cons (step657 p h) (sat_cons (step654 p h) (sat_nil p))))))))))))))
end B112E169
