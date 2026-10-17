import B112E152Part0002
namespace B112E152
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1139 : List Lit := [(50, true), (116, false), (1549, true), (1539, false)]
theorem step1139 (p : Nat → Bool) (h : Constraints p) : clause p c1139 = true :=
  Snake9.LocalRup.prove_clause [c420, c1104, c636, c638, c639, c661, c654, c649, c650, c1123, c102, c96] c1139 (by decide) p (sat_cons (step420 p h) (sat_cons (step1104 p h) (sat_cons (step636 p h) (sat_cons (step638 p h) (sat_cons (step639 p h) (sat_cons (step661 p h) (sat_cons (step654 p h) (sat_cons (step649 p h) (sat_cons (step650 p h) (sat_cons (step1123 p h) (sat_cons (step102 p h) (sat_cons (step96 p h) (sat_nil p)))))))))))))
def c1140 : List Lit := [(1500, true), (45, true), (47, false), (114, false)]
theorem step1140 (p : Nat → Bool) (h : Constraints p) : clause p c1140 = true :=
  Snake9.LocalRup.prove_clause [c971, c974, c415, c603, c600, c981, c1013, c979, c964, c578, c583, c584, c569, c45, c559, c557, c22, c79, c80, c926] c1140 (by decide) p (sat_cons (step971 p h) (sat_cons (step974 p h) (sat_cons (step415 p h) (sat_cons (step603 p h) (sat_cons (step600 p h) (sat_cons (step981 p h) (sat_cons (step1013 p h) (sat_cons (step979 p h) (sat_cons (step964 p h) (sat_cons (step578 p h) (sat_cons (step583 p h) (sat_cons (step584 p h) (sat_cons (step569 p h) (sat_cons (step45 p h) (sat_cons (step559 p h) (sat_cons (step557 p h) (sat_cons (step22 p h) (sat_cons (step79 p h) (sat_cons (step80 p h) (sat_cons (step926 p h) (sat_nil p)))))))))))))))))))))
def c1141 : List Lit := [(56, false), (59, false), (57, true), (48, false)]
theorem step1141 (p : Nat → Bool) (h : Constraints p) : clause p c1141 = true :=
  Snake9.LocalRup.prove_clause [c420, c102, c96] c1141 (by decide) p (sat_cons (step420 p h) (sat_cons (step102 p h) (sat_cons (step96 p h) (sat_nil p))))
def c1142 : List Lit := [(1557, true), (44, false), (1539, false)]
theorem step1142 (p : Nat → Bool) (h : Constraints p) : clause p c1142 = true :=
  Snake9.LocalRup.prove_clause [c970, c972, c969, c669, c672, c658, c983, c629, c654, c637, c998, c1015] c1142 (by decide) p (sat_cons (step970 p h) (sat_cons (step972 p h) (sat_cons (step969 p h) (sat_cons (step669 p h) (sat_cons (step672 p h) (sat_cons (step658 p h) (sat_cons (step983 p h) (sat_cons (step629 p h) (sat_cons (step654 p h) (sat_cons (step637 p h) (sat_cons (step998 p h) (sat_cons (step1015 p h) (sat_nil p)))))))))))))
def c1143 : List Lit := [(1500, true), (4, true)]
theorem step1143 (p : Nat → Bool) (h : Constraints p) : clause p c1143 = true :=
  Snake9.LocalRup.prove_clause [c971, c974, c401, c548, c964, c603, c600, c571, c569, c979, c965, c559, c583, c549, c557, c8, c10] c1143 (by decide) p (sat_cons (step971 p h) (sat_cons (step974 p h) (sat_cons (step401 p h) (sat_cons (step548 p h) (sat_cons (step964 p h) (sat_cons (step603 p h) (sat_cons (step600 p h) (sat_cons (step571 p h) (sat_cons (step569 p h) (sat_cons (step979 p h) (sat_cons (step965 p h) (sat_cons (step559 p h) (sat_cons (step583 p h) (sat_cons (step549 p h) (sat_cons (step557 p h) (sat_cons (step8 p h) (sat_cons (step10 p h) (sat_nil p))))))))))))))))))
def c1144 : List Lit := [(1557, true)]
theorem step1144 (p : Nat → Bool) (h : Constraints p) : clause p c1144 = true :=
  Snake9.LocalRup.prove_clause [c970, c972, c969, c669, c672, c983, c627, c629, c637, c1037, c998, c1142, c1014, c1034, c641] c1144 (by decide) p (sat_cons (step970 p h) (sat_cons (step972 p h) (sat_cons (step969 p h) (sat_cons (step669 p h) (sat_cons (step672 p h) (sat_cons (step983 p h) (sat_cons (step627 p h) (sat_cons (step629 p h) (sat_cons (step637 p h) (sat_cons (step1037 p h) (sat_cons (step998 p h) (sat_cons (step1142 p h) (sat_cons (step1014 p h) (sat_cons (step1034 p h) (sat_cons (step641 p h) (sat_nil p))))))))))))))))
def c1145 : List Lit := [(104, false), (107, true), (106, false), (50, false), (1513, true), (1676, false), (1500, true)]
theorem step1145 (p : Nat → Bool) (h : Constraints p) : clause p c1145 = true :=
  Snake9.TreeRup.prove_clause [c407, c405, c412, c410, c404, c400, c971, c411, c974, c986, c600, c979, c583, c610, c608, c612, c584, c52, c44, c56, c57, c603, c981, c964, c569, c561, c554, c1143, c6, c559, c556, c25, c14, c49, c607, c61, c60, c1013, c576, c574, c32, c573, c591, c588, c29, c582, c37, c33, c27, c315, c314, c306, c309, c191, c188, c833, c817, c703, c741, c781, c736, c838, c826, c1018, c787, c746, c852, c811, c752, c773, c908, c881, c875, c812, c856, c795, c797, c827, c793, c789, c1000] c1145 (by decide) p (sat_cons (step407 p h) (sat_cons (step405 p h) (sat_cons (step412 p h) (sat_cons (step410 p h) (sat_cons (step404 p h) (sat_cons (step400 p h) (sat_cons (step971 p h) (sat_cons (step411 p h) (sat_cons (step974 p h) (sat_cons (step986 p h) (sat_cons (step600 p h) (sat_cons (step979 p h) (sat_cons (step583 p h) (sat_cons (step610 p h) (sat_cons (step608 p h) (sat_cons (step612 p h) (sat_cons (step584 p h) (sat_cons (step52 p h) (sat_cons (step44 p h) (sat_cons (step56 p h) (sat_cons (step57 p h) (sat_cons (step603 p h) (sat_cons (step981 p h) (sat_cons (step964 p h) (sat_cons (step569 p h) (sat_cons (step561 p h) (sat_cons (step554 p h) (sat_cons (step1143 p h) (sat_cons (step6 p h) (sat_cons (step559 p h) (sat_cons (step556 p h) (sat_cons (step25 p h) (sat_cons (step14 p h) (sat_cons (step49 p h) (sat_cons (step607 p h) (sat_cons (step61 p h) (sat_cons (step60 p h) (sat_cons (step1013 p h) (sat_cons (step576 p h) (sat_cons (step574 p h) (sat_cons (step32 p h) (sat_cons (step573 p h) (sat_cons (step591 p h) (sat_cons (step588 p h) (sat_cons (step29 p h) (sat_cons (step582 p h) (sat_cons (step37 p h) (sat_cons (step33 p h) (sat_cons (step27 p h) (sat_cons (step315 p h) (sat_cons (step314 p h) (sat_cons (step306 p h) (sat_cons (step309 p h) (sat_cons (step191 p h) (sat_cons (step188 p h) (sat_cons (step833 p h) (sat_cons (step817 p h) (sat_cons (step703 p h) (sat_cons (step741 p h) (sat_cons (step781 p h) (sat_cons (step736 p h) (sat_cons (step838 p h) (sat_cons (step826 p h) (sat_cons (step1018 p h) (sat_cons (step787 p h) (sat_cons (step746 p h) (sat_cons (step852 p h) (sat_cons (step811 p h) (sat_cons (step752 p h) (sat_cons (step773 p h) (sat_cons (step908 p h) (sat_cons (step881 p h) (sat_cons (step875 p h) (sat_cons (step812 p h) (sat_cons (step856 p h) (sat_cons (step795 p h) (sat_cons (step797 p h) (sat_cons (step827 p h) (sat_cons (step793 p h) (sat_cons (step789 p h) (sat_cons (step1000 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1146 : List Lit := [(1670, false), (107, true), (1676, false), (1687, true), (106, false), (50, false)]
theorem step1146 (p : Nat → Bool) (h : Constraints p) : clause p c1146 = true :=
  Snake9.LocalRup.prove_clause [c816, c837, c855, c824, c827, c852, c817, c838, c318, c833] c1146 (by decide) p (sat_cons (step816 p h) (sat_cons (step837 p h) (sat_cons (step855 p h) (sat_cons (step824 p h) (sat_cons (step827 p h) (sat_cons (step852 p h) (sat_cons (step817 p h) (sat_cons (step838 p h) (sat_cons (step318 p h) (sat_cons (step833 p h) (sat_nil p)))))))))))
def c1147 : List Lit := [(2, false), (122, true)]
theorem step1147 (p : Nat → Bool) (h : Constraints p) : clause p c1147 = true :=
  Snake9.LocalRup.prove_clause [c957, c3] c1147 (by decide) p (sat_cons (step957 p h) (sat_cons (step3 p h) (sat_nil p)))
def c1148 : List Lit := [(4, false), (2, true)]
theorem step1148 (p : Nat → Bool) (h : Constraints p) : clause p c1148 = true :=
  Snake9.LocalRup.prove_clause [c400, c5] c1148 (by decide) p (sat_cons (step400 p h) (sat_cons (step5 p h) (sat_nil p)))
def c1149 : List Lit := [(4, false), (1, true)]
theorem step1149 (p : Nat → Bool) (h : Constraints p) : clause p c1149 = true :=
  Snake9.LocalRup.prove_clause [c400, c6] c1149 (by decide) p (sat_cons (step400 p h) (sat_cons (step6 p h) (sat_nil p)))
def c1150 : List Lit := [(6, false), (7, true)]
theorem step1150 (p : Nat → Bool) (h : Constraints p) : clause p c1150 = true :=
  Snake9.LocalRup.prove_clause [c401, c8] c1150 (by decide) p (sat_cons (step401 p h) (sat_cons (step8 p h) (sat_nil p)))
def c1151 : List Lit := [(6, false), (5, true)]
theorem step1151 (p : Nat → Bool) (h : Constraints p) : clause p c1151 = true :=
  Snake9.LocalRup.prove_clause [c401, c9] c1151 (by decide) p (sat_cons (step401 p h) (sat_cons (step9 p h) (sat_nil p)))
def c1152 : List Lit := [(11, false), (19, true), (10, true)]
theorem step1152 (p : Nat → Bool) (h : Constraints p) : clause p c1152 = true :=
  Snake9.LocalRup.prove_clause [c402, c16] c1152 (by decide) p (sat_cons (step402 p h) (sat_cons (step16 p h) (sat_nil p)))
def c1153 : List Lit := [(10, true), (12, true), (11, false)]
theorem step1153 (p : Nat → Bool) (h : Constraints p) : clause p c1153 = true :=
  Snake9.LocalRup.prove_clause [c402, c17] c1153 (by decide) p (sat_cons (step402 p h) (sat_cons (step17 p h) (sat_nil p)))
def c1154 : List Lit := [(7, true), (12, true), (13, false)]
theorem step1154 (p : Nat → Bool) (h : Constraints p) : clause p c1154 = true :=
  Snake9.LocalRup.prove_clause [c403, c24] c1154 (by decide) p (sat_cons (step403 p h) (sat_cons (step24 p h) (sat_nil p)))
def c1155 : List Lit := [(14, false), (15, true)]
theorem step1155 (p : Nat → Bool) (h : Constraints p) : clause p c1155 = true :=
  Snake9.LocalRup.prove_clause [c404, c25] c1155 (by decide) p (sat_cons (step404 p h) (sat_cons (step25 p h) (sat_nil p)))
def c1156 : List Lit := [(20, false), (18, true)]
theorem step1156 (p : Nat → Bool) (h : Constraints p) : clause p c1156 = true :=
  Snake9.LocalRup.prove_clause [c405, c32] c1156 (by decide) p (sat_cons (step405 p h) (sat_cons (step32 p h) (sat_nil p)))
def c1157 : List Lit := [(24, true), (71, true), (21, false)]
theorem step1157 (p : Nat → Bool) (h : Constraints p) : clause p c1157 = true :=
  Snake9.LocalRup.prove_clause [c406, c34] c1157 (by decide) p (sat_cons (step406 p h) (sat_cons (step34 p h) (sat_nil p)))
def c1158 : List Lit := [(23, false), (25, true)]
theorem step1158 (p : Nat → Bool) (h : Constraints p) : clause p c1158 = true :=
  Snake9.LocalRup.prove_clause [c407, c36] c1158 (by decide) p (sat_cons (step407 p h) (sat_cons (step36 p h) (sat_nil p)))
def c1159 : List Lit := [(24, true), (23, false)]
theorem step1159 (p : Nat → Bool) (h : Constraints p) : clause p c1159 = true :=
  Snake9.LocalRup.prove_clause [c407, c37] c1159 (by decide) p (sat_cons (step407 p h) (sat_cons (step37 p h) (sat_nil p)))
def c1160 : List Lit := [(26, true), (28, true), (27, false), (32, true)]
theorem step1160 (p : Nat → Bool) (h : Constraints p) : clause p c1160 = true :=
  Snake9.LocalRup.prove_clause [c408, c43] c1160 (by decide) p (sat_cons (step408 p h) (sat_cons (step43 p h) (sat_nil p)))
def c1161 : List Lit := [(34, true), (82, true), (28, true), (29, false)]
theorem step1161 (p : Nat → Bool) (h : Constraints p) : clause p c1161 = true :=
  Snake9.LocalRup.prove_clause [c409, c48] c1161 (by decide) p (sat_cons (step409 p h) (sat_cons (step48 p h) (sat_nil p)))
def c1162 : List Lit := [(83, true), (32, true), (31, true), (30, false)]
theorem step1162 (p : Nat → Bool) (h : Constraints p) : clause p c1162 = true :=
  Snake9.LocalRup.prove_clause [c410, c49] c1162 (by decide) p (sat_cons (step410 p h) (sat_cons (step49 p h) (sat_nil p)))
def c1163 : List Lit := [(26, true), (83, true), (30, false), (31, true)]
theorem step1163 (p : Nat → Bool) (h : Constraints p) : clause p c1163 = true :=
  Snake9.LocalRup.prove_clause [c410, c50] c1163 (by decide) p (sat_cons (step410 p h) (sat_cons (step50 p h) (sat_nil p)))
def c1164 : List Lit := [(34, true), (28, true), (32, true), (33, false)]
theorem step1164 (p : Nat → Bool) (h : Constraints p) : clause p c1164 = true :=
  Snake9.LocalRup.prove_clause [c411, c56] c1164 (by decide) p (sat_cons (step411 p h) (sat_cons (step56 p h) (sat_nil p)))
def c1165 : List Lit := [(37, false), (36, true)]
theorem step1165 (p : Nat → Bool) (h : Constraints p) : clause p c1165 = true :=
  Snake9.LocalRup.prove_clause [c412, c61] c1165 (by decide) p (sat_cons (step412 p h) (sat_cons (step61 p h) (sat_nil p)))
def c1166 : List Lit := [(37, false), (35, true)]
theorem step1166 (p : Nat → Bool) (h : Constraints p) : clause p c1166 = true :=
  Snake9.LocalRup.prove_clause [c412, c62] c1166 (by decide) p (sat_cons (step412 p h) (sat_cons (step62 p h) (sat_nil p)))
def c1167 : List Lit := [(40, false), (41, true)]
theorem step1167 (p : Nat → Bool) (h : Constraints p) : clause p c1167 = true :=
  Snake9.LocalRup.prove_clause [c413, c66] c1167 (by decide) p (sat_cons (step413 p h) (sat_cons (step66 p h) (sat_nil p)))
def c1168 : List Lit := [(49, true), (101, true), (44, false)]
theorem step1168 (p : Nat → Bool) (h : Constraints p) : clause p c1168 = true :=
  Snake9.LocalRup.prove_clause [c414, c71] c1168 (by decide) p (sat_cons (step414 p h) (sat_cons (step71 p h) (sat_nil p)))
def c1169 : List Lit := [(43, true), (101, true), (44, false)]
theorem step1169 (p : Nat → Bool) (h : Constraints p) : clause p c1169 = true :=
  Snake9.LocalRup.prove_clause [c414, c72] c1169 (by decide) p (sat_cons (step414 p h) (sat_cons (step72 p h) (sat_nil p)))
def c1170 : List Lit := [(103, true), (45, true), (47, false), (12, true), (28, true)]
theorem step1170 (p : Nat → Bool) (h : Constraints p) : clause p c1170 = true :=
  Snake9.LocalRup.prove_clause [c415, c79] c1170 (by decide) p (sat_cons (step415 p h) (sat_cons (step79 p h) (sat_nil p)))
def c1171 : List Lit := [(58, true), (49, true), (48, false), (32, true)]
theorem step1171 (p : Nat → Bool) (h : Constraints p) : clause p c1171 = true :=
  Snake9.LocalRup.prove_clause [c416, c83] c1171 (by decide) p (sat_cons (step416 p h) (sat_cons (step83 p h) (sat_nil p)))
def c1172 : List Lit := [(51, true), (106, true), (50, false)]
theorem step1172 (p : Nat → Bool) (h : Constraints p) : clause p c1172 = true :=
  Snake9.LocalRup.prove_clause [c417, c85] c1172 (by decide) p (sat_cons (step417 p h) (sat_cons (step85 p h) (sat_nil p)))
def c1173 : List Lit := [(51, true), (45, true), (50, false)]
theorem step1173 (p : Nat → Bool) (h : Constraints p) : clause p c1173 = true :=
  Snake9.LocalRup.prove_clause [c417, c87] c1173 (by decide) p (sat_cons (step417 p h) (sat_cons (step87 p h) (sat_nil p)))
def c1174 : List Lit := [(54, true), (45, true), (53, false)]
theorem step1174 (p : Nat → Bool) (h : Constraints p) : clause p c1174 = true :=
  Snake9.LocalRup.prove_clause [c418, c90] c1174 (by decide) p (sat_cons (step418 p h) (sat_cons (step90 p h) (sat_nil p)))
def c1175 : List Lit := [(60, true), (55, false), (115, true)]
theorem step1175 (p : Nat → Bool) (h : Constraints p) : clause p c1175 = true :=
  Snake9.LocalRup.prove_clause [c419, c94] c1175 (by decide) p (sat_cons (step419 p h) (sat_cons (step94 p h) (sat_nil p)))
def c1176 : List Lit := [(58, true), (52, true), (56, false)]
theorem step1176 (p : Nat → Bool) (h : Constraints p) : clause p c1176 = true :=
  Snake9.LocalRup.prove_clause [c420, c97] c1176 (by decide) p (sat_cons (step420 p h) (sat_cons (step97 p h) (sat_nil p)))
def c1177 : List Lit := [(66, true), (101, true), (62, false)]
theorem step1177 (p : Nat → Bool) (h : Constraints p) : clause p c1177 = true :=
  Snake9.LocalRup.prove_clause [c421, c111] c1177 (by decide) p (sat_cons (step421 p h) (sat_cons (step111 p h) (sat_nil p)))
def c1178 : List Lit := [(61, true), (101, true), (62, false)]
theorem step1178 (p : Nat → Bool) (h : Constraints p) : clause p c1178 = true :=
  Snake9.LocalRup.prove_clause [c421, c112] c1178 (by decide) p (sat_cons (step421 p h) (sat_cons (step112 p h) (sat_nil p)))
def c1179 : List Lit := [(66, true), (61, true), (62, false)]
theorem step1179 (p : Nat → Bool) (h : Constraints p) : clause p c1179 = true :=
  Snake9.LocalRup.prove_clause [c421, c113] c1179 (by decide) p (sat_cons (step421 p h) (sat_cons (step113 p h) (sat_nil p)))
def c1180 : List Lit := [(63, false), (102, true), (71, true), (68, true)]
theorem step1180 (p : Nat → Bool) (h : Constraints p) : clause p c1180 = true :=
  Snake9.LocalRup.prove_clause [c422, c114] c1180 (by decide) p (sat_cons (step422 p h) (sat_cons (step114 p h) (sat_nil p)))
def c1181 : List Lit := [(61, true), (102, true), (71, true), (63, false)]
theorem step1181 (p : Nat → Bool) (h : Constraints p) : clause p c1181 = true :=
  Snake9.LocalRup.prove_clause [c422, c115] c1181 (by decide) p (sat_cons (step422 p h) (sat_cons (step115 p h) (sat_nil p)))
def c1182 : List Lit := [(61, true), (63, false), (102, true), (68, true)]
theorem step1182 (p : Nat → Bool) (h : Constraints p) : clause p c1182 = true :=
  Snake9.LocalRup.prove_clause [c422, c116] c1182 (by decide) p (sat_cons (step422 p h) (sat_cons (step116 p h) (sat_nil p)))
def c1183 : List Lit := [(61, true), (63, false), (68, true), (71, true)]
theorem step1183 (p : Nat → Bool) (h : Constraints p) : clause p c1183 = true :=
  Snake9.LocalRup.prove_clause [c422, c117] c1183 (by decide) p (sat_cons (step422 p h) (sat_cons (step117 p h) (sat_nil p)))
def c1184 : List Lit := [(64, false), (72, true), (103, true)]
theorem step1184 (p : Nat → Bool) (h : Constraints p) : clause p c1184 = true :=
  Snake9.LocalRup.prove_clause [c423, c118] c1184 (by decide) p (sat_cons (step423 p h) (sat_cons (step118 p h) (sat_nil p)))
def c1185 : List Lit := [(64, false), (103, true), (12, true)]
theorem step1185 (p : Nat → Bool) (h : Constraints p) : clause p c1185 = true :=
  Snake9.LocalRup.prove_clause [c423, c119] c1185 (by decide) p (sat_cons (step423 p h) (sat_cons (step119 p h) (sat_nil p)))
def c1186 : List Lit := [(72, true), (64, false), (12, true)]
theorem step1186 (p : Nat → Bool) (h : Constraints p) : clause p c1186 = true :=
  Snake9.LocalRup.prove_clause [c423, c120] c1186 (by decide) p (sat_cons (step423 p h) (sat_cons (step120 p h) (sat_nil p)))
def c1187 : List Lit := [(15, true), (61, true), (65, false), (68, true)]
theorem step1187 (p : Nat → Bool) (h : Constraints p) : clause p c1187 = true :=
  Snake9.LocalRup.prove_clause [c424, c121] c1187 (by decide) p (sat_cons (step424 p h) (sat_cons (step121 p h) (sat_nil p)))
def c1188 : List Lit := [(67, false), (106, true)]
theorem step1188 (p : Nat → Bool) (h : Constraints p) : clause p c1188 = true :=
  Snake9.LocalRup.prove_clause [c425, c125] c1188 (by decide) p (sat_cons (step425 p h) (sat_cons (step125 p h) (sat_nil p)))
def c1189 : List Lit := [(67, false), (68, true)]
theorem step1189 (p : Nat → Bool) (h : Constraints p) : clause p c1189 = true :=
  Snake9.LocalRup.prove_clause [c425, c126] c1189 (by decide) p (sat_cons (step425 p h) (sat_cons (step126 p h) (sat_nil p)))
def c1190 : List Lit := [(72, true), (70, false), (71, true)]
theorem step1190 (p : Nat → Bool) (h : Constraints p) : clause p c1190 = true :=
  Snake9.LocalRup.prove_clause [c426, c133] c1190 (by decide) p (sat_cons (step426 p h) (sat_cons (step133 p h) (sat_nil p)))
def c1191 : List Lit := [(69, true), (72, true), (70, false)]
theorem step1191 (p : Nat → Bool) (h : Constraints p) : clause p c1191 = true :=
  Snake9.LocalRup.prove_clause [c426, c134] c1191 (by decide) p (sat_cons (step426 p h) (sat_cons (step134 p h) (sat_nil p)))
def c1192 : List Lit := [(69, true), (70, false), (71, true)]
theorem step1192 (p : Nat → Bool) (h : Constraints p) : clause p c1192 = true :=
  Snake9.LocalRup.prove_clause [c426, c135] c1192 (by decide) p (sat_cons (step426 p h) (sat_cons (step135 p h) (sat_nil p)))
def c1193 : List Lit := [(71, false), (63, false), (21, false)]
theorem step1193 (p : Nat → Bool) (h : Constraints p) : clause p c1193 = true :=
  Snake9.LocalRup.prove_clause [c152, c136] c1193 (by decide) p (sat_cons (step152 p h) (sat_cons (step136 p h) (sat_nil p)))
def c1194 : List Lit := [(71, false), (70, false), (21, false)]
theorem step1194 (p : Nat → Bool) (h : Constraints p) : clause p c1194 = true :=
  Snake9.LocalRup.prove_clause [c152, c137] c1194 (by decide) p (sat_cons (step152 p h) (sat_cons (step137 p h) (sat_nil p)))
def c1195 : List Lit := [(71, false), (113, false), (21, false)]
theorem step1195 (p : Nat → Bool) (h : Constraints p) : clause p c1195 = true :=
  Snake9.LocalRup.prove_clause [c152, c138] c1195 (by decide) p (sat_cons (step152 p h) (sat_cons (step138 p h) (sat_nil p)))
def c1196 : List Lit := [(63, false), (71, false), (70, false)]
theorem step1196 (p : Nat → Bool) (h : Constraints p) : clause p c1196 = true :=
  Snake9.LocalRup.prove_clause [c152, c139] c1196 (by decide) p (sat_cons (step152 p h) (sat_cons (step139 p h) (sat_nil p)))
def c1197 : List Lit := [(71, false), (63, false), (113, false)]
theorem step1197 (p : Nat → Bool) (h : Constraints p) : clause p c1197 = true :=
  Snake9.LocalRup.prove_clause [c152, c140] c1197 (by decide) p (sat_cons (step152 p h) (sat_cons (step140 p h) (sat_nil p)))
def c1198 : List Lit := [(71, false), (70, false), (113, false)]
theorem step1198 (p : Nat → Bool) (h : Constraints p) : clause p c1198 = true :=
  Snake9.LocalRup.prove_clause [c152, c141] c1198 (by decide) p (sat_cons (step152 p h) (sat_cons (step141 p h) (sat_nil p)))
def c1199 : List Lit := [(72, false), (64, false), (70, false)]
theorem step1199 (p : Nat → Bool) (h : Constraints p) : clause p c1199 = true :=
  Snake9.LocalRup.prove_clause [c152, c142] c1199 (by decide) p (sat_cons (step152 p h) (sat_cons (step142 p h) (sat_nil p)))
def c1200 : List Lit := [(72, false), (64, false), (114, false)]
theorem step1200 (p : Nat → Bool) (h : Constraints p) : clause p c1200 = true :=
  Snake9.LocalRup.prove_clause [c152, c143] c1200 (by decide) p (sat_cons (step152 p h) (sat_cons (step143 p h) (sat_nil p)))
def c1201 : List Lit := [(72, false), (70, false), (114, false)]
theorem step1201 (p : Nat → Bool) (h : Constraints p) : clause p c1201 = true :=
  Snake9.LocalRup.prove_clause [c152, c144] c1201 (by decide) p (sat_cons (step152 p h) (sat_cons (step144 p h) (sat_nil p)))
def c1202 : List Lit := [(72, true), (77, true), (71, true), (115, true)]
theorem step1202 (p : Nat → Bool) (h : Constraints p) : clause p c1202 = true :=
  Snake9.LocalRup.prove_clause [c152, c145] c1202 (by decide) p (sat_cons (step152 p h) (sat_cons (step145 p h) (sat_nil p)))
end B112E152
