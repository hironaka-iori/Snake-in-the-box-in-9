import B112E146Part0003
namespace B112E146
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1073 : List Lit := [(28, true), (36, true), (33, false)]
theorem step1073 (p : Nat → Bool) (h : Constraints p) : clause p c1073 = true :=
  Snake9.LocalRup.prove_clause [c327, c136] c1073 (by decide) p (sat_cons (step327 p h) (sat_cons (step136 p h) (sat_nil p)))
def c1074 : List Lit := [(28, true), (34, true), (33, false)]
theorem step1074 (p : Nat → Bool) (h : Constraints p) : clause p c1074 = true :=
  Snake9.LocalRup.prove_clause [c327, c137] c1074 (by decide) p (sat_cons (step327 p h) (sat_cons (step137 p h) (sat_nil p)))
def c1075 : List Lit := [(42, true), (52, true), (35, false)]
theorem step1075 (p : Nat → Bool) (h : Constraints p) : clause p c1075 = true :=
  Snake9.LocalRup.prove_clause [c328, c150] c1075 (by decide) p (sat_cons (step328 p h) (sat_cons (step150 p h) (sat_nil p)))
def c1076 : List Lit := [(52, true), (35, false), (36, true)]
theorem step1076 (p : Nat → Bool) (h : Constraints p) : clause p c1076 = true :=
  Snake9.LocalRup.prove_clause [c328, c151] c1076 (by decide) p (sat_cons (step328 p h) (sat_cons (step151 p h) (sat_nil p)))
def c1077 : List Lit := [(42, true), (35, false), (36, true)]
theorem step1077 (p : Nat → Bool) (h : Constraints p) : clause p c1077 = true :=
  Snake9.LocalRup.prove_clause [c328, c152] c1077 (by decide) p (sat_cons (step328 p h) (sat_cons (step152 p h) (sat_nil p)))
def c1078 : List Lit := [(40, false), (38, true)]
theorem step1078 (p : Nat → Bool) (h : Constraints p) : clause p c1078 = true :=
  Snake9.LocalRup.prove_clause [c329, c194] c1078 (by decide) p (sat_cons (step329 p h) (sat_cons (step194 p h) (sat_nil p)))
def c1079 : List Lit := [(40, false), (29, true)]
theorem step1079 (p : Nat → Bool) (h : Constraints p) : clause p c1079 = true :=
  Snake9.LocalRup.prove_clause [c329, c195] c1079 (by decide) p (sat_cons (step329 p h) (sat_cons (step195 p h) (sat_nil p)))
def c1080 : List Lit := [(41, false), (42, true)]
theorem step1080 (p : Nat → Bool) (h : Constraints p) : clause p c1080 = true :=
  Snake9.LocalRup.prove_clause [c330, c196] c1080 (by decide) p (sat_cons (step330 p h) (sat_cons (step196 p h) (sat_nil p)))
def c1081 : List Lit := [(41, false), (38, true)]
theorem step1081 (p : Nat → Bool) (h : Constraints p) : clause p c1081 = true :=
  Snake9.LocalRup.prove_clause [c330, c197] c1081 (by decide) p (sat_cons (step330 p h) (sat_cons (step197 p h) (sat_nil p)))
def c1082 : List Lit := [(43, false), (44, true)]
theorem step1082 (p : Nat → Bool) (h : Constraints p) : clause p c1082 = true :=
  Snake9.LocalRup.prove_clause [c331, c202] c1082 (by decide) p (sat_cons (step331 p h) (sat_cons (step202 p h) (sat_nil p)))
def c1083 : List Lit := [(43, false), (42, true)]
theorem step1083 (p : Nat → Bool) (h : Constraints p) : clause p c1083 = true :=
  Snake9.LocalRup.prove_clause [c331, c203] c1083 (by decide) p (sat_cons (step331 p h) (sat_cons (step203 p h) (sat_nil p)))
def c1084 : List Lit := [(45, true), (52, true), (48, false)]
theorem step1084 (p : Nat → Bool) (h : Constraints p) : clause p c1084 = true :=
  Snake9.LocalRup.prove_clause [c332, c214] c1084 (by decide) p (sat_cons (step332 p h) (sat_cons (step214 p h) (sat_nil p)))
def c1085 : List Lit := [(49, true), (45, true), (48, false)]
theorem step1085 (p : Nat → Bool) (h : Constraints p) : clause p c1085 = true :=
  Snake9.LocalRup.prove_clause [c332, c215] c1085 (by decide) p (sat_cons (step332 p h) (sat_cons (step215 p h) (sat_nil p)))
def c1086 : List Lit := [(47, true), (34, true), (51, false), (50, true)]
theorem step1086 (p : Nat → Bool) (h : Constraints p) : clause p c1086 = true :=
  Snake9.LocalRup.prove_clause [c333, c222] c1086 (by decide) p (sat_cons (step333 p h) (sat_cons (step222 p h) (sat_nil p)))
def c1087 : List Lit := [(14, true), (47, true), (50, true), (51, false)]
theorem step1087 (p : Nat → Bool) (h : Constraints p) : clause p c1087 = true :=
  Snake9.LocalRup.prove_clause [c333, c223] c1087 (by decide) p (sat_cons (step333 p h) (sat_cons (step223 p h) (sat_nil p)))
def c1088 : List Lit := [(14, true), (34, true), (51, false), (50, true)]
theorem step1088 (p : Nat → Bool) (h : Constraints p) : clause p c1088 = true :=
  Snake9.LocalRup.prove_clause [c333, c224] c1088 (by decide) p (sat_cons (step333 p h) (sat_cons (step224 p h) (sat_nil p)))
def c1089 : List Lit := [(14, true), (47, true), (51, false), (34, true)]
theorem step1089 (p : Nat → Bool) (h : Constraints p) : clause p c1089 = true :=
  Snake9.LocalRup.prove_clause [c333, c225] c1089 (by decide) p (sat_cons (step333 p h) (sat_cons (step225 p h) (sat_nil p)))
def c1090 : List Lit := [(52, true), (61, true), (36, true), (53, false)]
theorem step1090 (p : Nat → Bool) (h : Constraints p) : clause p c1090 = true :=
  Snake9.LocalRup.prove_clause [c334, c236] c1090 (by decide) p (sat_cons (step334 p h) (sat_cons (step236 p h) (sat_nil p)))
def c1091 : List Lit := [(16, true), (61, true), (52, true), (53, false)]
theorem step1091 (p : Nat → Bool) (h : Constraints p) : clause p c1091 = true :=
  Snake9.LocalRup.prove_clause [c334, c237] c1091 (by decide) p (sat_cons (step334 p h) (sat_cons (step237 p h) (sat_nil p)))
def c1092 : List Lit := [(61, true), (16, true), (53, false), (36, true)]
theorem step1092 (p : Nat → Bool) (h : Constraints p) : clause p c1092 = true :=
  Snake9.LocalRup.prove_clause [c334, c238] c1092 (by decide) p (sat_cons (step334 p h) (sat_cons (step238 p h) (sat_nil p)))
def c1093 : List Lit := [(57, true), (61, true), (55, false)]
theorem step1093 (p : Nat → Bool) (h : Constraints p) : clause p c1093 = true :=
  Snake9.LocalRup.prove_clause [c335, c241] c1093 (by decide) p (sat_cons (step335 p h) (sat_cons (step241 p h) (sat_nil p)))
def c1094 : List Lit := [(54, true), (61, true), (55, false)]
theorem step1094 (p : Nat → Bool) (h : Constraints p) : clause p c1094 = true :=
  Snake9.LocalRup.prove_clause [c335, c242] c1094 (by decide) p (sat_cons (step335 p h) (sat_cons (step242 p h) (sat_nil p)))
def c1095 : List Lit := [(54, true), (57, true), (55, false)]
theorem step1095 (p : Nat → Bool) (h : Constraints p) : clause p c1095 = true :=
  Snake9.LocalRup.prove_clause [c335, c243] c1095 (by decide) p (sat_cons (step335 p h) (sat_cons (step243 p h) (sat_nil p)))
def c1096 : List Lit := [(56, false), (57, true)]
theorem step1096 (p : Nat → Bool) (h : Constraints p) : clause p c1096 = true :=
  Snake9.LocalRup.prove_clause [c336, c244] c1096 (by decide) p (sat_cons (step336 p h) (sat_cons (step244 p h) (sat_nil p)))
def c1097 : List Lit := [(56, false), (49, true)]
theorem step1097 (p : Nat → Bool) (h : Constraints p) : clause p c1097 = true :=
  Snake9.LocalRup.prove_clause [c336, c245] c1097 (by decide) p (sat_cons (step336 p h) (sat_cons (step245 p h) (sat_nil p)))
def c1098 : List Lit := [(58, true), (54, true), (59, false)]
theorem step1098 (p : Nat → Bool) (h : Constraints p) : clause p c1098 = true :=
  Snake9.LocalRup.prove_clause [c337, c250] c1098 (by decide) p (sat_cons (step337 p h) (sat_cons (step250 p h) (sat_nil p)))
def c1099 : List Lit := [(58, true), (60, false), (50, true)]
theorem step1099 (p : Nat → Bool) (h : Constraints p) : clause p c1099 = true :=
  Snake9.LocalRup.prove_clause [c338, c251] c1099 (by decide) p (sat_cons (step338 p h) (sat_cons (step251 p h) (sat_nil p)))
def c1100 : List Lit := [(24, true), (60, false), (50, true)]
theorem step1100 (p : Nat → Bool) (h : Constraints p) : clause p c1100 = true :=
  Snake9.LocalRup.prove_clause [c338, c252] c1100 (by decide) p (sat_cons (step338 p h) (sat_cons (step252 p h) (sat_nil p)))
def c1101 : List Lit := [(177, true), (64, true)]
theorem step1101 (p : Nat → Bool) (h : Constraints p) : clause p c1101 = true :=
  Snake9.LocalRup.prove_clause [c817, c256] c1101 (by decide) p (sat_cons (step817 p h) (sat_cons (step256 p h) (sat_nil p)))
def c1102 : List Lit := [(64, false), (62, true)]
theorem step1102 (p : Nat → Bool) (h : Constraints p) : clause p c1102 = true :=
  Snake9.LocalRup.prove_clause [c339, c257] c1102 (by decide) p (sat_cons (step339 p h) (sat_cons (step257 p h) (sat_nil p)))
def c1103 : List Lit := [(68, true), (71, true), (72, false)]
theorem step1103 (p : Nat → Bool) (h : Constraints p) : clause p c1103 = true :=
  Snake9.LocalRup.prove_clause [c340, c266] c1103 (by decide) p (sat_cons (step340 p h) (sat_cons (step266 p h) (sat_nil p)))
def c1104 : List Lit := [(14, true), (71, true), (72, false)]
theorem step1104 (p : Nat → Bool) (h : Constraints p) : clause p c1104 = true :=
  Snake9.LocalRup.prove_clause [c340, c267] c1104 (by decide) p (sat_cons (step340 p h) (sat_cons (step267 p h) (sat_nil p)))
def c1105 : List Lit := [(68, true), (14, true), (72, false)]
theorem step1105 (p : Nat → Bool) (h : Constraints p) : clause p c1105 = true :=
  Snake9.LocalRup.prove_clause [c340, c268] c1105 (by decide) p (sat_cons (step340 p h) (sat_cons (step268 p h) (sat_nil p)))
def c1106 : List Lit := [(73, true), (74, false), (16, true)]
theorem step1106 (p : Nat → Bool) (h : Constraints p) : clause p c1106 = true :=
  Snake9.LocalRup.prove_clause [c341, c272] c1106 (by decide) p (sat_cons (step341 p h) (sat_cons (step272 p h) (sat_nil p)))
def c1107 : List Lit := [(77, false), (78, true)]
theorem step1107 (p : Nat → Bool) (h : Constraints p) : clause p c1107 = true :=
  Snake9.LocalRup.prove_clause [c343, c275] c1107 (by decide) p (sat_cons (step343 p h) (sat_cons (step275 p h) (sat_nil p)))
def c1108 : List Lit := [(82, true), (75, true), (80, false)]
theorem step1108 (p : Nat → Bool) (h : Constraints p) : clause p c1108 = true :=
  Snake9.LocalRup.prove_clause [c344, c278] c1108 (by decide) p (sat_cons (step344 p h) (sat_cons (step278 p h) (sat_nil p)))
def c1109 : List Lit := [(71, true), (81, false), (24, true)]
theorem step1109 (p : Nat → Bool) (h : Constraints p) : clause p c1109 = true :=
  Snake9.LocalRup.prove_clause [c345, c279] c1109 (by decide) p (sat_cons (step345 p h) (sat_cons (step279 p h) (sat_nil p)))
def c1110 : List Lit := [(85, true), (29, true), (84, false)]
theorem step1110 (p : Nat → Bool) (h : Constraints p) : clause p c1110 = true :=
  Snake9.LocalRup.prove_clause [c347, c285] c1110 (by decide) p (sat_cons (step347 p h) (sat_cons (step285 p h) (sat_nil p)))
def c1111 : List Lit := [(87, false), (84, true), (201, true)]
theorem step1111 (p : Nat → Bool) (h : Constraints p) : clause p c1111 = true :=
  Snake9.LocalRup.prove_clause [c818, c288] c1111 (by decide) p (sat_cons (step818 p h) (sat_cons (step288 p h) (sat_nil p)))
def c1112 : List Lit := [(88, false), (36, true), (93, true)]
theorem step1112 (p : Nat → Bool) (h : Constraints p) : clause p c1112 = true :=
  Snake9.LocalRup.prove_clause [c349, c291] c1112 (by decide) p (sat_cons (step349 p h) (sat_cons (step291 p h) (sat_nil p)))
def c1113 : List Lit := [(92, true), (90, false), (93, true)]
theorem step1113 (p : Nat → Bool) (h : Constraints p) : clause p c1113 = true :=
  Snake9.LocalRup.prove_clause [c350, c293] c1113 (by decide) p (sat_cons (step350 p h) (sat_cons (step293 p h) (sat_nil p)))
def c1114 : List Lit := [(90, false), (89, true), (93, true)]
theorem step1114 (p : Nat → Bool) (h : Constraints p) : clause p c1114 = true :=
  Snake9.LocalRup.prove_clause [c350, c294] c1114 (by decide) p (sat_cons (step350 p h) (sat_cons (step294 p h) (sat_nil p)))
def c1115 : List Lit := [(92, true), (90, false), (89, true)]
theorem step1115 (p : Nat → Bool) (h : Constraints p) : clause p c1115 = true :=
  Snake9.LocalRup.prove_clause [c350, c295] c1115 (by decide) p (sat_cons (step350 p h) (sat_cons (step295 p h) (sat_nil p)))
def c1116 : List Lit := [(91, false), (92, true)]
theorem step1116 (p : Nat → Bool) (h : Constraints p) : clause p c1116 = true :=
  Snake9.LocalRup.prove_clause [c351, c296] c1116 (by decide) p (sat_cons (step351 p h) (sat_cons (step296 p h) (sat_nil p)))
def c1117 : List Lit := [(91, false), (87, true)]
theorem step1117 (p : Nat → Bool) (h : Constraints p) : clause p c1117 = true :=
  Snake9.LocalRup.prove_clause [c351, c297] c1117 (by decide) p (sat_cons (step351 p h) (sat_cons (step297 p h) (sat_nil p)))
def c1118 : List Lit := [(95, false), (96, true)]
theorem step1118 (p : Nat → Bool) (h : Constraints p) : clause p c1118 = true :=
  Snake9.LocalRup.prove_clause [c352, c306] c1118 (by decide) p (sat_cons (step352 p h) (sat_cons (step306 p h) (sat_nil p)))
def c1119 : List Lit := [(101, false), (102, true)]
theorem step1119 (p : Nat → Bool) (h : Constraints p) : clause p c1119 = true :=
  Snake9.LocalRup.prove_clause [c354, c311] c1119 (by decide) p (sat_cons (step354 p h) (sat_cons (step311 p h) (sat_nil p)))
def c1120 : List Lit := [(104, false), (100, true)]
theorem step1120 (p : Nat → Bool) (h : Constraints p) : clause p c1120 = true :=
  Snake9.LocalRup.prove_clause [c355, c313] c1120 (by decide) p (sat_cons (step355 p h) (sat_cons (step313 p h) (sat_nil p)))
def c1121 : List Lit := [(231, false), (237, false)]
theorem step1121 (p : Nat → Bool) (h : Constraints p) : clause p c1121 = true :=
  Snake9.LocalRup.prove_clause [c834, c365] c1121 (by decide) p (sat_cons (step834 p h) (sat_cons (step365 p h) (sat_nil p)))
def c1122 : List Lit := [(239, false), (251, false)]
theorem step1122 (p : Nat → Bool) (h : Constraints p) : clause p c1122 = true :=
  Snake9.LocalRup.prove_clause [c830, c371] c1122 (by decide) p (sat_cons (step830 p h) (sat_cons (step371 p h) (sat_nil p)))
def c1123 : List Lit := [(253, false), (279, false)]
theorem step1123 (p : Nat → Bool) (h : Constraints p) : clause p c1123 = true :=
  Snake9.LocalRup.prove_clause [c825, c379] c1123 (by decide) p (sat_cons (step825 p h) (sat_cons (step379 p h) (sat_nil p)))
def c1124 : List Lit := [(158, false), (159, false)]
theorem step1124 (p : Nat → Bool) (h : Constraints p) : clause p c1124 = true :=
  Snake9.LocalRup.prove_clause [c837, c397] c1124 (by decide) p (sat_cons (step837 p h) (sat_cons (step397 p h) (sat_nil p)))
def c1125 : List Lit := [(311, false), (317, false)]
theorem step1125 (p : Nat → Bool) (h : Constraints p) : clause p c1125 = true :=
  Snake9.LocalRup.prove_clause [c833, c403] c1125 (by decide) p (sat_cons (step833 p h) (sat_cons (step403 p h) (sat_nil p)))
def c1126 : List Lit := [(307, false), (333, false)]
theorem step1126 (p : Nat → Bool) (h : Constraints p) : clause p c1126 = true :=
  Snake9.LocalRup.prove_clause [c824, c414] c1126 (by decide) p (sat_cons (step824 p h) (sat_cons (step414 p h) (sat_nil p)))
def c1127 : List Lit := [(281, false), (335, false)]
theorem step1127 (p : Nat → Bool) (h : Constraints p) : clause p c1127 = true :=
  Snake9.LocalRup.prove_clause [c821, c419] c1127 (by decide) p (sat_cons (step821 p h) (sat_cons (step419 p h) (sat_nil p)))
def c1128 : List Lit := [(341, false), (347, false)]
theorem step1128 (p : Nat → Bool) (h : Constraints p) : clause p c1128 = true :=
  Snake9.LocalRup.prove_clause [c832, c432] c1128 (by decide) p (sat_cons (step832 p h) (sat_cons (step432 p h) (sat_nil p)))
def c1129 : List Lit := [(395, false), (401, false)]
theorem step1129 (p : Nat → Bool) (h : Constraints p) : clause p c1129 = true :=
  Snake9.LocalRup.prove_clause [c831, c446] c1129 (by decide) p (sat_cons (step831 p h) (sat_cons (step446 p h) (sat_nil p)))
def c1130 : List Lit := [(403, false), (415, false)]
theorem step1130 (p : Nat → Bool) (h : Constraints p) : clause p c1130 = true :=
  Snake9.LocalRup.prove_clause [c826, c451] c1130 (by decide) p (sat_cons (step826 p h) (sat_cons (step451 p h) (sat_nil p)))
def c1131 : List Lit := [(391, false), (447, false)]
theorem step1131 (p : Nat → Bool) (h : Constraints p) : clause p c1131 = true :=
  Snake9.LocalRup.prove_clause [c820, c458] c1131 (by decide) p (sat_cons (step820 p h) (sat_cons (step458 p h) (sat_nil p)))
def c1132 : List Lit := [(337, false), (449, false)]
theorem step1132 (p : Nat → Bool) (h : Constraints p) : clause p c1132 = true :=
  Snake9.LocalRup.prove_clause [c463, c461] c1132 (by decide) p (sat_cons (step463 p h) (sat_cons (step461 p h) (sat_nil p)))
def c1133 : List Lit := [(1375, false), (1380, true)]
theorem step1133 (p : Nat → Bool) (h : Constraints p) : clause p c1133 = true :=
  Snake9.LocalRup.prove_clause [c851, c518] c1133 (by decide) p (sat_cons (step851 p h) (sat_cons (step518 p h) (sat_nil p)))
def c1134 : List Lit := [(1371, false), (1384, true)]
theorem step1134 (p : Nat → Bool) (h : Constraints p) : clause p c1134 = true :=
  Snake9.LocalRup.prove_clause [c859, c521] c1134 (by decide) p (sat_cons (step859 p h) (sat_cons (step521 p h) (sat_nil p)))
def c1135 : List Lit := [(1372, false), (1385, true)]
theorem step1135 (p : Nat → Bool) (h : Constraints p) : clause p c1135 = true :=
  Snake9.LocalRup.prove_clause [c859, c523] c1135 (by decide) p (sat_cons (step859 p h) (sat_cons (step523 p h) (sat_nil p)))
def c1136 : List Lit := [(1386, true), (1373, false)]
theorem step1136 (p : Nat → Bool) (h : Constraints p) : clause p c1136 = true :=
  Snake9.LocalRup.prove_clause [c859, c525] c1136 (by decide) p (sat_cons (step859 p h) (sat_cons (step525 p h) (sat_nil p)))
end B112E146
