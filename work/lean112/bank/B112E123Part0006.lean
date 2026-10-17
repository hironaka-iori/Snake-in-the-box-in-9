import B112E123Part0005
namespace B112E123
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1095 : List Lit := [(771, true), (1, true), (12, false)]
theorem step1095 (p : Nat → Bool) (h : Constraints p) : clause p c1095 = true :=
  Snake9.LocalRup.prove_clause [c1082, c388, c384, c364, c372, c1004, c370] c1095 (by decide) p (sat_cons (step1082 p h) (sat_cons (step388 p h) (sat_cons (step384 p h) (sat_cons (step364 p h) (sat_cons (step372 p h) (sat_cons (step1004 p h) (sat_cons (step370 p h) (sat_nil p))))))))
def c1096 : List Lit := [(802, false), (18, true), (12, false), (9, false), (14, false), (3, true), (788, false), (4, false)]
theorem step1096 (p : Nat → Bool) (h : Constraints p) : clause p c1096 = true :=
  Snake9.LocalRup.prove_clause [c1030, c1067, c1072, c488, c1092, c901, c1094, c509, c506, c500, c46, c824, c825, c815, c703, c75, c399, c812, c401, c1095, c425, c433] c1096 (by decide) p (sat_cons (step1030 p h) (sat_cons (step1067 p h) (sat_cons (step1072 p h) (sat_cons (step488 p h) (sat_cons (step1092 p h) (sat_cons (step901 p h) (sat_cons (step1094 p h) (sat_cons (step509 p h) (sat_cons (step506 p h) (sat_cons (step500 p h) (sat_cons (step46 p h) (sat_cons (step824 p h) (sat_cons (step825 p h) (sat_cons (step815 p h) (sat_cons (step703 p h) (sat_cons (step75 p h) (sat_cons (step399 p h) (sat_cons (step812 p h) (sat_cons (step401 p h) (sat_cons (step1095 p h) (sat_cons (step425 p h) (sat_cons (step433 p h) (sat_nil p)))))))))))))))))))))))
def c1097 : List Lit := [(9, false), (3, true), (788, false), (6, false), (4, false)]
theorem step1097 (p : Nat → Bool) (h : Constraints p) : clause p c1097 = true :=
  Snake9.LocalRup.prove_clause [c1072, c1082, c1078, c1083, c822, c421, c1089, c1011, c1093, c81, c397, c1096, c430, c432, c425, c1095, c403, c812, c60] c1097 (by decide) p (sat_cons (step1072 p h) (sat_cons (step1082 p h) (sat_cons (step1078 p h) (sat_cons (step1083 p h) (sat_cons (step822 p h) (sat_cons (step421 p h) (sat_cons (step1089 p h) (sat_cons (step1011 p h) (sat_cons (step1093 p h) (sat_cons (step81 p h) (sat_cons (step397 p h) (sat_cons (step1096 p h) (sat_cons (step430 p h) (sat_cons (step432 p h) (sat_cons (step425 p h) (sat_cons (step1095 p h) (sat_cons (step403 p h) (sat_cons (step812 p h) (sat_cons (step60 p h) (sat_nil p))))))))))))))))))))
def c1098 : List Lit := [(4, false), (785, false)]
theorem step1098 (p : Nat → Bool) (h : Constraints p) : clause p c1098 = true :=
  Snake9.LocalRup.prove_clause [c1072, c1078, c1087, c1089, c413, c421, c437, c1091, c1097, c366, c1086, c993] c1098 (by decide) p (sat_cons (step1072 p h) (sat_cons (step1078 p h) (sat_cons (step1087 p h) (sat_cons (step1089 p h) (sat_cons (step413 p h) (sat_cons (step421 p h) (sat_cons (step437 p h) (sat_cons (step1091 p h) (sat_cons (step1097 p h) (sat_cons (step366 p h) (sat_cons (step1086 p h) (sat_cons (step993 p h) (sat_nil p)))))))))))))
def c1099 : List Lit := [(12, true), (788, false), (3, true), (757, false)]
theorem step1099 (p : Nat → Bool) (h : Constraints p) : clause p c1099 = true :=
  Snake9.LocalRup.prove_clause [c1078, c1082, c1072, c421, c437, c385, c373, c369, c371, c939, c1016, c364] c1099 (by decide) p (sat_cons (step1078 p h) (sat_cons (step1082 p h) (sat_cons (step1072 p h) (sat_cons (step421 p h) (sat_cons (step437 p h) (sat_cons (step385 p h) (sat_cons (step373 p h) (sat_cons (step369 p h) (sat_cons (step371 p h) (sat_cons (step939 p h) (sat_cons (step1016 p h) (sat_cons (step364 p h) (sat_nil p)))))))))))))
def c1100 : List Lit := [(1, true), (3, true), (785, false)]
theorem step1100 (p : Nat → Bool) (h : Constraints p) : clause p c1100 = true :=
  Snake9.LocalRup.prove_clause [c1078, c1072, c1030, c1068, c909, c1067, c1071, c1098, c359, c840, c406, c413, c1099, c421, c437, c393, c365, c1095, c364, c360, c433, c432, c389, c939, c425, c488, c988, c374, c370, c401, c901, c531, c535, c366, c367, c1094, c516, c822, c81, c509, c397, c399, c506, c403, c50, c501, c63, c823, c832, c925, c98, c817, c762, c166, c528, c514, c186, c185, c521] c1100 (by decide) p (sat_cons (step1078 p h) (sat_cons (step1072 p h) (sat_cons (step1030 p h) (sat_cons (step1068 p h) (sat_cons (step909 p h) (sat_cons (step1067 p h) (sat_cons (step1071 p h) (sat_cons (step1098 p h) (sat_cons (step359 p h) (sat_cons (step840 p h) (sat_cons (step406 p h) (sat_cons (step413 p h) (sat_cons (step1099 p h) (sat_cons (step421 p h) (sat_cons (step437 p h) (sat_cons (step393 p h) (sat_cons (step365 p h) (sat_cons (step1095 p h) (sat_cons (step364 p h) (sat_cons (step360 p h) (sat_cons (step433 p h) (sat_cons (step432 p h) (sat_cons (step389 p h) (sat_cons (step939 p h) (sat_cons (step425 p h) (sat_cons (step488 p h) (sat_cons (step988 p h) (sat_cons (step374 p h) (sat_cons (step370 p h) (sat_cons (step401 p h) (sat_cons (step901 p h) (sat_cons (step531 p h) (sat_cons (step535 p h) (sat_cons (step366 p h) (sat_cons (step367 p h) (sat_cons (step1094 p h) (sat_cons (step516 p h) (sat_cons (step822 p h) (sat_cons (step81 p h) (sat_cons (step509 p h) (sat_cons (step397 p h) (sat_cons (step399 p h) (sat_cons (step506 p h) (sat_cons (step403 p h) (sat_cons (step50 p h) (sat_cons (step501 p h) (sat_cons (step63 p h) (sat_cons (step823 p h) (sat_cons (step832 p h) (sat_cons (step925 p h) (sat_cons (step98 p h) (sat_cons (step817 p h) (sat_cons (step762 p h) (sat_cons (step166 p h) (sat_cons (step528 p h) (sat_cons (step514 p h) (sat_cons (step186 p h) (sat_cons (step185 p h) (sat_cons (step521 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1101 : List Lit := [(3, true), (785, false)]
theorem step1101 (p : Nat → Bool) (h : Constraints p) : clause p c1101 = true :=
  Snake9.LocalRup.prove_clause [c1078, c1082, c1072, c1098, c359, c840, c406, c413, c421, c437, c385, c1099, c1100, c812, c1016, c60, c370, c372, c375, c384, c367, c433, c822, c81, c425, c397, c403] c1101 (by decide) p (sat_cons (step1078 p h) (sat_cons (step1082 p h) (sat_cons (step1072 p h) (sat_cons (step1098 p h) (sat_cons (step359 p h) (sat_cons (step840 p h) (sat_cons (step406 p h) (sat_cons (step413 p h) (sat_cons (step421 p h) (sat_cons (step437 p h) (sat_cons (step385 p h) (sat_cons (step1099 p h) (sat_cons (step1100 p h) (sat_cons (step812 p h) (sat_cons (step1016 p h) (sat_cons (step60 p h) (sat_cons (step370 p h) (sat_cons (step372 p h) (sat_cons (step375 p h) (sat_cons (step384 p h) (sat_cons (step367 p h) (sat_cons (step433 p h) (sat_cons (step822 p h) (sat_cons (step81 p h) (sat_cons (step425 p h) (sat_cons (step397 p h) (sat_cons (step403 p h) (sat_nil p))))))))))))))))))))))))))))
def c1102 : List Lit := [(1, false), (772, true), (12, false), (785, false)]
theorem step1102 (p : Nat → Bool) (h : Constraints p) : clause p c1102 = true :=
  Snake9.LocalRup.prove_clause [c1082, c385, c1101, c1098, c700, c14, c813, c367, c374, c375, c389, c370, c362, c7, c360] c1102 (by decide) p (sat_cons (step1082 p h) (sat_cons (step385 p h) (sat_cons (step1101 p h) (sat_cons (step1098 p h) (sat_cons (step700 p h) (sat_cons (step14 p h) (sat_cons (step813 p h) (sat_cons (step367 p h) (sat_cons (step374 p h) (sat_cons (step375 p h) (sat_cons (step389 p h) (sat_cons (step370 p h) (sat_cons (step362 p h) (sat_cons (step7 p h) (sat_cons (step360 p h) (sat_nil p))))))))))))))))
def c1103 : List Lit := [(788, false), (12, false), (785, false)]
theorem step1103 (p : Nat → Bool) (h : Constraints p) : clause p c1103 = true :=
  Snake9.LocalRup.prove_clause [c1078, c1072, c1030, c1071, c1068, c1101, c1098, c359, c421, c437, c393, c1102, c365, c1095, c364, c360, c433, c432, c389, c425, c488, c489, c374, c401, c901, c886, c366, c367, c1094, c756, c701, c511, c459, c1052, c498, c941, c858, c453, c454, c857, c457, c458, c853, c854, c755, c455, c131, c482, c477, c471, c465, c466, c140] c1103 (by decide) p (sat_cons (step1078 p h) (sat_cons (step1072 p h) (sat_cons (step1030 p h) (sat_cons (step1071 p h) (sat_cons (step1068 p h) (sat_cons (step1101 p h) (sat_cons (step1098 p h) (sat_cons (step359 p h) (sat_cons (step421 p h) (sat_cons (step437 p h) (sat_cons (step393 p h) (sat_cons (step1102 p h) (sat_cons (step365 p h) (sat_cons (step1095 p h) (sat_cons (step364 p h) (sat_cons (step360 p h) (sat_cons (step433 p h) (sat_cons (step432 p h) (sat_cons (step389 p h) (sat_cons (step425 p h) (sat_cons (step488 p h) (sat_cons (step489 p h) (sat_cons (step374 p h) (sat_cons (step401 p h) (sat_cons (step901 p h) (sat_cons (step886 p h) (sat_cons (step366 p h) (sat_cons (step367 p h) (sat_cons (step1094 p h) (sat_cons (step756 p h) (sat_cons (step701 p h) (sat_cons (step511 p h) (sat_cons (step459 p h) (sat_cons (step1052 p h) (sat_cons (step498 p h) (sat_cons (step941 p h) (sat_cons (step858 p h) (sat_cons (step453 p h) (sat_cons (step454 p h) (sat_cons (step857 p h) (sat_cons (step457 p h) (sat_cons (step458 p h) (sat_cons (step853 p h) (sat_cons (step854 p h) (sat_cons (step755 p h) (sat_cons (step455 p h) (sat_cons (step131 p h) (sat_cons (step482 p h) (sat_cons (step477 p h) (sat_cons (step471 p h) (sat_cons (step465 p h) (sat_cons (step466 p h) (sat_cons (step140 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1104 : List Lit := [(32, true), (802, false)]
theorem step1104 (p : Nat → Bool) (h : Constraints p) : clause p c1104 = true :=
  Snake9.LocalRup.prove_clause [c1071, c1030, c1068, c488, c901, c1094, c511, c498, c858, c857, c489, c886, c756, c459, c453, c454, c457, c458, c853, c854, c755, c455, c131, c482, c477, c471, c465, c466, c140] c1104 (by decide) p (sat_cons (step1071 p h) (sat_cons (step1030 p h) (sat_cons (step1068 p h) (sat_cons (step488 p h) (sat_cons (step901 p h) (sat_cons (step1094 p h) (sat_cons (step511 p h) (sat_cons (step498 p h) (sat_cons (step858 p h) (sat_cons (step857 p h) (sat_cons (step489 p h) (sat_cons (step886 p h) (sat_cons (step756 p h) (sat_cons (step459 p h) (sat_cons (step453 p h) (sat_cons (step454 p h) (sat_cons (step457 p h) (sat_cons (step458 p h) (sat_cons (step853 p h) (sat_cons (step854 p h) (sat_cons (step755 p h) (sat_cons (step455 p h) (sat_cons (step131 p h) (sat_cons (step482 p h) (sat_cons (step477 p h) (sat_cons (step471 p h) (sat_cons (step465 p h) (sat_cons (step466 p h) (sat_cons (step140 p h) (sat_nil p))))))))))))))))))))))))))))))
def c1105 : List Lit := [(12, false), (785, false)]
theorem step1105 (p : Nat → Bool) (h : Constraints p) : clause p c1105 = true :=
  Snake9.LocalRup.prove_clause [c1078, c1072, c1101, c1098, c359, c411, c420, c441, c1103, c413, c406, c1089, c16, c367, c364, c374, c390, c394, c389, c377, c375, c365, c437, c436, c368, c370, c360, c424, c401, c1104, c984, c941, c826, c1052, c74] c1105 (by decide) p (sat_cons (step1078 p h) (sat_cons (step1072 p h) (sat_cons (step1101 p h) (sat_cons (step1098 p h) (sat_cons (step359 p h) (sat_cons (step411 p h) (sat_cons (step420 p h) (sat_cons (step441 p h) (sat_cons (step1103 p h) (sat_cons (step413 p h) (sat_cons (step406 p h) (sat_cons (step1089 p h) (sat_cons (step16 p h) (sat_cons (step367 p h) (sat_cons (step364 p h) (sat_cons (step374 p h) (sat_cons (step390 p h) (sat_cons (step394 p h) (sat_cons (step389 p h) (sat_cons (step377 p h) (sat_cons (step375 p h) (sat_cons (step365 p h) (sat_cons (step437 p h) (sat_cons (step436 p h) (sat_cons (step368 p h) (sat_cons (step370 p h) (sat_cons (step360 p h) (sat_cons (step424 p h) (sat_cons (step401 p h) (sat_cons (step1104 p h) (sat_cons (step984 p h) (sat_cons (step941 p h) (sat_cons (step826 p h) (sat_cons (step1052 p h) (sat_cons (step74 p h) (sat_nil p))))))))))))))))))))))))))))))))))))
def c1106 : List Lit := [(772, false), (785, false)]
theorem step1106 (p : Nat → Bool) (h : Constraints p) : clause p c1106 = true :=
  Snake9.LocalRup.prove_clause [c1082, c1072, c1078, c411, c420, c441, c386, c1105, c369, c378, c1101, c1098, c359, c437, c436, c421, c1104, c413, c406, c1089, c367, c368, c376, c375, c371, c390, c984, c362, c364, c813, c360, c7] c1106 (by decide) p (sat_cons (step1082 p h) (sat_cons (step1072 p h) (sat_cons (step1078 p h) (sat_cons (step411 p h) (sat_cons (step420 p h) (sat_cons (step441 p h) (sat_cons (step386 p h) (sat_cons (step1105 p h) (sat_cons (step369 p h) (sat_cons (step378 p h) (sat_cons (step1101 p h) (sat_cons (step1098 p h) (sat_cons (step359 p h) (sat_cons (step437 p h) (sat_cons (step436 p h) (sat_cons (step421 p h) (sat_cons (step1104 p h) (sat_cons (step413 p h) (sat_cons (step406 p h) (sat_cons (step1089 p h) (sat_cons (step367 p h) (sat_cons (step368 p h) (sat_cons (step376 p h) (sat_cons (step375 p h) (sat_cons (step371 p h) (sat_cons (step390 p h) (sat_cons (step984 p h) (sat_cons (step362 p h) (sat_cons (step364 p h) (sat_cons (step813 p h) (sat_cons (step360 p h) (sat_cons (step7 p h) (sat_nil p)))))))))))))))))))))))))))))))))
def c1107 : List Lit := [(785, false)]
theorem step1107 (p : Nat → Bool) (h : Constraints p) : clause p c1107 = true :=
  Snake9.LocalRup.prove_clause [c1072, c1082, c1078, c1098, c359, c1105, c369, c372, c384, c433, c1106, c385, c389, c373, c375, c362, c364, c371, c366, c367, c360, c7, c1089, c813, c413, c58, c421, c425, c403, c432, c398, c1104, c1008] c1107 (by decide) p (sat_cons (step1072 p h) (sat_cons (step1082 p h) (sat_cons (step1078 p h) (sat_cons (step1098 p h) (sat_cons (step359 p h) (sat_cons (step1105 p h) (sat_cons (step369 p h) (sat_cons (step372 p h) (sat_cons (step384 p h) (sat_cons (step433 p h) (sat_cons (step1106 p h) (sat_cons (step385 p h) (sat_cons (step389 p h) (sat_cons (step373 p h) (sat_cons (step375 p h) (sat_cons (step362 p h) (sat_cons (step364 p h) (sat_cons (step371 p h) (sat_cons (step366 p h) (sat_cons (step367 p h) (sat_cons (step360 p h) (sat_cons (step7 p h) (sat_cons (step1089 p h) (sat_cons (step813 p h) (sat_cons (step413 p h) (sat_cons (step58 p h) (sat_cons (step421 p h) (sat_cons (step425 p h) (sat_cons (step403 p h) (sat_cons (step432 p h) (sat_cons (step398 p h) (sat_cons (step1104 p h) (sat_cons (step1008 p h) (sat_nil p))))))))))))))))))))))))))))))))))
def c1108 : List Lit := [(24, true)]
theorem step1108 (p : Nat → Bool) (h : Constraints p) : clause p c1108 = true :=
  Snake9.LocalRup.prove_clause [c1107, c741] c1108 (by decide) p (sat_cons (step1107 p h) (sat_cons (step741 p h) (sat_nil p)))
def c1109 : List Lit := [(31, true)]
theorem step1109 (p : Nat → Bool) (h : Constraints p) : clause p c1109 = true :=
  Snake9.LocalRup.prove_clause [c1108, c846] c1109 (by decide) p (sat_cons (step1108 p h) (sat_cons (step846 p h) (sat_nil p)))
def c1110 : List Lit := [(7, true)]
theorem step1110 (p : Nat → Bool) (h : Constraints p) : clause p c1110 = true :=
  Snake9.LocalRup.prove_clause [c1108, c847] c1110 (by decide) p (sat_cons (step1108 p h) (sat_cons (step847 p h) (sat_nil p)))
def c1111 : List Lit := [(12, true), (3, false), (32, false), (9, false), (772, true)]
theorem step1111 (p : Nat → Bool) (h : Constraints p) : clause p c1111 = true :=
  Snake9.LocalRup.prove_clause [c1082, c1108, c1110, c923, c359, c385, c373, c369, c371, c372, c375, c389, c367, c362, c364, c1089, c360, c7, c743, c813, c827, c961] c1111 (by decide) p (sat_cons (step1082 p h) (sat_cons (step1108 p h) (sat_cons (step1110 p h) (sat_cons (step923 p h) (sat_cons (step359 p h) (sat_cons (step385 p h) (sat_cons (step373 p h) (sat_cons (step369 p h) (sat_cons (step371 p h) (sat_cons (step372 p h) (sat_cons (step375 p h) (sat_cons (step389 p h) (sat_cons (step367 p h) (sat_cons (step362 p h) (sat_cons (step364 p h) (sat_cons (step1089 p h) (sat_cons (step360 p h) (sat_cons (step7 p h) (sat_cons (step743 p h) (sat_cons (step813 p h) (sat_cons (step827 p h) (sat_cons (step961 p h) (sat_nil p)))))))))))))))))))))))
def c1112 : List Lit := [(1, false), (12, false), (3, false), (4, true), (772, true)]
theorem step1112 (p : Nat → Bool) (h : Constraints p) : clause p c1112 = true :=
  Snake9.LocalRup.prove_clause [c1082, c385, c700, c14, c813, c367, c374, c375, c389, c370, c362, c7, c360] c1112 (by decide) p (sat_cons (step1082 p h) (sat_cons (step385 p h) (sat_cons (step700 p h) (sat_cons (step14 p h) (sat_cons (step813 p h) (sat_cons (step367 p h) (sat_cons (step374 p h) (sat_cons (step375 p h) (sat_cons (step389 p h) (sat_cons (step370 p h) (sat_cons (step362 p h) (sat_cons (step7 p h) (sat_cons (step360 p h) (sat_nil p))))))))))))))
def c1113 : List Lit := [(3, false), (32, false), (9, false), (772, true)]
theorem step1113 (p : Nat → Bool) (h : Constraints p) : clause p c1113 = true :=
  Snake9.LocalRup.prove_clause [c1110, c1108, c1067, c1030, c48, c500, c506, c509, c1094, c901, c488, c923, c359, c393, c1111, c1112, c1095, c364, c365, c432, c389, c360, c374, c367, c1089, c701, c743, c424, c401, c941, c1052] c1113 (by decide) p (sat_cons (step1110 p h) (sat_cons (step1108 p h) (sat_cons (step1067 p h) (sat_cons (step1030 p h) (sat_cons (step48 p h) (sat_cons (step500 p h) (sat_cons (step506 p h) (sat_cons (step509 p h) (sat_cons (step1094 p h) (sat_cons (step901 p h) (sat_cons (step488 p h) (sat_cons (step923 p h) (sat_cons (step359 p h) (sat_cons (step393 p h) (sat_cons (step1111 p h) (sat_cons (step1112 p h) (sat_cons (step1095 p h) (sat_cons (step364 p h) (sat_cons (step365 p h) (sat_cons (step432 p h) (sat_cons (step389 p h) (sat_cons (step360 p h) (sat_cons (step374 p h) (sat_cons (step367 p h) (sat_cons (step1089 p h) (sat_cons (step701 p h) (sat_cons (step743 p h) (sat_cons (step424 p h) (sat_cons (step401 p h) (sat_cons (step941 p h) (sat_cons (step1052 p h) (sat_nil p))))))))))))))))))))))))))))))))
def c1114 : List Lit := [(32, false), (9, false), (772, true)]
theorem step1114 (p : Nat → Bool) (h : Constraints p) : clause p c1114 = true :=
  Snake9.LocalRup.prove_clause [c1110, c1108, c1067, c1030, c1078, c1082, c48, c500, c506, c509, c1094, c901, c488, c923, c359, c393, c1113, c840, c998, c999, c406, c372, c374, c743, c370, c367, c1016, c822, c1095, c365, c81, c432, c360, c424, c1008, c401, c399] c1114 (by decide) p (sat_cons (step1110 p h) (sat_cons (step1108 p h) (sat_cons (step1067 p h) (sat_cons (step1030 p h) (sat_cons (step1078 p h) (sat_cons (step1082 p h) (sat_cons (step48 p h) (sat_cons (step500 p h) (sat_cons (step506 p h) (sat_cons (step509 p h) (sat_cons (step1094 p h) (sat_cons (step901 p h) (sat_cons (step488 p h) (sat_cons (step923 p h) (sat_cons (step359 p h) (sat_cons (step393 p h) (sat_cons (step1113 p h) (sat_cons (step840 p h) (sat_cons (step998 p h) (sat_cons (step999 p h) (sat_cons (step406 p h) (sat_cons (step372 p h) (sat_cons (step374 p h) (sat_cons (step743 p h) (sat_cons (step370 p h) (sat_cons (step367 p h) (sat_cons (step1016 p h) (sat_cons (step822 p h) (sat_cons (step1095 p h) (sat_cons (step365 p h) (sat_cons (step81 p h) (sat_cons (step432 p h) (sat_cons (step360 p h) (sat_cons (step424 p h) (sat_cons (step1008 p h) (sat_cons (step401 p h) (sat_cons (step399 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))
def c1115 : List Lit := [(3, true), (9, false), (772, true)]
theorem step1115 (p : Nat → Bool) (h : Constraints p) : clause p c1115 = true :=
  Snake9.LocalRup.prove_clause [c1110, c1108, c1067, c1030, c1082, c1078, c1109, c1114, c849, c297, c298, c305, c307, c881, c291, c288, c287, c283, c281, c48, c500, c506, c509, c1094, c901, c488, c923, c359, c393, c840, c998, c999, c406, c372, c374, c743, c370, c367, c420, c1016, c821, c1095, c365, c844, c431, c360, c486, c1059, c886] c1115 (by decide) p (sat_cons (step1110 p h) (sat_cons (step1108 p h) (sat_cons (step1067 p h) (sat_cons (step1030 p h) (sat_cons (step1082 p h) (sat_cons (step1078 p h) (sat_cons (step1109 p h) (sat_cons (step1114 p h) (sat_cons (step849 p h) (sat_cons (step297 p h) (sat_cons (step298 p h) (sat_cons (step305 p h) (sat_cons (step307 p h) (sat_cons (step881 p h) (sat_cons (step291 p h) (sat_cons (step288 p h) (sat_cons (step287 p h) (sat_cons (step283 p h) (sat_cons (step281 p h) (sat_cons (step48 p h) (sat_cons (step500 p h) (sat_cons (step506 p h) (sat_cons (step509 p h) (sat_cons (step1094 p h) (sat_cons (step901 p h) (sat_cons (step488 p h) (sat_cons (step923 p h) (sat_cons (step359 p h) (sat_cons (step393 p h) (sat_cons (step840 p h) (sat_cons (step998 p h) (sat_cons (step999 p h) (sat_cons (step406 p h) (sat_cons (step372 p h) (sat_cons (step374 p h) (sat_cons (step743 p h) (sat_cons (step370 p h) (sat_cons (step367 p h) (sat_cons (step420 p h) (sat_cons (step1016 p h) (sat_cons (step821 p h) (sat_cons (step1095 p h) (sat_cons (step365 p h) (sat_cons (step844 p h) (sat_cons (step431 p h) (sat_cons (step360 p h) (sat_cons (step486 p h) (sat_cons (step1059 p h) (sat_cons (step886 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))
def c1116 : List Lit := [(12, false), (9, false), (772, true)]
theorem step1116 (p : Nat → Bool) (h : Constraints p) : clause p c1116 = true :=
  Snake9.LocalRup.prove_clause [c1110, c1108, c1067, c1030, c1078, c1109, c1115, c1114, c48, c500, c506, c509, c1094, c901, c488, c923, c359, c393, c1112, c1095, c364, c365, c432, c389, c360, c421, c374, c744, c367, c1089, c1090, c743, c407, c420, c1059, c431, c886, c486] c1116 (by decide) p (sat_cons (step1110 p h) (sat_cons (step1108 p h) (sat_cons (step1067 p h) (sat_cons (step1030 p h) (sat_cons (step1078 p h) (sat_cons (step1109 p h) (sat_cons (step1115 p h) (sat_cons (step1114 p h) (sat_cons (step48 p h) (sat_cons (step500 p h) (sat_cons (step506 p h) (sat_cons (step509 p h) (sat_cons (step1094 p h) (sat_cons (step901 p h) (sat_cons (step488 p h) (sat_cons (step923 p h) (sat_cons (step359 p h) (sat_cons (step393 p h) (sat_cons (step1112 p h) (sat_cons (step1095 p h) (sat_cons (step364 p h) (sat_cons (step365 p h) (sat_cons (step432 p h) (sat_cons (step389 p h) (sat_cons (step360 p h) (sat_cons (step421 p h) (sat_cons (step374 p h) (sat_cons (step744 p h) (sat_cons (step367 p h) (sat_cons (step1089 p h) (sat_cons (step1090 p h) (sat_cons (step743 p h) (sat_cons (step407 p h) (sat_cons (step420 p h) (sat_cons (step1059 p h) (sat_cons (step431 p h) (sat_cons (step886 p h) (sat_cons (step486 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))
def c1117 : List Lit := [(9, false), (772, true)]
theorem step1117 (p : Nat → Bool) (h : Constraints p) : clause p c1117 = true :=
  Snake9.LocalRup.prove_clause [c1082, c1108, c385, c373, c923, c359, c1114, c1115, c1116, c369, c371, c914, c372, c826, c827, c389, c1, c364] c1117 (by decide) p (sat_cons (step1082 p h) (sat_cons (step1108 p h) (sat_cons (step385 p h) (sat_cons (step373 p h) (sat_cons (step923 p h) (sat_cons (step359 p h) (sat_cons (step1114 p h) (sat_cons (step1115 p h) (sat_cons (step1116 p h) (sat_cons (step369 p h) (sat_cons (step371 p h) (sat_cons (step914 p h) (sat_cons (step372 p h) (sat_cons (step826 p h) (sat_cons (step827 p h) (sat_cons (step389 p h) (sat_cons (step1 p h) (sat_cons (step364 p h) (sat_nil p)))))))))))))))))))
def c1118 : List Lit := [(772, true)]
theorem step1118 (p : Nat → Bool) (h : Constraints p) : clause p c1118 = true :=
  Snake9.LocalRup.prove_clause [c1082, c385, c377, c1117, c366, c368, c374, c375, c389, c369, c370, c1004, c364, c1016, c14] c1118 (by decide) p (sat_cons (step1082 p h) (sat_cons (step385 p h) (sat_cons (step377 p h) (sat_cons (step1117 p h) (sat_cons (step366 p h) (sat_cons (step368 p h) (sat_cons (step374 p h) (sat_cons (step375 p h) (sat_cons (step389 p h) (sat_cons (step369 p h) (sat_cons (step370 p h) (sat_cons (step1004 p h) (sat_cons (step364 p h) (sat_cons (step1016 p h) (sat_cons (step14 p h) (sat_nil p))))))))))))))))
def c1119 : List Lit := [(801, true)]
theorem step1119 (p : Nat → Bool) (h : Constraints p) : clause p c1119 = true :=
  Snake9.LocalRup.prove_clause [c1118, c1079, c435] c1119 (by decide) p (sat_cons (step1118 p h) (sat_cons (step1079 p h) (sat_cons (step435 p h) (sat_nil p))))
def c1120 : List Lit := [(802, true), (9, true)]
theorem step1120 (p : Nat → Bool) (h : Constraints p) : clause p c1120 = true :=
  Snake9.LocalRup.prove_clause [c1079, c1118, c1082, c1078, c440, c436, c386, c420, c743, c406, c1089, c840, c368, c377, c378, c390, c369, c370, c16, c1004, c364] c1120 (by decide) p (sat_cons (step1079 p h) (sat_cons (step1118 p h) (sat_cons (step1082 p h) (sat_cons (step1078 p h) (sat_cons (step440 p h) (sat_cons (step436 p h) (sat_cons (step386 p h) (sat_cons (step420 p h) (sat_cons (step743 p h) (sat_cons (step406 p h) (sat_cons (step1089 p h) (sat_cons (step840 p h) (sat_cons (step368 p h) (sat_cons (step377 p h) (sat_cons (step378 p h) (sat_cons (step390 p h) (sat_cons (step369 p h) (sat_cons (step370 p h) (sat_cons (step16 p h) (sat_cons (step1004 p h) (sat_cons (step364 p h) (sat_nil p))))))))))))))))))))))
def c1121 : List Lit := [(902, true), (72, false), (65, false)]
theorem step1121 (p : Nat → Bool) (h : Constraints p) : clause p c1121 = true :=
  Snake9.LocalRup.prove_clause [c512, c513, c179] c1121 (by decide) p (sat_cons (step512 p h) (sat_cons (step513 p h) (sat_cons (step179 p h) (sat_nil p))))
def c1122 : List Lit := [(902, false), (802, false)]
theorem step1122 (p : Nat → Bool) (h : Constraints p) : clause p c1122 = true :=
  Snake9.LocalRup.prove_clause [c1068, c909, c1030, c1067, c1110, c488, c901, c1094, c509, c506, c500, c988, c535, c515, c518, c533, c865, c171, c764, c172, c521, c868] c1122 (by decide) p (sat_cons (step1068 p h) (sat_cons (step909 p h) (sat_cons (step1030 p h) (sat_cons (step1067 p h) (sat_cons (step1110 p h) (sat_cons (step488 p h) (sat_cons (step901 p h) (sat_cons (step1094 p h) (sat_cons (step509 p h) (sat_cons (step506 p h) (sat_cons (step500 p h) (sat_cons (step988 p h) (sat_cons (step535 p h) (sat_cons (step515 p h) (sat_cons (step518 p h) (sat_cons (step533 p h) (sat_cons (step865 p h) (sat_cons (step171 p h) (sat_cons (step764 p h) (sat_cons (step172 p h) (sat_cons (step521 p h) (sat_cons (step868 p h) (sat_nil p)))))))))))))))))))))))
def c1123 : List Lit := [(761, false), (9, true)]
theorem step1123 (p : Nat → Bool) (h : Constraints p) : clause p c1123 = true :=
  Snake9.LocalRup.prove_clause [c1080, c1072, c1078, c366, c374, c394, c395, c441, c377, c420, c368, c743, c1089] c1123 (by decide) p (sat_cons (step1080 p h) (sat_cons (step1072 p h) (sat_cons (step1078 p h) (sat_cons (step366 p h) (sat_cons (step374 p h) (sat_cons (step394 p h) (sat_cons (step395 p h) (sat_cons (step441 p h) (sat_cons (step377 p h) (sat_cons (step420 p h) (sat_cons (step368 p h) (sat_cons (step743 p h) (sat_cons (step1089 p h) (sat_nil p))))))))))))))
def c1124 : List Lit := [(12, false), (3, false), (9, true)]
theorem step1124 (p : Nat → Bool) (h : Constraints p) : clause p c1124 = true :=
  Snake9.LocalRup.prove_clause [c1030, c1067, c1108, c1078, c1072, c1120, c488, c901, c1094, c509, c506, c500, c934, c501, c1122, c512, c1121, c867, c166, c360, c1123, c365, c362, c16, c14, c406, c368, c743, c377, c420, c390, c441] c1124 (by decide) p (sat_cons (step1030 p h) (sat_cons (step1067 p h) (sat_cons (step1108 p h) (sat_cons (step1078 p h) (sat_cons (step1072 p h) (sat_cons (step1120 p h) (sat_cons (step488 p h) (sat_cons (step901 p h) (sat_cons (step1094 p h) (sat_cons (step509 p h) (sat_cons (step506 p h) (sat_cons (step500 p h) (sat_cons (step934 p h) (sat_cons (step501 p h) (sat_cons (step1122 p h) (sat_cons (step512 p h) (sat_cons (step1121 p h) (sat_cons (step867 p h) (sat_cons (step166 p h) (sat_cons (step360 p h) (sat_cons (step1123 p h) (sat_cons (step365 p h) (sat_cons (step362 p h) (sat_cons (step16 p h) (sat_cons (step14 p h) (sat_cons (step406 p h) (sat_cons (step368 p h) (sat_cons (step743 p h) (sat_cons (step377 p h) (sat_cons (step420 p h) (sat_cons (step390 p h) (sat_cons (step441 p h) (sat_nil p)))))))))))))))))))))))))))))))))
def c1125 : List Lit := [(764, false), (9, true)]
theorem step1125 (p : Nat → Bool) (h : Constraints p) : clause p c1125 = true :=
  Snake9.LocalRup.prove_clause [c1030, c1067, c1108, c1080, c1072, c1078, c1120, c488, c901, c1094, c509, c506, c500, c934, c501, c1122, c512, c1121, c867, c166, c360, c362, c391, c366, c378, c375, c368, c390, c1089, c441, c743, c420] c1125 (by decide) p (sat_cons (step1030 p h) (sat_cons (step1067 p h) (sat_cons (step1108 p h) (sat_cons (step1080 p h) (sat_cons (step1072 p h) (sat_cons (step1078 p h) (sat_cons (step1120 p h) (sat_cons (step488 p h) (sat_cons (step901 p h) (sat_cons (step1094 p h) (sat_cons (step509 p h) (sat_cons (step506 p h) (sat_cons (step500 p h) (sat_cons (step934 p h) (sat_cons (step501 p h) (sat_cons (step1122 p h) (sat_cons (step512 p h) (sat_cons (step1121 p h) (sat_cons (step867 p h) (sat_cons (step166 p h) (sat_cons (step360 p h) (sat_cons (step362 p h) (sat_cons (step391 p h) (sat_cons (step366 p h) (sat_cons (step378 p h) (sat_cons (step375 p h) (sat_cons (step368 p h) (sat_cons (step390 p h) (sat_cons (step1089 p h) (sat_cons (step441 p h) (sat_cons (step743 p h) (sat_cons (step420 p h) (sat_nil p)))))))))))))))))))))))))))))))))
def c1126 : List Lit := [(9, true)]
theorem step1126 (p : Nat → Bool) (h : Constraints p) : clause p c1126 = true :=
  Snake9.LocalRup.prove_clause [c1030, c1067, c1108, c1120, c488, c901, c1094, c509, c506, c500, c501, c934, c1122, c512, c1121, c867, c166, c360, c1123, c365, c1125, c369, c370, c1124, c1016] c1126 (by decide) p (sat_cons (step1030 p h) (sat_cons (step1067 p h) (sat_cons (step1108 p h) (sat_cons (step1120 p h) (sat_cons (step488 p h) (sat_cons (step901 p h) (sat_cons (step1094 p h) (sat_cons (step509 p h) (sat_cons (step506 p h) (sat_cons (step500 p h) (sat_cons (step501 p h) (sat_cons (step934 p h) (sat_cons (step1122 p h) (sat_cons (step512 p h) (sat_cons (step1121 p h) (sat_cons (step867 p h) (sat_cons (step166 p h) (sat_cons (step360 p h) (sat_cons (step1123 p h) (sat_cons (step365 p h) (sat_cons (step1125 p h) (sat_cons (step369 p h) (sat_cons (step370 p h) (sat_cons (step1124 p h) (sat_cons (step1016 p h) (sat_nil p))))))))))))))))))))))))))
def c1127 : List Lit := [(4, false)]
theorem step1127 (p : Nat → Bool) (h : Constraints p) : clause p c1127 = true :=
  Snake9.LocalRup.prove_clause [c1126, c1108, c923] c1127 (by decide) p (sat_cons (step1126 p h) (sat_cons (step1108 p h) (sat_cons (step923 p h) (sat_nil p))))
def c1128 : List Lit := [(68, false)]
theorem step1128 (p : Nat → Bool) (h : Constraints p) : clause p c1128 = true :=
  Snake9.LocalRup.prove_clause [c1126, c1110, c1108, c48] c1128 (by decide) p (sat_cons (step1126 p h) (sat_cons (step1110 p h) (sat_cons (step1108 p h) (sat_cons (step48 p h) (sat_nil p)))))
def c1129 : List Lit := [(757, true)]
theorem step1129 (p : Nat → Bool) (h : Constraints p) : clause p c1129 = true :=
  Snake9.LocalRup.prove_clause [c1127, c359] c1129 (by decide) p (sat_cons (step1127 p h) (sat_cons (step359 p h) (sat_nil p)))
def c1130 : List Lit := [(889, true)]
theorem step1130 (p : Nat → Bool) (h : Constraints p) : clause p c1130 = true :=
  Snake9.LocalRup.prove_clause [c1128, c500] c1130 (by decide) p (sat_cons (step1128 p h) (sat_cons (step500 p h) (sat_nil p)))
def c1131 : List Lit := [(892, true)]
theorem step1131 (p : Nat → Bool) (h : Constraints p) : clause p c1131 = true :=
  Snake9.LocalRup.prove_clause [c1130, c1067, c506] c1131 (by decide) p (sat_cons (step1130 p h) (sat_cons (step1067 p h) (sat_cons (step506 p h) (sat_nil p))))
def c1132 : List Lit := [(896, true)]
theorem step1132 (p : Nat → Bool) (h : Constraints p) : clause p c1132 = true :=
  Snake9.LocalRup.prove_clause [c1131, c509] c1132 (by decide) p (sat_cons (step1131 p h) (sat_cons (step509 p h) (sat_nil p)))
def c1133 : List Lit := [(1001, true)]
theorem step1133 (p : Nat → Bool) (h : Constraints p) : clause p c1133 = true :=
  Snake9.LocalRup.prove_clause [c1132, c1094] c1133 (by decide) p (sat_cons (step1132 p h) (sat_cons (step1094 p h) (sat_nil p)))
def c1134 : List Lit := [(874, false)]
theorem step1134 (p : Nat → Bool) (h : Constraints p) : clause p c1134 = true :=
  Snake9.LocalRup.prove_clause [c1133, c901] c1134 (by decide) p (sat_cons (step1133 p h) (sat_cons (step901 p h) (sat_nil p)))
def c1135 : List Lit := [(802, false)]
theorem step1135 (p : Nat → Bool) (h : Constraints p) : clause p c1135 = true :=
  Snake9.LocalRup.prove_clause [c1134, c1030, c488] c1135 (by decide) p (sat_cons (step1134 p h) (sat_cons (step1030 p h) (sat_cons (step488 p h) (sat_nil p))))
def c1136 : List Lit := [(855, false)]
theorem step1136 (p : Nat → Bool) (h : Constraints p) : clause p c1136 = true :=
  Snake9.LocalRup.prove_clause [c1134, c1119, c486] c1136 (by decide) p (sat_cons (step1134 p h) (sat_cons (step1119 p h) (sat_cons (step486 p h) (sat_nil p))))
def c1137 : List Lit := [(773, false)]
theorem step1137 (p : Nat → Bool) (h : Constraints p) : clause p c1137 = true :=
  Snake9.LocalRup.prove_clause [c1135, c1079, c440] c1137 (by decide) p (sat_cons (step1135 p h) (sat_cons (step1079 p h) (sat_cons (step440 p h) (sat_nil p))))
def c1138 : List Lit := [(792, false)]
theorem step1138 (p : Nat → Bool) (h : Constraints p) : clause p c1138 = true :=
  Snake9.LocalRup.prove_clause [c1135, c1118, c436] c1138 (by decide) p (sat_cons (step1135 p h) (sat_cons (step1118 p h) (sat_cons (step436 p h) (sat_nil p))))
def c1139 : List Lit := [(827, false)]
theorem step1139 (p : Nat → Bool) (h : Constraints p) : clause p c1139 = true :=
  Snake9.LocalRup.prove_clause [c1136, c886] c1139 (by decide) p (sat_cons (step1136 p h) (sat_cons (step886 p h) (sat_nil p)))
def c1140 : List Lit := [(768, false)]
theorem step1140 (p : Nat → Bool) (h : Constraints p) : clause p c1140 = true :=
  Snake9.LocalRup.prove_clause [c1137, c1082, c386] c1140 (by decide) p (sat_cons (step1137 p h) (sat_cons (step1082 p h) (sat_cons (step386 p h) (sat_nil p))))
def c1141 : List Lit := [(780, false)]
theorem step1141 (p : Nat → Bool) (h : Constraints p) : clause p c1141 = true :=
  Snake9.LocalRup.prove_clause [c1138, c747] c1141 (by decide) p (sat_cons (step1138 p h) (sat_cons (step747 p h) (sat_nil p)))
def c1142 : List Lit := [(787, false)]
theorem step1142 (p : Nat → Bool) (h : Constraints p) : clause p c1142 = true :=
  Snake9.LocalRup.prove_clause [c1138, c1078, c420] c1142 (by decide) p (sat_cons (step1138 p h) (sat_cons (step1078 p h) (sat_cons (step420 p h) (sat_nil p))))
def c1143 : List Lit := [(778, false)]
theorem step1143 (p : Nat → Bool) (h : Constraints p) : clause p c1143 = true :=
  Snake9.LocalRup.prove_clause [c1141, c401] c1143 (by decide) p (sat_cons (step1141 p h) (sat_cons (step401 p h) (sat_nil p)))
def c1144 : List Lit := [(782, false)]
theorem step1144 (p : Nat → Bool) (h : Constraints p) : clause p c1144 = true :=
  Snake9.LocalRup.prove_clause [c1142, c743] c1144 (by decide) p (sat_cons (step1142 p h) (sat_cons (step743 p h) (sat_nil p)))
def c1145 : List Lit := [(21, true)]
theorem step1145 (p : Nat → Bool) (h : Constraints p) : clause p c1145 = true :=
  Snake9.LocalRup.prove_clause [c1144, c405] c1145 (by decide) p (sat_cons (step1144 p h) (sat_cons (step405 p h) (sat_nil p)))
def c1146 : List Lit := [(20, true)]
theorem step1146 (p : Nat → Bool) (h : Constraints p) : clause p c1146 = true :=
  Snake9.LocalRup.prove_clause [c1144, c406] c1146 (by decide) p (sat_cons (step1144 p h) (sat_cons (step406 p h) (sat_nil p)))
def c1147 : List Lit := [(6, false)]
theorem step1147 (p : Nat → Bool) (h : Constraints p) : clause p c1147 = true :=
  Snake9.LocalRup.prove_clause [c1144, c1089] c1147 (by decide) p (sat_cons (step1144 p h) (sat_cons (step1089 p h) (sat_nil p)))
def c1148 : List Lit := [(3, true)]
theorem step1148 (p : Nat → Bool) (h : Constraints p) : clause p c1148 = true :=
  Snake9.LocalRup.prove_clause [c1146, c840] c1148 (by decide) p (sat_cons (step1146 p h) (sat_cons (step840 p h) (sat_nil p)))
def c1149 : List Lit := [(762, true)]
theorem step1149 (p : Nat → Bool) (h : Constraints p) : clause p c1149 = true :=
  Snake9.LocalRup.prove_clause [c1147, c367] c1149 (by decide) p (sat_cons (step1147 p h) (sat_cons (step367 p h) (sat_nil p)))
def c1150 : List Lit := [(766, true)]
theorem step1150 (p : Nat → Bool) (h : Constraints p) : clause p c1150 = true :=
  Snake9.LocalRup.prove_clause [c1149, c374] c1150 (by decide) p (sat_cons (step1149 p h) (sat_cons (step374 p h) (sat_nil p)))
def c1151 : List Lit := [(765, false)]
theorem step1151 (p : Nat → Bool) (h : Constraints p) : clause p c1151 = true :=
  Snake9.LocalRup.prove_clause [c1149, c1140, c376] c1151 (by decide) p (sat_cons (step1149 p h) (sat_cons (step1140 p h) (sat_cons (step376 p h) (sat_nil p))))
def c1152 : List Lit := [(761, false)]
theorem step1152 (p : Nat → Bool) (h : Constraints p) : clause p c1152 = true :=
  Snake9.LocalRup.prove_clause [c1150, c1137, c394] c1152 (by decide) p (sat_cons (step1150 p h) (sat_cons (step1137 p h) (sat_cons (step394 p h) (sat_nil p))))
def c1153 : List Lit := [(760, true)]
theorem step1153 (p : Nat → Bool) (h : Constraints p) : clause p c1153 = true :=
  Snake9.LocalRup.prove_clause [c1129, c1127, c1139, c1145, c1109, c1151, c1148, c1146, c1126, c362, c364, c360, c16, c1059, c371, c984, c7, c813] c1153 (by decide) p (sat_cons (step1129 p h) (sat_cons (step1127 p h) (sat_cons (step1139 p h) (sat_cons (step1145 p h) (sat_cons (step1109 p h) (sat_cons (step1151 p h) (sat_cons (step1148 p h) (sat_cons (step1146 p h) (sat_cons (step1126 p h) (sat_cons (step362 p h) (sat_cons (step364 p h) (sat_cons (step360 p h) (sat_cons (step16 p h) (sat_cons (step1059 p h) (sat_cons (step371 p h) (sat_cons (step984 p h) (sat_cons (step7 p h) (sat_cons (step813 p h) (sat_nil p)))))))))))))))))))
def c1154 : List Lit := [(767, false)]
theorem step1154 (p : Nat → Bool) (h : Constraints p) : clause p c1154 = true :=
  Snake9.LocalRup.prove_clause [c1153, c1137, c390] c1154 (by decide) p (sat_cons (step1153 p h) (sat_cons (step1137 p h) (sat_cons (step390 p h) (sat_nil p))))
def c1155 : List Lit := [(764, false)]
theorem step1155 (p : Nat → Bool) (h : Constraints p) : clause p c1155 = true :=
  Snake9.LocalRup.prove_clause [c1154, c1149, c375] c1155 (by decide) p (sat_cons (step1154 p h) (sat_cons (step1149 p h) (sat_cons (step375 p h) (sat_nil p))))
def c1156 : List Lit := [(12, true)]
theorem step1156 (p : Nat → Bool) (h : Constraints p) : clause p c1156 = true :=
  Snake9.LocalRup.prove_clause [c1155, c369] c1156 (by decide) p (sat_cons (step1155 p h) (sat_cons (step369 p h) (sat_nil p)))
def c1157 : List Lit := [(11, true)]
theorem step1157 (p : Nat → Bool) (h : Constraints p) : clause p c1157 = true :=
  Snake9.LocalRup.prove_clause [c1155, c370] c1157 (by decide) p (sat_cons (step1155 p h) (sat_cons (step370 p h) (sat_nil p)))
def c1158 : List Lit := [(1, false)]
theorem step1158 (p : Nat → Bool) (h : Constraints p) : clause p c1158 = true :=
  Snake9.LocalRup.prove_clause [c1156, c1146, c1148, c16] c1158 (by decide) p (sat_cons (step1156 p h) (sat_cons (step1146 p h) (sat_cons (step1148 p h) (sat_cons (step16 p h) (sat_nil p)))))
end B112E123
