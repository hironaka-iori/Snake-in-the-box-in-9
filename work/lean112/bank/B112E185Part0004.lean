import B112E185Part0003
namespace B112E185
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1053 : List Lit := [(57, true), (63, true), (56, false)]
theorem step1053 (p : Nat → Bool) (h : Constraints p) : clause p c1053 = true :=
  Snake9.LocalRup.prove_clause [c282, c168] c1053 (by decide) p (sat_cons (step282 p h) (sat_cons (step168 p h) (sat_nil p)))
def c1054 : List Lit := [(61, false), (60, true)]
theorem step1054 (p : Nat → Bool) (h : Constraints p) : clause p c1054 = true :=
  Snake9.LocalRup.prove_clause [c283, c177] c1054 (by decide) p (sat_cons (step283 p h) (sat_cons (step177 p h) (sat_nil p)))
def c1055 : List Lit := [(61, false), (58, true)]
theorem step1055 (p : Nat → Bool) (h : Constraints p) : clause p c1055 = true :=
  Snake9.LocalRup.prove_clause [c283, c178] c1055 (by decide) p (sat_cons (step283 p h) (sat_cons (step178 p h) (sat_nil p)))
def c1056 : List Lit := [(80, true), (66, true), (63, true), (62, false)]
theorem step1056 (p : Nat → Bool) (h : Constraints p) : clause p c1056 = true :=
  Snake9.LocalRup.prove_clause [c284, c179] c1056 (by decide) p (sat_cons (step284 p h) (sat_cons (step179 p h) (sat_nil p)))
def c1057 : List Lit := [(80, true), (63, true), (10, true), (62, false)]
theorem step1057 (p : Nat → Bool) (h : Constraints p) : clause p c1057 = true :=
  Snake9.LocalRup.prove_clause [c284, c180] c1057 (by decide) p (sat_cons (step284 p h) (sat_cons (step180 p h) (sat_nil p)))
def c1058 : List Lit := [(63, true), (65, true), (64, false)]
theorem step1058 (p : Nat → Bool) (h : Constraints p) : clause p c1058 = true :=
  Snake9.LocalRup.prove_clause [c285, c185] c1058 (by decide) p (sat_cons (step285 p h) (sat_cons (step185 p h) (sat_nil p)))
def c1059 : List Lit := [(67, false), (68, true)]
theorem step1059 (p : Nat → Bool) (h : Constraints p) : clause p c1059 = true :=
  Snake9.LocalRup.prove_clause [c286, c191] c1059 (by decide) p (sat_cons (step286 p h) (sat_cons (step191 p h) (sat_nil p)))
def c1060 : List Lit := [(70, false), (71, true)]
theorem step1060 (p : Nat → Bool) (h : Constraints p) : clause p c1060 = true :=
  Snake9.LocalRup.prove_clause [c288, c197] c1060 (by decide) p (sat_cons (step288 p h) (sat_cons (step197 p h) (sat_nil p)))
def c1061 : List Lit := [(70, false), (23, true)]
theorem step1061 (p : Nat → Bool) (h : Constraints p) : clause p c1061 = true :=
  Snake9.LocalRup.prove_clause [c288, c198] c1061 (by decide) p (sat_cons (step288 p h) (sat_cons (step198 p h) (sat_nil p)))
def c1062 : List Lit := [(26, true), (102, true), (75, false), (63, true)]
theorem step1062 (p : Nat → Bool) (h : Constraints p) : clause p c1062 = true :=
  Snake9.LocalRup.prove_clause [c290, c205] c1062 (by decide) p (sat_cons (step290 p h) (sat_cons (step205 p h) (sat_nil p)))
def c1063 : List Lit := [(77, false), (73, true)]
theorem step1063 (p : Nat → Bool) (h : Constraints p) : clause p c1063 = true :=
  Snake9.LocalRup.prove_clause [c291, c208] c1063 (by decide) p (sat_cons (step291 p h) (sat_cons (step208 p h) (sat_nil p)))
def c1064 : List Lit := [(82, true), (94, true), (55, true), (79, false)]
theorem step1064 (p : Nat → Bool) (h : Constraints p) : clause p c1064 = true :=
  Snake9.LocalRup.prove_clause [c293, c212] c1064 (by decide) p (sat_cons (step293 p h) (sat_cons (step212 p h) (sat_nil p)))
def c1065 : List Lit := [(83, true), (82, true), (55, true), (79, false)]
theorem step1065 (p : Nat → Bool) (h : Constraints p) : clause p c1065 = true :=
  Snake9.LocalRup.prove_clause [c293, c213] c1065 (by decide) p (sat_cons (step293 p h) (sat_cons (step213 p h) (sat_nil p)))
def c1066 : List Lit := [(81, false), (82, true)]
theorem step1066 (p : Nat → Bool) (h : Constraints p) : clause p c1066 = true :=
  Snake9.LocalRup.prove_clause [c294, c218] c1066 (by decide) p (sat_cons (step294 p h) (sat_cons (step218 p h) (sat_nil p)))
def c1067 : List Lit := [(81, false), (80, true)]
theorem step1067 (p : Nat → Bool) (h : Constraints p) : clause p c1067 = true :=
  Snake9.LocalRup.prove_clause [c294, c219] c1067 (by decide) p (sat_cons (step294 p h) (sat_cons (step219 p h) (sat_nil p)))
def c1068 : List Lit := [(35, true), (83, true), (85, false)]
theorem step1068 (p : Nat → Bool) (h : Constraints p) : clause p c1068 = true :=
  Snake9.LocalRup.prove_clause [c295, c223] c1068 (by decide) p (sat_cons (step295 p h) (sat_cons (step223 p h) (sat_nil p)))
def c1069 : List Lit := [(87, true), (86, false), (38, true)]
theorem step1069 (p : Nat → Bool) (h : Constraints p) : clause p c1069 = true :=
  Snake9.LocalRup.prove_clause [c296, c224] c1069 (by decide) p (sat_cons (step296 p h) (sat_cons (step224 p h) (sat_nil p)))
def c1070 : List Lit := [(86, false), (38, true), (80, true)]
theorem step1070 (p : Nat → Bool) (h : Constraints p) : clause p c1070 = true :=
  Snake9.LocalRup.prove_clause [c296, c225] c1070 (by decide) p (sat_cons (step296 p h) (sat_cons (step225 p h) (sat_nil p)))
def c1071 : List Lit := [(89, true), (88, false), (84, true)]
theorem step1071 (p : Nat → Bool) (h : Constraints p) : clause p c1071 = true :=
  Snake9.LocalRup.prove_clause [c297, c228] c1071 (by decide) p (sat_cons (step297 p h) (sat_cons (step228 p h) (sat_nil p)))
def c1072 : List Lit := [(87, true), (88, false), (84, true)]
theorem step1072 (p : Nat → Bool) (h : Constraints p) : clause p c1072 = true :=
  Snake9.LocalRup.prove_clause [c297, c229] c1072 (by decide) p (sat_cons (step297 p h) (sat_cons (step229 p h) (sat_nil p)))
def c1073 : List Lit := [(91, false), (85, true), (199, true)]
theorem step1073 (p : Nat → Bool) (h : Constraints p) : clause p c1073 = true :=
  Snake9.LocalRup.prove_clause [c803, c234] c1073 (by decide) p (sat_cons (step803 p h) (sat_cons (step234 p h) (sat_nil p)))
def c1074 : List Lit := [(91, true), (92, false), (47, true)]
theorem step1074 (p : Nat → Bool) (h : Constraints p) : clause p c1074 = true :=
  Snake9.LocalRup.prove_clause [c299, c235] c1074 (by decide) p (sat_cons (step299 p h) (sat_cons (step235 p h) (sat_nil p)))
def c1075 : List Lit := [(89, true), (92, false), (47, true)]
theorem step1075 (p : Nat → Bool) (h : Constraints p) : clause p c1075 = true :=
  Snake9.LocalRup.prove_clause [c299, c236] c1075 (by decide) p (sat_cons (step299 p h) (sat_cons (step236 p h) (sat_nil p)))
def c1076 : List Lit := [(93, false), (97, true)]
theorem step1076 (p : Nat → Bool) (h : Constraints p) : clause p c1076 = true :=
  Snake9.LocalRup.prove_clause [c300, c237] c1076 (by decide) p (sat_cons (step300 p h) (sat_cons (step237 p h) (sat_nil p)))
def c1077 : List Lit := [(93, false), (94, true)]
theorem step1077 (p : Nat → Bool) (h : Constraints p) : clause p c1077 = true :=
  Snake9.LocalRup.prove_clause [c300, c238] c1077 (by decide) p (sat_cons (step300 p h) (sat_cons (step238 p h) (sat_nil p)))
def c1078 : List Lit := [(100, false), (97, true)]
theorem step1078 (p : Nat → Bool) (h : Constraints p) : clause p c1078 = true :=
  Snake9.LocalRup.prove_clause [c301, c241] c1078 (by decide) p (sat_cons (step301 p h) (sat_cons (step241 p h) (sat_nil p)))
def c1079 : List Lit := [(106, false), (107, true)]
theorem step1079 (p : Nat → Bool) (h : Constraints p) : clause p c1079 = true :=
  Snake9.LocalRup.prove_clause [c302, c251] c1079 (by decide) p (sat_cons (step302 p h) (sat_cons (step251 p h) (sat_nil p)))
def c1080 : List Lit := [(106, false), (105, true)]
theorem step1080 (p : Nat → Bool) (h : Constraints p) : clause p c1080 = true :=
  Snake9.LocalRup.prove_clause [c302, c252] c1080 (by decide) p (sat_cons (step302 p h) (sat_cons (step252 p h) (sat_nil p)))
def c1081 : List Lit := [(108, false), (107, true)]
theorem step1081 (p : Nat → Bool) (h : Constraints p) : clause p c1081 = true :=
  Snake9.LocalRup.prove_clause [c303, c255] c1081 (by decide) p (sat_cons (step303 p h) (sat_cons (step255 p h) (sat_nil p)))
def c1082 : List Lit := [(279, false), (285, false)]
theorem step1082 (p : Nat → Bool) (h : Constraints p) : clause p c1082 = true :=
  Snake9.LocalRup.prove_clause [c819, c331] c1082 (by decide) p (sat_cons (step819 p h) (sat_cons (step331 p h) (sat_nil p)))
def c1083 : List Lit := [(149, false), (150, false)]
theorem step1083 (p : Nat → Bool) (h : Constraints p) : clause p c1083 = true :=
  Snake9.LocalRup.prove_clause [c826, c338] c1083 (by decide) p (sat_cons (step826 p h) (sat_cons (step338 p h) (sat_nil p)))
def c1084 : List Lit := [(293, false), (299, false)]
theorem step1084 (p : Nat → Bool) (h : Constraints p) : clause p c1084 = true :=
  Snake9.LocalRup.prove_clause [c818, c345] c1084 (by decide) p (sat_cons (step818 p h) (sat_cons (step345 p h) (sat_nil p)))
def c1085 : List Lit := [(157, false), (158, false)]
theorem step1085 (p : Nat → Bool) (h : Constraints p) : clause p c1085 = true :=
  Snake9.LocalRup.prove_clause [c825, c349] c1085 (by decide) p (sat_cons (step825 p h) (sat_cons (step349 p h) (sat_nil p)))
def c1086 : List Lit := [(305, false), (311, false)]
theorem step1086 (p : Nat → Bool) (h : Constraints p) : clause p c1086 = true :=
  Snake9.LocalRup.prove_clause [c817, c355] c1086 (by decide) p (sat_cons (step817 p h) (sat_cons (step355 p h) (sat_nil p)))
def c1087 : List Lit := [(301, false), (313, false)]
theorem step1087 (p : Nat → Bool) (h : Constraints p) : clause p c1087 = true :=
  Snake9.LocalRup.prove_clause [c812, c360] c1087 (by decide) p (sat_cons (step812 p h) (sat_cons (step360 p h) (sat_nil p)))
def c1088 : List Lit := [(289, false), (315, false)]
theorem step1088 (p : Nat → Bool) (h : Constraints p) : clause p c1088 = true :=
  Snake9.LocalRup.prove_clause [c808, c365] c1088 (by decide) p (sat_cons (step808 p h) (sat_cons (step365 p h) (sat_nil p)))
def c1089 : List Lit := [(265, false), (317, false)]
theorem step1089 (p : Nat → Bool) (h : Constraints p) : clause p c1089 = true :=
  Snake9.LocalRup.prove_clause [c805, c370] c1089 (by decide) p (sat_cons (step805 p h) (sat_cons (step370 p h) (sat_nil p)))
def c1090 : List Lit := [(375, false), (379, false)]
theorem step1090 (p : Nat → Bool) (h : Constraints p) : clause p c1090 = true :=
  Snake9.LocalRup.prove_clause [c814, c409] c1090 (by decide) p (sat_cons (step814 p h) (sat_cons (step409 p h) (sat_nil p)))
def c1091 : List Lit := [(395, false), (421, false)]
theorem step1091 (p : Nat → Bool) (h : Constraints p) : clause p c1091 = true :=
  Snake9.LocalRup.prove_clause [c806, c430] c1091 (by decide) p (sat_cons (step806 p h) (sat_cons (step430 p h) (sat_nil p)))
def c1092 : List Lit := [(371, false), (423, false)]
theorem step1092 (p : Nat → Bool) (h : Constraints p) : clause p c1092 = true :=
  Snake9.LocalRup.prove_clause [c804, c435] c1092 (by decide) p (sat_cons (step804 p h) (sat_cons (step435 p h) (sat_nil p)))
def c1093 : List Lit := [(319, false), (425, false)]
theorem step1093 (p : Nat → Bool) (h : Constraints p) : clause p c1093 = true :=
  Snake9.LocalRup.prove_clause [c440, c438] c1093 (by decide) p (sat_cons (step440 p h) (sat_cons (step438 p h) (sat_nil p)))
def c1094 : List Lit := [(787, false), (857, true)]
theorem step1094 (p : Nat → Bool) (h : Constraints p) : clause p c1094 = true :=
  Snake9.LocalRup.prove_clause [c886, c589] c1094 (by decide) p (sat_cons (step886 p h) (sat_cons (step589 p h) (sat_nil p)))
def c1095 : List Lit := [(842, false), (788, false)]
theorem step1095 (p : Nat → Bool) (h : Constraints p) : clause p c1095 = true :=
  Snake9.LocalRup.prove_clause [c929, c596] c1095 (by decide) p (sat_cons (step929 p h) (sat_cons (step596 p h) (sat_nil p)))
def c1096 : List Lit := [(979, true), (908, false)]
theorem step1096 (p : Nat → Bool) (h : Constraints p) : clause p c1096 = true :=
  Snake9.LocalRup.prove_clause [c919, c728] c1096 (by decide) p (sat_cons (step919 p h) (sat_cons (step728 p h) (sat_nil p)))
def c1097 : List Lit := [(980, true), (909, false)]
theorem step1097 (p : Nat → Bool) (h : Constraints p) : clause p c1097 = true :=
  Snake9.LocalRup.prove_clause [c919, c731] c1097 (by decide) p (sat_cons (step919 p h) (sat_cons (step731 p h) (sat_nil p)))
def c1098 : List Lit := [(981, true), (910, false)]
theorem step1098 (p : Nat → Bool) (h : Constraints p) : clause p c1098 = true :=
  Snake9.LocalRup.prove_clause [c919, c733] c1098 (by decide) p (sat_cons (step919 p h) (sat_cons (step733 p h) (sat_nil p)))
def c1099 : List Lit := [(982, true), (911, false)]
theorem step1099 (p : Nat → Bool) (h : Constraints p) : clause p c1099 = true :=
  Snake9.LocalRup.prove_clause [c919, c735] c1099 (by decide) p (sat_cons (step919 p h) (sat_cons (step735 p h) (sat_nil p)))
def c1100 : List Lit := [(983, true), (912, false)]
theorem step1100 (p : Nat → Bool) (h : Constraints p) : clause p c1100 = true :=
  Snake9.LocalRup.prove_clause [c919, c736] c1100 (by decide) p (sat_cons (step919 p h) (sat_cons (step736 p h) (sat_nil p)))
def c1101 : List Lit := [(857, false), (983, false)]
theorem step1101 (p : Nat → Bool) (h : Constraints p) : clause p c1101 = true :=
  Snake9.LocalRup.prove_clause [c743, c737] c1101 (by decide) p (sat_cons (step743 p h) (sat_cons (step737 p h) (sat_nil p)))
def c1102 : List Lit := [(858, false), (982, false)]
theorem step1102 (p : Nat → Bool) (h : Constraints p) : clause p c1102 = true :=
  Snake9.LocalRup.prove_clause [c743, c738] c1102 (by decide) p (sat_cons (step743 p h) (sat_cons (step738 p h) (sat_nil p)))
def c1103 : List Lit := [(859, false), (981, false)]
theorem step1103 (p : Nat → Bool) (h : Constraints p) : clause p c1103 = true :=
  Snake9.LocalRup.prove_clause [c743, c739] c1103 (by decide) p (sat_cons (step743 p h) (sat_cons (step739 p h) (sat_nil p)))
def c1104 : List Lit := [(860, false), (980, false)]
theorem step1104 (p : Nat → Bool) (h : Constraints p) : clause p c1104 = true :=
  Snake9.LocalRup.prove_clause [c743, c740] c1104 (by decide) p (sat_cons (step743 p h) (sat_cons (step740 p h) (sat_nil p)))
def c1105 : List Lit := [(861, false), (979, false)]
theorem step1105 (p : Nat → Bool) (h : Constraints p) : clause p c1105 = true :=
  Snake9.LocalRup.prove_clause [c743, c741] c1105 (by decide) p (sat_cons (step743 p h) (sat_cons (step741 p h) (sat_nil p)))
def c1106 : List Lit := [(1415, false), (1442, true)]
theorem step1106 (p : Nat → Bool) (h : Constraints p) : clause p c1106 = true :=
  Snake9.LocalRup.prove_clause [c874, c774] c1106 (by decide) p (sat_cons (step874 p h) (sat_cons (step774 p h) (sat_nil p)))
def c1107 : List Lit := [(1398, false), (1506, false)]
theorem step1107 (p : Nat → Bool) (h : Constraints p) : clause p c1107 = true :=
  Snake9.LocalRup.prove_clause [c785, c784] c1107 (by decide) p (sat_cons (step785 p h) (sat_cons (step784 p h) (sat_nil p)))
def c1108 : List Lit := [(902, false), (867, false), (778, false), (3, false), (6, false), (876, false)]
theorem step1108 (p : Nat → Bool) (h : Constraints p) : clause p c1108 = true :=
  Snake9.LocalRup.prove_clause [c919, c904] c1108 (by decide) p (sat_cons (step919 p h) (sat_cons (step904 p h) (sat_nil p)))
def c1109 : List Lit := [(789, true), (18, false), (6, true), (72, true), (748, false), (746, true), (3, true)]
theorem step1109 (p : Nat → Bool) (h : Constraints p) : clause p c1109 = true :=
  Snake9.LocalRup.prove_clause [c900, c921, c458, c468, c445, c1028, c486, c830, c975, c499, c517, c513, c469, c502, c500, c461, c459, c492, c451, c828, c1029, c39, c968, c443, c447, c937, c454, c986, c483, c478, c953, c43] c1109 (by decide) p (sat_cons (step900 p h) (sat_cons (step921 p h) (sat_cons (step458 p h) (sat_cons (step468 p h) (sat_cons (step445 p h) (sat_cons (step1028 p h) (sat_cons (step486 p h) (sat_cons (step830 p h) (sat_cons (step975 p h) (sat_cons (step499 p h) (sat_cons (step517 p h) (sat_cons (step513 p h) (sat_cons (step469 p h) (sat_cons (step502 p h) (sat_cons (step500 p h) (sat_cons (step461 p h) (sat_cons (step459 p h) (sat_cons (step492 p h) (sat_cons (step451 p h) (sat_cons (step828 p h) (sat_cons (step1029 p h) (sat_cons (step39 p h) (sat_cons (step968 p h) (sat_cons (step443 p h) (sat_cons (step447 p h) (sat_cons (step937 p h) (sat_cons (step454 p h) (sat_cons (step986 p h) (sat_cons (step483 p h) (sat_cons (step478 p h) (sat_cons (step953 p h) (sat_cons (step43 p h) (sat_nil p)))))))))))))))))))))))))))))))))
def c1110 : List Lit := [(909, true), (744, true), (3, true)]
theorem step1110 (p : Nat → Bool) (h : Constraints p) : clause p c1110 = true :=
  Snake9.LocalRup.prove_clause [c930, c860, c952, c628, c626, c443, c606, c616, c618, c946, c614, c610, c923, c943, c604] c1110 (by decide) p (sat_cons (step930 p h) (sat_cons (step860 p h) (sat_cons (step952 p h) (sat_cons (step628 p h) (sat_cons (step626 p h) (sat_cons (step443 p h) (sat_cons (step606 p h) (sat_cons (step616 p h) (sat_cons (step618 p h) (sat_cons (step946 p h) (sat_cons (step614 p h) (sat_cons (step610 p h) (sat_cons (step923 p h) (sat_cons (step943 p h) (sat_cons (step604 p h) (sat_nil p))))))))))))))))
def c1111 : List Lit := [(6, true), (72, true), (748, false), (802, false), (3, true)]
theorem step1111 (p : Nat → Bool) (h : Constraints p) : clause p c1111 = true :=
  Snake9.LocalRup.prove_clause [c1028, c486, c975, c900, c1012, c921, c458, c468, c990, c445, c1110, c1097, c1104, c598, c513, c500, c492, c828, c1029, c830, c502, c481, c499, c517, c469, c461, c978, c536, c930, c1109, c477, c483, c451, c479, c989, c39, c626, c443, c983, c43, c1017] c1111 (by decide) p (sat_cons (step1028 p h) (sat_cons (step486 p h) (sat_cons (step975 p h) (sat_cons (step900 p h) (sat_cons (step1012 p h) (sat_cons (step921 p h) (sat_cons (step458 p h) (sat_cons (step468 p h) (sat_cons (step990 p h) (sat_cons (step445 p h) (sat_cons (step1110 p h) (sat_cons (step1097 p h) (sat_cons (step1104 p h) (sat_cons (step598 p h) (sat_cons (step513 p h) (sat_cons (step500 p h) (sat_cons (step492 p h) (sat_cons (step828 p h) (sat_cons (step1029 p h) (sat_cons (step830 p h) (sat_cons (step502 p h) (sat_cons (step481 p h) (sat_cons (step499 p h) (sat_cons (step517 p h) (sat_cons (step469 p h) (sat_cons (step461 p h) (sat_cons (step978 p h) (sat_cons (step536 p h) (sat_cons (step930 p h) (sat_cons (step1109 p h) (sat_cons (step477 p h) (sat_cons (step483 p h) (sat_cons (step451 p h) (sat_cons (step479 p h) (sat_cons (step989 p h) (sat_cons (step39 p h) (sat_cons (step626 p h) (sat_cons (step443 p h) (sat_cons (step983 p h) (sat_cons (step43 p h) (sat_cons (step1017 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))
def c1112 : List Lit := [(72, true), (748, false), (802, false), (3, true)]
theorem step1112 (p : Nat → Bool) (h : Constraints p) : clause p c1112 = true :=
  Snake9.LocalRup.prove_clause [c1028, c486, c975, c900, c1012, c921, c458, c468, c990, c445, c1110, c1097, c1104, c598, c513, c500, c492, c828, c830, c499, c517, c469, c459, c502, c1111, c968, c1016, c447, c937, c454, c63, c986, c477, c483] c1112 (by decide) p (sat_cons (step1028 p h) (sat_cons (step486 p h) (sat_cons (step975 p h) (sat_cons (step900 p h) (sat_cons (step1012 p h) (sat_cons (step921 p h) (sat_cons (step458 p h) (sat_cons (step468 p h) (sat_cons (step990 p h) (sat_cons (step445 p h) (sat_cons (step1110 p h) (sat_cons (step1097 p h) (sat_cons (step1104 p h) (sat_cons (step598 p h) (sat_cons (step513 p h) (sat_cons (step500 p h) (sat_cons (step492 p h) (sat_cons (step828 p h) (sat_cons (step830 p h) (sat_cons (step499 p h) (sat_cons (step517 p h) (sat_cons (step469 p h) (sat_cons (step459 p h) (sat_cons (step502 p h) (sat_cons (step1111 p h) (sat_cons (step968 p h) (sat_cons (step1016 p h) (sat_cons (step447 p h) (sat_cons (step937 p h) (sat_cons (step454 p h) (sat_cons (step63 p h) (sat_cons (step986 p h) (sat_cons (step477 p h) (sat_cons (step483 p h) (sat_nil p)))))))))))))))))))))))))))))))))))
def c1113 : List Lit := [(70, true), (748, false), (802, false), (3, true)]
theorem step1113 (p : Nat → Bool) (h : Constraints p) : clause p c1113 = true :=
  Snake9.LocalRup.prove_clause [c1112, c1028, c486, c975, c900, c1012, c921, c458, c468, c990, c445, c1110, c1097, c1104, c598, c513, c500, c492, c828, c830, c499, c517, c469, c459, c930, c625, c978, c593, c1103, c1098, c663, c856, c637, c634, c635, c636, c201, c855, c964, c665, c447, c626, c1008, c618, c610] c1113 (by decide) p (sat_cons (step1112 p h) (sat_cons (step1028 p h) (sat_cons (step486 p h) (sat_cons (step975 p h) (sat_cons (step900 p h) (sat_cons (step1012 p h) (sat_cons (step921 p h) (sat_cons (step458 p h) (sat_cons (step468 p h) (sat_cons (step990 p h) (sat_cons (step445 p h) (sat_cons (step1110 p h) (sat_cons (step1097 p h) (sat_cons (step1104 p h) (sat_cons (step598 p h) (sat_cons (step513 p h) (sat_cons (step500 p h) (sat_cons (step492 p h) (sat_cons (step828 p h) (sat_cons (step830 p h) (sat_cons (step499 p h) (sat_cons (step517 p h) (sat_cons (step469 p h) (sat_cons (step459 p h) (sat_cons (step930 p h) (sat_cons (step625 p h) (sat_cons (step978 p h) (sat_cons (step593 p h) (sat_cons (step1103 p h) (sat_cons (step1098 p h) (sat_cons (step663 p h) (sat_cons (step856 p h) (sat_cons (step637 p h) (sat_cons (step634 p h) (sat_cons (step635 p h) (sat_cons (step636 p h) (sat_cons (step201 p h) (sat_cons (step855 p h) (sat_cons (step964 p h) (sat_cons (step665 p h) (sat_cons (step447 p h) (sat_cons (step626 p h) (sat_cons (step1008 p h) (sat_cons (step618 p h) (sat_cons (step610 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))
def c1114 : List Lit := [(748, false), (802, false), (3, true)]
theorem step1114 (p : Nat → Bool) (h : Constraints p) : clause p c1114 = true :=
  Snake9.LocalRup.prove_clause [c900, c1028, c486, c830, c975, c499, c990, c1012, c445, c1110, c1097, c1104, c598, c517, c469, c930, c625, c978, c593, c1103, c1098, c663, c921, c458, c468, c513, c500, c459, c492, c828, c1112, c1113, c1060, c873, c1063, c641, c852, c652, c655, c665, c636, c626, c633, c618, c201, c610, c964, c1008, c447] c1114 (by decide) p (sat_cons (step900 p h) (sat_cons (step1028 p h) (sat_cons (step486 p h) (sat_cons (step830 p h) (sat_cons (step975 p h) (sat_cons (step499 p h) (sat_cons (step990 p h) (sat_cons (step1012 p h) (sat_cons (step445 p h) (sat_cons (step1110 p h) (sat_cons (step1097 p h) (sat_cons (step1104 p h) (sat_cons (step598 p h) (sat_cons (step517 p h) (sat_cons (step469 p h) (sat_cons (step930 p h) (sat_cons (step625 p h) (sat_cons (step978 p h) (sat_cons (step593 p h) (sat_cons (step1103 p h) (sat_cons (step1098 p h) (sat_cons (step663 p h) (sat_cons (step921 p h) (sat_cons (step458 p h) (sat_cons (step468 p h) (sat_cons (step513 p h) (sat_cons (step500 p h) (sat_cons (step459 p h) (sat_cons (step492 p h) (sat_cons (step828 p h) (sat_cons (step1112 p h) (sat_cons (step1113 p h) (sat_cons (step1060 p h) (sat_cons (step873 p h) (sat_cons (step1063 p h) (sat_cons (step641 p h) (sat_cons (step852 p h) (sat_cons (step652 p h) (sat_cons (step655 p h) (sat_cons (step665 p h) (sat_cons (step636 p h) (sat_cons (step626 p h) (sat_cons (step633 p h) (sat_cons (step618 p h) (sat_cons (step201 p h) (sat_cons (step610 p h) (sat_cons (step964 p h) (sat_cons (step1008 p h) (sat_cons (step447 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))
def c1115 : List Lit := [(751, true), (1, false), (24, false), (802, false), (3, true)]
theorem step1115 (p : Nat → Bool) (h : Constraints p) : clause p c1115 = true :=
  Snake9.LocalRup.prove_clause [c937, c1114, c450, c1016, c1028, c486, c830, c900, c1012, c921, c455, c467, c990, c445, c1110, c1097, c1104, c598, c509, c505, c449, c978, c536, c930, c1008, c454, c610, c63, c986, c618, c484, c626, c479, c983, c1017, c1018, c43, c39, c443] c1115 (by decide) p (sat_cons (step937 p h) (sat_cons (step1114 p h) (sat_cons (step450 p h) (sat_cons (step1016 p h) (sat_cons (step1028 p h) (sat_cons (step486 p h) (sat_cons (step830 p h) (sat_cons (step900 p h) (sat_cons (step1012 p h) (sat_cons (step921 p h) (sat_cons (step455 p h) (sat_cons (step467 p h) (sat_cons (step990 p h) (sat_cons (step445 p h) (sat_cons (step1110 p h) (sat_cons (step1097 p h) (sat_cons (step1104 p h) (sat_cons (step598 p h) (sat_cons (step509 p h) (sat_cons (step505 p h) (sat_cons (step449 p h) (sat_cons (step978 p h) (sat_cons (step536 p h) (sat_cons (step930 p h) (sat_cons (step1008 p h) (sat_cons (step454 p h) (sat_cons (step610 p h) (sat_cons (step63 p h) (sat_cons (step986 p h) (sat_cons (step618 p h) (sat_cons (step484 p h) (sat_cons (step626 p h) (sat_cons (step479 p h) (sat_cons (step983 p h) (sat_cons (step1017 p h) (sat_cons (step1018 p h) (sat_cons (step43 p h) (sat_cons (step39 p h) (sat_cons (step443 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))
def c1116 : List Lit := [(70, true), (24, false), (72, false), (802, false), (3, true)]
theorem step1116 (p : Nat → Bool) (h : Constraints p) : clause p c1116 = true :=
  Snake9.LocalRup.prove_clause [c930, c625, c990, c1012, c978, c593, c1103, c1098, c663, c856, c637, c445, c634, c635, c636, c201, c855, c655, c602, c665, c647, c628, c626, c850, c606, c608, c616, c618, c604, c1052, c614, c610, c166, c943, c443] c1116 (by decide) p (sat_cons (step930 p h) (sat_cons (step625 p h) (sat_cons (step990 p h) (sat_cons (step1012 p h) (sat_cons (step978 p h) (sat_cons (step593 p h) (sat_cons (step1103 p h) (sat_cons (step1098 p h) (sat_cons (step663 p h) (sat_cons (step856 p h) (sat_cons (step637 p h) (sat_cons (step445 p h) (sat_cons (step634 p h) (sat_cons (step635 p h) (sat_cons (step636 p h) (sat_cons (step201 p h) (sat_cons (step855 p h) (sat_cons (step655 p h) (sat_cons (step602 p h) (sat_cons (step665 p h) (sat_cons (step647 p h) (sat_cons (step628 p h) (sat_cons (step626 p h) (sat_cons (step850 p h) (sat_cons (step606 p h) (sat_cons (step608 p h) (sat_cons (step616 p h) (sat_cons (step618 p h) (sat_cons (step604 p h) (sat_cons (step1052 p h) (sat_cons (step614 p h) (sat_cons (step610 p h) (sat_cons (step166 p h) (sat_cons (step943 p h) (sat_cons (step443 p h) (sat_nil p))))))))))))))))))))))))))))))))))))
end B112E185
