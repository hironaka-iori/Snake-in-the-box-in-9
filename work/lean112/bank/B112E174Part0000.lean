import B112E174Inputs
namespace B112E174
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1021 : List Lit := [(69, true)]
theorem step1021 (p : Nat → Bool) (h : Constraints p) : clause p c1021 = true :=
  Snake9.LocalRup.prove_clause [c214, c213] c1021 (by decide) p (sat_cons (step214 p h) (sat_cons (step213 p h) (sat_nil p)))
def c1022 : List Lit := [(9, false)]
theorem step1022 (p : Nat → Bool) (h : Constraints p) : clause p c1022 = true :=
  Snake9.LocalRup.prove_clause [c257, c28] c1022 (by decide) p (sat_cons (step257 p h) (sat_cons (step28 p h) (sat_nil p)))
def c1023 : List Lit := [(11, false)]
theorem step1023 (p : Nat → Bool) (h : Constraints p) : clause p c1023 = true :=
  Snake9.LocalRup.prove_clause [c258, c33] c1023 (by decide) p (sat_cons (step258 p h) (sat_cons (step33 p h) (sat_nil p)))
def c1024 : List Lit := [(410, false)]
theorem step1024 (p : Nat → Bool) (h : Constraints p) : clause p c1024 = true :=
  Snake9.LocalRup.prove_clause [c499, c496] c1024 (by decide) p (sat_cons (step499 p h) (sat_cons (step496 p h) (sat_nil p)))
def c1025 : List Lit := [(308, false)]
theorem step1025 (p : Nat → Bool) (h : Constraints p) : clause p c1025 = true :=
  Snake9.LocalRup.prove_clause [c499, c498] c1025 (by decide) p (sat_cons (step499 p h) (sat_cons (step498 p h) (sat_nil p)))
def c1026 : List Lit := [(408, false)]
theorem step1026 (p : Nat → Bool) (h : Constraints p) : clause p c1026 = true :=
  Snake9.LocalRup.prove_clause [c1024, c492] c1026 (by decide) p (sat_cons (step1024 p h) (sat_cons (step492 p h) (sat_nil p)))
def c1027 : List Lit := [(358, false)]
theorem step1027 (p : Nat → Bool) (h : Constraints p) : clause p c1027 = true :=
  Snake9.LocalRup.prove_clause [c1024, c495] c1027 (by decide) p (sat_cons (step1024 p h) (sat_cons (step495 p h) (sat_nil p)))
def c1028 : List Lit := [(306, false)]
theorem step1028 (p : Nat → Bool) (h : Constraints p) : clause p c1028 = true :=
  Snake9.LocalRup.prove_clause [c1025, c394] c1028 (by decide) p (sat_cons (step1025 p h) (sat_cons (step394 p h) (sat_nil p)))
def c1029 : List Lit := [(256, false)]
theorem step1029 (p : Nat → Bool) (h : Constraints p) : clause p c1029 = true :=
  Snake9.LocalRup.prove_clause [c1025, c397] c1029 (by decide) p (sat_cons (step1025 p h) (sat_cons (step397 p h) (sat_nil p)))
def c1030 : List Lit := [(356, false)]
theorem step1030 (p : Nat → Bool) (h : Constraints p) : clause p c1030 = true :=
  Snake9.LocalRup.prove_clause [c1027, c449] c1030 (by decide) p (sat_cons (step1027 p h) (sat_cons (step449 p h) (sat_nil p)))
def c1031 : List Lit := [(332, false)]
theorem step1031 (p : Nat → Bool) (h : Constraints p) : clause p c1031 = true :=
  Snake9.LocalRup.prove_clause [c1027, c452] c1031 (by decide) p (sat_cons (step1027 p h) (sat_cons (step452 p h) (sat_nil p)))
def c1032 : List Lit := [(304, false)]
theorem step1032 (p : Nat → Bool) (h : Constraints p) : clause p c1032 = true :=
  Snake9.LocalRup.prove_clause [c1028, c389] c1032 (by decide) p (sat_cons (step1028 p h) (sat_cons (step389 p h) (sat_nil p)))
def c1033 : List Lit := [(280, false)]
theorem step1033 (p : Nat → Bool) (h : Constraints p) : clause p c1033 = true :=
  Snake9.LocalRup.prove_clause [c1028, c392] c1033 (by decide) p (sat_cons (step1028 p h) (sat_cons (step392 p h) (sat_nil p)))
def c1034 : List Lit := [(254, false)]
theorem step1034 (p : Nat → Bool) (h : Constraints p) : clause p c1034 = true :=
  Snake9.LocalRup.prove_clause [c1029, c343] c1034 (by decide) p (sat_cons (step1029 p h) (sat_cons (step343 p h) (sat_nil p)))
def c1035 : List Lit := [(230, false)]
theorem step1035 (p : Nat → Bool) (h : Constraints p) : clause p c1035 = true :=
  Snake9.LocalRup.prove_clause [c1029, c346] c1035 (by decide) p (sat_cons (step1029 p h) (sat_cons (step346 p h) (sat_nil p)))
def c1036 : List Lit := [(342, false)]
theorem step1036 (p : Nat → Bool) (h : Constraints p) : clause p c1036 = true :=
  Snake9.LocalRup.prove_clause [c1030, c447] c1036 (by decide) p (sat_cons (step1030 p h) (sat_cons (step447 p h) (sat_nil p)))
def c1037 : List Lit := [(330, false)]
theorem step1037 (p : Nat → Bool) (h : Constraints p) : clause p c1037 = true :=
  Snake9.LocalRup.prove_clause [c1031, c420] c1037 (by decide) p (sat_cons (step1031 p h) (sat_cons (step420 p h) (sat_nil p)))
def c1038 : List Lit := [(318, false)]
theorem step1038 (p : Nat → Bool) (h : Constraints p) : clause p c1038 = true :=
  Snake9.LocalRup.prove_clause [c1031, c423] c1038 (by decide) p (sat_cons (step1031 p h) (sat_cons (step423 p h) (sat_nil p)))
def c1039 : List Lit := [(302, false)]
theorem step1039 (p : Nat → Bool) (h : Constraints p) : clause p c1039 = true :=
  Snake9.LocalRup.prove_clause [c1032, c385] c1039 (by decide) p (sat_cons (step1032 p h) (sat_cons (step385 p h) (sat_nil p)))
def c1040 : List Lit := [(278, false)]
theorem step1040 (p : Nat → Bool) (h : Constraints p) : clause p c1040 = true :=
  Snake9.LocalRup.prove_clause [c1033, c365] c1040 (by decide) p (sat_cons (step1033 p h) (sat_cons (step365 p h) (sat_nil p)))
def c1041 : List Lit := [(240, false)]
theorem step1041 (p : Nat → Bool) (h : Constraints p) : clause p c1041 = true :=
  Snake9.LocalRup.prove_clause [c1034, c341] c1041 (by decide) p (sat_cons (step1034 p h) (sat_cons (step341 p h) (sat_nil p)))
def c1042 : List Lit := [(228, false)]
theorem step1042 (p : Nat → Bool) (h : Constraints p) : clause p c1042 = true :=
  Snake9.LocalRup.prove_clause [c1035, c318] c1042 (by decide) p (sat_cons (step1035 p h) (sat_cons (step318 p h) (sat_nil p)))
def c1043 : List Lit := [(336, false)]
theorem step1043 (p : Nat → Bool) (h : Constraints p) : clause p c1043 = true :=
  Snake9.LocalRup.prove_clause [c1036, c434] c1043 (by decide) p (sat_cons (step1036 p h) (sat_cons (step434 p h) (sat_nil p)))
def c1044 : List Lit := [(328, false)]
theorem step1044 (p : Nat → Bool) (h : Constraints p) : clause p c1044 = true :=
  Snake9.LocalRup.prove_clause [c1037, c415] c1044 (by decide) p (sat_cons (step1037 p h) (sat_cons (step415 p h) (sat_nil p)))
def c1045 : List Lit := [(322, false)]
theorem step1045 (p : Nat → Bool) (h : Constraints p) : clause p c1045 = true :=
  Snake9.LocalRup.prove_clause [c1037, c418] c1045 (by decide) p (sat_cons (step1037 p h) (sat_cons (step418 p h) (sat_nil p)))
def c1046 : List Lit := [(300, false)]
theorem step1046 (p : Nat → Bool) (h : Constraints p) : clause p c1046 = true :=
  Snake9.LocalRup.prove_clause [c1039, c382] c1046 (by decide) p (sat_cons (step1039 p h) (sat_cons (step382 p h) (sat_nil p)))
def c1047 : List Lit := [(226, false)]
theorem step1047 (p : Nat → Bool) (h : Constraints p) : clause p c1047 = true :=
  Snake9.LocalRup.prove_clause [c1042, c316] c1047 (by decide) p (sat_cons (step1042 p h) (sat_cons (step316 p h) (sat_nil p)))
def c1048 : List Lit := [(334, false)]
theorem step1048 (p : Nat → Bool) (h : Constraints p) : clause p c1048 = true :=
  Snake9.LocalRup.prove_clause [c1043, c428] c1048 (by decide) p (sat_cons (step1043 p h) (sat_cons (step428 p h) (sat_nil p)))
def c1049 : List Lit := [(107, true), (108, true), (110, true), (114, true), (116, true), (118, true), (120, true), (121, true), (122, true), (125, true), (126, true), (129, true), (131, true), (132, true), (135, true), (137, true), (138, true), (140, true), (142, true), (145, true), (147, true), (149, true), (152, true), (154, true), (155, true), (157, true), (160, true), (162, true), (163, true), (165, true), (168, true), (170, true), (171, true), (173, true), (177, true), (178, true), (179, true), (181, true), (185, true), (186, true), (188, true), (190, true), (192, true), (193, true), (195, true), (198, true), (200, true), (201, true), (203, true), (206, true), (208, true)]
theorem step1049 (p : Nat → Bool) (h : Constraints p) : clause p c1049 = true :=
  Snake9.LocalRup.prove_clause [c252, c253, c254, c255, c256, c257, c258, c259, c260, c261, c262, c263, c264, c265, c266, c267, c268, c269, c270, c271, c272, c273, c274, c275, c276, c277, c278, c279, c280, c281, c282, c283, c284, c285, c286, c287, c288, c289, c290, c291, c292, c293, c294, c295, c296, c297, c298, c299, c300, c301, c302, c303, c500] c1049 (by decide) p (sat_cons (step252 p h) (sat_cons (step253 p h) (sat_cons (step254 p h) (sat_cons (step255 p h) (sat_cons (step256 p h) (sat_cons (step257 p h) (sat_cons (step258 p h) (sat_cons (step259 p h) (sat_cons (step260 p h) (sat_cons (step261 p h) (sat_cons (step262 p h) (sat_cons (step263 p h) (sat_cons (step264 p h) (sat_cons (step265 p h) (sat_cons (step266 p h) (sat_cons (step267 p h) (sat_cons (step268 p h) (sat_cons (step269 p h) (sat_cons (step270 p h) (sat_cons (step271 p h) (sat_cons (step272 p h) (sat_cons (step273 p h) (sat_cons (step274 p h) (sat_cons (step275 p h) (sat_cons (step276 p h) (sat_cons (step277 p h) (sat_cons (step278 p h) (sat_cons (step279 p h) (sat_cons (step280 p h) (sat_cons (step281 p h) (sat_cons (step282 p h) (sat_cons (step283 p h) (sat_cons (step284 p h) (sat_cons (step285 p h) (sat_cons (step286 p h) (sat_cons (step287 p h) (sat_cons (step288 p h) (sat_cons (step289 p h) (sat_cons (step290 p h) (sat_cons (step291 p h) (sat_cons (step292 p h) (sat_cons (step293 p h) (sat_cons (step294 p h) (sat_cons (step295 p h) (sat_cons (step296 p h) (sat_cons (step297 p h) (sat_cons (step298 p h) (sat_cons (step299 p h) (sat_cons (step300 p h) (sat_cons (step301 p h) (sat_cons (step302 p h) (sat_cons (step303 p h) (sat_cons (step500 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1050 : List Lit := [(1215, true)]
theorem step1050 (p : Nat → Bool) (h : Constraints p) : clause p c1050 = true :=
  Snake9.LocalRup.prove_clause [c1022, c771] c1050 (by decide) p (sat_cons (step1022 p h) (sat_cons (step771 p h) (sat_nil p)))
def c1051 : List Lit := [(8, true), (1216, true)]
theorem step1051 (p : Nat → Bool) (h : Constraints p) : clause p c1051 = true :=
  Snake9.LocalRup.prove_clause [c1022, c772] c1051 (by decide) p (sat_cons (step1022 p h) (sat_cons (step772 p h) (sat_nil p)))
def c1052 : List Lit := [(1217, true)]
theorem step1052 (p : Nat → Bool) (h : Constraints p) : clause p c1052 = true :=
  Snake9.LocalRup.prove_clause [c1050, c773] c1052 (by decide) p (sat_cons (step1050 p h) (sat_cons (step773 p h) (sat_nil p)))
def c1053 : List Lit := [(7, true), (1218, true)]
theorem step1053 (p : Nat → Bool) (h : Constraints p) : clause p c1053 = true :=
  Snake9.LocalRup.prove_clause [c1050, c775] c1053 (by decide) p (sat_cons (step1050 p h) (sat_cons (step775 p h) (sat_nil p)))
def c1054 : List Lit := [(1220, true)]
theorem step1054 (p : Nat → Bool) (h : Constraints p) : clause p c1054 = true :=
  Snake9.LocalRup.prove_clause [c1052, c777] c1054 (by decide) p (sat_cons (step1052 p h) (sat_cons (step777 p h) (sat_nil p)))
def c1055 : List Lit := [(1212, false), (1221, true)]
theorem step1055 (p : Nat → Bool) (h : Constraints p) : clause p c1055 = true :=
  Snake9.LocalRup.prove_clause [c1052, c780] c1055 (by decide) p (sat_cons (step1052 p h) (sat_cons (step780 p h) (sat_nil p)))
def c1056 : List Lit := [(1213, false), (1222, true)]
theorem step1056 (p : Nat → Bool) (h : Constraints p) : clause p c1056 = true :=
  Snake9.LocalRup.prove_clause [c1052, c783] c1056 (by decide) p (sat_cons (step1052 p h) (sat_cons (step783 p h) (sat_nil p)))
def c1057 : List Lit := [(1214, false), (1223, true)]
theorem step1057 (p : Nat → Bool) (h : Constraints p) : clause p c1057 = true :=
  Snake9.LocalRup.prove_clause [c1052, c785] c1057 (by decide) p (sat_cons (step1052 p h) (sat_cons (step785 p h) (sat_nil p)))
def c1058 : List Lit := [(1228, true)]
theorem step1058 (p : Nat → Bool) (h : Constraints p) : clause p c1058 = true :=
  Snake9.LocalRup.prove_clause [c1023, c791] c1058 (by decide) p (sat_cons (step1023 p h) (sat_cons (step791 p h) (sat_nil p)))
def c1059 : List Lit := [(1226, false), (1229, true)]
theorem step1059 (p : Nat → Bool) (h : Constraints p) : clause p c1059 = true :=
  Snake9.LocalRup.prove_clause [c1023, c792] c1059 (by decide) p (sat_cons (step1023 p h) (sat_cons (step792 p h) (sat_nil p)))
def c1060 : List Lit := [(1227, false), (1230, true)]
theorem step1060 (p : Nat → Bool) (h : Constraints p) : clause p c1060 = true :=
  Snake9.LocalRup.prove_clause [c1023, c793] c1060 (by decide) p (sat_cons (step1023 p h) (sat_cons (step793 p h) (sat_nil p)))
def c1061 : List Lit := [(1239, true)]
theorem step1061 (p : Nat → Bool) (h : Constraints p) : clause p c1061 = true :=
  Snake9.LocalRup.prove_clause [c1058, c804] c1061 (by decide) p (sat_cons (step1058 p h) (sat_cons (step804 p h) (sat_nil p)))
def c1062 : List Lit := [(1235, false), (1240, true)]
theorem step1062 (p : Nat → Bool) (h : Constraints p) : clause p c1062 = true :=
  Snake9.LocalRup.prove_clause [c1058, c805] c1062 (by decide) p (sat_cons (step1058 p h) (sat_cons (step805 p h) (sat_nil p)))
def c1063 : List Lit := [(1236, false), (1241, true)]
theorem step1063 (p : Nat → Bool) (h : Constraints p) : clause p c1063 = true :=
  Snake9.LocalRup.prove_clause [c1058, c806] c1063 (by decide) p (sat_cons (step1058 p h) (sat_cons (step806 p h) (sat_nil p)))
def c1064 : List Lit := [(1237, false), (1242, true)]
theorem step1064 (p : Nat → Bool) (h : Constraints p) : clause p c1064 = true :=
  Snake9.LocalRup.prove_clause [c1058, c807] c1064 (by decide) p (sat_cons (step1058 p h) (sat_cons (step807 p h) (sat_nil p)))
def c1065 : List Lit := [(1240, false), (1248, true)]
theorem step1065 (p : Nat → Bool) (h : Constraints p) : clause p c1065 = true :=
  Snake9.LocalRup.prove_clause [c1054, c813] c1065 (by decide) p (sat_cons (step1054 p h) (sat_cons (step813 p h) (sat_nil p)))
def c1066 : List Lit := [(1221, false), (1248, true)]
theorem step1066 (p : Nat → Bool) (h : Constraints p) : clause p c1066 = true :=
  Snake9.LocalRup.prove_clause [c1061, c814] c1066 (by decide) p (sat_cons (step1061 p h) (sat_cons (step814 p h) (sat_nil p)))
def c1067 : List Lit := [(1222, false), (1249, true)]
theorem step1067 (p : Nat → Bool) (h : Constraints p) : clause p c1067 = true :=
  Snake9.LocalRup.prove_clause [c1061, c818] c1067 (by decide) p (sat_cons (step1061 p h) (sat_cons (step818 p h) (sat_nil p)))
def c1068 : List Lit := [(1223, false), (1250, true)]
theorem step1068 (p : Nat → Bool) (h : Constraints p) : clause p c1068 = true :=
  Snake9.LocalRup.prove_clause [c1061, c821] c1068 (by decide) p (sat_cons (step1061 p h) (sat_cons (step821 p h) (sat_nil p)))
def c1069 : List Lit := [(1224, false), (1251, true)]
theorem step1069 (p : Nat → Bool) (h : Constraints p) : clause p c1069 = true :=
  Snake9.LocalRup.prove_clause [c1061, c824] c1069 (by decide) p (sat_cons (step1061 p h) (sat_cons (step824 p h) (sat_nil p)))
def c1070 : List Lit := [(1295, true)]
theorem step1070 (p : Nat → Bool) (h : Constraints p) : clause p c1070 = true :=
  Snake9.LocalRup.prove_clause [c276, c873, c874, c866, c842, c843, c862, c840, c832, c861, c137, c95] c1070 (by decide) p (sat_cons (step276 p h) (sat_cons (step873 p h) (sat_cons (step874 p h) (sat_cons (step866 p h) (sat_cons (step842 p h) (sat_cons (step843 p h) (sat_cons (step862 p h) (sat_cons (step840 p h) (sat_cons (step832 p h) (sat_cons (step861 p h) (sat_cons (step137 p h) (sat_cons (step95 p h) (sat_nil p)))))))))))))
def c1071 : List Lit := [(7, false), (15, false), (13, false)]
theorem step1071 (p : Nat → Bool) (h : Constraints p) : clause p c1071 = true :=
  Snake9.LocalRup.prove_clause [c259, c48, c37] c1071 (by decide) p (sat_cons (step259 p h) (sat_cons (step48 p h) (sat_cons (step37 p h) (sat_nil p))))
def c1072 : List Lit := [(1248, true)]
theorem step1072 (p : Nat → Bool) (h : Constraints p) : clause p c1072 = true :=
  Snake9.LocalRup.prove_clause [c1065, c1066, c808, c778, c1059, c1053, c787, c788, c1071] c1072 (by decide) p (sat_cons (step1065 p h) (sat_cons (step1066 p h) (sat_cons (step808 p h) (sat_cons (step778 p h) (sat_cons (step1059 p h) (sat_cons (step1053 p h) (sat_cons (step787 p h) (sat_cons (step788 p h) (sat_cons (step1071 p h) (sat_nil p))))))))))
def c1073 : List Lit := [(26, false), (30, false), (29, false)]
theorem step1073 (p : Nat → Bool) (h : Constraints p) : clause p c1073 = true :=
  Snake9.LocalRup.prove_clause [c267, c88, c94] c1073 (by decide) p (sat_cons (step267 p h) (sat_cons (step88 p h) (sat_cons (step94 p h) (sat_nil p))))
def c1074 : List Lit := [(1261, true)]
theorem step1074 (p : Nat → Bool) (h : Constraints p) : clause p c1074 = true :=
  Snake9.LocalRup.prove_clause [c830, c832, c827, c828, c1073] c1074 (by decide) p (sat_cons (step830 p h) (sat_cons (step832 p h) (sat_cons (step827 p h) (sat_cons (step828 p h) (sat_cons (step1073 p h) (sat_nil p))))))
def c1075 : List Lit := [(1267, true), (30, false), (37, true)]
theorem step1075 (p : Nat → Bool) (h : Constraints p) : clause p c1075 = true :=
  Snake9.LocalRup.prove_clause [c267, c93, c835, c839, c841, c837, c104] c1075 (by decide) p (sat_cons (step267 p h) (sat_cons (step93 p h) (sat_cons (step835 p h) (sat_cons (step839 p h) (sat_cons (step841 p h) (sat_cons (step837 p h) (sat_cons (step104 p h) (sat_nil p))))))))
def c1076 : List Lit := [(39, false), (46, false), (44, false)]
theorem step1076 (p : Nat → Bool) (h : Constraints p) : clause p c1076 = true :=
  Snake9.LocalRup.prove_clause [c275, c131, c135] c1076 (by decide) p (sat_cons (step275 p h) (sat_cons (step131 p h) (sat_cons (step135 p h) (sat_nil p))))
def c1077 : List Lit := [(1289, true), (1282, false)]
theorem step1077 (p : Nat → Bool) (h : Constraints p) : clause p c1077 = true :=
  Snake9.LocalRup.prove_clause [c862, c867, c869, c864, c855, c857, c858, c1076] c1077 (by decide) p (sat_cons (step862 p h) (sat_cons (step867 p h) (sat_cons (step869 p h) (sat_cons (step864 p h) (sat_cons (step855 p h) (sat_cons (step857 p h) (sat_cons (step858 p h) (sat_cons (step1076 p h) (sat_nil p)))))))))
def c1078 : List Lit := [(894, true), (409, true)]
theorem step1078 (p : Nat → Bool) (h : Constraints p) : clause p c1078 = true :=
  Snake9.LocalRup.prove_clause [c493, c448, c444, c443, c437, c435, c219, c674, c679, c682, c688, c491, c489, c469, c468, c461, c460, c238, c708, c710, c729, c442, c440, c439, c741, c739, c689, c731, c730, c683, c713, c724, c680, c703, c722, c675, c702, c718, c226, c228] c1078 (by decide) p (sat_cons (step493 p h) (sat_cons (step448 p h) (sat_cons (step444 p h) (sat_cons (step443 p h) (sat_cons (step437 p h) (sat_cons (step435 p h) (sat_cons (step219 p h) (sat_cons (step674 p h) (sat_cons (step679 p h) (sat_cons (step682 p h) (sat_cons (step688 p h) (sat_cons (step491 p h) (sat_cons (step489 p h) (sat_cons (step469 p h) (sat_cons (step468 p h) (sat_cons (step461 p h) (sat_cons (step460 p h) (sat_cons (step238 p h) (sat_cons (step708 p h) (sat_cons (step710 p h) (sat_cons (step729 p h) (sat_cons (step442 p h) (sat_cons (step440 p h) (sat_cons (step439 p h) (sat_cons (step741 p h) (sat_cons (step739 p h) (sat_cons (step689 p h) (sat_cons (step731 p h) (sat_cons (step730 p h) (sat_cons (step683 p h) (sat_cons (step713 p h) (sat_cons (step724 p h) (sat_cons (step680 p h) (sat_cons (step703 p h) (sat_cons (step722 p h) (sat_cons (step675 p h) (sat_cons (step702 p h) (sat_cons (step718 p h) (sat_cons (step226 p h) (sat_cons (step228 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))
def c1079 : List Lit := [(882, true), (379, true)]
theorem step1079 (p : Nat → Bool) (h : Constraints p) : clause p c1079 = true :=
  Snake9.LocalRup.prove_clause [c468, c461, c460, c238, c708, c710, c467, c466, c462, c731, c730, c711, c726, c709, c717, c705, c715, c716, c242, c245] c1079 (by decide) p (sat_cons (step468 p h) (sat_cons (step461 p h) (sat_cons (step460 p h) (sat_cons (step238 p h) (sat_cons (step708 p h) (sat_cons (step710 p h) (sat_cons (step467 p h) (sat_cons (step466 p h) (sat_cons (step462 p h) (sat_cons (step731 p h) (sat_cons (step730 p h) (sat_cons (step711 p h) (sat_cons (step726 p h) (sat_cons (step709 p h) (sat_cons (step717 p h) (sat_cons (step705 p h) (sat_cons (step715 p h) (sat_cons (step716 p h) (sat_cons (step242 p h) (sat_cons (step245 p h) (sat_nil p)))))))))))))))))))))
def c1080 : List Lit := [(699, true), (1, true), (7, false), (107, true)]
theorem step1080 (p : Nat → Bool) (h : Constraints p) : clause p c1080 = true :=
  Snake9.LocalRup.prove_clause [c504, c506, c501, c11, c1014] c1080 (by decide) p (sat_cons (step504 p h) (sat_cons (step506 p h) (sat_cons (step501 p h) (sat_cons (step11 p h) (sat_cons (step1014 p h) (sat_nil p))))))
def c1081 : List Lit := [(724, true), (20, true), (122, true), (16, true)]
theorem step1081 (p : Nat → Bool) (h : Constraints p) : clause p c1081 = true :=
  Snake9.LocalRup.prove_clause [c528, c540, c538, c529, c532, c533, c526, c531, c58, c59] c1081 (by decide) p (sat_cons (step528 p h) (sat_cons (step540 p h) (sat_cons (step538 p h) (sat_cons (step529 p h) (sat_cons (step532 p h) (sat_cons (step533 p h) (sat_cons (step526 p h) (sat_cons (step531 p h) (sat_cons (step58 p h) (sat_cons (step59 p h) (sat_nil p)))))))))))
def c1082 : List Lit := [(742, true), (29, true), (28, false), (131, true)]
theorem step1082 (p : Nat → Bool) (h : Constraints p) : clause p c1082 = true :=
  Snake9.LocalRup.prove_clause [c563, c565, c560, c81, c83] c1082 (by decide) p (sat_cons (step563 p h) (sat_cons (step565 p h) (sat_cons (step560 p h) (sat_cons (step81 p h) (sat_cons (step83 p h) (sat_nil p))))))
def c1083 : List Lit := [(769, true), (49, false), (48, false)]
theorem step1083 (p : Nat → Bool) (h : Constraints p) : clause p c1083 = true :=
  Snake9.LocalRup.prove_clause [c597, c600, c592, c584, c590, c582, c142] c1083 (by decide) p (sat_cons (step597 p h) (sat_cons (step600 p h) (sat_cons (step592 p h) (sat_cons (step584 p h) (sat_cons (step590 p h) (sat_cons (step582 p h) (sat_cons (step142 p h) (sat_nil p))))))))
def c1084 : List Lit := [(724, true), (20, false), (28, false), (16, true)]
theorem step1084 (p : Nat → Bool) (h : Constraints p) : clause p c1084 = true :=
  Snake9.LocalRup.prove_clause [c528, c540, c538, c529, c533, c526, c61] c1084 (by decide) p (sat_cons (step528 p h) (sat_cons (step540 p h) (sat_cons (step538 p h) (sat_cons (step529 p h) (sat_cons (step533 p h) (sat_cons (step526 p h) (sat_cons (step61 p h) (sat_nil p))))))))
end B112E174
