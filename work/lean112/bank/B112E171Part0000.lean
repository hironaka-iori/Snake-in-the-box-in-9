import B112E171Inputs
namespace B112E171
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1056 : List Lit := [(8, true)]
theorem step1056 (p : Nat → Bool) (h : Constraints p) : clause p c1056 = true :=
  Snake9.LocalRup.prove_clause [c24, c23] c1056 (by decide) p (sat_cons (step24 p h) (sat_cons (step23 p h) (sat_nil p)))
def c1057 : List Lit := [(33, false)]
theorem step1057 (p : Nat → Bool) (h : Constraints p) : clause p c1057 = true :=
  Snake9.LocalRup.prove_clause [c406, c79] c1057 (by decide) p (sat_cons (step406 p h) (sat_cons (step79 p h) (sat_nil p)))
def c1058 : List Lit := [(39, false)]
theorem step1058 (p : Nat → Bool) (h : Constraints p) : clause p c1058 = true :=
  Snake9.LocalRup.prove_clause [c409, c89] c1058 (by decide) p (sat_cons (step409 p h) (sat_cons (step89 p h) (sat_nil p)))
def c1059 : List Lit := [(450, false)]
theorem step1059 (p : Nat → Bool) (h : Constraints p) : clause p c1059 = true :=
  Snake9.LocalRup.prove_clause [c666, c663] c1059 (by decide) p (sat_cons (step666 p h) (sat_cons (step663 p h) (sat_nil p)))
def c1060 : List Lit := [(338, false)]
theorem step1060 (p : Nat → Bool) (h : Constraints p) : clause p c1060 = true :=
  Snake9.LocalRup.prove_clause [c666, c665] c1060 (by decide) p (sat_cons (step666 p h) (sat_cons (step665 p h) (sat_nil p)))
def c1061 : List Lit := [(448, false)]
theorem step1061 (p : Nat → Bool) (h : Constraints p) : clause p c1061 = true :=
  Snake9.LocalRup.prove_clause [c1059, c659] c1061 (by decide) p (sat_cons (step1059 p h) (sat_cons (step659 p h) (sat_nil p)))
def c1062 : List Lit := [(392, false)]
theorem step1062 (p : Nat → Bool) (h : Constraints p) : clause p c1062 = true :=
  Snake9.LocalRup.prove_clause [c1059, c662] c1062 (by decide) p (sat_cons (step1059 p h) (sat_cons (step662 p h) (sat_nil p)))
def c1063 : List Lit := [(336, false)]
theorem step1063 (p : Nat → Bool) (h : Constraints p) : clause p c1063 = true :=
  Snake9.LocalRup.prove_clause [c1060, c543] c1063 (by decide) p (sat_cons (step1060 p h) (sat_cons (step543 p h) (sat_nil p)))
def c1064 : List Lit := [(282, false)]
theorem step1064 (p : Nat → Bool) (h : Constraints p) : clause p c1064 = true :=
  Snake9.LocalRup.prove_clause [c1060, c546] c1064 (by decide) p (sat_cons (step1060 p h) (sat_cons (step546 p h) (sat_nil p)))
def c1065 : List Lit := [(446, false)]
theorem step1065 (p : Nat → Bool) (h : Constraints p) : clause p c1065 = true :=
  Snake9.LocalRup.prove_clause [c1061, c654] c1065 (by decide) p (sat_cons (step1061 p h) (sat_cons (step654 p h) (sat_nil p)))
def c1066 : List Lit := [(418, false)]
theorem step1066 (p : Nat → Bool) (h : Constraints p) : clause p c1066 = true :=
  Snake9.LocalRup.prove_clause [c1061, c657] c1066 (by decide) p (sat_cons (step1061 p h) (sat_cons (step657 p h) (sat_nil p)))
def c1067 : List Lit := [(390, false)]
theorem step1067 (p : Nat → Bool) (h : Constraints p) : clause p c1067 = true :=
  Snake9.LocalRup.prove_clause [c1062, c602] c1067 (by decide) p (sat_cons (step1062 p h) (sat_cons (step602 p h) (sat_nil p)))
def c1068 : List Lit := [(364, false)]
theorem step1068 (p : Nat → Bool) (h : Constraints p) : clause p c1068 = true :=
  Snake9.LocalRup.prove_clause [c1062, c605] c1068 (by decide) p (sat_cons (step1062 p h) (sat_cons (step605 p h) (sat_nil p)))
def c1069 : List Lit := [(334, false)]
theorem step1069 (p : Nat → Bool) (h : Constraints p) : clause p c1069 = true :=
  Snake9.LocalRup.prove_clause [c1063, c538] c1069 (by decide) p (sat_cons (step1063 p h) (sat_cons (step538 p h) (sat_nil p)))
def c1070 : List Lit := [(308, false)]
theorem step1070 (p : Nat → Bool) (h : Constraints p) : clause p c1070 = true :=
  Snake9.LocalRup.prove_clause [c1063, c541] c1070 (by decide) p (sat_cons (step1063 p h) (sat_cons (step541 p h) (sat_nil p)))
def c1071 : List Lit := [(280, false)]
theorem step1071 (p : Nat → Bool) (h : Constraints p) : clause p c1071 = true :=
  Snake9.LocalRup.prove_clause [c1064, c491] c1071 (by decide) p (sat_cons (step1064 p h) (sat_cons (step491 p h) (sat_nil p)))
def c1072 : List Lit := [(254, false)]
theorem step1072 (p : Nat → Bool) (h : Constraints p) : clause p c1072 = true :=
  Snake9.LocalRup.prove_clause [c1064, c494] c1072 (by decide) p (sat_cons (step1064 p h) (sat_cons (step494 p h) (sat_nil p)))
def c1073 : List Lit := [(444, false)]
theorem step1073 (p : Nat → Bool) (h : Constraints p) : clause p c1073 = true :=
  Snake9.LocalRup.prove_clause [c1065, c651] c1073 (by decide) p (sat_cons (step1065 p h) (sat_cons (step651 p h) (sat_nil p)))
def c1074 : List Lit := [(416, false)]
theorem step1074 (p : Nat → Bool) (h : Constraints p) : clause p c1074 = true :=
  Snake9.LocalRup.prove_clause [c1066, c626] c1074 (by decide) p (sat_cons (step1066 p h) (sat_cons (step626 p h) (sat_nil p)))
def c1075 : List Lit := [(404, false)]
theorem step1075 (p : Nat → Bool) (h : Constraints p) : clause p c1075 = true :=
  Snake9.LocalRup.prove_clause [c1066, c629] c1075 (by decide) p (sat_cons (step1066 p h) (sat_cons (step629 p h) (sat_nil p)))
def c1076 : List Lit := [(388, false)]
theorem step1076 (p : Nat → Bool) (h : Constraints p) : clause p c1076 = true :=
  Snake9.LocalRup.prove_clause [c1067, c597] c1076 (by decide) p (sat_cons (step1067 p h) (sat_cons (step597 p h) (sat_nil p)))
def c1077 : List Lit := [(376, false)]
theorem step1077 (p : Nat → Bool) (h : Constraints p) : clause p c1077 = true :=
  Snake9.LocalRup.prove_clause [c1067, c600] c1077 (by decide) p (sat_cons (step1067 p h) (sat_cons (step600 p h) (sat_nil p)))
def c1078 : List Lit := [(362, false)]
theorem step1078 (p : Nat → Bool) (h : Constraints p) : clause p c1078 = true :=
  Snake9.LocalRup.prove_clause [c1068, c572] c1078 (by decide) p (sat_cons (step1068 p h) (sat_cons (step572 p h) (sat_nil p)))
def c1079 : List Lit := [(350, false)]
theorem step1079 (p : Nat → Bool) (h : Constraints p) : clause p c1079 = true :=
  Snake9.LocalRup.prove_clause [c1068, c575] c1079 (by decide) p (sat_cons (step1068 p h) (sat_cons (step575 p h) (sat_nil p)))
def c1080 : List Lit := [(294, false)]
theorem step1080 (p : Nat → Bool) (h : Constraints p) : clause p c1080 = true :=
  Snake9.LocalRup.prove_clause [c1070, c517] c1080 (by decide) p (sat_cons (step1070 p h) (sat_cons (step517 p h) (sat_nil p)))
def c1081 : List Lit := [(266, false)]
theorem step1081 (p : Nat → Bool) (h : Constraints p) : clause p c1081 = true :=
  Snake9.LocalRup.prove_clause [c1071, c489] c1081 (by decide) p (sat_cons (step1071 p h) (sat_cons (step489 p h) (sat_nil p)))
def c1082 : List Lit := [(240, false)]
theorem step1082 (p : Nat → Bool) (h : Constraints p) : clause p c1082 = true :=
  Snake9.LocalRup.prove_clause [c1072, c469] c1082 (by decide) p (sat_cons (step1072 p h) (sat_cons (step469 p h) (sat_nil p)))
def c1083 : List Lit := [(442, false)]
theorem step1083 (p : Nat → Bool) (h : Constraints p) : clause p c1083 = true :=
  Snake9.LocalRup.prove_clause [c1073, c648] c1083 (by decide) p (sat_cons (step1073 p h) (sat_cons (step648 p h) (sat_nil p)))
def c1084 : List Lit := [(396, false)]
theorem step1084 (p : Nat → Bool) (h : Constraints p) : clause p c1084 = true :=
  Snake9.LocalRup.prove_clause [c1075, c615] c1084 (by decide) p (sat_cons (step1075 p h) (sat_cons (step615 p h) (sat_nil p)))
def c1085 : List Lit := [(374, false)]
theorem step1085 (p : Nat → Bool) (h : Constraints p) : clause p c1085 = true :=
  Snake9.LocalRup.prove_clause [c1077, c585] c1085 (by decide) p (sat_cons (step1077 p h) (sat_cons (step585 p h) (sat_nil p)))
def c1086 : List Lit := [(360, false)]
theorem step1086 (p : Nat → Bool) (h : Constraints p) : clause p c1086 = true :=
  Snake9.LocalRup.prove_clause [c1078, c568] c1086 (by decide) p (sat_cons (step1078 p h) (sat_cons (step568 p h) (sat_nil p)))
def c1087 : List Lit := [(342, false)]
theorem step1087 (p : Nat → Bool) (h : Constraints p) : clause p c1087 = true :=
  Snake9.LocalRup.prove_clause [c1079, c556] c1087 (by decide) p (sat_cons (step1079 p h) (sat_cons (step556 p h) (sat_nil p)))
def c1088 : List Lit := [(292, false)]
theorem step1088 (p : Nat → Bool) (h : Constraints p) : clause p c1088 = true :=
  Snake9.LocalRup.prove_clause [c1080, c506] c1088 (by decide) p (sat_cons (step1080 p h) (sat_cons (step506 p h) (sat_nil p)))
def c1089 : List Lit := [(238, false)]
theorem step1089 (p : Nat → Bool) (h : Constraints p) : clause p c1089 = true :=
  Snake9.LocalRup.prove_clause [c1082, c455] c1089 (by decide) p (sat_cons (step1082 p h) (sat_cons (step455 p h) (sat_nil p)))
def c1090 : List Lit := [(438, false)]
theorem step1090 (p : Nat → Bool) (h : Constraints p) : clause p c1090 = true :=
  Snake9.LocalRup.prove_clause [c1083, c646] c1090 (by decide) p (sat_cons (step1083 p h) (sat_cons (step646 p h) (sat_nil p)))
def c1091 : List Lit := [(372, false)]
theorem step1091 (p : Nat → Bool) (h : Constraints p) : clause p c1091 = true :=
  Snake9.LocalRup.prove_clause [c1085, c582] c1091 (by decide) p (sat_cons (step1085 p h) (sat_cons (step582 p h) (sat_nil p)))
def c1092 : List Lit := [(356, false)]
theorem step1092 (p : Nat → Bool) (h : Constraints p) : clause p c1092 = true :=
  Snake9.LocalRup.prove_clause [c1086, c566] c1092 (by decide) p (sat_cons (step1086 p h) (sat_cons (step566 p h) (sat_nil p)))
def c1093 : List Lit := [(290, false)]
theorem step1093 (p : Nat → Bool) (h : Constraints p) : clause p c1093 = true :=
  Snake9.LocalRup.prove_clause [c1088, c503] c1093 (by decide) p (sat_cons (step1088 p h) (sat_cons (step503 p h) (sat_nil p)))
def c1094 : List Lit := [(234, false)]
theorem step1094 (p : Nat → Bool) (h : Constraints p) : clause p c1094 = true :=
  Snake9.LocalRup.prove_clause [c1089, c453] c1094 (by decide) p (sat_cons (step1089 p h) (sat_cons (step453 p h) (sat_nil p)))
def c1095 : List Lit := [(116, true), (118, true), (119, true), (122, true), (123, true), (125, true), (128, true), (131, true), (132, true), (133, true), (135, true), (137, true), (140, true), (141, true), (144, true), (146, true), (148, true), (149, true), (150, true), (154, true), (156, true), (158, true), (162, true), (163, true), (166, true), (168, true), (170, true), (171, true), (172, true), (174, true), (177, true), (180, true), (182, true), (183, true), (185, true), (186, true), (190, true), (191, true), (192, true), (193, true), (197, true), (199, true), (200, true), (202, true), (203, true), (207, true), (208, true), (209, true), (210, true), (214, true), (216, true), (217, true), (219, true), (223, true), (224, true), (225, true), (226, true)]
theorem step1095 (p : Nat → Bool) (h : Constraints p) : clause p c1095 = true :=
  Snake9.LocalRup.prove_clause [c391, c392, c393, c394, c395, c396, c397, c398, c399, c400, c401, c402, c403, c404, c405, c406, c407, c408, c409, c410, c411, c412, c413, c414, c415, c416, c417, c418, c419, c420, c421, c422, c423, c424, c425, c426, c427, c428, c429, c430, c431, c432, c433, c434, c435, c436, c437, c438, c439, c440, c441, c442, c443, c444, c445, c446, c667] c1095 (by decide) p (sat_cons (step391 p h) (sat_cons (step392 p h) (sat_cons (step393 p h) (sat_cons (step394 p h) (sat_cons (step395 p h) (sat_cons (step396 p h) (sat_cons (step397 p h) (sat_cons (step398 p h) (sat_cons (step399 p h) (sat_cons (step400 p h) (sat_cons (step401 p h) (sat_cons (step402 p h) (sat_cons (step403 p h) (sat_cons (step404 p h) (sat_cons (step405 p h) (sat_cons (step406 p h) (sat_cons (step407 p h) (sat_cons (step408 p h) (sat_cons (step409 p h) (sat_cons (step410 p h) (sat_cons (step411 p h) (sat_cons (step412 p h) (sat_cons (step413 p h) (sat_cons (step414 p h) (sat_cons (step415 p h) (sat_cons (step416 p h) (sat_cons (step417 p h) (sat_cons (step418 p h) (sat_cons (step419 p h) (sat_cons (step420 p h) (sat_cons (step421 p h) (sat_cons (step422 p h) (sat_cons (step423 p h) (sat_cons (step424 p h) (sat_cons (step425 p h) (sat_cons (step426 p h) (sat_cons (step427 p h) (sat_cons (step428 p h) (sat_cons (step429 p h) (sat_cons (step430 p h) (sat_cons (step431 p h) (sat_cons (step432 p h) (sat_cons (step433 p h) (sat_cons (step434 p h) (sat_cons (step435 p h) (sat_cons (step436 p h) (sat_cons (step437 p h) (sat_cons (step438 p h) (sat_cons (step439 p h) (sat_cons (step440 p h) (sat_cons (step441 p h) (sat_cons (step442 p h) (sat_cons (step443 p h) (sat_cons (step444 p h) (sat_cons (step445 p h) (sat_cons (step446 p h) (sat_cons (step667 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1096 : List Lit := [(1452, true)]
theorem step1096 (p : Nat → Bool) (h : Constraints p) : clause p c1096 = true :=
  Snake9.LocalRup.prove_clause [c782, c786, c774, c776, c763, c765, c772, c768, c769, c760, c761, c129, c164, c205, c196] c1096 (by decide) p (sat_cons (step782 p h) (sat_cons (step786 p h) (sat_cons (step774 p h) (sat_cons (step776 p h) (sat_cons (step763 p h) (sat_cons (step765 p h) (sat_cons (step772 p h) (sat_cons (step768 p h) (sat_cons (step769 p h) (sat_cons (step760 p h) (sat_cons (step761 p h) (sat_cons (step129 p h) (sat_cons (step164 p h) (sat_cons (step205 p h) (sat_cons (step196 p h) (sat_nil p))))))))))))))))
def c1097 : List Lit := [(1523, true)]
theorem step1097 (p : Nat → Bool) (h : Constraints p) : clause p c1097 = true :=
  Snake9.LocalRup.prove_clause [c1091, c909, c912, c903, c890, c895, c896, c887, c888, c321, c302, c312, c308, c580] c1097 (by decide) p (sat_cons (step1091 p h) (sat_cons (step909 p h) (sat_cons (step912 p h) (sat_cons (step903 p h) (sat_cons (step890 p h) (sat_cons (step895 p h) (sat_cons (step896 p h) (sat_cons (step887 p h) (sat_cons (step888 p h) (sat_cons (step321 p h) (sat_cons (step302 p h) (sat_cons (step312 p h) (sat_cons (step308 p h) (sat_cons (step580 p h) (sat_nil p)))))))))))))))
def c1098 : List Lit := [(1510, true), (1515, true)]
theorem step1098 (p : Nat → Bool) (h : Constraints p) : clause p c1098 = true :=
  Snake9.LocalRup.prove_clause [c1091, c896, c895, c887, c888, c321, c302, c312, c308, c580] c1098 (by decide) p (sat_cons (step1091 p h) (sat_cons (step896 p h) (sat_cons (step895 p h) (sat_cons (step887 p h) (sat_cons (step888 p h) (sat_cons (step321 p h) (sat_cons (step302 p h) (sat_cons (step312 p h) (sat_cons (step308 p h) (sat_cons (step580 p h) (sat_nil p)))))))))))
def c1099 : List Lit := [(1519, true), (1531, true)]
theorem step1099 (p : Nat → Bool) (h : Constraints p) : clause p c1099 = true :=
  Snake9.LocalRup.prove_clause [c1097, c1086, c926, c874, c866, c863, c864, c868, c861, c273, c877, c855, c853, c860, c923, c917, c901, c903, c898, c163, c1098, c893, c296, c285, c264, c562, c560, c565] c1099 (by decide) p (sat_cons (step1097 p h) (sat_cons (step1086 p h) (sat_cons (step926 p h) (sat_cons (step874 p h) (sat_cons (step866 p h) (sat_cons (step863 p h) (sat_cons (step864 p h) (sat_cons (step868 p h) (sat_cons (step861 p h) (sat_cons (step273 p h) (sat_cons (step877 p h) (sat_cons (step855 p h) (sat_cons (step853 p h) (sat_cons (step860 p h) (sat_cons (step923 p h) (sat_cons (step917 p h) (sat_cons (step901 p h) (sat_cons (step903 p h) (sat_cons (step898 p h) (sat_cons (step163 p h) (sat_cons (step1098 p h) (sat_cons (step893 p h) (sat_cons (step296 p h) (sat_cons (step285 p h) (sat_cons (step264 p h) (sat_cons (step562 p h) (sat_cons (step560 p h) (sat_cons (step565 p h) (sat_nil p)))))))))))))))))))))))))))))
def c1100 : List Lit := [(1531, true)]
theorem step1100 (p : Nat → Bool) (h : Constraints p) : clause p c1100 = true :=
  Snake9.LocalRup.prove_clause [c1097, c1086, c923, c926, c910, c874, c877, c866, c868, c855, c863, c864, c860, c861, c853, c273, c1099, c913, c890, c892, c1098, c296, c904, c285, c898, c562, c163, c565, c264, c560] c1100 (by decide) p (sat_cons (step1097 p h) (sat_cons (step1086 p h) (sat_cons (step923 p h) (sat_cons (step926 p h) (sat_cons (step910 p h) (sat_cons (step874 p h) (sat_cons (step877 p h) (sat_cons (step866 p h) (sat_cons (step868 p h) (sat_cons (step855 p h) (sat_cons (step863 p h) (sat_cons (step864 p h) (sat_cons (step860 p h) (sat_cons (step861 p h) (sat_cons (step853 p h) (sat_cons (step273 p h) (sat_cons (step1099 p h) (sat_cons (step913 p h) (sat_cons (step890 p h) (sat_cons (step892 p h) (sat_cons (step1098 p h) (sat_cons (step296 p h) (sat_cons (step904 p h) (sat_cons (step285 p h) (sat_cons (step898 p h) (sat_cons (step562 p h) (sat_cons (step163 p h) (sat_cons (step565 p h) (sat_cons (step264 p h) (sat_cons (step560 p h) (sat_nil p)))))))))))))))))))))))))))))))
def c1101 : List Lit := [(1394, true), (135, true)]
theorem step1101 (p : Nat → Bool) (h : Constraints p) : clause p c1101 = true :=
  Snake9.LocalRup.prove_clause [c709, c711, c706, c703, c704, c54, c52] c1101 (by decide) p (sat_cons (step709 p h) (sat_cons (step711 p h) (sat_cons (step706 p h) (sat_cons (step703 p h) (sat_cons (step704 p h) (sat_cons (step54 p h) (sat_cons (step52 p h) (sat_nil p))))))))
def c1102 : List Lit := [(38, true), (1424, true)]
theorem step1102 (p : Nat → Bool) (h : Constraints p) : clause p c1102 = true :=
  Snake9.LocalRup.prove_clause [c1093, c742, c741, c85, c83, c501] c1102 (by decide) p (sat_cons (step1093 p h) (sat_cons (step742 p h) (sat_cons (step741 p h) (sat_cons (step85 p h) (sat_cons (step83 p h) (sat_cons (step501 p h) (sat_nil p)))))))
def c1103 : List Lit := [(1387, true), (14, false), (133, true)]
theorem step1103 (p : Nat → Bool) (h : Constraints p) : clause p c1103 = true :=
  Snake9.LocalRup.prove_clause [c699, c701, c696, c697, c36, c49, c51] c1103 (by decide) p (sat_cons (step699 p h) (sat_cons (step701 p h) (sat_cons (step696 p h) (sat_cons (step697 p h) (sat_cons (step36 p h) (sat_cons (step49 p h) (sat_cons (step51 p h) (sat_nil p))))))))
def c1104 : List Lit := [(1385, true), (1372, true)]
theorem step1104 (p : Nat → Bool) (h : Constraints p) : clause p c1104 = true :=
  Snake9.LocalRup.prove_clause [c678, c677, c696, c697, c27, c35, c51, c48] c1104 (by decide) p (sat_cons (step678 p h) (sat_cons (step677 p h) (sat_cons (step696 p h) (sat_cons (step697 p h) (sat_cons (step27 p h) (sat_cons (step35 p h) (sat_cons (step51 p h) (sat_cons (step48 p h) (sat_nil p)))))))))
def c1105 : List Lit := [(1553, true), (210, true)]
theorem step1105 (p : Nat → Bool) (h : Constraints p) : clause p c1105 = true :=
  Snake9.LocalRup.prove_clause [c958, c959, c956, c957, c953, c373, c374] c1105 (by decide) p (sat_cons (step958 p h) (sat_cons (step959 p h) (sat_cons (step956 p h) (sat_cons (step957 p h) (sat_cons (step953 p h) (sat_cons (step373 p h) (sat_cons (step374 p h) (sat_nil p))))))))
def c1106 : List Lit := [(1576, true), (226, true)]
theorem step1106 (p : Nat → Bool) (h : Constraints p) : clause p c1106 = true :=
  Snake9.LocalRup.prove_clause [c984, c986, c981, c982, c979, c388, c390] c1106 (by decide) p (sat_cons (step984 p h) (sat_cons (step986 p h) (sat_cons (step981 p h) (sat_cons (step982 p h) (sat_cons (step979 p h) (sat_cons (step388 p h) (sat_cons (step390 p h) (sat_nil p))))))))
def c1107 : List Lit := [(85, true), (1518, true), (89, false), (86, false), (203, true), (88, true), (56, true)]
theorem step1107 (p : Nat → Bool) (h : Constraints p) : clause p c1107 = true :=
  Snake9.LocalRup.prove_clause [c434, c364, c358, c349, c900] c1107 (by decide) p (sat_cons (step434 p h) (sat_cons (step364 p h) (sat_cons (step358 p h) (sat_cons (step349 p h) (sat_cons (step900 p h) (sat_nil p))))))
def c1108 : List Lit := [(45, true), (2, false), (116, true), (197, true), (87, true), (83, false), (86, false)]
theorem step1108 (p : Nat → Bool) (h : Constraints p) : clause p c1108 = true :=
  Snake9.LocalRup.prove_clause [c391, c5, c335, c326, c327, c2] c1108 (by decide) p (sat_cons (step391 p h) (sat_cons (step5 p h) (sat_cons (step335 p h) (sat_cons (step326 p h) (sat_cons (step327 p h) (sat_cons (step2 p h) (sat_nil p)))))))
def c1109 : List Lit := [(1525, true), (76, true), (193, true), (1517, false)]
theorem step1109 (p : Nat → Bool) (h : Constraints p) : clause p c1109 = true :=
  Snake9.LocalRup.prove_clause [c888, c890, c901, c918, c914, c891, c904, c889, c895, c896, c321, c317] c1109 (by decide) p (sat_cons (step888 p h) (sat_cons (step890 p h) (sat_cons (step901 p h) (sat_cons (step918 p h) (sat_cons (step914 p h) (sat_cons (step891 p h) (sat_cons (step904 p h) (sat_cons (step889 p h) (sat_cons (step895 p h) (sat_cons (step896 p h) (sat_cons (step321 p h) (sat_cons (step317 p h) (sat_nil p)))))))))))))
def c1110 : List Lit := [(1407, true), (1394, false), (1367, false)]
theorem step1110 (p : Nat → Bool) (h : Constraints p) : clause p c1110 = true :=
  Snake9.LocalRup.prove_clause [c714, c687, c724, c722, c688, c716, c680, c699, c1104] c1110 (by decide) p (sat_cons (step714 p h) (sat_cons (step687 p h) (sat_cons (step724 p h) (sat_cons (step722 p h) (sat_cons (step688 p h) (sat_cons (step716 p h) (sat_cons (step680 p h) (sat_cons (step699 p h) (sat_cons (step1104 p h) (sat_nil p))))))))))
def c1111 : List Lit := [(66, true), (355, true), (60, false), (71, true), (56, false), (44, true), (1501, true)]
theorem step1111 (p : Nat → Bool) (h : Constraints p) : clause p c1111 = true :=
  Snake9.LocalRup.prove_clause [c423, c425, c560, c559, c863, c872, c861, c249, c862, c870, c160, c865, c264, c270, c294, c277] c1111 (by decide) p (sat_cons (step423 p h) (sat_cons (step425 p h) (sat_cons (step560 p h) (sat_cons (step559 p h) (sat_cons (step863 p h) (sat_cons (step872 p h) (sat_cons (step861 p h) (sat_cons (step249 p h) (sat_cons (step862 p h) (sat_cons (step870 p h) (sat_cons (step160 p h) (sat_cons (step865 p h) (sat_cons (step264 p h) (sat_cons (step270 p h) (sat_cons (step294 p h) (sat_cons (step277 p h) (sat_nil p)))))))))))))))))
def c1112 : List Lit := [(72, true), (1526, true), (193, true), (1510, false), (1517, false)]
theorem step1112 (p : Nat → Bool) (h : Constraints p) : clause p c1112 = true :=
  Snake9.LocalRup.prove_clause [c429, c320, c893, c318, c919, c895, c904] c1112 (by decide) p (sat_cons (step429 p h) (sat_cons (step320 p h) (sat_cons (step893 p h) (sat_cons (step318 p h) (sat_cons (step919 p h) (sat_cons (step895 p h) (sat_cons (step904 p h) (sat_nil p))))))))
def c1113 : List Lit := [(68, false), (60, false), (182, true), (56, false), (72, false)]
theorem step1113 (p : Nat → Bool) (h : Constraints p) : clause p c1113 = true :=
  Snake9.LocalRup.prove_clause [c160, c294, c264] c1113 (by decide) p (sat_cons (step160 p h) (sat_cons (step294 p h) (sat_cons (step264 p h) (sat_nil p))))
def c1114 : List Lit := [(182, true), (73, true), (68, false), (56, false), (77, true)]
theorem step1114 (p : Nat → Bool) (h : Constraints p) : clause p c1114 = true :=
  Snake9.LocalRup.prove_clause [c424, c264, c263, c156, c260] c1114 (by decide) p (sat_cons (step424 p h) (sat_cons (step264 p h) (sat_cons (step263 p h) (sat_cons (step156 p h) (sat_cons (step260 p h) (sat_nil p))))))
def c1115 : List Lit := [(52, true), (1445, true), (49, true), (56, true), (44, false), (168, true)]
theorem step1115 (p : Nat → Bool) (h : Constraints p) : clause p c1115 = true :=
  Snake9.LocalRup.prove_clause [c418, c206, c770, c200, c199, c1040] c1115 (by decide) p (sat_cons (step418 p h) (sat_cons (step206 p h) (sat_cons (step770 p h) (sat_cons (step200 p h) (sat_cons (step199 p h) (sat_cons (step1040 p h) (sat_nil p)))))))
def c1116 : List Lit := [(62, true), (76, true), (192, true), (78, false)]
theorem step1116 (p : Nat → Bool) (h : Constraints p) : clause p c1116 = true :=
  Snake9.LocalRup.prove_clause [c428, c314, c313, c304, c1053] c1116 (by decide) p (sat_cons (step428 p h) (sat_cons (step314 p h) (sat_cons (step313 p h) (sat_cons (step304 p h) (sat_cons (step1053 p h) (sat_nil p))))))
def c1117 : List Lit := [(1506, true), (1498, false), (73, true), (1500, false), (85, false), (58, true), (182, true)]
theorem step1117 (p : Nat → Bool) (h : Constraints p) : clause p c1117 = true :=
  Snake9.LocalRup.prove_clause [c857, c884, c880, c858, c870, c853, c860, c163, c264] c1117 (by decide) p (sat_cons (step857 p h) (sat_cons (step884 p h) (sat_cons (step880 p h) (sat_cons (step858 p h) (sat_cons (step870 p h) (sat_cons (step853 p h) (sat_cons (step860 p h) (sat_cons (step163 p h) (sat_cons (step264 p h) (sat_nil p))))))))))
def c1118 : List Lit := [(68, false), (60, false), (73, true), (85, false), (182, true)]
theorem step1118 (p : Nat → Bool) (h : Constraints p) : clause p c1118 = true :=
  Snake9.LocalRup.prove_clause [c264, c163] c1118 (by decide) p (sat_cons (step264 p h) (sat_cons (step163 p h) (sat_nil p)))
def c1119 : List Lit := [(1525, true), (76, true), (79, true), (191, true), (67, true)]
theorem step1119 (p : Nat → Bool) (h : Constraints p) : clause p c1119 = true :=
  Snake9.LocalRup.prove_clause [c888, c890, c895, c903, c918, c914, c891, c906, c889, c897, c310, c309, c1053] c1119 (by decide) p (sat_cons (step888 p h) (sat_cons (step890 p h) (sat_cons (step895 p h) (sat_cons (step903 p h) (sat_cons (step918 p h) (sat_cons (step914 p h) (sat_cons (step891 p h) (sat_cons (step906 p h) (sat_cons (step889 p h) (sat_cons (step897 p h) (sat_cons (step310 p h) (sat_cons (step309 p h) (sat_cons (step1053 p h) (sat_nil p))))))))))))))
end B112E171
