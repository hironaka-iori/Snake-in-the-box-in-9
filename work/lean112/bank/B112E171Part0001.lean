import B112E171Part0000
namespace B112E171
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1120 : List Lit := [(78, false), (52, false), (76, true), (63, false), (192, true)]
theorem step1120 (p : Nat → Bool) (h : Constraints p) : clause p c1120 = true :=
  Snake9.LocalRup.prove_clause [c1116, c238] c1120 (by decide) p (sat_cons (step1116 p h) (sat_cons (step238 p h) (sat_nil p)))
def c1121 : List Lit := [(83, false), (82, true), (88, false), (86, false), (45, true), (197, true)]
theorem step1121 (p : Nat → Bool) (h : Constraints p) : clause p c1121 = true :=
  Snake9.LocalRup.prove_clause [c335, c348] c1121 (by decide) p (sat_cons (step335 p h) (sat_cons (step348 p h) (sat_nil p)))
def c1122 : List Lit := [(4, true), (119, true), (1366, true), (56, true)]
theorem step1122 (p : Nat → Bool) (h : Constraints p) : clause p c1122 = true :=
  Snake9.LocalRup.prove_clause [c393, c19, c670, c15] c1122 (by decide) p (sat_cons (step393 p h) (sat_cons (step19 p h) (sat_cons (step670 p h) (sat_cons (step15 p h) (sat_nil p)))))
def c1123 : List Lit := [(4, false), (52, false), (88, false), (87, true)]
theorem step1123 (p : Nat → Bool) (h : Constraints p) : clause p c1123 = true :=
  Snake9.LocalRup.prove_clause [c666, c180, c11, c356, c450, c606, c452, c607, c454, c613, c467, c627, c492, c655, c544, c658, c664] c1123 (by decide) p (sat_cons (step666 p h) (sat_cons (step180 p h) (sat_cons (step11 p h) (sat_cons (step356 p h) (sat_cons (step450 p h) (sat_cons (step606 p h) (sat_cons (step452 p h) (sat_cons (step607 p h) (sat_cons (step454 p h) (sat_cons (step613 p h) (sat_cons (step467 p h) (sat_cons (step627 p h) (sat_cons (step492 p h) (sat_cons (step655 p h) (sat_cons (step544 p h) (sat_cons (step658 p h) (sat_cons (step664 p h) (sat_nil p))))))))))))))))))
def c1124 : List Lit := [(1432, true)]
theorem step1124 (p : Nat → Bool) (h : Constraints p) : clause p c1124 = true :=
  Snake9.LocalRup.prove_clause [c750, c752, c748, c736, c741, c742, c1102, c733, c87] c1124 (by decide) p (sat_cons (step750 p h) (sat_cons (step752 p h) (sat_cons (step748 p h) (sat_cons (step736 p h) (sat_cons (step741 p h) (sat_cons (step742 p h) (sat_cons (step1102 p h) (sat_cons (step733 p h) (sat_cons (step87 p h) (sat_nil p))))))))))
def c1125 : List Lit := [(1460, true)]
theorem step1125 (p : Nat → Bool) (h : Constraints p) : clause p c1125 = true :=
  Snake9.LocalRup.prove_clause [c1124, c1096, c802] c1125 (by decide) p (sat_cons (step1124 p h) (sat_cons (step1096 p h) (sat_cons (step802 p h) (sat_nil p))))
def c1126 : List Lit := [(58, false), (48, false), (172, true)]
theorem step1126 (p : Nat → Bool) (h : Constraints p) : clause p c1126 = true :=
  Snake9.LocalRup.prove_clause [c222, c223, c1044] c1126 (by decide) p (sat_cons (step222 p h) (sat_cons (step223 p h) (sat_cons (step1044 p h) (sat_nil p))))
def c1127 : List Lit := [(1500, true), (86, false), (71, true), (183, true), (52, false)]
theorem step1127 (p : Nat → Bool) (h : Constraints p) : clause p c1127 = true :=
  Snake9.LocalRup.prove_clause [c863, c867, c869, c865, c861, c172, c271, c1051, c272] c1127 (by decide) p (sat_cons (step863 p h) (sat_cons (step867 p h) (sat_cons (step869 p h) (sat_cons (step865 p h) (sat_cons (step861 p h) (sat_cons (step172 p h) (sat_cons (step271 p h) (sat_cons (step1051 p h) (sat_cons (step272 p h) (sat_nil p))))))))))
def c1128 : List Lit := [(60, false), (68, false), (48, false), (64, true), (174, true)]
theorem step1128 (p : Nat → Bool) (h : Constraints p) : clause p c1128 = true :=
  Snake9.LocalRup.prove_clause [c235, c152] c1128 (by decide) p (sat_cons (step235 p h) (sat_cons (step152 p h) (sat_nil p)))
def c1129 : List Lit := [(1524, true), (1517, false)]
theorem step1129 (p : Nat → Bool) (h : Constraints p) : clause p c1129 = true :=
  Snake9.LocalRup.prove_clause [c901, c910, c913, c904, c890, c1098] c1129 (by decide) p (sat_cons (step901 p h) (sat_cons (step910 p h) (sat_cons (step913 p h) (sat_cons (step904 p h) (sat_cons (step890 p h) (sat_cons (step1098 p h) (sat_nil p)))))))
def c1130 : List Lit := [(1558, false), (1454, false), (1535, false), (1576, false), (1407, false), (41, false), (9, false)]
theorem step1130 (p : Nat → Bool) (h : Constraints p) : clause p c1130 = true :=
  Snake9.LocalRup.prove_clause [c1124, c1036, c804, c829, c1030, c1024, c988, c996, c997, c1023, c989, c1031, c975, c830, c973, c811, c93, c94, c738, c743, c753, c746] c1130 (by decide) p (sat_cons (step1124 p h) (sat_cons (step1036 p h) (sat_cons (step804 p h) (sat_cons (step829 p h) (sat_cons (step1030 p h) (sat_cons (step1024 p h) (sat_cons (step988 p h) (sat_cons (step996 p h) (sat_cons (step997 p h) (sat_cons (step1023 p h) (sat_cons (step989 p h) (sat_cons (step1031 p h) (sat_cons (step975 p h) (sat_cons (step830 p h) (sat_cons (step973 p h) (sat_cons (step811 p h) (sat_cons (step93 p h) (sat_cons (step94 p h) (sat_cons (step738 p h) (sat_cons (step743 p h) (sat_cons (step753 p h) (sat_cons (step746 p h) (sat_nil p)))))))))))))))))))))))
def c1131 : List Lit := [(1408, true), (1368, false), (1394, false)]
theorem step1131 (p : Nat → Bool) (h : Constraints p) : clause p c1131 = true :=
  Snake9.LocalRup.prove_clause [c691, c714, c727, c725, c692, c716, c680, c699, c1104] c1131 (by decide) p (sat_cons (step691 p h) (sat_cons (step714 p h) (sat_cons (step727 p h) (sat_cons (step725 p h) (sat_cons (step692 p h) (sat_cons (step716 p h) (sat_cons (step680 p h) (sat_cons (step699 p h) (sat_cons (step1104 p h) (sat_nil p))))))))))
def c1132 : List Lit := [(4, true), (48, false), (56, true), (1368, true)]
theorem step1132 (p : Nat → Bool) (h : Constraints p) : clause p c1132 = true :=
  Snake9.LocalRup.prove_clause [c393, c672, c669, c19, c674, c670, c6, c14] c1132 (by decide) p (sat_cons (step393 p h) (sat_cons (step672 p h) (sat_cons (step669 p h) (sat_cons (step19 p h) (sat_cons (step674 p h) (sat_cons (step670 p h) (sat_cons (step6 p h) (sat_cons (step14 p h) (sat_nil p)))))))))
def c1133 : List Lit := [(1546, true), (85, false), (88, false)]
theorem step1133 (p : Nat → Bool) (h : Constraints p) : clause p c1133 = true :=
  Snake9.LocalRup.prove_clause [c1075, c948, c950, c945, c351, c362, c354, c358, c606, c610, c607, c611, c614] c1133 (by decide) p (sat_cons (step1075 p h) (sat_cons (step948 p h) (sat_cons (step950 p h) (sat_cons (step945 p h) (sat_cons (step351 p h) (sat_cons (step362 p h) (sat_cons (step354 p h) (sat_cons (step358 p h) (sat_cons (step606 p h) (sat_cons (step610 p h) (sat_cons (step607 p h) (sat_cons (step611 p h) (sat_cons (step614 p h) (sat_nil p))))))))))))))
def c1134 : List Lit := [(89, false), (87, true), (85, false), (88, false)]
theorem step1134 (p : Nat → Bool) (h : Constraints p) : clause p c1134 = true :=
  Snake9.LocalRup.prove_clause [c1075, c362, c354, c358, c606, c610, c607, c611, c614] c1134 (by decide) p (sat_cons (step1075 p h) (sat_cons (step362 p h) (sat_cons (step354 p h) (sat_cons (step358 p h) (sat_cons (step606 p h) (sat_cons (step610 p h) (sat_cons (step607 p h) (sat_cons (step611 p h) (sat_cons (step614 p h) (sat_nil p))))))))))
def c1135 : List Lit := [(202, false), (51, true), (87, true), (86, false), (1373, true), (1442, true), (85, false), (83, false), (53, false)]
theorem step1135 (p : Nat → Bool) (h : Constraints p) : clause p c1135 = true :=
  Snake9.LocalRup.prove_clause [c1084, c1059, c353, c606, c607, c609, c613, c341, c627, c327, c326, c655, c766, c679, c661, c760, c761, c601, c148, c336, c596, c338, c593, c590, c591] c1135 (by decide) p (sat_cons (step1084 p h) (sat_cons (step1059 p h) (sat_cons (step353 p h) (sat_cons (step606 p h) (sat_cons (step607 p h) (sat_cons (step609 p h) (sat_cons (step613 p h) (sat_cons (step341 p h) (sat_cons (step627 p h) (sat_cons (step327 p h) (sat_cons (step326 p h) (sat_cons (step655 p h) (sat_cons (step766 p h) (sat_cons (step679 p h) (sat_cons (step661 p h) (sat_cons (step760 p h) (sat_cons (step761 p h) (sat_cons (step601 p h) (sat_cons (step148 p h) (sat_cons (step336 p h) (sat_cons (step596 p h) (sat_cons (step338 p h) (sat_cons (step593 p h) (sat_cons (step590 p h) (sat_cons (step591 p h) (sat_nil p))))))))))))))))))))))))))
def c1136 : List Lit := [(183, true), (51, true), (74, false), (66, false), (69, false)]
theorem step1136 (p : Nat → Bool) (h : Constraints p) : clause p c1136 = true :=
  Snake9.LocalRup.prove_clause [c272, c271, c253] c1136 (by decide) p (sat_cons (step272 p h) (sat_cons (step271 p h) (sat_cons (step253 p h) (sat_nil p))))
def c1137 : List Lit := [(89, false), (85, false), (83, false), (88, false)]
theorem step1137 (p : Nat → Bool) (h : Constraints p) : clause p c1137 = true :=
  Snake9.LocalRup.prove_clause [c350, c1134] c1137 (by decide) p (sat_cons (step350 p h) (sat_cons (step1134 p h) (sat_nil p)))
def c1138 : List Lit := [(63, true), (85, false), (1491, true), (56, true), (68, false), (174, true)]
theorem step1138 (p : Nat → Bool) (h : Constraints p) : clause p c1138 = true :=
  Snake9.LocalRup.prove_clause [c422, c245, c854, c163, c235] c1138 (by decide) p (sat_cons (step422 p h) (sat_cons (step245 p h) (sat_cons (step854 p h) (sat_cons (step163 p h) (sat_cons (step235 p h) (sat_nil p))))))
def c1139 : List Lit := [(1524, true), (76, true), (193, true)]
theorem step1139 (p : Nat → Bool) (h : Constraints p) : clause p c1139 = true :=
  Snake9.LocalRup.prove_clause [c888, c890, c917, c913, c891, c903, c889, c895, c896, c317, c321] c1139 (by decide) p (sat_cons (step888 p h) (sat_cons (step890 p h) (sat_cons (step917 p h) (sat_cons (step913 p h) (sat_cons (step891 p h) (sat_cons (step903 p h) (sat_cons (step889 p h) (sat_cons (step895 p h) (sat_cons (step896 p h) (sat_cons (step317 p h) (sat_cons (step321 p h) (sat_nil p))))))))))))
def c1140 : List Lit := [(1457, true), (52, true), (168, true), (1447, false), (1440, false), (49, true), (56, true)]
theorem step1140 (p : Nat → Bool) (h : Constraints p) : clause p c1140 = true :=
  Snake9.LocalRup.prove_clause [c769, c778, c764, c795, c799, c781, c767, c1115] c1140 (by decide) p (sat_cons (step769 p h) (sat_cons (step778 p h) (sat_cons (step764 p h) (sat_cons (step795 p h) (sat_cons (step799 p h) (sat_cons (step781 p h) (sat_cons (step767 p h) (sat_cons (step1115 p h) (sat_nil p)))))))))
def c1141 : List Lit := [(54, false), (86, false), (69, false), (168, true), (55, true)]
theorem step1141 (p : Nat → Bool) (h : Constraints p) : clause p c1141 = true :=
  Snake9.LocalRup.prove_clause [c173, c199] c1141 (by decide) p (sat_cons (step173 p h) (sat_cons (step199 p h) (sat_nil p)))
def c1142 : List Lit := [(1406, true), (1394, false)]
theorem step1142 (p : Nat → Bool) (h : Constraints p) : clause p c1142 = true :=
  Snake9.LocalRup.prove_clause [c714, c719, c721, c716, c685, c699, c680, c1104] c1142 (by decide) p (sat_cons (step714 p h) (sat_cons (step719 p h) (sat_cons (step721 p h) (sat_cons (step716 p h) (sat_cons (step685 p h) (sat_cons (step699 p h) (sat_cons (step680 p h) (sat_cons (step1104 p h) (sat_nil p)))))))))
def c1143 : List Lit := [(58, false), (60, false), (57, false), (47, true)]
theorem step1143 (p : Nat → Bool) (h : Constraints p) : clause p c1143 = true :=
  Snake9.LocalRup.prove_clause [c220, c227] c1143 (by decide) p (sat_cons (step220 p h) (sat_cons (step227 p h) (sat_nil p)))
def c1144 : List Lit := [(1576, true)]
theorem step1144 (p : Nat → Bool) (h : Constraints p) : clause p c1144 = true :=
  Snake9.LocalRup.prove_clause [c1090, c984, c986, c1106, c982, c979, c980, c644, c387, c385] c1144 (by decide) p (sat_cons (step1090 p h) (sat_cons (step984 p h) (sat_cons (step986 p h) (sat_cons (step1106 p h) (sat_cons (step982 p h) (sat_cons (step979 p h) (sat_cons (step980 p h) (sat_cons (step644 p h) (sat_cons (step387 p h) (sat_cons (step385 p h) (sat_nil p)))))))))))
def c1145 : List Lit := [(1580, true)]
theorem step1145 (p : Nat → Bool) (h : Constraints p) : clause p c1145 = true :=
  Snake9.LocalRup.prove_clause [c1144, c988] c1145 (by decide) p (sat_cons (step1144 p h) (sat_cons (step988 p h) (sat_nil p)))
def c1146 : List Lit := [(1553, true)]
theorem step1146 (p : Nat → Bool) (h : Constraints p) : clause p c1146 = true :=
  Snake9.LocalRup.prove_clause [c1074, c958, c959, c1105, c957, c953, c954, c620, c367, c621, c370, c624, c619] c1146 (by decide) p (sat_cons (step1074 p h) (sat_cons (step958 p h) (sat_cons (step959 p h) (sat_cons (step1105 p h) (sat_cons (step957 p h) (sat_cons (step953 p h) (sat_cons (step954 p h) (sat_cons (step620 p h) (sat_cons (step367 p h) (sat_cons (step621 p h) (sat_cons (step370 p h) (sat_cons (step624 p h) (sat_cons (step619 p h) (sat_nil p))))))))))))))
def c1147 : List Lit := [(1557, true)]
theorem step1147 (p : Nat → Bool) (h : Constraints p) : clause p c1147 = true :=
  Snake9.LocalRup.prove_clause [c1146, c962] c1147 (by decide) p (sat_cons (step1146 p h) (sat_cons (step962 p h) (sat_nil p)))
def c1148 : List Lit := [(1589, true)]
theorem step1148 (p : Nat → Bool) (h : Constraints p) : clause p c1148 = true :=
  Snake9.LocalRup.prove_clause [c1147, c1145, c993] c1148 (by decide) p (sat_cons (step1147 p h) (sat_cons (step1145 p h) (sat_cons (step993 p h) (sat_nil p))))
def c1149 : List Lit := [(1518, false), (1525, true)]
theorem step1149 (p : Nat → Bool) (h : Constraints p) : clause p c1149 = true :=
  Snake9.LocalRup.prove_clause [c911, c902, c905, c914, c1098, c890] c1149 (by decide) p (sat_cons (step911 p h) (sat_cons (step902 p h) (sat_cons (step905 p h) (sat_cons (step914 p h) (sat_cons (step1098 p h) (sat_cons (step890 p h) (sat_nil p)))))))
def c1150 : List Lit := [(1392, true), (24, false), (17, false)]
theorem step1150 (p : Nat → Bool) (h : Constraints p) : clause p c1150 = true :=
  Snake9.LocalRup.prove_clause [c706, c707, c59] c1150 (by decide) p (sat_cons (step706 p h) (sat_cons (step707 p h) (sat_cons (step59 p h) (sat_nil p))))
def c1151 : List Lit := [(21, false), (135, true), (1372, true)]
theorem step1151 (p : Nat → Bool) (h : Constraints p) : clause p c1151 = true :=
  Snake9.LocalRup.prove_clause [c678, c677, c53, c28] c1151 (by decide) p (sat_cons (step678 p h) (sat_cons (step677 p h) (sat_cons (step53 p h) (sat_cons (step28 p h) (sat_nil p)))))
def c1152 : List Lit := [(279, true), (17, false), (1395, true), (1372, true)]
theorem step1152 (p : Nat → Bool) (h : Constraints p) : clause p c1152 = true :=
  Snake9.LocalRup.prove_clause [c713, c486, c487, c484, c477, c483, c475, c482, c474, c1151, c704, c705, c712, c706, c707, c1150, c67, c63] c1152 (by decide) p (sat_cons (step713 p h) (sat_cons (step486 p h) (sat_cons (step487 p h) (sat_cons (step484 p h) (sat_cons (step477 p h) (sat_cons (step483 p h) (sat_cons (step475 p h) (sat_cons (step482 p h) (sat_cons (step474 p h) (sat_cons (step1151 p h) (sat_cons (step704 p h) (sat_cons (step705 p h) (sat_cons (step712 p h) (sat_cons (step706 p h) (sat_cons (step707 p h) (sat_cons (step1150 p h) (sat_cons (step67 p h) (sat_cons (step63 p h) (sat_nil p)))))))))))))))))))
def c1153 : List Lit := [(87, false), (1545, true), (86, false), (17, false)]
theorem step1153 (p : Nat → Bool) (h : Constraints p) : clause p c1153 = true :=
  Snake9.LocalRup.prove_clause [c346, c345, c947] c1153 (by decide) p (sat_cons (step346 p h) (sat_cons (step345 p h) (sat_cons (step947 p h) (sat_nil p))))
def c1154 : List Lit := [(16, false), (17, false), (1386, true), (11, false)]
theorem step1154 (p : Nat → Bool) (h : Constraints p) : clause p c1154 = true :=
  Snake9.LocalRup.prove_clause [c32, c33, c698] c1154 (by decide) p (sat_cons (step32 p h) (sat_cons (step33 p h) (sat_cons (step698 p h) (sat_nil p))))
def c1155 : List Lit := [(1424, false), (41, false), (1433, true), (9, false)]
theorem step1155 (p : Nat → Bool) (h : Constraints p) : clause p c1155 = true :=
  Snake9.LocalRup.prove_clause [c751, c748, c749, c753, c743, c738, c92] c1155 (by decide) p (sat_cons (step751 p h) (sat_cons (step748 p h) (sat_cons (step749 p h) (sat_cons (step753 p h) (sat_cons (step743 p h) (sat_cons (step738 p h) (sat_cons (step92 p h) (sat_nil p))))))))
def c1156 : List Lit := [(1457, false), (1374, true), (1482, true), (1394, false)]
theorem step1156 (p : Nat → Bool) (h : Constraints p) : clause p c1156 = true :=
  Snake9.LocalRup.prove_clause [c1124, c1064, c1060, c1057, c680, c1104, c699, c682, c676, c1142, c826, c807, c814, c832, c755, c720, c737, c718, c717, c702, c1152, c490, c493, c545, c466, c539, c465, c515, c460, c507, c459, c496, c22, c495, c1155, c741, c742, c1102, c87, c733, c735, c739, c78, c73] c1156 (by decide) p (sat_cons (step1124 p h) (sat_cons (step1064 p h) (sat_cons (step1060 p h) (sat_cons (step1057 p h) (sat_cons (step680 p h) (sat_cons (step1104 p h) (sat_cons (step699 p h) (sat_cons (step682 p h) (sat_cons (step676 p h) (sat_cons (step1142 p h) (sat_cons (step826 p h) (sat_cons (step807 p h) (sat_cons (step814 p h) (sat_cons (step832 p h) (sat_cons (step755 p h) (sat_cons (step720 p h) (sat_cons (step737 p h) (sat_cons (step718 p h) (sat_cons (step717 p h) (sat_cons (step702 p h) (sat_cons (step1152 p h) (sat_cons (step490 p h) (sat_cons (step493 p h) (sat_cons (step545 p h) (sat_cons (step466 p h) (sat_cons (step539 p h) (sat_cons (step465 p h) (sat_cons (step515 p h) (sat_cons (step460 p h) (sat_cons (step507 p h) (sat_cons (step459 p h) (sat_cons (step496 p h) (sat_cons (step22 p h) (sat_cons (step495 p h) (sat_cons (step1155 p h) (sat_cons (step741 p h) (sat_cons (step742 p h) (sat_cons (step1102 p h) (sat_cons (step87 p h) (sat_cons (step733 p h) (sat_cons (step735 p h) (sat_cons (step739 p h) (sat_cons (step78 p h) (sat_cons (step73 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))
def c1157 : List Lit := [(41, false), (1433, true), (35, false), (9, false)]
theorem step1157 (p : Nat → Bool) (h : Constraints p) : clause p c1157 = true :=
  Snake9.LocalRup.prove_clause [c755, c1155, c741, c1102, c87, c733, c736, c739, c753, c92, c746, c743] c1157 (by decide) p (sat_cons (step755 p h) (sat_cons (step1155 p h) (sat_cons (step741 p h) (sat_cons (step1102 p h) (sat_cons (step87 p h) (sat_cons (step733 p h) (sat_cons (step736 p h) (sat_cons (step739 p h) (sat_cons (step753 p h) (sat_cons (step92 p h) (sat_cons (step746 p h) (sat_cons (step743 p h) (sat_nil p)))))))))))))
def c1158 : List Lit := [(1433, true), (35, false), (1374, true)]
theorem step1158 (p : Nat → Bool) (h : Constraints p) : clause p c1158 = true :=
  Snake9.LocalRup.prove_clause [c1060, c411, c1058, c682, c676, c680, c677, c751, c747, c1157, c22, c459, c460, c465, c466, c492, c545, c539, c514, c513, c511, c512, c510, c509, c97, c98, c743, c745, c746, c91, c753, c68, c736, c733] c1158 (by decide) p (sat_cons (step1060 p h) (sat_cons (step411 p h) (sat_cons (step1058 p h) (sat_cons (step682 p h) (sat_cons (step676 p h) (sat_cons (step680 p h) (sat_cons (step677 p h) (sat_cons (step751 p h) (sat_cons (step747 p h) (sat_cons (step1157 p h) (sat_cons (step22 p h) (sat_cons (step459 p h) (sat_cons (step460 p h) (sat_cons (step465 p h) (sat_cons (step466 p h) (sat_cons (step492 p h) (sat_cons (step545 p h) (sat_cons (step539 p h) (sat_cons (step514 p h) (sat_cons (step513 p h) (sat_cons (step511 p h) (sat_cons (step512 p h) (sat_cons (step510 p h) (sat_cons (step509 p h) (sat_cons (step97 p h) (sat_cons (step98 p h) (sat_cons (step743 p h) (sat_cons (step745 p h) (sat_cons (step746 p h) (sat_cons (step91 p h) (sat_cons (step753 p h) (sat_cons (step68 p h) (sat_cons (step736 p h) (sat_cons (step733 p h) (sat_nil p)))))))))))))))))))))))))))))))))))
def c1159 : List Lit := [(1433, true), (1374, true)]
theorem step1159 (p : Nat → Bool) (h : Constraints p) : clause p c1159 = true :=
  Snake9.LocalRup.prove_clause [c1070, c682, c676, c680, c677, c751, c1158, c742, c748, c749, c1155, c753, c743, c744, c736, c97, c733, c510, c68, c511, c82, c513, c498, c516, c504, c505] c1159 (by decide) p (sat_cons (step1070 p h) (sat_cons (step682 p h) (sat_cons (step676 p h) (sat_cons (step680 p h) (sat_cons (step677 p h) (sat_cons (step751 p h) (sat_cons (step1158 p h) (sat_cons (step742 p h) (sat_cons (step748 p h) (sat_cons (step749 p h) (sat_cons (step1155 p h) (sat_cons (step753 p h) (sat_cons (step743 p h) (sat_cons (step744 p h) (sat_cons (step736 p h) (sat_cons (step97 p h) (sat_cons (step733 p h) (sat_cons (step510 p h) (sat_cons (step68 p h) (sat_cons (step511 p h) (sat_cons (step82 p h) (sat_cons (step513 p h) (sat_cons (step498 p h) (sat_cons (step516 p h) (sat_cons (step504 p h) (sat_cons (step505 p h) (sat_nil p)))))))))))))))))))))))))))
def c1160 : List Lit := [(1493, false), (1544, false), (71, true), (52, false), (183, true), (1610, true)]
theorem step1160 (p : Nat → Bool) (h : Constraints p) : clause p c1160 = true :=
  Snake9.LocalRup.prove_clause [c1097, c1145, c1146, c948, c964, c996, c1019, c940, c863, c866, c883, c884, c936, c1127, c1015, c951, c1000, c967] c1160 (by decide) p (sat_cons (step1097 p h) (sat_cons (step1145 p h) (sat_cons (step1146 p h) (sat_cons (step948 p h) (sat_cons (step964 p h) (sat_cons (step996 p h) (sat_cons (step1019 p h) (sat_cons (step940 p h) (sat_cons (step863 p h) (sat_cons (step866 p h) (sat_cons (step883 p h) (sat_cons (step884 p h) (sat_cons (step936 p h) (sat_cons (step1127 p h) (sat_cons (step1015 p h) (sat_cons (step951 p h) (sat_cons (step1000 p h) (sat_cons (step967 p h) (sat_nil p)))))))))))))))))))
def c1161 : List Lit := [(1533, true), (1491, true), (1497, false), (63, true), (174, true), (56, true)]
theorem step1161 (p : Nat → Bool) (h : Constraints p) : clause p c1161 = true :=
  Snake9.LocalRup.prove_clause [c1097, c852, c855, c866, c878, c936, c931, c879, c1129, c869, c898, c860, c1138] c1161 (by decide) p (sat_cons (step1097 p h) (sat_cons (step852 p h) (sat_cons (step855 p h) (sat_cons (step866 p h) (sat_cons (step878 p h) (sat_cons (step936 p h) (sat_cons (step931 p h) (sat_cons (step879 p h) (sat_cons (step1129 p h) (sat_cons (step869 p h) (sat_cons (step898 p h) (sat_cons (step860 p h) (sat_cons (step1138 p h) (sat_nil p))))))))))))))
def c1162 : List Lit := [(52, false), (174, true), (183, true), (200, true), (53, false), (16, true), (17, false), (1610, true), (54, false), (56, true), (4, false)]
theorem step1162 (p : Nat → Bool) (h : Constraints p) : clause p c1162 = true :=
  Snake9.LocalRup.prove_clause [c1145, c1146, c180, c179, c178, c946, c863, c1160, c856, c1161, c1015, c1000, c967, c949, c951, c1153, c343, c171] c1162 (by decide) p (sat_cons (step1145 p h) (sat_cons (step1146 p h) (sat_cons (step180 p h) (sat_cons (step179 p h) (sat_cons (step178 p h) (sat_cons (step946 p h) (sat_cons (step863 p h) (sat_cons (step1160 p h) (sat_cons (step856 p h) (sat_cons (step1161 p h) (sat_cons (step1015 p h) (sat_cons (step1000 p h) (sat_cons (step967 p h) (sat_cons (step949 p h) (sat_cons (step951 p h) (sat_cons (step1153 p h) (sat_cons (step343 p h) (sat_cons (step171 p h) (sat_nil p)))))))))))))))))))
def c1163 : List Lit := [(60, false), (58, false), (174, true), (64, true), (57, false)]
theorem step1163 (p : Nat → Bool) (h : Constraints p) : clause p c1163 = true :=
  Snake9.LocalRup.prove_clause [c234, c227] c1163 (by decide) p (sat_cons (step234 p h) (sat_cons (step227 p h) (sat_nil p)))
def c1164 : List Lit := [(1493, false), (193, true), (190, true), (1534, true), (1497, false), (57, false)]
theorem step1164 (p : Nat → Bool) (h : Constraints p) : clause p c1164 = true :=
  Snake9.LocalRup.prove_clause [c1097, c940, c866, c884, c883, c869, c937, c861, c1139, c306, c300] c1164 (by decide) p (sat_cons (step1097 p h) (sat_cons (step940 p h) (sat_cons (step866 p h) (sat_cons (step884 p h) (sat_cons (step883 p h) (sat_cons (step869 p h) (sat_cons (step937 p h) (sat_cons (step861 p h) (sat_cons (step1139 p h) (sat_cons (step306 p h) (sat_cons (step300 p h) (sat_nil p))))))))))))
def c1165 : List Lit := [(58, false), (60, false), (57, false), (64, true)]
theorem step1165 (p : Nat → Bool) (h : Constraints p) : clause p c1165 = true :=
  Snake9.LocalRup.prove_clause [c1087, c1163, c227, c547, c222, c550] c1165 (by decide) p (sat_cons (step1087 p h) (sat_cons (step1163 p h) (sat_cons (step227 p h) (sat_cons (step547 p h) (sat_cons (step222 p h) (sat_cons (step550 p h) (sat_nil p)))))))
def c1166 : List Lit := [(1493, true), (64, true), (63, true), (57, false)]
theorem step1166 (p : Nat → Bool) (h : Constraints p) : clause p c1166 = true :=
  Snake9.LocalRup.prove_clause [c852, c856, c858, c854, c1165] c1166 (by decide) p (sat_cons (step852 p h) (sat_cons (step856 p h) (sat_cons (step858 p h) (sat_cons (step854 p h) (sat_cons (step1165 p h) (sat_nil p))))))
def c1167 : List Lit := [(1546, true), (52, false), (4, false)]
theorem step1167 (p : Nat → Bool) (h : Constraints p) : clause p c1167 = true :=
  Snake9.LocalRup.prove_clause [c948, c950, c945, c946, c351, c1123] c1167 (by decide) p (sat_cons (step948 p h) (sat_cons (step950 p h) (sat_cons (step945 p h) (sat_cons (step946 p h) (sat_cons (step351 p h) (sat_cons (step1123 p h) (sat_nil p)))))))
def c1168 : List Lit := [(66, true), (72, true), (70, false), (183, true), (52, false), (54, false), (44, true)]
theorem step1168 (p : Nat → Bool) (h : Constraints p) : clause p c1168 = true :=
  Snake9.LocalRup.prove_clause [c423, c425, c249, c278, c170, c272] c1168 (by decide) p (sat_cons (step423 p h) (sat_cons (step425 p h) (sat_cons (step249 p h) (sat_cons (step278 p h) (sat_cons (step170 p h) (sat_cons (step272 p h) (sat_nil p)))))))
def c1169 : List Lit := [(71, false), (1526, true), (1491, true), (174, true), (180, true), (183, true), (185, true), (192, true), (193, true), (53, true), (52, false), (57, false), (54, false), (44, true), (56, true), (2, false)]
theorem step1169 (p : Nat → Bool) (h : Constraints p) : clause p c1169 = true :=
  Snake9.LocalRup.prove_clause [c429, c426, c423, c286, c287, c1052, c320, c298, c318, c1168, c115, c273, c248, c257, c300, c888, c893, c1112, c919, c898, c906, c1138, c897, c1120] c1169 (by decide) p (sat_cons (step429 p h) (sat_cons (step426 p h) (sat_cons (step423 p h) (sat_cons (step286 p h) (sat_cons (step287 p h) (sat_cons (step1052 p h) (sat_cons (step320 p h) (sat_cons (step298 p h) (sat_cons (step318 p h) (sat_cons (step1168 p h) (sat_cons (step115 p h) (sat_cons (step273 p h) (sat_cons (step248 p h) (sat_cons (step257 p h) (sat_cons (step300 p h) (sat_cons (step888 p h) (sat_cons (step893 p h) (sat_cons (step1112 p h) (sat_cons (step919 p h) (sat_cons (step898 p h) (sat_cons (step906 p h) (sat_cons (step1138 p h) (sat_cons (step897 p h) (sat_cons (step1120 p h) (sat_nil p)))))))))))))))))))))))))
def c1170 : List Lit := [(1492, true), (172, true), (57, false)]
theorem step1170 (p : Nat → Bool) (h : Constraints p) : clause p c1170 = true :=
  Snake9.LocalRup.prove_clause [c855, c857, c853, c222, c227] c1170 (by decide) p (sat_cons (step855 p h) (sat_cons (step857 p h) (sat_cons (step853 p h) (sat_cons (step222 p h) (sat_cons (step227 p h) (sat_nil p))))))
def c1171 : List Lit := [(69, false), (66, false), (183, true), (52, false), (54, false)]
theorem step1171 (p : Nat → Bool) (h : Constraints p) : clause p c1171 = true :=
  Snake9.LocalRup.prove_clause [c170, c271, c1051, c272] c1171 (by decide) p (sat_cons (step170 p h) (sat_cons (step271 p h) (sat_cons (step1051 p h) (sat_cons (step272 p h) (sat_nil p)))))
def c1172 : List Lit := [(66, false), (1492, false), (71, true), (1534, true), (180, true), (183, true), (193, true), (52, false), (57, false), (54, false), (44, true), (2, false)]
theorem step1172 (p : Nat → Bool) (h : Constraints p) : clause p c1172 = true :=
  Snake9.LocalRup.prove_clause [c423, c115, c1171, c248, c865, c257, c867, c300, c879, c1139, c937] c1172 (by decide) p (sat_cons (step423 p h) (sat_cons (step115 p h) (sat_cons (step1171 p h) (sat_cons (step248 p h) (sat_cons (step865 p h) (sat_cons (step257 p h) (sat_cons (step867 p h) (sat_cons (step300 p h) (sat_cons (step879 p h) (sat_cons (step1139 p h) (sat_cons (step937 p h) (sat_nil p))))))))))))
def c1173 : List Lit := [(52, false), (1547, true), (1498, true), (183, true), (65, true), (53, false), (4, false)]
theorem step1173 (p : Nat → Bool) (h : Constraints p) : clause p c1173 = true :=
  Snake9.LocalRup.prove_clause [c180, c179, c946, c865, c951, c272, c172] c1173 (by decide) p (sat_cons (step180 p h) (sat_cons (step179 p h) (sat_cons (step946 p h) (sat_cons (step865 p h) (sat_cons (step951 p h) (sat_cons (step272 p h) (sat_cons (step172 p h) (sat_nil p))))))))
def c1174 : List Lit := [(50, true), (193, true), (1525, true), (68, false), (182, true), (71, false), (49, false)]
theorem step1174 (p : Nat → Bool) (h : Constraints p) : clause p c1174 = true :=
  Snake9.LocalRup.prove_clause [c429, c264, c265, c296, c259, c320, c887, c318, c893, c895, c918, c903] c1174 (by decide) p (sat_cons (step429 p h) (sat_cons (step264 p h) (sat_cons (step265 p h) (sat_cons (step296 p h) (sat_cons (step259 p h) (sat_cons (step320 p h) (sat_cons (step887 p h) (sat_cons (step318 p h) (sat_cons (step893 p h) (sat_cons (step895 p h) (sat_cons (step918 p h) (sat_cons (step903 p h) (sat_nil p)))))))))))))
def c1175 : List Lit := [(45, true), (1545, true), (197, true), (82, true), (86, false), (83, false)]
theorem step1175 (p : Nat → Bool) (h : Constraints p) : clause p c1175 = true :=
  Snake9.LocalRup.prove_clause [c335, c1121, c349, c947] c1175 (by decide) p (sat_cons (step335 p h) (sat_cons (step1121 p h) (sat_cons (step349 p h) (sat_cons (step947 p h) (sat_nil p)))))
def c1176 : List Lit := [(1394, false), (1407, true), (1372, true), (53, true)]
theorem step1176 (p : Nat → Bool) (h : Constraints p) : clause p c1176 = true :=
  Snake9.LocalRup.prove_clause [c1064, c1104, c699, c720, c717, c1110, c718, c671, c702, c669, c1152, c11, c493, c450, c467, c452, c454] c1176 (by decide) p (sat_cons (step1064 p h) (sat_cons (step1104 p h) (sat_cons (step699 p h) (sat_cons (step720 p h) (sat_cons (step717 p h) (sat_cons (step1110 p h) (sat_cons (step718 p h) (sat_cons (step671 p h) (sat_cons (step702 p h) (sat_cons (step669 p h) (sat_cons (step1152 p h) (sat_cons (step11 p h) (sat_cons (step493 p h) (sat_cons (step450 p h) (sat_cons (step467 p h) (sat_cons (step452 p h) (sat_cons (step454 p h) (sat_nil p))))))))))))))))))
def c1177 : List Lit := [(1394, true)]
theorem step1177 (p : Nat → Bool) (h : Constraints p) : clause p c1177 = true :=
  Snake9.LocalRup.prove_clause [c1071, c709, c711, c1101, c706, c707, c703, c704, c474, c54, c67, c475, c56, c477, c480, c488, c485] c1177 (by decide) p (sat_cons (step1071 p h) (sat_cons (step709 p h) (sat_cons (step711 p h) (sat_cons (step1101 p h) (sat_cons (step706 p h) (sat_cons (step707 p h) (sat_cons (step703 p h) (sat_cons (step704 p h) (sat_cons (step474 p h) (sat_cons (step54 p h) (sat_cons (step67 p h) (sat_cons (step475 p h) (sat_cons (step56 p h) (sat_cons (step477 p h) (sat_cons (step480 p h) (sat_cons (step488 p h) (sat_cons (step485 p h) (sat_nil p))))))))))))))))))
def c1178 : List Lit := [(1398, true)]
theorem step1178 (p : Nat → Bool) (h : Constraints p) : clause p c1178 = true :=
  Snake9.LocalRup.prove_clause [c1177, c714] c1178 (by decide) p (sat_cons (step1177 p h) (sat_cons (step714 p h) (sat_nil p)))
def c1179 : List Lit := [(1406, true)]
theorem step1179 (p : Nat → Bool) (h : Constraints p) : clause p c1179 = true :=
  Snake9.LocalRup.prove_clause [c1177, c1142] c1179 (by decide) p (sat_cons (step1177 p h) (sat_cons (step1142 p h) (sat_nil p)))
def c1180 : List Lit := [(1407, true), (1378, false), (53, true)]
theorem step1180 (p : Nat → Bool) (h : Constraints p) : clause p c1180 = true :=
  Snake9.LocalRup.prove_clause [c1178, c1177, c1064, c724, c722, c1110, c686, c715, c716, c671, c681, c713, c699, c701, c669, c696, c697, c11, c36, c450, c452, c454, c467, c493, c486, c487, c484, c477, c483, c476, c482, c473, c1103, c50, c679, c29, c704, c705, c712, c706, c707, c1150, c67, c63] c1180 (by decide) p (sat_cons (step1178 p h) (sat_cons (step1177 p h) (sat_cons (step1064 p h) (sat_cons (step724 p h) (sat_cons (step722 p h) (sat_cons (step1110 p h) (sat_cons (step686 p h) (sat_cons (step715 p h) (sat_cons (step716 p h) (sat_cons (step671 p h) (sat_cons (step681 p h) (sat_cons (step713 p h) (sat_cons (step699 p h) (sat_cons (step701 p h) (sat_cons (step669 p h) (sat_cons (step696 p h) (sat_cons (step697 p h) (sat_cons (step11 p h) (sat_cons (step36 p h) (sat_cons (step450 p h) (sat_cons (step452 p h) (sat_cons (step454 p h) (sat_cons (step467 p h) (sat_cons (step493 p h) (sat_cons (step486 p h) (sat_cons (step487 p h) (sat_cons (step484 p h) (sat_cons (step477 p h) (sat_cons (step483 p h) (sat_cons (step476 p h) (sat_cons (step482 p h) (sat_cons (step473 p h) (sat_cons (step1103 p h) (sat_cons (step50 p h) (sat_cons (step679 p h) (sat_cons (step29 p h) (sat_cons (step704 p h) (sat_cons (step705 p h) (sat_cons (step712 p h) (sat_cons (step706 p h) (sat_cons (step707 p h) (sat_cons (step1150 p h) (sat_cons (step67 p h) (sat_cons (step63 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))
def c1181 : List Lit := [(1607, true), (53, true)]
theorem step1181 (p : Nat → Bool) (h : Constraints p) : clause p c1181 = true :=
  Snake9.LocalRup.prove_clause [c1100, c1148, c1145, c1146, c1059, c1004, c1008, c996, c964, c948, c950, c945, c946, c1133, c351, c898, c356, c1129, c606, c927, c607, c874, c613, c866, c868, c627, c863, c864, c861, c655, c273, c661, c287, c603, c562, c571, c563, c567] c1181 (by decide) p (sat_cons (step1100 p h) (sat_cons (step1148 p h) (sat_cons (step1145 p h) (sat_cons (step1146 p h) (sat_cons (step1059 p h) (sat_cons (step1004 p h) (sat_cons (step1008 p h) (sat_cons (step996 p h) (sat_cons (step964 p h) (sat_cons (step948 p h) (sat_cons (step950 p h) (sat_cons (step945 p h) (sat_cons (step946 p h) (sat_cons (step1133 p h) (sat_cons (step351 p h) (sat_cons (step898 p h) (sat_cons (step356 p h) (sat_cons (step1129 p h) (sat_cons (step606 p h) (sat_cons (step927 p h) (sat_cons (step607 p h) (sat_cons (step874 p h) (sat_cons (step613 p h) (sat_cons (step866 p h) (sat_cons (step868 p h) (sat_cons (step627 p h) (sat_cons (step863 p h) (sat_cons (step864 p h) (sat_cons (step861 p h) (sat_cons (step655 p h) (sat_cons (step273 p h) (sat_cons (step661 p h) (sat_cons (step287 p h) (sat_cons (step603 p h) (sat_cons (step562 p h) (sat_cons (step571 p h) (sat_cons (step563 p h) (sat_cons (step567 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))
def c1182 : List Lit := [(72, true), (1518, false), (1527, true), (389, true)]
theorem step1182 (p : Nat → Bool) (h : Constraints p) : clause p c1182 = true :=
  Snake9.LocalRup.prove_clause [c429, c598, c584, c583, c577, c596, c594, c588, c320, c892, c318, c916, c895, c908, c905, c897, c920, c893, c887, c888, c302, c305] c1182 (by decide) p (sat_cons (step429 p h) (sat_cons (step598 p h) (sat_cons (step584 p h) (sat_cons (step583 p h) (sat_cons (step577 p h) (sat_cons (step596 p h) (sat_cons (step594 p h) (sat_cons (step588 p h) (sat_cons (step320 p h) (sat_cons (step892 p h) (sat_cons (step318 p h) (sat_cons (step916 p h) (sat_cons (step895 p h) (sat_cons (step908 p h) (sat_cons (step905 p h) (sat_cons (step897 p h) (sat_cons (step920 p h) (sat_cons (step893 p h) (sat_cons (step887 p h) (sat_cons (step888 p h) (sat_cons (step302 p h) (sat_cons (step305 p h) (sat_nil p)))))))))))))))))))))))
def c1183 : List Lit := [(1433, true), (9, false), (41, false)]
theorem step1183 (p : Nat → Bool) (h : Constraints p) : clause p c1183 = true :=
  Snake9.LocalRup.prove_clause [c1155, c1157, c742] c1183 (by decide) p (sat_cons (step1155 p h) (sat_cons (step1157 p h) (sat_cons (step742 p h) (sat_nil p))))
end B112E171
