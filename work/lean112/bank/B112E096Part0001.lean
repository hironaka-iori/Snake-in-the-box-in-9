import B112E096Part0000
namespace B112E096
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1100 : List Lit := [(113, true), (107, false), (1643, true)]
theorem step1100 (p : Nat → Bool) (h : Constraints p) : clause p c1100 = true :=
  Snake9.LocalRup.prove_clause [c494, c904, c894, c895, c902, c896, c897, c446, c437, c439] c1100 (by decide) p (sat_cons (step494 p h) (sat_cons (step904 p h) (sat_cons (step894 p h) (sat_cons (step895 p h) (sat_cons (step902 p h) (sat_cons (step896 p h) (sat_cons (step897 p h) (sat_cons (step446 p h) (sat_cons (step437 p h) (sat_cons (step439 p h) (sat_nil p)))))))))))
def c1101 : List Lit := [(43, false), (35, false), (37, false), (113, false)]
theorem step1101 (p : Nat → Bool) (h : Constraints p) : clause p c1101 = true :=
  Snake9.LocalRup.prove_clause [c467, c109, c79, c103] c1101 (by decide) p (sat_cons (step467 p h) (sat_cons (step109 p h) (sat_cons (step79 p h) (sat_cons (step103 p h) (sat_nil p)))))
def c1102 : List Lit := [(44, true), (1497, true), (103, true), (34, false), (39, false)]
theorem step1102 (p : Nat → Bool) (h : Constraints p) : clause p c1102 = true :=
  Snake9.LocalRup.prove_clause [c465, c697, c687, c688, c695, c690, c88, c122, c90] c1102 (by decide) p (sat_cons (step465 p h) (sat_cons (step697 p h) (sat_cons (step687 p h) (sat_cons (step688 p h) (sat_cons (step695 p h) (sat_cons (step690 p h) (sat_cons (step88 p h) (sat_cons (step122 p h) (sat_cons (step90 p h) (sat_nil p))))))))))
def c1103 : List Lit := [(44, false), (117, false), (45, true), (113, false)]
theorem step1103 (p : Nat → Bool) (h : Constraints p) : clause p c1103 = true :=
  Snake9.LocalRup.prove_clause [c468, c413, c106] c1103 (by decide) p (sat_cons (step468 p h) (sat_cons (step413 p h) (sat_cons (step106 p h) (sat_nil p))))
def c1104 : List Lit := [(1625, true), (1617, false), (96, true)]
theorem step1104 (p : Nat → Bool) (h : Constraints p) : clause p c1104 = true :=
  Snake9.LocalRup.prove_clause [c486, c849, c858, c865, c869, c861, c844, c846, c851, c841, c842, c253, c229, c247] c1104 (by decide) p (sat_cons (step486 p h) (sat_cons (step849 p h) (sat_cons (step858 p h) (sat_cons (step865 p h) (sat_cons (step869 p h) (sat_cons (step861 p h) (sat_cons (step844 p h) (sat_cons (step846 p h) (sat_cons (step851 p h) (sat_cons (step841 p h) (sat_cons (step842 p h) (sat_cons (step253 p h) (sat_cons (step229 p h) (sat_cons (step247 p h) (sat_nil p)))))))))))))))
def c1105 : List Lit := [(85, true), (1589, true), (1680, true), (1566, false), (86, true), (101, true), (113, false), (1620, false), (1648, false)]
theorem step1105 (p : Nat → Bool) (h : Constraints p) : clause p c1105 = true :=
  Snake9.LocalRup.prove_clause [c482, c809, c1087, c798, c833, c800, c803, c975, c813, c794, c950, c788, c874, c785, c786, c190, c194, c242, c243, c847, c842] c1105 (by decide) p (sat_cons (step482 p h) (sat_cons (step809 p h) (sat_cons (step1087 p h) (sat_cons (step798 p h) (sat_cons (step833 p h) (sat_cons (step800 p h) (sat_cons (step803 p h) (sat_cons (step975 p h) (sat_cons (step813 p h) (sat_cons (step794 p h) (sat_cons (step950 p h) (sat_cons (step788 p h) (sat_cons (step874 p h) (sat_cons (step785 p h) (sat_cons (step786 p h) (sat_cons (step190 p h) (sat_cons (step194 p h) (sat_cons (step242 p h) (sat_cons (step243 p h) (sat_cons (step847 p h) (sat_cons (step842 p h) (sat_nil p))))))))))))))))))))))
def c1106 : List Lit := [(80, true), (78, false), (1585, true), (86, true), (105, true)]
theorem step1106 (p : Nat → Bool) (h : Constraints p) : clause p c1106 = true :=
  Snake9.LocalRup.prove_clause [c484, c796, c805, c794, c795, c803, c798, c226, c215] c1106 (by decide) p (sat_cons (step484 p h) (sat_cons (step796 p h) (sat_cons (step805 p h) (sat_cons (step794 p h) (sat_cons (step795 p h) (sat_cons (step803 p h) (sat_cons (step798 p h) (sat_cons (step226 p h) (sat_cons (step215 p h) (sat_nil p))))))))))
def c1107 : List Lit := [(1584, true), (86, true), (105, true), (102, false)]
theorem step1107 (p : Nat → Bool) (h : Constraints p) : clause p c1107 = true :=
  Snake9.LocalRup.prove_clause [c484, c796, c800, c802, c798, c793, c227, c208] c1107 (by decide) p (sat_cons (step484 p h) (sat_cons (step796 p h) (sat_cons (step800 p h) (sat_cons (step802 p h) (sat_cons (step798 p h) (sat_cons (step793 p h) (sat_cons (step227 p h) (sat_cons (step208 p h) (sat_nil p)))))))))
def c1108 : List Lit := [(85, false), (81, false), (105, true), (102, false)]
theorem step1108 (p : Nat → Bool) (h : Constraints p) : clause p c1108 = true :=
  Snake9.LocalRup.prove_clause [c484, c227, c208] c1108 (by decide) p (sat_cons (step484 p h) (sat_cons (step227 p h) (sat_cons (step208 p h) (sat_nil p))))
def c1109 : List Lit := [(1461, true), (1436, false)]
theorem step1109 (p : Nat → Bool) (h : Constraints p) : clause p c1109 = true :=
  Snake9.LocalRup.prove_clause [c1065, c454, c619, c638, c1057, c646, c640, c1053, c622, c600, c614, c597, c598, c28, c26] c1109 (by decide) p (sat_cons (step1065 p h) (sat_cons (step454 p h) (sat_cons (step619 p h) (sat_cons (step638 p h) (sat_cons (step1057 p h) (sat_cons (step646 p h) (sat_cons (step640 p h) (sat_cons (step1053 p h) (sat_cons (step622 p h) (sat_cons (step600 p h) (sat_cons (step614 p h) (sat_cons (step597 p h) (sat_cons (step598 p h) (sat_cons (step28 p h) (sat_cons (step26 p h) (sat_nil p))))))))))))))))
def c1110 : List Lit := [(15, false), (1420, true)]
theorem step1110 (p : Nat → Bool) (h : Constraints p) : clause p c1110 = true :=
  Snake9.LocalRup.prove_clause [c454, c598, c597, c28, c26] c1110 (by decide) p (sat_cons (step454 p h) (sat_cons (step598 p h) (sat_cons (step597 p h) (sat_cons (step28 p h) (sat_cons (step26 p h) (sat_nil p))))))
def c1111 : List Lit := [(1481, true), (37, false), (113, false)]
theorem step1111 (p : Nat → Bool) (h : Constraints p) : clause p c1111 = true :=
  Snake9.LocalRup.prove_clause [c669, c1082, c666, c109] c1111 (by decide) p (sat_cons (step669 p h) (sat_cons (step1082 p h) (sat_cons (step666 p h) (sat_cons (step109 p h) (sat_nil p)))))
def c1112 : List Lit := [(38, true), (34, false), (35, true), (151, true)]
theorem step1112 (p : Nat → Bool) (h : Constraints p) : clause p c1112 = true :=
  Snake9.LocalRup.prove_clause [c462, c73, c75, c999, c72] c1112 (by decide) p (sat_cons (step462 p h) (sat_cons (step73 p h) (sat_cons (step75 p h) (sat_cons (step999 p h) (sat_cons (step72 p h) (sat_nil p))))))
def c1113 : List Lit := [(44, false), (1648, true), (113, false), (45, true)]
theorem step1113 (p : Nat → Bool) (h : Constraints p) : clause p c1113 = true :=
  Snake9.LocalRup.prove_clause [c468, c1103, c106, c896, c411, c409, c899, c884, c916, c886] c1113 (by decide) p (sat_cons (step468 p h) (sat_cons (step1103 p h) (sat_cons (step106 p h) (sat_cons (step896 p h) (sat_cons (step411 p h) (sat_cons (step409 p h) (sat_cons (step899 p h) (sat_cons (step884 p h) (sat_cons (step916 p h) (sat_cons (step886 p h) (sat_nil p)))))))))))
def c1114 : List Lit := [(1612, true), (113, false)]
theorem step1114 (p : Nat → Bool) (h : Constraints p) : clause p c1114 = true :=
  Snake9.LocalRup.prove_clause [c485, c844, c846, c841, c842, c229, c244, c239] c1114 (by decide) p (sat_cons (step485 p h) (sat_cons (step844 p h) (sat_cons (step846 p h) (sat_cons (step841 p h) (sat_cons (step842 p h) (sat_cons (step229 p h) (sat_cons (step244 p h) (sat_cons (step239 p h) (sat_nil p)))))))))
def c1115 : List Lit := [(80, true), (1588, true), (76, true), (100, true)]
theorem step1115 (p : Nat → Bool) (h : Constraints p) : clause p c1115 = true :=
  Snake9.LocalRup.prove_clause [c481, c808, c804, c1087, c794, c795, c801, c802, c812, c796, c788, c221, c785, c786, c176, c191] c1115 (by decide) p (sat_cons (step481 p h) (sat_cons (step808 p h) (sat_cons (step804 p h) (sat_cons (step1087 p h) (sat_cons (step794 p h) (sat_cons (step795 p h) (sat_cons (step801 p h) (sat_cons (step802 p h) (sat_cons (step812 p h) (sat_cons (step796 p h) (sat_cons (step788 p h) (sat_cons (step221 p h) (sat_cons (step785 p h) (sat_cons (step786 p h) (sat_cons (step176 p h) (sat_cons (step191 p h) (sat_nil p)))))))))))))))))
def c1116 : List Lit := [(1451, true), (1435, false), (20, false), (80, false), (88, false)]
theorem step1116 (p : Nat → Bool) (h : Constraints p) : clause p c1116 = true :=
  Snake9.LocalRup.prove_clause [c1065, c459, c618, c638, c621, c636, c613, c631, c43, c625, c61, c63] c1116 (by decide) p (sat_cons (step1065 p h) (sat_cons (step459 p h) (sat_cons (step618 p h) (sat_cons (step638 p h) (sat_cons (step621 p h) (sat_cons (step636 p h) (sat_cons (step613 p h) (sat_cons (step631 p h) (sat_cons (step43 p h) (sat_cons (step625 p h) (sat_cons (step61 p h) (sat_cons (step63 p h) (sat_nil p)))))))))))))
def c1117 : List Lit := [(1509, true), (70, false)]
theorem step1117 (p : Nat → Bool) (h : Constraints p) : clause p c1117 = true :=
  Snake9.LocalRup.prove_clause [c1058, c472, c708, c709, c1089, c692, c126, c127, c689] c1117 (by decide) p (sat_cons (step1058 p h) (sat_cons (step472 p h) (sat_cons (step708 p h) (sat_cons (step709 p h) (sat_cons (step1089 p h) (sat_cons (step692 p h) (sat_cons (step126 p h) (sat_cons (step127 p h) (sat_cons (step689 p h) (sat_nil p))))))))))
def c1118 : List Lit := [(54, false), (51, false), (70, false)]
theorem step1118 (p : Nat → Bool) (h : Constraints p) : clause p c1118 = true :=
  Snake9.LocalRup.prove_clause [c472, c126, c127] c1118 (by decide) p (sat_cons (step472 p h) (sat_cons (step126 p h) (sat_cons (step127 p h) (sat_nil p))))
def c1119 : List Lit := [(79, false), (1574, true), (80, false), (51, false)]
theorem step1119 (p : Nat → Bool) (h : Constraints p) : clause p c1119 = true :=
  Snake9.LocalRup.prove_clause [c185, c187, c787] c1119 (by decide) p (sat_cons (step185 p h) (sat_cons (step187 p h) (sat_cons (step787 p h) (sat_nil p))))
def c1120 : List Lit := [(39, false), (103, true), (34, false), (1496, true)]
theorem step1120 (p : Nat → Bool) (h : Constraints p) : clause p c1120 = true :=
  Snake9.LocalRup.prove_clause [c465, c694, c686, c692, c690, c88, c122, c90] c1120 (by decide) p (sat_cons (step465 p h) (sat_cons (step694 p h) (sat_cons (step686 p h) (sat_cons (step692 p h) (sat_cons (step690 p h) (sat_cons (step88 p h) (sat_cons (step122 p h) (sat_cons (step90 p h) (sat_nil p)))))))))
def c1121 : List Lit := [(39, true), (1482, true), (44, false)]
theorem step1121 (p : Nat → Bool) (h : Constraints p) : clause p c1121 = true :=
  Snake9.LocalRup.prove_clause [c674, c663, c665, c672, c1072] c1121 (by decide) p (sat_cons (step674 p h) (sat_cons (step663 p h) (sat_cons (step665 p h) (sat_cons (step672 p h) (sat_cons (step1072 p h) (sat_nil p))))))
def c1122 : List Lit := [(37, false), (43, false), (35, false), (44, false)]
theorem step1122 (p : Nat → Bool) (h : Constraints p) : clause p c1122 = true :=
  Snake9.LocalRup.prove_clause [c467, c79, c108, c103] c1122 (by decide) p (sat_cons (step467 p h) (sat_cons (step79 p h) (sat_cons (step108 p h) (sat_cons (step103 p h) (sat_nil p)))))
def c1123 : List Lit := [(32, false), (150, true), (1436, true), (22, false), (39, false), (79, true), (20, true)]
theorem step1123 (p : Nat → Bool) (h : Constraints p) : clause p c1123 = true :=
  Snake9.LocalRup.prove_clause [c456, c69, c54, c58, c617, c38] c1123 (by decide) p (sat_cons (step456 p h) (sat_cons (step69 p h) (sat_cons (step54 p h) (sat_cons (step58 p h) (sat_cons (step617 p h) (sat_cons (step38 p h) (sat_nil p)))))))
def c1124 : List Lit := [(24, false), (1438, true), (22, false), (39, false)]
theorem step1124 (p : Nat → Bool) (h : Constraints p) : clause p c1124 = true :=
  Snake9.LocalRup.prove_clause [c53, c54, c613, c615, c621] c1124 (by decide) p (sat_cons (step53 p h) (sat_cons (step54 p h) (sat_cons (step613 p h) (sat_cons (step615 p h) (sat_cons (step621 p h) (sat_nil p))))))
def c1125 : List Lit := [(1437, true), (22, false), (39, false)]
theorem step1125 (p : Nat → Bool) (h : Constraints p) : clause p c1125 = true :=
  Snake9.LocalRup.prove_clause [c618, c620, c615, c613, c52] c1125 (by decide) p (sat_cons (step618 p h) (sat_cons (step620 p h) (sat_cons (step615 p h) (sat_cons (step613 p h) (sat_cons (step52 p h) (sat_nil p))))))
def c1126 : List Lit := [(21, false), (1462, true), (1422, false), (1443, false), (22, false), (39, false), (1, false), (51, false)]
theorem step1126 (p : Nat → Bool) (h : Constraints p) : clause p c1126 = true :=
  Snake9.LocalRup.prove_clause [c1053, c647, c1125, c52, c54, c613, c624, c630, c639, c636, c621, c650, c616, c608, c1, c591, c1049] c1126 (by decide) p (sat_cons (step1053 p h) (sat_cons (step647 p h) (sat_cons (step1125 p h) (sat_cons (step52 p h) (sat_cons (step54 p h) (sat_cons (step613 p h) (sat_cons (step624 p h) (sat_cons (step630 p h) (sat_cons (step639 p h) (sat_cons (step636 p h) (sat_cons (step621 p h) (sat_cons (step650 p h) (sat_cons (step616 p h) (sat_cons (step608 p h) (sat_cons (step1 p h) (sat_cons (step591 p h) (sat_cons (step1049 p h) (sat_nil p))))))))))))))))))
def c1127 : List Lit := [(1433, false), (21, true), (1462, true), (1422, false), (1, false), (51, false)]
theorem step1127 (p : Nat → Bool) (h : Constraints p) : clause p c1127 = true :=
  Snake9.LocalRup.prove_clause [c1065, c615, c1053, c647, c640, c622, c621, c617, c638, c1, c650, c1049, c608, c591] c1127 (by decide) p (sat_cons (step1065 p h) (sat_cons (step615 p h) (sat_cons (step1053 p h) (sat_cons (step647 p h) (sat_cons (step640 p h) (sat_cons (step622 p h) (sat_cons (step621 p h) (sat_cons (step617 p h) (sat_cons (step638 p h) (sat_cons (step1 p h) (sat_cons (step650 p h) (sat_cons (step1049 p h) (sat_cons (step608 p h) (sat_cons (step591 p h) (sat_nil p)))))))))))))))
def c1128 : List Lit := [(1462, true), (1422, false), (1443, false), (22, false), (39, false), (1, false), (51, false)]
theorem step1128 (p : Nat → Bool) (h : Constraints p) : clause p c1128 = true :=
  Snake9.LocalRup.prove_clause [c1125, c1053, c647, c1126, c1127, c613, c53, c624, c630, c639, c636, c619, c650, c617, c608, c1, c591, c1049] c1128 (by decide) p (sat_cons (step1125 p h) (sat_cons (step1053 p h) (sat_cons (step647 p h) (sat_cons (step1126 p h) (sat_cons (step1127 p h) (sat_cons (step613 p h) (sat_cons (step53 p h) (sat_cons (step624 p h) (sat_cons (step630 p h) (sat_cons (step639 p h) (sat_cons (step636 p h) (sat_cons (step619 p h) (sat_cons (step650 p h) (sat_cons (step617 p h) (sat_cons (step608 p h) (sat_cons (step1 p h) (sat_cons (step591 p h) (sat_cons (step1049 p h) (sat_nil p)))))))))))))))))))
def c1129 : List Lit := [(41, false), (1631, true), (103, false), (36, true), (101, false)]
theorem step1129 (p : Nat → Bool) (h : Constraints p) : clause p c1129 = true :=
  Snake9.LocalRup.prove_clause [c466, c98, c99, c379, c1003, c881] c1129 (by decide) p (sat_cons (step466 p h) (sat_cons (step98 p h) (sat_cons (step99 p h) (sat_cons (step379 p h) (sat_cons (step1003 p h) (sat_cons (step881 p h) (sat_nil p)))))))
def c1130 : List Lit := [(1612, true), (91, false), (80, false)]
theorem step1130 (p : Nat → Bool) (h : Constraints p) : clause p c1130 = true :=
  Snake9.LocalRup.prove_clause [c844, c846, c842, c241] c1130 (by decide) p (sat_cons (step844 p h) (sat_cons (step846 p h) (sat_cons (step842 p h) (sat_cons (step241 p h) (sat_nil p)))))
def c1131 : List Lit := [(1626, true), (86, false), (96, true), (1620, false), (90, true), (88, false), (1617, false), (1612, false)]
theorem step1131 (p : Nat → Bool) (h : Constraints p) : clause p c1131 = true :=
  Snake9.LocalRup.prove_clause [c487, c874, c870, c845, c861, c843, c851, c253, c250, c252, c1019] c1131 (by decide) p (sat_cons (step487 p h) (sat_cons (step874 p h) (sat_cons (step870 p h) (sat_cons (step845 p h) (sat_cons (step861 p h) (sat_cons (step843 p h) (sat_cons (step851 p h) (sat_cons (step253 p h) (sat_cons (step250 p h) (sat_cons (step252 p h) (sat_cons (step1019 p h) (sat_nil p))))))))))))
def c1132 : List Lit := [(94, true), (93, false), (86, false)]
theorem step1132 (p : Nat → Bool) (h : Constraints p) : clause p c1132 = true :=
  Snake9.LocalRup.prove_clause [c487, c250, c252, c1019] c1132 (by decide) p (sat_cons (step487 p h) (sat_cons (step250 p h) (sat_cons (step252 p h) (sat_cons (step1019 p h) (sat_nil p)))))
def c1133 : List Lit := [(85, false), (86, false), (104, false), (105, true)]
theorem step1133 (p : Nat → Bool) (h : Constraints p) : clause p c1133 = true :=
  Snake9.LocalRup.prove_clause [c484, c224, c226] c1133 (by decide) p (sat_cons (step484 p h) (sat_cons (step224 p h) (sat_cons (step226 p h) (sat_nil p))))
def c1134 : List Lit := [(1486, true), (1477, false), (105, true)]
theorem step1134 (p : Nat → Bool) (h : Constraints p) : clause p c1134 = true :=
  Snake9.LocalRup.prove_clause [c466, c671, c677, c680, c672, c659, c666, c667, c656, c80, c98] c1134 (by decide) p (sat_cons (step466 p h) (sat_cons (step671 p h) (sat_cons (step677 p h) (sat_cons (step680 p h) (sat_cons (step672 p h) (sat_cons (step659 p h) (sat_cons (step666 p h) (sat_cons (step667 p h) (sat_cons (step656 p h) (sat_cons (step80 p h) (sat_cons (step98 p h) (sat_nil p))))))))))))
def c1135 : List Lit := [(1588, true), (105, true)]
theorem step1135 (p : Nat → Bool) (h : Constraints p) : clause p c1135 = true :=
  Snake9.LocalRup.prove_clause [c484, c808, c1087, c227, c226, c1017, c793, c801, c802, c812, c796, c788, c218, c785] c1135 (by decide) p (sat_cons (step484 p h) (sat_cons (step808 p h) (sat_cons (step1087 p h) (sat_cons (step227 p h) (sat_cons (step226 p h) (sat_cons (step1017 p h) (sat_cons (step793 p h) (sat_cons (step801 p h) (sat_cons (step802 p h) (sat_cons (step812 p h) (sat_cons (step796 p h) (sat_cons (step788 p h) (sat_cons (step218 p h) (sat_cons (step785 p h) (sat_nil p)))))))))))))))
def c1136 : List Lit := [(1565, true), (1556, false), (62, false)]
theorem step1136 (p : Nat → Bool) (h : Constraints p) : clause p c1136 = true :=
  Snake9.LocalRup.prove_clause [c478, c765, c772, c776, c766, c752, c760, c761, c750, c159, c154, c158] c1136 (by decide) p (sat_cons (step478 p h) (sat_cons (step765 p h) (sat_cons (step772 p h) (sat_cons (step776 p h) (sat_cons (step766 p h) (sat_cons (step752 p h) (sat_cons (step760 p h) (sat_cons (step761 p h) (sat_cons (step750 p h) (sat_cons (step159 p h) (sat_cons (step154 p h) (sat_cons (step158 p h) (sat_nil p)))))))))))))
def c1137 : List Lit := [(31, true), (1518, true)]
theorem step1137 (p : Nat → Bool) (h : Constraints p) : clause p c1137 = true :=
  Snake9.LocalRup.prove_clause [c1059, c1058, c722, c661, c1070, c679, c687, c719, c694, c709] c1137 (by decide) p (sat_cons (step1059 p h) (sat_cons (step1058 p h) (sat_cons (step722 p h) (sat_cons (step661 p h) (sat_cons (step1070 p h) (sat_cons (step679 p h) (sat_cons (step687 p h) (sat_cons (step719 p h) (sat_cons (step694 p h) (sat_cons (step709 p h) (sat_nil p)))))))))))
def c1138 : List Lit := [(1496, true), (1536, true), (34, false)]
theorem step1138 (p : Nat → Bool) (h : Constraints p) : clause p c1138 = true :=
  Snake9.LocalRup.prove_clause [c1067, c1059, c465, c469, c1065, c731, c722, c677, c692, c694, c690, c686, c687, c1071, c1121, c676, c88, c122, c718, c93, c115, c735, c1125, c112, c635, c597, c645, c600, c1053] c1138 (by decide) p (sat_cons (step1067 p h) (sat_cons (step1059 p h) (sat_cons (step465 p h) (sat_cons (step469 p h) (sat_cons (step1065 p h) (sat_cons (step731 p h) (sat_cons (step722 p h) (sat_cons (step677 p h) (sat_cons (step692 p h) (sat_cons (step694 p h) (sat_cons (step690 p h) (sat_cons (step686 p h) (sat_cons (step687 p h) (sat_cons (step1071 p h) (sat_cons (step1121 p h) (sat_cons (step676 p h) (sat_cons (step88 p h) (sat_cons (step122 p h) (sat_cons (step718 p h) (sat_cons (step93 p h) (sat_cons (step115 p h) (sat_cons (step735 p h) (sat_cons (step1125 p h) (sat_cons (step112 p h) (sat_cons (step635 p h) (sat_cons (step597 p h) (sat_cons (step645 p h) (sat_cons (step600 p h) (sat_cons (step1053 p h) (sat_nil p))))))))))))))))))))))))))))))
def c1139 : List Lit := [(1536, true), (34, false)]
theorem step1139 (p : Nat → Bool) (h : Constraints p) : clause p c1139 = true :=
  Snake9.LocalRup.prove_clause [c1067, c1058, c1065, c465, c469, c731, c716, c711, c697, c1138, c709, c715, c719, c735, c676, c1056, c671, c1071, c638, c663, c687, c688, c695, c690, c88, c122, c93, c115, c1125, c1124, c113, c636, c624, c626, c630] c1139 (by decide) p (sat_cons (step1067 p h) (sat_cons (step1058 p h) (sat_cons (step1065 p h) (sat_cons (step465 p h) (sat_cons (step469 p h) (sat_cons (step731 p h) (sat_cons (step716 p h) (sat_cons (step711 p h) (sat_cons (step697 p h) (sat_cons (step1138 p h) (sat_cons (step709 p h) (sat_cons (step715 p h) (sat_cons (step719 p h) (sat_cons (step735 p h) (sat_cons (step676 p h) (sat_cons (step1056 p h) (sat_cons (step671 p h) (sat_cons (step1071 p h) (sat_cons (step638 p h) (sat_cons (step663 p h) (sat_cons (step687 p h) (sat_cons (step688 p h) (sat_cons (step695 p h) (sat_cons (step690 p h) (sat_cons (step88 p h) (sat_cons (step122 p h) (sat_cons (step93 p h) (sat_cons (step115 p h) (sat_cons (step1125 p h) (sat_cons (step1124 p h) (sat_cons (step113 p h) (sat_cons (step636 p h) (sat_cons (step624 p h) (sat_cons (step626 p h) (sat_cons (step630 p h) (sat_nil p))))))))))))))))))))))))))))))))))))
def c1140 : List Lit := [(1583, true), (77, false), (98, true)]
theorem step1140 (p : Nat → Bool) (h : Constraints p) : clause p c1140 = true :=
  Snake9.LocalRup.prove_clause [c480, c799, c801, c796, c793, c794, c192, c211, c169] c1140 (by decide) p (sat_cons (step480 p h) (sat_cons (step799 p h) (sat_cons (step801 p h) (sat_cons (step796 p h) (sat_cons (step793 p h) (sat_cons (step794 p h) (sat_cons (step192 p h) (sat_cons (step211 p h) (sat_cons (step169 p h) (sat_nil p))))))))))
def c1141 : List Lit := [(1617, false), (86, false), (1626, true), (96, true), (90, true), (1612, false), (88, false)]
theorem step1141 (p : Nat → Bool) (h : Constraints p) : clause p c1141 = true :=
  Snake9.LocalRup.prove_clause [c849, c858, c1131] c1141 (by decide) p (sat_cons (step849 p h) (sat_cons (step858 p h) (sat_cons (step1131 p h) (sat_nil p))))
def c1142 : List Lit := [(1536, true)]
theorem step1142 (p : Nat → Bool) (h : Constraints p) : clause p c1142 = true :=
  Snake9.LocalRup.prove_clause [c1067, c1059, c1058, c731, c1139, c722, c657, c659, c679, c680, c719, c1071, c709, c687, c694] c1142 (by decide) p (sat_cons (step1067 p h) (sat_cons (step1059 p h) (sat_cons (step1058 p h) (sat_cons (step731 p h) (sat_cons (step1139 p h) (sat_cons (step722 p h) (sat_cons (step657 p h) (sat_cons (step659 p h) (sat_cons (step679 p h) (sat_cons (step680 p h) (sat_cons (step719 p h) (sat_cons (step1071 p h) (sat_cons (step709 p h) (sat_cons (step687 p h) (sat_cons (step694 p h) (sat_nil p))))))))))))))))
def c1143 : List Lit := [(1682, false)]
theorem step1143 (p : Nat → Bool) (h : Constraints p) : clause p c1143 = true :=
  Snake9.LocalRup.prove_clause [c1142, c993, c987] c1143 (by decide) p (sat_cons (step1142 p h) (sat_cons (step993 p h) (sat_cons (step987 p h) (sat_nil p))))
def c1144 : List Lit := [(78, true), (1576, true), (63, false), (60, false), (99, false)]
theorem step1144 (p : Nat → Bool) (h : Constraints p) : clause p c1144 = true :=
  Snake9.LocalRup.prove_clause [c473, c789, c785, c791, c787, c784, c276, c147, c135] c1144 (by decide) p (sat_cons (step473 p h) (sat_cons (step789 p h) (sat_cons (step785 p h) (sat_cons (step791 p h) (sat_cons (step787 p h) (sat_cons (step784 p h) (sat_cons (step276 p h) (sat_cons (step147 p h) (sat_cons (step135 p h) (sat_nil p))))))))))
def c1145 : List Lit := [(1566, true), (80, false), (1557, false), (99, false)]
theorem step1145 (p : Nat → Bool) (h : Constraints p) : clause p c1145 = true :=
  Snake9.LocalRup.prove_clause [c475, c768, c773, c777, c769, c752, c760, c761, c749, c315, c159, c140] c1145 (by decide) p (sat_cons (step475 p h) (sat_cons (step768 p h) (sat_cons (step773 p h) (sat_cons (step777 p h) (sat_cons (step769 p h) (sat_cons (step752 p h) (sat_cons (step760 p h) (sat_cons (step761 p h) (sat_cons (step749 p h) (sat_cons (step315 p h) (sat_cons (step159 p h) (sat_cons (step140 p h) (sat_nil p)))))))))))))
def c1146 : List Lit := [(1558, true), (71, false), (62, false)]
theorem step1146 (p : Nat → Bool) (h : Constraints p) : clause p c1146 = true :=
  Snake9.LocalRup.prove_clause [c760, c761, c159] c1146 (by decide) p (sat_cons (step760 p h) (sat_cons (step761 p h) (sat_cons (step159 p h) (sat_nil p))))
def c1147 : List Lit := [(1647, true), (1638, false)]
theorem step1147 (p : Nat → Bool) (h : Constraints p) : clause p c1147 = true :=
  Snake9.LocalRup.prove_clause [c901, c908, c911, c902, c1076] c1147 (by decide) p (sat_cons (step901 p h) (sat_cons (step908 p h) (sat_cons (step911 p h) (sat_cons (step902 p h) (sat_cons (step1076 p h) (sat_nil p))))))
def c1148 : List Lit := [(1648, true), (1630, false), (113, true)]
theorem step1148 (p : Nat → Bool) (h : Constraints p) : clause p c1148 = true :=
  Snake9.LocalRup.prove_clause [c887, c894, c901, c916, c912, c888, c904, c902, c882, c883, c895, c896, c1079] c1148 (by decide) p (sat_cons (step887 p h) (sat_cons (step894 p h) (sat_cons (step901 p h) (sat_cons (step916 p h) (sat_cons (step912 p h) (sat_cons (step888 p h) (sat_cons (step904 p h) (sat_cons (step902 p h) (sat_cons (step882 p h) (sat_cons (step883 p h) (sat_cons (step895 p h) (sat_cons (step896 p h) (sat_cons (step1079 p h) (sat_nil p))))))))))))))
def c1149 : List Lit := [(93, false), (117, false), (86, false), (81, false)]
theorem step1149 (p : Nat → Bool) (h : Constraints p) : clause p c1149 = true :=
  Snake9.LocalRup.prove_clause [c487, c214, c251, c255] c1149 (by decide) p (sat_cons (step487 p h) (sat_cons (step214 p h) (sat_cons (step251 p h) (sat_cons (step255 p h) (sat_nil p)))))
def c1150 : List Lit := [(1649, true), (1638, false), (117, true), (105, false), (85, false)]
theorem step1150 (p : Nat → Bool) (h : Constraints p) : clause p c1150 = true :=
  Snake9.LocalRup.prove_clause [c1093, c887, c913, c1095, c903, c370, c898] c1150 (by decide) p (sat_cons (step1093 p h) (sat_cons (step887 p h) (sat_cons (step913 p h) (sat_cons (step1095 p h) (sat_cons (step903 p h) (sat_cons (step370 p h) (sat_cons (step898 p h) (sat_nil p))))))))
def c1151 : List Lit := [(60, true), (1566, true), (111, false)]
theorem step1151 (p : Nat → Bool) (h : Constraints p) : clause p c1151 = true :=
  Snake9.LocalRup.prove_clause [c477, c782, c1088, c756, c757, c758, c152, c148, c750, c751, c755, c780, c763, c1146, c1080] c1151 (by decide) p (sat_cons (step477 p h) (sat_cons (step782 p h) (sat_cons (step1088 p h) (sat_cons (step756 p h) (sat_cons (step757 p h) (sat_cons (step758 p h) (sat_cons (step152 p h) (sat_cons (step148 p h) (sat_cons (step750 p h) (sat_cons (step751 p h) (sat_cons (step755 p h) (sat_cons (step780 p h) (sat_cons (step763 p h) (sat_cons (step1146 p h) (sat_cons (step1080 p h) (sat_nil p))))))))))))))))
def c1152 : List Lit := [(1558, true), (62, false), (111, false)]
theorem step1152 (p : Nat → Bool) (h : Constraints p) : clause p c1152 = true :=
  Snake9.LocalRup.prove_clause [c1146, c1080] c1152 (by decide) p (sat_cons (step1146 p h) (sat_cons (step1080 p h) (sat_nil p)))
def c1153 : List Lit := [(1612, true), (87, false), (90, false)]
theorem step1153 (p : Nat → Bool) (h : Constraints p) : clause p c1153 = true :=
  Snake9.LocalRup.prove_clause [c844, c846, c841, c229] c1153 (by decide) p (sat_cons (step844 p h) (sat_cons (step846 p h) (sat_cons (step841 p h) (sat_cons (step229 p h) (sat_nil p)))))
def c1154 : List Lit := [(1579, true), (98, true), (1573, true)]
theorem step1154 (p : Nat → Bool) (h : Constraints p) : clause p c1154 = true :=
  Snake9.LocalRup.prove_clause [c480, c786, c785, c793, c794, c165, c190, c171] c1154 (by decide) p (sat_cons (step480 p h) (sat_cons (step786 p h) (sat_cons (step785 p h) (sat_cons (step793 p h) (sat_cons (step794 p h) (sat_cons (step165 p h) (sat_cons (step190 p h) (sat_cons (step171 p h) (sat_nil p)))))))))
def c1155 : List Lit := [(1565, true), (1556, false)]
theorem step1155 (p : Nat → Bool) (h : Constraints p) : clause p c1155 = true :=
  Snake9.LocalRup.prove_clause [c765, c776, c1136, c752, c749] c1155 (by decide) p (sat_cons (step765 p h) (sat_cons (step776 p h) (sat_cons (step1136 p h) (sat_cons (step752 p h) (sat_cons (step749 p h) (sat_nil p))))))
def c1156 : List Lit := [(60, false), (98, true), (63, false), (65, false)]
theorem step1156 (p : Nat → Bool) (h : Constraints p) : clause p c1156 = true :=
  Snake9.LocalRup.prove_clause [c473, c135, c136, c143] c1156 (by decide) p (sat_cons (step473 p h) (sat_cons (step135 p h) (sat_cons (step136 p h) (sat_cons (step143 p h) (sat_nil p)))))
def c1157 : List Lit := [(1649, true), (109, false), (1643, false), (113, true), (116, true), (1630, false)]
theorem step1157 (p : Nat → Bool) (h : Constraints p) : clause p c1157 = true :=
  Snake9.LocalRup.prove_clause [c894, c897, c887, c913, c917, c903, c905, c888, c898, c895, c882, c1079] c1157 (by decide) p (sat_cons (step894 p h) (sat_cons (step897 p h) (sat_cons (step887 p h) (sat_cons (step913 p h) (sat_cons (step917 p h) (sat_cons (step903 p h) (sat_cons (step905 p h) (sat_cons (step888 p h) (sat_cons (step898 p h) (sat_cons (step895 p h) (sat_cons (step882 p h) (sat_cons (step1079 p h) (sat_nil p)))))))))))))
def c1158 : List Lit := [(1565, true), (62, true), (66, false)]
theorem step1158 (p : Nat → Bool) (h : Constraints p) : clause p c1158 = true :=
  Snake9.LocalRup.prove_clause [c477, c152, c779, c1155, c753, c758, c751, c148] c1158 (by decide) p (sat_cons (step477 p h) (sat_cons (step152 p h) (sat_cons (step779 p h) (sat_cons (step1155 p h) (sat_cons (step753 p h) (sat_cons (step758 p h) (sat_cons (step751 p h) (sat_cons (step148 p h) (sat_nil p)))))))))
def c1159 : List Lit := [(1486, true), (113, false), (41, true)]
theorem step1159 (p : Nat → Bool) (h : Constraints p) : clause p c1159 = true :=
  Snake9.LocalRup.prove_clause [c667, c669, c677, c680, c670, c672, c659, c668, c664, c656, c1101] c1159 (by decide) p (sat_cons (step667 p h) (sat_cons (step669 p h) (sat_cons (step677 p h) (sat_cons (step680 p h) (sat_cons (step670 p h) (sat_cons (step672 p h) (sat_cons (step659 p h) (sat_cons (step668 p h) (sat_cons (step664 p h) (sat_cons (step656 p h) (sat_cons (step1101 p h) (sat_nil p))))))))))))
def c1160 : List Lit := [(80, true), (1589, true), (85, true)]
theorem step1160 (p : Nat → Bool) (h : Constraints p) : clause p c1160 = true :=
  Snake9.LocalRup.prove_clause [c480, c797, c809, c805, c794, c802, c813, c803, c788, c795, c798, c785, c786, c165, c211, c191, c172] c1160 (by decide) p (sat_cons (step480 p h) (sat_cons (step797 p h) (sat_cons (step809 p h) (sat_cons (step805 p h) (sat_cons (step794 p h) (sat_cons (step802 p h) (sat_cons (step813 p h) (sat_cons (step803 p h) (sat_cons (step788 p h) (sat_cons (step795 p h) (sat_cons (step798 p h) (sat_cons (step785 p h) (sat_cons (step786 p h) (sat_cons (step165 p h) (sat_cons (step211 p h) (sat_cons (step191 p h) (sat_cons (step172 p h) (sat_nil p))))))))))))))))))
def c1161 : List Lit := [(1420, true), (1496, true)]
theorem step1161 (p : Nat → Bool) (h : Constraints p) : clause p c1161 = true :=
  Snake9.LocalRup.prove_clause [c453, c694, c686, c692, c690, c597, c598, c112, c24, c25, c995] c1161 (by decide) p (sat_cons (step453 p h) (sat_cons (step694 p h) (sat_cons (step686 p h) (sat_cons (step692 p h) (sat_cons (step690 p h) (sat_cons (step597 p h) (sat_cons (step598 p h) (sat_cons (step112 p h) (sat_cons (step24 p h) (sat_cons (step25 p h) (sat_cons (step995 p h) (sat_nil p))))))))))))
def c1162 : List Lit := [(1416, true), (5, false), (62, false)]
theorem step1162 (p : Nat → Bool) (h : Constraints p) : clause p c1162 = true :=
  Snake9.LocalRup.prove_clause [c591, c1051, c1049, c8] c1162 (by decide) p (sat_cons (step591 p h) (sat_cons (step1051 p h) (sat_cons (step1049 p h) (sat_cons (step8 p h) (sat_nil p)))))
def c1163 : List Lit := [(8, true), (1423, true)]
theorem step1163 (p : Nat → Bool) (h : Constraints p) : clause p c1163 = true :=
  Snake9.LocalRup.prove_clause [c452, c604, c595, c596, c603, c22, c597, c598, c20] c1163 (by decide) p (sat_cons (step452 p h) (sat_cons (step604 p h) (sat_cons (step595 p h) (sat_cons (step596 p h) (sat_cons (step603 p h) (sat_cons (step22 p h) (sat_cons (step597 p h) (sat_cons (step598 p h) (sat_cons (step20 p h) (sat_nil p))))))))))
end B112E096
