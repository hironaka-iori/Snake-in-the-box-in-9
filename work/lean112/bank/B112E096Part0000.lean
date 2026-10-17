import B112E096Inputs
namespace B112E096
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1036 : List Lit := [(57, true)]
theorem step1036 (p : Nat → Bool) (h : Constraints p) : clause p c1036 = true :=
  Snake9.LocalRup.prove_clause [c131, c130] c1036 (by decide) p (sat_cons (step131 p h) (sat_cons (step130 p h) (sat_nil p)))
def c1037 : List Lit := [(6, false)]
theorem step1037 (p : Nat → Bool) (h : Constraints p) : clause p c1037 = true :=
  Snake9.LocalRup.prove_clause [c450, c16] c1037 (by decide) p (sat_cons (step450 p h) (sat_cons (step16 p h) (sat_nil p)))
def c1038 : List Lit := [(466, false)]
theorem step1038 (p : Nat → Bool) (h : Constraints p) : clause p c1038 = true :=
  Snake9.LocalRup.prove_clause [c587, c584] c1038 (by decide) p (sat_cons (step587 p h) (sat_cons (step584 p h) (sat_nil p)))
def c1039 : List Lit := [(350, false)]
theorem step1039 (p : Nat → Bool) (h : Constraints p) : clause p c1039 = true :=
  Snake9.LocalRup.prove_clause [c587, c586] c1039 (by decide) p (sat_cons (step587 p h) (sat_cons (step586 p h) (sat_nil p)))
def c1040 : List Lit := [(464, false)]
theorem step1040 (p : Nat → Bool) (h : Constraints p) : clause p c1040 = true :=
  Snake9.LocalRup.prove_clause [c1038, c582] c1040 (by decide) p (sat_cons (step1038 p h) (sat_cons (step582 p h) (sat_nil p)))
def c1041 : List Lit := [(348, false)]
theorem step1041 (p : Nat → Bool) (h : Constraints p) : clause p c1041 = true :=
  Snake9.LocalRup.prove_clause [c1039, c546] c1041 (by decide) p (sat_cons (step1039 p h) (sat_cons (step546 p h) (sat_nil p)))
def c1042 : List Lit := [(292, false)]
theorem step1042 (p : Nat → Bool) (h : Constraints p) : clause p c1042 = true :=
  Snake9.LocalRup.prove_clause [c1039, c549] c1042 (by decide) p (sat_cons (step1039 p h) (sat_cons (step549 p h) (sat_nil p)))
def c1043 : List Lit := [(462, false)]
theorem step1043 (p : Nat → Bool) (h : Constraints p) : clause p c1043 = true :=
  Snake9.LocalRup.prove_clause [c1040, c578] c1043 (by decide) p (sat_cons (step1040 p h) (sat_cons (step578 p h) (sat_nil p)))
def c1044 : List Lit := [(318, false)]
theorem step1044 (p : Nat → Bool) (h : Constraints p) : clause p c1044 = true :=
  Snake9.LocalRup.prove_clause [c1041, c544] c1044 (by decide) p (sat_cons (step1041 p h) (sat_cons (step544 p h) (sat_nil p)))
def c1045 : List Lit := [(262, false)]
theorem step1045 (p : Nat → Bool) (h : Constraints p) : clause p c1045 = true :=
  Snake9.LocalRup.prove_clause [c1042, c521] c1045 (by decide) p (sat_cons (step1042 p h) (sat_cons (step521 p h) (sat_nil p)))
def c1046 : List Lit := [(304, false)]
theorem step1046 (p : Nat → Bool) (h : Constraints p) : clause p c1046 = true :=
  Snake9.LocalRup.prove_clause [c1044, c537] c1046 (by decide) p (sat_cons (step1044 p h) (sat_cons (step537 p h) (sat_nil p)))
def c1047 : List Lit := [(248, false)]
theorem step1047 (p : Nat → Bool) (h : Constraints p) : clause p c1047 = true :=
  Snake9.LocalRup.prove_clause [c1045, c508] c1047 (by decide) p (sat_cons (step1045 p h) (sat_cons (step508 p h) (sat_nil p)))
def c1048 : List Lit := [(1413, true)]
theorem step1048 (p : Nat → Bool) (h : Constraints p) : clause p c1048 = true :=
  Snake9.LocalRup.prove_clause [c1037, c588] c1048 (by decide) p (sat_cons (step1037 p h) (sat_cons (step588 p h) (sat_nil p)))
def c1049 : List Lit := [(4, true), (1414, true)]
theorem step1049 (p : Nat → Bool) (h : Constraints p) : clause p c1049 = true :=
  Snake9.LocalRup.prove_clause [c1037, c589] c1049 (by decide) p (sat_cons (step1037 p h) (sat_cons (step589 p h) (sat_nil p)))
def c1050 : List Lit := [(1415, true)]
theorem step1050 (p : Nat → Bool) (h : Constraints p) : clause p c1050 = true :=
  Snake9.LocalRup.prove_clause [c1048, c590] c1050 (by decide) p (sat_cons (step1048 p h) (sat_cons (step590 p h) (sat_nil p)))
def c1051 : List Lit := [(3, true), (1416, true)]
theorem step1051 (p : Nat → Bool) (h : Constraints p) : clause p c1051 = true :=
  Snake9.LocalRup.prove_clause [c1048, c592] c1051 (by decide) p (sat_cons (step1048 p h) (sat_cons (step592 p h) (sat_nil p)))
def c1052 : List Lit := [(1426, true)]
theorem step1052 (p : Nat → Bool) (h : Constraints p) : clause p c1052 = true :=
  Snake9.LocalRup.prove_clause [c1050, c605] c1052 (by decide) p (sat_cons (step1050 p h) (sat_cons (step605 p h) (sat_nil p)))
def c1053 : List Lit := [(1422, false), (1427, true)]
theorem step1053 (p : Nat → Bool) (h : Constraints p) : clause p c1053 = true :=
  Snake9.LocalRup.prove_clause [c1050, c606] c1053 (by decide) p (sat_cons (step1050 p h) (sat_cons (step606 p h) (sat_nil p)))
def c1054 : List Lit := [(1423, false), (1428, true)]
theorem step1054 (p : Nat → Bool) (h : Constraints p) : clause p c1054 = true :=
  Snake9.LocalRup.prove_clause [c1050, c607] c1054 (by decide) p (sat_cons (step1050 p h) (sat_cons (step607 p h) (sat_nil p)))
def c1055 : List Lit := [(1450, false), (1459, true)]
theorem step1055 (p : Nat → Bool) (h : Constraints p) : clause p c1055 = true :=
  Snake9.LocalRup.prove_clause [c1052, c641] c1055 (by decide) p (sat_cons (step1052 p h) (sat_cons (step641 p h) (sat_nil p)))
def c1056 : List Lit := [(1451, false), (1460, true)]
theorem step1056 (p : Nat → Bool) (h : Constraints p) : clause p c1056 = true :=
  Snake9.LocalRup.prove_clause [c1052, c642] c1056 (by decide) p (sat_cons (step1052 p h) (sat_cons (step642 p h) (sat_nil p)))
def c1057 : List Lit := [(1452, false), (1461, true)]
theorem step1057 (p : Nat → Bool) (h : Constraints p) : clause p c1057 = true :=
  Snake9.LocalRup.prove_clause [c1052, c643] c1057 (by decide) p (sat_cons (step1052 p h) (sat_cons (step643 p h) (sat_nil p)))
def c1058 : List Lit := [(1504, true)]
theorem step1058 (p : Nat → Bool) (h : Constraints p) : clause p c1058 = true :=
  Snake9.LocalRup.prove_clause [c131, c1036, c703, c704, c702, c700, c129] c1058 (by decide) p (sat_cons (step131 p h) (sat_cons (step1036 p h) (sat_cons (step703 p h) (sat_cons (step704 p h) (sat_cons (step702 p h) (sat_cons (step700 p h) (sat_cons (step129 p h) (sat_nil p))))))))
def c1059 : List Lit := [(1508, true)]
theorem step1059 (p : Nat → Bool) (h : Constraints p) : clause p c1059 = true :=
  Snake9.LocalRup.prove_clause [c1058, c707] c1059 (by decide) p (sat_cons (step1058 p h) (sat_cons (step707 p h) (sat_nil p)))
def c1060 : List Lit := [(1516, true)]
theorem step1060 (p : Nat → Bool) (h : Constraints p) : clause p c1060 = true :=
  Snake9.LocalRup.prove_clause [c1059, c714] c1060 (by decide) p (sat_cons (step1059 p h) (sat_cons (step714 p h) (sat_nil p)))
def c1061 : List Lit := [(1564, true)]
theorem step1061 (p : Nat → Bool) (h : Constraints p) : clause p c1061 = true :=
  Snake9.LocalRup.prove_clause [c477, c771, c775, c765, c752, c757, c758, c750, c152, c148] c1061 (by decide) p (sat_cons (step477 p h) (sat_cons (step771 p h) (sat_cons (step775 p h) (sat_cons (step765 p h) (sat_cons (step752 p h) (sat_cons (step757 p h) (sat_cons (step758 p h) (sat_cons (step750 p h) (sat_cons (step152 p h) (sat_cons (step148 p h) (sat_nil p)))))))))))
def c1062 : List Lit := [(1587, true)]
theorem step1062 (p : Nat → Bool) (h : Constraints p) : clause p c1062 = true :=
  Snake9.LocalRup.prove_clause [c480, c807, c811, c799, c801, c788, c796, c793, c794, c785, c786, c193, c165, c211, c172] c1062 (by decide) p (sat_cons (step480 p h) (sat_cons (step807 p h) (sat_cons (step811 p h) (sat_cons (step799 p h) (sat_cons (step801 p h) (sat_cons (step788 p h) (sat_cons (step796 p h) (sat_cons (step793 p h) (sat_cons (step794 p h) (sat_cons (step785 p h) (sat_cons (step786 p h) (sat_cons (step193 p h) (sat_cons (step165 p h) (sat_cons (step211 p h) (sat_cons (step172 p h) (sat_nil p))))))))))))))))
def c1063 : List Lit := [(1596, true)]
theorem step1063 (p : Nat → Bool) (h : Constraints p) : clause p c1063 = true :=
  Snake9.LocalRup.prove_clause [c1062, c1061, c823] c1063 (by decide) p (sat_cons (step1062 p h) (sat_cons (step1061 p h) (sat_cons (step823 p h) (sat_nil p))))
def c1064 : List Lit := [(26, false), (29, false), (28, false)]
theorem step1064 (p : Nat → Bool) (h : Constraints p) : clause p c1064 = true :=
  Snake9.LocalRup.prove_clause [c459, c60, c62] c1064 (by decide) p (sat_cons (step459 p h) (sat_cons (step60 p h) (sat_cons (step62 p h) (sat_nil p))))
def c1065 : List Lit := [(1445, true)]
theorem step1065 (p : Nat → Bool) (h : Constraints p) : clause p c1065 = true :=
  Snake9.LocalRup.prove_clause [c628, c629, c626, c627, c623, c1064] c1065 (by decide) p (sat_cons (step628 p h) (sat_cons (step629 p h) (sat_cons (step626 p h) (sat_cons (step627 p h) (sat_cons (step623 p h) (sat_cons (step1064 p h) (sat_nil p)))))))
def c1066 : List Lit := [(1449, true)]
theorem step1066 (p : Nat → Bool) (h : Constraints p) : clause p c1066 = true :=
  Snake9.LocalRup.prove_clause [c1065, c633] c1066 (by decide) p (sat_cons (step1065 p h) (sat_cons (step633 p h) (sat_nil p)))
def c1067 : List Lit := [(1459, true)]
theorem step1067 (p : Nat → Bool) (h : Constraints p) : clause p c1067 = true :=
  Snake9.LocalRup.prove_clause [c1065, c1066, c454, c1055, c635, c644, c620, c1053, c614, c600, c28, c597, c598, c26] c1067 (by decide) p (sat_cons (step1065 p h) (sat_cons (step1066 p h) (sat_cons (step454 p h) (sat_cons (step1055 p h) (sat_cons (step635 p h) (sat_cons (step644 p h) (sat_cons (step620 p h) (sat_cons (step1053 p h) (sat_cons (step614 p h) (sat_cons (step600 p h) (sat_cons (step28 p h) (sat_cons (step597 p h) (sat_cons (step598 p h) (sat_cons (step26 p h) (sat_nil p)))))))))))))))
def c1068 : List Lit := [(1496, true), (46, false), (29, false)]
theorem step1068 (p : Nat → Bool) (h : Constraints p) : clause p c1068 = true :=
  Snake9.LocalRup.prove_clause [c692, c694, c690, c686, c113] c1068 (by decide) p (sat_cons (step692 p h) (sat_cons (step694 p h) (sat_cons (step690 p h) (sat_cons (step686 p h) (sat_cons (step113 p h) (sat_nil p))))))
def c1069 : List Lit := [(1519, true), (47, true), (1509, false), (31, true)]
theorem step1069 (p : Nat → Bool) (h : Constraints p) : clause p c1069 = true :=
  Snake9.LocalRup.prove_clause [c1058, c467, c661, c679, c720, c723, c711, c683, c680, c697, c662, c669, c671, c688, c656, c666, c667, c664, c80, c108, c103] c1069 (by decide) p (sat_cons (step1058 p h) (sat_cons (step467 p h) (sat_cons (step661 p h) (sat_cons (step679 p h) (sat_cons (step720 p h) (sat_cons (step723 p h) (sat_cons (step711 p h) (sat_cons (step683 p h) (sat_cons (step680 p h) (sat_cons (step697 p h) (sat_cons (step662 p h) (sat_cons (step669 p h) (sat_cons (step671 p h) (sat_cons (step688 p h) (sat_cons (step656 p h) (sat_cons (step666 p h) (sat_cons (step667 p h) (sat_cons (step664 p h) (sat_cons (step80 p h) (sat_cons (step108 p h) (sat_cons (step103 p h) (sat_nil p))))))))))))))))))))))
def c1070 : List Lit := [(1486, true), (44, false), (31, true)]
theorem step1070 (p : Nat → Bool) (h : Constraints p) : clause p c1070 = true :=
  Snake9.LocalRup.prove_clause [c467, c661, c683, c680, c662, c669, c671, c656, c666, c667, c664, c80, c108, c103] c1070 (by decide) p (sat_cons (step467 p h) (sat_cons (step661 p h) (sat_cons (step683 p h) (sat_cons (step680 p h) (sat_cons (step662 p h) (sat_cons (step669 p h) (sat_cons (step671 p h) (sat_cons (step656 p h) (sat_cons (step666 p h) (sat_cons (step667 p h) (sat_cons (step664 p h) (sat_cons (step80 p h) (sat_cons (step108 p h) (sat_cons (step103 p h) (sat_nil p)))))))))))))))
def c1071 : List Lit := [(1481, true), (44, false)]
theorem step1071 (p : Nat → Bool) (h : Constraints p) : clause p c1071 = true :=
  Snake9.LocalRup.prove_clause [c467, c669, c671, c666, c667, c664, c81, c108, c103] c1071 (by decide) p (sat_cons (step467 p h) (sat_cons (step669 p h) (sat_cons (step671 p h) (sat_cons (step666 p h) (sat_cons (step667 p h) (sat_cons (step664 p h) (sat_cons (step81 p h) (sat_cons (step108 p h) (sat_cons (step103 p h) (sat_nil p))))))))))
def c1072 : List Lit := [(37, false), (1479, true), (44, false)]
theorem step1072 (p : Nat → Bool) (h : Constraints p) : clause p c1072 = true :=
  Snake9.LocalRup.prove_clause [c467, c667, c666, c81, c108, c103] c1072 (by decide) p (sat_cons (step467 p h) (sat_cons (step667 p h) (sat_cons (step666 p h) (sat_cons (step81 p h) (sat_cons (step108 p h) (sat_cons (step103 p h) (sat_nil p)))))))
def c1073 : List Lit := [(1428, true), (2, true), (1420, false)]
theorem step1073 (p : Nat → Bool) (h : Constraints p) : clause p c1073 = true :=
  Snake9.LocalRup.prove_clause [c448, c600, c1054, c608, c603, c591, c1051, c595, c1049, c4, c6] c1073 (by decide) p (sat_cons (step448 p h) (sat_cons (step600 p h) (sat_cons (step1054 p h) (sat_cons (step608 p h) (sat_cons (step603 p h) (sat_cons (step591 p h) (sat_cons (step1051 p h) (sat_cons (step595 p h) (sat_cons (step1049 p h) (sat_cons (step4 p h) (sat_cons (step6 p h) (sat_nil p))))))))))))
def c1074 : List Lit := [(295, false), (39, false), (1473, true), (47, true), (48, false), (1479, true)]
theorem step1074 (p : Nat → Bool) (h : Constraints p) : clause p c1074 = true :=
  Snake9.LocalRup.prove_clause [c1046, c1044, c467, c462, c667, c666, c527, c528, c536, c525, c533, c524, c531, c530, c100, c104, c80, c658, c88, c73, c75, c999, c72] c1074 (by decide) p (sat_cons (step1046 p h) (sat_cons (step1044 p h) (sat_cons (step467 p h) (sat_cons (step462 p h) (sat_cons (step667 p h) (sat_cons (step666 p h) (sat_cons (step527 p h) (sat_cons (step528 p h) (sat_cons (step536 p h) (sat_cons (step525 p h) (sat_cons (step533 p h) (sat_cons (step524 p h) (sat_cons (step531 p h) (sat_cons (step530 p h) (sat_cons (step100 p h) (sat_cons (step104 p h) (sat_cons (step80 p h) (sat_cons (step658 p h) (sat_cons (step88 p h) (sat_cons (step73 p h) (sat_cons (step75 p h) (sat_cons (step999 p h) (sat_cons (step72 p h) (sat_nil p))))))))))))))))))))))))
def c1075 : List Lit := [(1584, true), (86, true), (82, false), (21, false)]
theorem step1075 (p : Nat → Bool) (h : Constraints p) : clause p c1075 = true :=
  Snake9.LocalRup.prove_clause [c796, c800, c802, c798, c793, c201] c1075 (by decide) p (sat_cons (step796 p h) (sat_cons (step800 p h) (sat_cons (step802 p h) (sat_cons (step798 p h) (sat_cons (step793 p h) (sat_cons (step201 p h) (sat_nil p)))))))
def c1076 : List Lit := [(1640, true), (1634, true)]
theorem step1076 (p : Nat → Bool) (h : Constraints p) : clause p c1076 = true :=
  Snake9.LocalRup.prove_clause [c494, c887, c880, c879, c885, c882, c896, c897, c430, c446, c439] c1076 (by decide) p (sat_cons (step494 p h) (sat_cons (step887 p h) (sat_cons (step880 p h) (sat_cons (step879 p h) (sat_cons (step885 p h) (sat_cons (step882 p h) (sat_cons (step896 p h) (sat_cons (step897 p h) (sat_cons (step430 p h) (sat_cons (step446 p h) (sat_cons (step439 p h) (sat_nil p))))))))))))
def c1077 : List Lit := [(104, false), (107, false), (118, true), (117, false), (101, true), (102, false)]
theorem step1077 (p : Nat → Bool) (h : Constraints p) : clause p c1077 = true :=
  Snake9.LocalRup.prove_clause [c490, c372, c378, c381] c1077 (by decide) p (sat_cons (step490 p h) (sat_cons (step372 p h) (sat_cons (step378 p h) (sat_cons (step381 p h) (sat_nil p)))))
def c1078 : List Lit := [(1496, true), (117, false), (112, true)]
theorem step1078 (p : Nat → Bool) (h : Constraints p) : clause p c1078 = true :=
  Snake9.LocalRup.prove_clause [c468, c692, c694, c690, c687, c123, c105] c1078 (by decide) p (sat_cons (step468 p h) (sat_cons (step692 p h) (sat_cons (step694 p h) (sat_cons (step690 p h) (sat_cons (step687 p h) (sat_cons (step123 p h) (sat_cons (step105 p h) (sat_nil p))))))))
def c1079 : List Lit := [(114, false), (117, false), (109, false), (111, false)]
theorem step1079 (p : Nat → Bool) (h : Constraints p) : clause p c1079 = true :=
  Snake9.LocalRup.prove_clause [c493, c435, c390, c425] c1079 (by decide) p (sat_cons (step493 p h) (sat_cons (step435 p h) (sat_cons (step390 p h) (sat_cons (step425 p h) (sat_nil p)))))
def c1080 : List Lit := [(1558, true), (71, true), (111, false)]
theorem step1080 (p : Nat → Bool) (h : Constraints p) : clause p c1080 = true :=
  Snake9.LocalRup.prove_clause [c478, c760, c761, c158, c157] c1080 (by decide) p (sat_cons (step478 p h) (sat_cons (step760 p h) (sat_cons (step761 p h) (sat_cons (step158 p h) (sat_cons (step157 p h) (sat_nil p))))))
def c1081 : List Lit := [(1567, true), (60, true), (1558, false), (62, true)]
theorem step1081 (p : Nat → Bool) (h : Constraints p) : clause p c1081 = true :=
  Snake9.LocalRup.prove_clause [c477, c749, c755, c763, c781, c766, c783, c757, c758, c756, c152, c751, c148] c1081 (by decide) p (sat_cons (step477 p h) (sat_cons (step749 p h) (sat_cons (step755 p h) (sat_cons (step763 p h) (sat_cons (step781 p h) (sat_cons (step766 p h) (sat_cons (step783 p h) (sat_cons (step757 p h) (sat_cons (step758 p h) (sat_cons (step756 p h) (sat_cons (step152 p h) (sat_cons (step751 p h) (sat_cons (step148 p h) (sat_nil p))))))))))))))
def c1082 : List Lit := [(1481, true), (45, true)]
theorem step1082 (p : Nat → Bool) (h : Constraints p) : clause p c1082 = true :=
  Snake9.LocalRup.prove_clause [c467, c669, c671, c666, c667, c664, c103, c81] c1082 (by decide) p (sat_cons (step467 p h) (sat_cons (step669 p h) (sat_cons (step671 p h) (sat_cons (step666 p h) (sat_cons (step667 p h) (sat_cons (step664 p h) (sat_cons (step103 p h) (sat_cons (step81 p h) (sat_nil p)))))))))
def c1083 : List Lit := [(43, false), (41, false), (35, false), (45, true)]
theorem step1083 (p : Nat → Bool) (h : Constraints p) : clause p c1083 = true :=
  Snake9.LocalRup.prove_clause [c467, c103, c80] c1083 (by decide) p (sat_cons (step467 p h) (sat_cons (step103 p h) (sat_cons (step80 p h) (sat_nil p))))
def c1084 : List Lit := [(104, false), (107, false), (1641, true), (102, false), (101, true), (118, true)]
theorem step1084 (p : Nat → Bool) (h : Constraints p) : clause p c1084 = true :=
  Snake9.LocalRup.prove_clause [c494, c372, c1077, c440, c898] c1084 (by decide) p (sat_cons (step494 p h) (sat_cons (step372 p h) (sat_cons (step1077 p h) (sat_cons (step440 p h) (sat_cons (step898 p h) (sat_nil p))))))
def c1085 : List Lit := [(114, false), (108, true), (47, false), (48, false)]
theorem step1085 (p : Nat → Bool) (h : Constraints p) : clause p c1085 = true :=
  Snake9.LocalRup.prove_clause [c493, c427, c114] c1085 (by decide) p (sat_cons (step493 p h) (sat_cons (step427 p h) (sat_cons (step114 p h) (sat_nil p))))
def c1086 : List Lit := [(1519, true), (1639, true), (117, false), (41, true), (116, false), (1509, false)]
theorem step1086 (p : Nat → Bool) (h : Constraints p) : clause p c1086 = true :=
  Snake9.LocalRup.prove_clause [c1058, c467, c493, c667, c669, c676, c723, c720, c677, c680, c711, c670, c672, c659, c697, c668, c664, c656, c79, c103, c108, c109, c687, c688, c895, c695, c437, c690, c426, c114] c1086 (by decide) p (sat_cons (step1058 p h) (sat_cons (step467 p h) (sat_cons (step493 p h) (sat_cons (step667 p h) (sat_cons (step669 p h) (sat_cons (step676 p h) (sat_cons (step723 p h) (sat_cons (step720 p h) (sat_cons (step677 p h) (sat_cons (step680 p h) (sat_cons (step711 p h) (sat_cons (step670 p h) (sat_cons (step672 p h) (sat_cons (step659 p h) (sat_cons (step697 p h) (sat_cons (step668 p h) (sat_cons (step664 p h) (sat_cons (step656 p h) (sat_cons (step79 p h) (sat_cons (step103 p h) (sat_cons (step108 p h) (sat_cons (step109 p h) (sat_cons (step687 p h) (sat_cons (step688 p h) (sat_cons (step895 p h) (sat_cons (step695 p h) (sat_cons (step437 p h) (sat_cons (step690 p h) (sat_cons (step426 p h) (sat_cons (step114 p h) (sat_nil p)))))))))))))))))))))))))))))))
def c1087 : List Lit := [(1588, true), (85, true)]
theorem step1087 (p : Nat → Bool) (h : Constraints p) : clause p c1087 = true :=
  Snake9.LocalRup.prove_clause [c483, c797, c799, c808, c812, c800, c802, c788, c798, c793, c785, c786, c216, c165, c211, c199] c1087 (by decide) p (sat_cons (step483 p h) (sat_cons (step797 p h) (sat_cons (step799 p h) (sat_cons (step808 p h) (sat_cons (step812 p h) (sat_cons (step800 p h) (sat_cons (step802 p h) (sat_cons (step788 p h) (sat_cons (step798 p h) (sat_cons (step793 p h) (sat_cons (step785 p h) (sat_cons (step786 p h) (sat_cons (step216 p h) (sat_cons (step165 p h) (sat_cons (step211 p h) (sat_cons (step199 p h) (sat_nil p)))))))))))))))))
def c1088 : List Lit := [(60, true), (1566, true), (1556, false)]
theorem step1088 (p : Nat → Bool) (h : Constraints p) : clause p c1088 = true :=
  Snake9.LocalRup.prove_clause [c478, c765, c780, c754, c777, c755, c766, c749, c750, c760, c761, c159, c154, c158] c1088 (by decide) p (sat_cons (step478 p h) (sat_cons (step765 p h) (sat_cons (step780 p h) (sat_cons (step754 p h) (sat_cons (step777 p h) (sat_cons (step755 p h) (sat_cons (step766 p h) (sat_cons (step749 p h) (sat_cons (step750 p h) (sat_cons (step760 p h) (sat_cons (step761 p h) (sat_cons (step159 p h) (sat_cons (step154 p h) (sat_cons (step158 p h) (sat_nil p)))))))))))))))
def c1089 : List Lit := [(1505, true), (54, true)]
theorem step1089 (p : Nat → Bool) (h : Constraints p) : clause p c1089 = true :=
  Snake9.LocalRup.prove_clause [c131, c1036, c699, c706, c705, c701, c702, c129] c1089 (by decide) p (sat_cons (step131 p h) (sat_cons (step1036 p h) (sat_cons (step699 p h) (sat_cons (step706 p h) (sat_cons (step705 p h) (sat_cons (step701 p h) (sat_cons (step702 p h) (sat_cons (step129 p h) (sat_nil p)))))))))
def c1090 : List Lit := [(1428, true), (1420, false), (5, false), (62, false)]
theorem step1090 (p : Nat → Bool) (h : Constraints p) : clause p c1090 = true :=
  Snake9.LocalRup.prove_clause [c1037, c1054, c1073, c603, c2, c595, c10] c1090 (by decide) p (sat_cons (step1037 p h) (sat_cons (step1054 p h) (sat_cons (step1073 p h) (sat_cons (step603 p h) (sat_cons (step2 p h) (sat_cons (step595 p h) (sat_cons (step10 p h) (sat_nil p))))))))
def c1091 : List Lit := [(65, true), (63, false), (60, false)]
theorem step1091 (p : Nat → Bool) (h : Constraints p) : clause p c1091 = true :=
  Snake9.LocalRup.prove_clause [c476, c144, c145, c1006] c1091 (by decide) p (sat_cons (step476 p h) (sat_cons (step144 p h) (sat_cons (step145 p h) (sat_cons (step1006 p h) (sat_nil p)))))
def c1092 : List Lit := [(1566, true), (1428, true), (1556, false), (61, true), (71, true), (68, false), (70, false)]
theorem step1092 (p : Nat → Bool) (h : Constraints p) : clause p c1092 = true :=
  Snake9.LocalRup.prove_clause [c475, c765, c750, c752, c777, c780, c766, c753, c761, c751, c153, c142, c598, c1090] c1092 (by decide) p (sat_cons (step475 p h) (sat_cons (step765 p h) (sat_cons (step750 p h) (sat_cons (step752 p h) (sat_cons (step777 p h) (sat_cons (step780 p h) (sat_cons (step766 p h) (sat_cons (step753 p h) (sat_cons (step761 p h) (sat_cons (step751 p h) (sat_cons (step153 p h) (sat_cons (step142 p h) (sat_cons (step598 p h) (sat_cons (step1090 p h) (sat_nil p)))))))))))))))
def c1093 : List Lit := [(1630, true), (105, false), (85, false)]
theorem step1093 (p : Nat → Bool) (h : Constraints p) : clause p c1093 = true :=
  Snake9.LocalRup.prove_clause [c879, c880, c369] c1093 (by decide) p (sat_cons (step879 p h) (sat_cons (step880 p h) (sat_cons (step369 p h) (sat_nil p))))
def c1094 : List Lit := [(114, false), (115, true), (1632, true)]
theorem step1094 (p : Nat → Bool) (h : Constraints p) : clause p c1094 = true :=
  Snake9.LocalRup.prove_clause [c493, c883, c882, c390, c425] c1094 (by decide) p (sat_cons (step493 p h) (sat_cons (step883 p h) (sat_cons (step882 p h) (sat_cons (step390 p h) (sat_cons (step425 p h) (sat_nil p))))))
def c1095 : List Lit := [(117, true), (1638, false), (1649, true), (104, true), (105, false), (85, false)]
theorem step1095 (p : Nat → Bool) (h : Constraints p) : clause p c1095 = true :=
  Snake9.LocalRup.prove_clause [c1093, c887, c913, c903, c896, c902, c917, c898, c890, c371, c881] c1095 (by decide) p (sat_cons (step1093 p h) (sat_cons (step887 p h) (sat_cons (step913 p h) (sat_cons (step903 p h) (sat_cons (step896 p h) (sat_cons (step902 p h) (sat_cons (step917 p h) (sat_cons (step898 p h) (sat_cons (step890 p h) (sat_cons (step371 p h) (sat_cons (step881 p h) (sat_nil p))))))))))))
def c1096 : List Lit := [(62, false), (71, true), (113, false), (107, false)]
theorem step1096 (p : Nat → Bool) (h : Constraints p) : clause p c1096 = true :=
  Snake9.LocalRup.prove_clause [c475, c140, c320] c1096 (by decide) p (sat_cons (step475 p h) (sat_cons (step140 p h) (sat_cons (step320 p h) (sat_nil p))))
def c1097 : List Lit := [(1589, true), (1571, false), (80, true)]
theorem step1097 (p : Nat → Bool) (h : Constraints p) : clause p c1097 = true :=
  Snake9.LocalRup.prove_clause [c480, c790, c794, c801, c813, c817, c804, c802, c791, c795, c796, c785, c786, c191, c165, c211, c172] c1097 (by decide) p (sat_cons (step480 p h) (sat_cons (step790 p h) (sat_cons (step794 p h) (sat_cons (step801 p h) (sat_cons (step813 p h) (sat_cons (step817 p h) (sat_cons (step804 p h) (sat_cons (step802 p h) (sat_cons (step791 p h) (sat_cons (step795 p h) (sat_cons (step796 p h) (sat_cons (step785 p h) (sat_cons (step786 p h) (sat_cons (step191 p h) (sat_cons (step165 p h) (sat_cons (step211 p h) (sat_cons (step172 p h) (sat_nil p))))))))))))))))))
def c1098 : List Lit := [(110, false), (1477, false), (113, false), (101, false), (1520, true), (34, true), (98, false), (109, false)]
theorem step1098 (p : Nat → Bool) (h : Constraints p) : clause p c1098 = true :=
  Snake9.LocalRup.prove_clause [c468, c1058, c671, c657, c659, c393, c422, c106, c687, c694, c709, c727, c684, c681, c660, c672, c658, c666, c667, c1083] c1098 (by decide) p (sat_cons (step468 p h) (sat_cons (step1058 p h) (sat_cons (step671 p h) (sat_cons (step657 p h) (sat_cons (step659 p h) (sat_cons (step393 p h) (sat_cons (step422 p h) (sat_cons (step106 p h) (sat_cons (step687 p h) (sat_cons (step694 p h) (sat_cons (step709 p h) (sat_cons (step727 p h) (sat_cons (step684 p h) (sat_cons (step681 p h) (sat_cons (step660 p h) (sat_cons (step672 p h) (sat_cons (step658 p h) (sat_cons (step666 p h) (sat_cons (step667 p h) (sat_cons (step1083 p h) (sat_nil p)))))))))))))))))))))
def c1099 : List Lit := [(1487, true), (1477, false), (107, false), (102, false), (34, true)]
theorem step1099 (p : Nat → Bool) (h : Constraints p) : clause p c1099 = true :=
  Snake9.LocalRup.prove_clause [c466, c671, c657, c659, c684, c681, c660, c672, c658, c666, c667, c80, c352, c98] c1099 (by decide) p (sat_cons (step466 p h) (sat_cons (step671 p h) (sat_cons (step657 p h) (sat_cons (step659 p h) (sat_cons (step684 p h) (sat_cons (step681 p h) (sat_cons (step660 p h) (sat_cons (step672 p h) (sat_cons (step658 p h) (sat_cons (step666 p h) (sat_cons (step667 p h) (sat_cons (step80 p h) (sat_cons (step352 p h) (sat_cons (step98 p h) (sat_nil p)))))))))))))))
end B112E096
