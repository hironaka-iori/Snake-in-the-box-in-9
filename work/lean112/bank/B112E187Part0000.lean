import B112E187Inputs
namespace B112E187
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1017 : List Lit := [(117, false), (118, false), (119, false)]
theorem step1017 (p : Nat → Bool) (h : Constraints p) : clause p c1017 = true :=
  Snake9.LocalRup.prove_clause [c390, c392] c1017 (by decide) p (sat_cons (step390 p h) (sat_cons (step392 p h) (sat_nil p)))
def c1018 : List Lit := [(1, false)]
theorem step1018 (p : Nat → Bool) (h : Constraints p) : clause p c1018 = true :=
  Snake9.LocalRup.prove_clause [c395, c1] c1018 (by decide) p (sat_cons (step395 p h) (sat_cons (step1 p h) (sat_nil p)))
def c1019 : List Lit := [(16, false)]
theorem step1019 (p : Nat → Bool) (h : Constraints p) : clause p c1019 = true :=
  Snake9.LocalRup.prove_clause [c397, c12] c1019 (by decide) p (sat_cons (step397 p h) (sat_cons (step12 p h) (sat_nil p)))
def c1020 : List Lit := [(18, false)]
theorem step1020 (p : Nat → Bool) (h : Constraints p) : clause p c1020 = true :=
  Snake9.LocalRup.prove_clause [c398, c14] c1020 (by decide) p (sat_cons (step398 p h) (sat_cons (step14 p h) (sat_nil p)))
def c1021 : List Lit := [(22, false)]
theorem step1021 (p : Nat → Bool) (h : Constraints p) : clause p c1021 = true :=
  Snake9.LocalRup.prove_clause [c400, c19] c1021 (by decide) p (sat_cons (step400 p h) (sat_cons (step19 p h) (sat_nil p)))
def c1022 : List Lit := [(470, false)]
theorem step1022 (p : Nat → Bool) (h : Constraints p) : clause p c1022 = true :=
  Snake9.LocalRup.prove_clause [c636, c633] c1022 (by decide) p (sat_cons (step636 p h) (sat_cons (step633 p h) (sat_nil p)))
def c1023 : List Lit := [(354, false)]
theorem step1023 (p : Nat → Bool) (h : Constraints p) : clause p c1023 = true :=
  Snake9.LocalRup.prove_clause [c636, c635] c1023 (by decide) p (sat_cons (step636 p h) (sat_cons (step635 p h) (sat_nil p)))
def c1024 : List Lit := [(468, false)]
theorem step1024 (p : Nat → Bool) (h : Constraints p) : clause p c1024 = true :=
  Snake9.LocalRup.prove_clause [c1022, c629] c1024 (by decide) p (sat_cons (step1022 p h) (sat_cons (step629 p h) (sat_nil p)))
def c1025 : List Lit := [(410, false)]
theorem step1025 (p : Nat → Bool) (h : Constraints p) : clause p c1025 = true :=
  Snake9.LocalRup.prove_clause [c1022, c632] c1025 (by decide) p (sat_cons (step1022 p h) (sat_cons (step632 p h) (sat_nil p)))
def c1026 : List Lit := [(352, false)]
theorem step1026 (p : Nat → Bool) (h : Constraints p) : clause p c1026 = true :=
  Snake9.LocalRup.prove_clause [c1023, c534] c1026 (by decide) p (sat_cons (step1023 p h) (sat_cons (step534 p h) (sat_nil p)))
def c1027 : List Lit := [(294, false)]
theorem step1027 (p : Nat → Bool) (h : Constraints p) : clause p c1027 = true :=
  Snake9.LocalRup.prove_clause [c1023, c537] c1027 (by decide) p (sat_cons (step1023 p h) (sat_cons (step537 p h) (sat_nil p)))
def c1028 : List Lit := [(466, false)]
theorem step1028 (p : Nat → Bool) (h : Constraints p) : clause p c1028 = true :=
  Snake9.LocalRup.prove_clause [c1024, c624] c1028 (by decide) p (sat_cons (step1024 p h) (sat_cons (step624 p h) (sat_nil p)))
def c1029 : List Lit := [(438, false)]
theorem step1029 (p : Nat → Bool) (h : Constraints p) : clause p c1029 = true :=
  Snake9.LocalRup.prove_clause [c1024, c627] c1029 (by decide) p (sat_cons (step1024 p h) (sat_cons (step627 p h) (sat_nil p)))
def c1030 : List Lit := [(408, false)]
theorem step1030 (p : Nat → Bool) (h : Constraints p) : clause p c1030 = true :=
  Snake9.LocalRup.prove_clause [c1025, c575] c1030 (by decide) p (sat_cons (step1025 p h) (sat_cons (step575 p h) (sat_nil p)))
def c1031 : List Lit := [(380, false)]
theorem step1031 (p : Nat → Bool) (h : Constraints p) : clause p c1031 = true :=
  Snake9.LocalRup.prove_clause [c1025, c578] c1031 (by decide) p (sat_cons (step1025 p h) (sat_cons (step578 p h) (sat_nil p)))
def c1032 : List Lit := [(350, false)]
theorem step1032 (p : Nat → Bool) (h : Constraints p) : clause p c1032 = true :=
  Snake9.LocalRup.prove_clause [c1026, c529] c1032 (by decide) p (sat_cons (step1026 p h) (sat_cons (step529 p h) (sat_nil p)))
def c1033 : List Lit := [(322, false)]
theorem step1033 (p : Nat → Bool) (h : Constraints p) : clause p c1033 = true :=
  Snake9.LocalRup.prove_clause [c1026, c532] c1033 (by decide) p (sat_cons (step1026 p h) (sat_cons (step532 p h) (sat_nil p)))
def c1034 : List Lit := [(292, false)]
theorem step1034 (p : Nat → Bool) (h : Constraints p) : clause p c1034 = true :=
  Snake9.LocalRup.prove_clause [c1027, c466] c1034 (by decide) p (sat_cons (step1027 p h) (sat_cons (step466 p h) (sat_nil p)))
def c1035 : List Lit := [(464, false)]
theorem step1035 (p : Nat → Bool) (h : Constraints p) : clause p c1035 = true :=
  Snake9.LocalRup.prove_clause [c1028, c619] c1035 (by decide) p (sat_cons (step1028 p h) (sat_cons (step619 p h) (sat_nil p)))
def c1036 : List Lit := [(450, false)]
theorem step1036 (p : Nat → Bool) (h : Constraints p) : clause p c1036 = true :=
  Snake9.LocalRup.prove_clause [c1028, c622] c1036 (by decide) p (sat_cons (step1028 p h) (sat_cons (step622 p h) (sat_nil p)))
def c1037 : List Lit := [(422, false)]
theorem step1037 (p : Nat → Bool) (h : Constraints p) : clause p c1037 = true :=
  Snake9.LocalRup.prove_clause [c1029, c597] c1037 (by decide) p (sat_cons (step1029 p h) (sat_cons (step597 p h) (sat_nil p)))
def c1038 : List Lit := [(406, false)]
theorem step1038 (p : Nat → Bool) (h : Constraints p) : clause p c1038 = true :=
  Snake9.LocalRup.prove_clause [c1030, c572] c1038 (by decide) p (sat_cons (step1030 p h) (sat_cons (step572 p h) (sat_nil p)))
def c1039 : List Lit := [(378, false)]
theorem step1039 (p : Nat → Bool) (h : Constraints p) : clause p c1039 = true :=
  Snake9.LocalRup.prove_clause [c1031, c555] c1039 (by decide) p (sat_cons (step1031 p h) (sat_cons (step555 p h) (sat_nil p)))
def c1040 : List Lit := [(348, false)]
theorem step1040 (p : Nat → Bool) (h : Constraints p) : clause p c1040 = true :=
  Snake9.LocalRup.prove_clause [c1032, c524] c1040 (by decide) p (sat_cons (step1032 p h) (sat_cons (step524 p h) (sat_nil p)))
def c1041 : List Lit := [(334, false)]
theorem step1041 (p : Nat → Bool) (h : Constraints p) : clause p c1041 = true :=
  Snake9.LocalRup.prove_clause [c1032, c527] c1041 (by decide) p (sat_cons (step1032 p h) (sat_cons (step527 p h) (sat_nil p)))
def c1042 : List Lit := [(320, false)]
theorem step1042 (p : Nat → Bool) (h : Constraints p) : clause p c1042 = true :=
  Snake9.LocalRup.prove_clause [c1033, c496] c1042 (by decide) p (sat_cons (step1033 p h) (sat_cons (step496 p h) (sat_nil p)))
def c1043 : List Lit := [(306, false)]
theorem step1043 (p : Nat → Bool) (h : Constraints p) : clause p c1043 = true :=
  Snake9.LocalRup.prove_clause [c1033, c499] c1043 (by decide) p (sat_cons (step1033 p h) (sat_cons (step499 p h) (sat_nil p)))
def c1044 : List Lit := [(290, false)]
theorem step1044 (p : Nat → Bool) (h : Constraints p) : clause p c1044 = true :=
  Snake9.LocalRup.prove_clause [c1034, c463] c1044 (by decide) p (sat_cons (step1034 p h) (sat_cons (step463 p h) (sat_nil p)))
def c1045 : List Lit := [(448, false)]
theorem step1045 (p : Nat → Bool) (h : Constraints p) : clause p c1045 = true :=
  Snake9.LocalRup.prove_clause [c1036, c608] c1045 (by decide) p (sat_cons (step1036 p h) (sat_cons (step608 p h) (sat_nil p)))
def c1046 : List Lit := [(376, false)]
theorem step1046 (p : Nat → Bool) (h : Constraints p) : clause p c1046 = true :=
  Snake9.LocalRup.prove_clause [c1039, c552] c1046 (by decide) p (sat_cons (step1039 p h) (sat_cons (step552 p h) (sat_nil p)))
def c1047 : List Lit := [(346, false)]
theorem step1047 (p : Nat → Bool) (h : Constraints p) : clause p c1047 = true :=
  Snake9.LocalRup.prove_clause [c1040, c520] c1047 (by decide) p (sat_cons (step1040 p h) (sat_cons (step520 p h) (sat_nil p)))
def c1048 : List Lit := [(332, false)]
theorem step1048 (p : Nat → Bool) (h : Constraints p) : clause p c1048 = true :=
  Snake9.LocalRup.prove_clause [c1041, c508] c1048 (by decide) p (sat_cons (step1041 p h) (sat_cons (step508 p h) (sat_nil p)))
def c1049 : List Lit := [(318, false)]
theorem step1049 (p : Nat → Bool) (h : Constraints p) : clause p c1049 = true :=
  Snake9.LocalRup.prove_clause [c1042, c493] c1049 (by decide) p (sat_cons (step1042 p h) (sat_cons (step493 p h) (sat_nil p)))
def c1050 : List Lit := [(304, false)]
theorem step1050 (p : Nat → Bool) (h : Constraints p) : clause p c1050 = true :=
  Snake9.LocalRup.prove_clause [c1043, c480] c1050 (by decide) p (sat_cons (step1043 p h) (sat_cons (step480 p h) (sat_nil p)))
def c1051 : List Lit := [(298, false)]
theorem step1051 (p : Nat → Bool) (h : Constraints p) : clause p c1051 = true :=
  Snake9.LocalRup.prove_clause [c1043, c483] c1051 (by decide) p (sat_cons (step1043 p h) (sat_cons (step483 p h) (sat_nil p)))
def c1052 : List Lit := [(282, false)]
theorem step1052 (p : Nat → Bool) (h : Constraints p) : clause p c1052 = true :=
  Snake9.LocalRup.prove_clause [c1044, c461] c1052 (by decide) p (sat_cons (step1044 p h) (sat_cons (step461 p h) (sat_nil p)))
def c1053 : List Lit := [(444, false)]
theorem step1053 (p : Nat → Bool) (h : Constraints p) : clause p c1053 = true :=
  Snake9.LocalRup.prove_clause [c1045, c606] c1053 (by decide) p (sat_cons (step1045 p h) (sat_cons (step606 p h) (sat_nil p)))
def c1054 : List Lit := [(314, false)]
theorem step1054 (p : Nat → Bool) (h : Constraints p) : clause p c1054 = true :=
  Snake9.LocalRup.prove_clause [c1049, c491] c1054 (by decide) p (sat_cons (step1049 p h) (sat_cons (step491 p h) (sat_nil p)))
def c1055 : List Lit := [(296, false)]
theorem step1055 (p : Nat → Bool) (h : Constraints p) : clause p c1055 = true :=
  Snake9.LocalRup.prove_clause [c1051, c473] c1055 (by decide) p (sat_cons (step1051 p h) (sat_cons (step473 p h) (sat_nil p)))
def c1056 : List Lit := [(280, false)]
theorem step1056 (p : Nat → Bool) (h : Constraints p) : clause p c1056 = true :=
  Snake9.LocalRup.prove_clause [c1052, c455] c1056 (by decide) p (sat_cons (step1052 p h) (sat_cons (step455 p h) (sat_nil p)))
def c1057 : List Lit := [(1456, true)]
theorem step1057 (p : Nat → Bool) (h : Constraints p) : clause p c1057 = true :=
  Snake9.LocalRup.prove_clause [c646, c648, c643, c644, c641, c642, c11, c7, c9] c1057 (by decide) p (sat_cons (step646 p h) (sat_cons (step648 p h) (sat_cons (step643 p h) (sat_cons (step644 p h) (sat_cons (step641 p h) (sat_cons (step642 p h) (sat_cons (step11 p h) (sat_cons (step7 p h) (sat_cons (step9 p h) (sat_nil p))))))))))
def c1058 : List Lit := [(1460, true)]
theorem step1058 (p : Nat → Bool) (h : Constraints p) : clause p c1058 = true :=
  Snake9.LocalRup.prove_clause [c1057, c650] c1058 (by decide) p (sat_cons (step1057 p h) (sat_cons (step650 p h) (sat_nil p)))
def c1059 : List Lit := [(25, false), (24, false), (23, false)]
theorem step1059 (p : Nat → Bool) (h : Constraints p) : clause p c1059 = true :=
  Snake9.LocalRup.prove_clause [c1056, c27, c22, c23, c453] c1059 (by decide) p (sat_cons (step1056 p h) (sat_cons (step27 p h) (sat_cons (step22 p h) (sat_cons (step23 p h) (sat_cons (step453 p h) (sat_nil p))))))
def c1060 : List Lit := [(1480, true)]
theorem step1060 (p : Nat → Bool) (h : Constraints p) : clause p c1060 = true :=
  Snake9.LocalRup.prove_clause [c672, c674, c667, c656, c660, c661, c653, c1059] c1060 (by decide) p (sat_cons (step672 p h) (sat_cons (step674 p h) (sat_cons (step667 p h) (sat_cons (step656 p h) (sat_cons (step660 p h) (sat_cons (step661 p h) (sat_cons (step653 p h) (sat_cons (step1059 p h) (sat_nil p)))))))))
def c1061 : List Lit := [(1488, true)]
theorem step1061 (p : Nat → Bool) (h : Constraints p) : clause p c1061 = true :=
  Snake9.LocalRup.prove_clause [c1060, c1058, c680] c1061 (by decide) p (sat_cons (step1060 p h) (sat_cons (step1058 p h) (sat_cons (step680 p h) (sat_nil p))))
def c1062 : List Lit := [(1510, true), (161, true)]
theorem step1062 (p : Nat → Bool) (h : Constraints p) : clause p c1062 = true :=
  Snake9.LocalRup.prove_clause [c702, c704, c699, c700, c696, c74, c78] c1062 (by decide) p (sat_cons (step702 p h) (sat_cons (step704 p h) (sat_cons (step699 p h) (sat_cons (step700 p h) (sat_cons (step696 p h) (sat_cons (step74 p h) (sat_cons (step78 p h) (sat_nil p))))))))
def c1063 : List Lit := [(1525, true), (53, false), (52, false)]
theorem step1063 (p : Nat → Bool) (h : Constraints p) : clause p c1063 = true :=
  Snake9.LocalRup.prove_clause [c725, c727, c722, c719, c117] c1063 (by decide) p (sat_cons (step725 p h) (sat_cons (step727 p h) (sat_cons (step722 p h) (sat_cons (step719 p h) (sat_cons (step117 p h) (sat_nil p))))))
def c1064 : List Lit := [(1664, true)]
theorem step1064 (p : Nat → Bool) (h : Constraints p) : clause p c1064 = true :=
  Snake9.LocalRup.prove_clause [c391, c923, c925, c920, c918, c389] c1064 (by decide) p (sat_cons (step391 p h) (sat_cons (step923 p h) (sat_cons (step925 p h) (sat_cons (step920 p h) (sat_cons (step918 p h) (sat_cons (step389 p h) (sat_nil p)))))))
def c1065 : List Lit := [(92, false), (1527, true), (49, true), (53, false), (52, false)]
theorem step1065 (p : Nat → Bool) (h : Constraints p) : clause p c1065 = true :=
  Snake9.LocalRup.prove_clause [c120, c119, c724, c719, c729] c1065 (by decide) p (sat_cons (step120 p h) (sat_cons (step119 p h) (sat_cons (step724 p h) (sat_cons (step719 p h) (sat_cons (step729 p h) (sat_nil p))))))
def c1066 : List Lit := [(1593, true), (1583, false), (72, true), (189, true)]
theorem step1066 (p : Nat → Bool) (h : Constraints p) : clause p c1066 = true :=
  Snake9.LocalRup.prove_clause [c791, c797, c803, c806, c798, c783, c793, c780, c157, c158, c1006] c1066 (by decide) p (sat_cons (step791 p h) (sat_cons (step797 p h) (sat_cons (step803 p h) (sat_cons (step806 p h) (sat_cons (step798 p h) (sat_cons (step783 p h) (sat_cons (step793 p h) (sat_cons (step780 p h) (sat_cons (step157 p h) (sat_cons (step158 p h) (sat_cons (step1006 p h) (sat_nil p))))))))))))
def c1067 : List Lit := [(70, false), (69, true), (189, true)]
theorem step1067 (p : Nat → Bool) (h : Constraints p) : clause p c1067 = true :=
  Snake9.LocalRup.prove_clause [c414, c157, c158, c161, c1006] c1067 (by decide) p (sat_cons (step414 p h) (sat_cons (step157 p h) (sat_cons (step158 p h) (sat_cons (step161 p h) (sat_cons (step1006 p h) (sat_nil p))))))
def c1068 : List Lit := [(66, false), (1681, false), (1593, false), (1523, false), (1600, false), (88, true), (47, false), (58, false), (1489, false), (1514, false)]
theorem step1068 (p : Nat → Bool) (h : Constraints p) : clause p c1068 = true :=
  Snake9.LocalRup.prove_clause [c991, c90, c88, c825, c719, c827, c728, c840, c748, c859, c754, c982, c772, c988] c1068 (by decide) p (sat_cons (step991 p h) (sat_cons (step90 p h) (sat_cons (step88 p h) (sat_cons (step825 p h) (sat_cons (step719 p h) (sat_cons (step827 p h) (sat_cons (step728 p h) (sat_cons (step840 p h) (sat_cons (step748 p h) (sat_cons (step859 p h) (sat_cons (step754 p h) (sat_cons (step982 p h) (sat_cons (step772 p h) (sat_cons (step988 p h) (sat_nil p)))))))))))))))
def c1069 : List Lit := [(1669, true)]
theorem step1069 (p : Nat → Bool) (h : Constraints p) : clause p c1069 = true :=
  Snake9.LocalRup.prove_clause [c1064, c391, c931, c934, c912, c904, c387, c388, c918, c920, c926] c1069 (by decide) p (sat_cons (step1064 p h) (sat_cons (step391 p h) (sat_cons (step931 p h) (sat_cons (step934 p h) (sat_cons (step912 p h) (sat_cons (step904 p h) (sat_cons (step387 p h) (sat_cons (step388 p h) (sat_cons (step918 p h) (sat_cons (step920 p h) (sat_cons (step926 p h) (sat_nil p))))))))))))
def c1070 : List Lit := [(1594, false), (1523, false), (88, true), (47, false), (1612, false), (1600, false), (1624, true), (1489, false), (1681, false), (58, false), (1514, false)]
theorem step1070 (p : Nat → Bool) (h : Constraints p) : clause p c1070 = true :=
  Snake9.LocalRup.prove_clause [c991, c863, c864, c982, c840, c988, c827, c772, c825, c754, c89, c748, c719, c728] c1070 (by decide) p (sat_cons (step991 p h) (sat_cons (step863 p h) (sat_cons (step864 p h) (sat_cons (step982 p h) (sat_cons (step840 p h) (sat_cons (step988 p h) (sat_cons (step827 p h) (sat_cons (step772 p h) (sat_cons (step825 p h) (sat_cons (step754 p h) (sat_cons (step89 p h) (sat_cons (step748 p h) (sat_cons (step719 p h) (sat_cons (step728 p h) (sat_nil p)))))))))))))))
def c1071 : List Lit := [(1523, false), (88, true), (47, false), (77, false), (1612, false), (1600, false), (1602, true), (1624, true), (1489, false), (1681, false), (58, false), (1583, false), (1593, false), (59, false), (72, true), (293, false)]
theorem step1071 (p : Nat → Bool) (h : Constraints p) : clause p c1071 = true :=
  Snake9.LocalRup.prove_clause [c636, c1023, c416, c791, c797, c536, c530, c495, c492, c490, c487, c1062, c709, c535, c634, c630, c576, c554, c551, c549, c546, c574, c573, c564, c560, c1068, c780, c783, c1070, c810, c807, c784, c798, c782, c793, c1067, c176, c177, c183, c814, c819, c165, c166, c1007] c1071 (by decide) p (sat_cons (step636 p h) (sat_cons (step1023 p h) (sat_cons (step416 p h) (sat_cons (step791 p h) (sat_cons (step797 p h) (sat_cons (step536 p h) (sat_cons (step530 p h) (sat_cons (step495 p h) (sat_cons (step492 p h) (sat_cons (step490 p h) (sat_cons (step487 p h) (sat_cons (step1062 p h) (sat_cons (step709 p h) (sat_cons (step535 p h) (sat_cons (step634 p h) (sat_cons (step630 p h) (sat_cons (step576 p h) (sat_cons (step554 p h) (sat_cons (step551 p h) (sat_cons (step549 p h) (sat_cons (step546 p h) (sat_cons (step574 p h) (sat_cons (step573 p h) (sat_cons (step564 p h) (sat_cons (step560 p h) (sat_cons (step1068 p h) (sat_cons (step780 p h) (sat_cons (step783 p h) (sat_cons (step1070 p h) (sat_cons (step810 p h) (sat_cons (step807 p h) (sat_cons (step784 p h) (sat_cons (step798 p h) (sat_cons (step782 p h) (sat_cons (step793 p h) (sat_cons (step1067 p h) (sat_cons (step176 p h) (sat_cons (step177 p h) (sat_cons (step183 p h) (sat_cons (step814 p h) (sat_cons (step819 p h) (sat_cons (step165 p h) (sat_cons (step166 p h) (sat_cons (step1007 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))
def c1072 : List Lit := [(90, false), (1603, true), (209, true), (88, false)]
theorem step1072 (p : Nat → Bool) (h : Constraints p) : clause p c1072 = true :=
  Snake9.LocalRup.prove_clause [c821, c820, c247, c200, c279] c1072 (by decide) p (sat_cons (step821 p h) (sat_cons (step820 p h) (sat_cons (step247 p h) (sat_cons (step200 p h) (sat_cons (step279 p h) (sat_nil p))))))
def c1073 : List Lit := [(49, false), (50, true), (80, false), (168, true), (88, false)]
theorem step1073 (p : Nat → Bool) (h : Constraints p) : clause p c1073 = true :=
  Snake9.LocalRup.prove_clause [c92, c240] c1073 (by decide) p (sat_cons (step92 p h) (sat_cons (step240 p h) (sat_nil p)))
def c1074 : List Lit := [(1538, true), (48, true), (92, false), (170, true)]
theorem step1074 (p : Nat → Bool) (h : Constraints p) : clause p c1074 = true :=
  Snake9.LocalRup.prove_clause [c719, c727, c748, c746, c730, c728, c738, c721, c722, c733, c98, c120, c111] c1074 (by decide) p (sat_cons (step719 p h) (sat_cons (step727 p h) (sat_cons (step748 p h) (sat_cons (step746 p h) (sat_cons (step730 p h) (sat_cons (step728 p h) (sat_cons (step738 p h) (sat_cons (step721 p h) (sat_cons (step722 p h) (sat_cons (step733 p h) (sat_cons (step98 p h) (sat_cons (step120 p h) (sat_cons (step111 p h) (sat_nil p))))))))))))))
def c1075 : List Lit := [(53, false), (48, false), (1538, true), (92, false)]
theorem step1075 (p : Nat → Bool) (h : Constraints p) : clause p c1075 = true :=
  Snake9.LocalRup.prove_clause [c119, c118, c733, c722, c738, c725, c746] c1075 (by decide) p (sat_cons (step119 p h) (sat_cons (step118 p h) (sat_cons (step733 p h) (sat_cons (step722 p h) (sat_cons (step738 p h) (sat_cons (step725 p h) (sat_cons (step746 p h) (sat_nil p))))))))
def c1076 : List Lit := [(1537, true), (171, true)]
theorem step1076 (p : Nat → Bool) (h : Constraints p) : clause p c1076 = true :=
  Snake9.LocalRup.prove_clause [c742, c745, c738, c725, c727, c733, c722, c720, c1063, c116, c98] c1076 (by decide) p (sat_cons (step742 p h) (sat_cons (step745 p h) (sat_cons (step738 p h) (sat_cons (step725 p h) (sat_cons (step727 p h) (sat_cons (step733 p h) (sat_cons (step722 p h) (sat_cons (step720 p h) (sat_cons (step1063 p h) (sat_cons (step116 p h) (sat_cons (step98 p h) (sat_nil p))))))))))))
def c1077 : List Lit := [(1525, true), (168, true), (80, false), (88, false)]
theorem step1077 (p : Nat → Bool) (h : Constraints p) : clause p c1077 = true :=
  Snake9.LocalRup.prove_clause [c725, c727, c722, c723, c720, c1073, c95] c1077 (by decide) p (sat_cons (step725 p h) (sat_cons (step727 p h) (sat_cons (step722 p h) (sat_cons (step723 p h) (sat_cons (step720 p h) (sat_cons (step1073 p h) (sat_cons (step95 p h) (sat_nil p))))))))
def c1078 : List Lit := [(101, true), (1635, false), (1681, true)]
theorem step1078 (p : Nat → Bool) (h : Constraints p) : clause p c1078 = true :=
  Snake9.LocalRup.prove_clause [c1069, c391, c956, c898, c880, c876, c878, c879, c384, c385, c386, c897, c904, c918, c920, c953, c912, c926, c935] c1078 (by decide) p (sat_cons (step1069 p h) (sat_cons (step391 p h) (sat_cons (step956 p h) (sat_cons (step898 p h) (sat_cons (step880 p h) (sat_cons (step876 p h) (sat_cons (step878 p h) (sat_cons (step879 p h) (sat_cons (step384 p h) (sat_cons (step385 p h) (sat_cons (step386 p h) (sat_cons (step897 p h) (sat_cons (step904 p h) (sat_cons (step918 p h) (sat_cons (step920 p h) (sat_cons (step953 p h) (sat_cons (step912 p h) (sat_cons (step926 p h) (sat_cons (step935 p h) (sat_nil p))))))))))))))))))))
def c1079 : List Lit := [(90, false), (83, true), (85, false), (87, true), (88, false)]
theorem step1079 (p : Nat → Bool) (h : Constraints p) : clause p c1079 = true :=
  Snake9.LocalRup.prove_clause [c280, c276] c1079 (by decide) p (sat_cons (step280 p h) (sat_cons (step276 p h) (sat_nil p)))
def c1080 : List Lit := [(93, false), (203, true), (1638, true), (83, true), (86, true), (1603, true)]
theorem step1080 (p : Nat → Bool) (h : Constraints p) : clause p c1080 = true :=
  Snake9.LocalRup.prove_clause [c821, c820, c194, c214, c315, c316, c875] c1080 (by decide) p (sat_cons (step821 p h) (sat_cons (step820 p h) (sat_cons (step194 p h) (sat_cons (step214 p h) (sat_cons (step315 p h) (sat_cons (step316 p h) (sat_cons (step875 p h) (sat_nil p))))))))
end B112E187
