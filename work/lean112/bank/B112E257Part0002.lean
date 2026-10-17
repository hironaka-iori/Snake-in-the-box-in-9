import B112E257Part0001
namespace B112E257
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1646 : List Lit := [(24, false), (823, true), (803, false), (15, true), (10, false), (32, false), (889, false), (959, false), (46, false)]
theorem step1646 (p : Nat → Bool) (h : Constraints p) : clause p c1646 = true :=
  Snake9.LocalRup.prove_clause [c1317, c846, c1644, c1595, c1278, c1314, c1091, c912, c869, c1645, c841, c127, c124, c853, c849, c858] c1646 (by decide) p (sat_cons (step1317 p h) (sat_cons (step846 p h) (sat_cons (step1644 p h) (sat_cons (step1595 p h) (sat_cons (step1278 p h) (sat_cons (step1314 p h) (sat_cons (step1091 p h) (sat_cons (step912 p h) (sat_cons (step869 p h) (sat_cons (step1645 p h) (sat_cons (step841 p h) (sat_cons (step127 p h) (sat_cons (step124 p h) (sat_cons (step853 p h) (sat_cons (step849 p h) (sat_cons (step858 p h) (sat_nil p)))))))))))))))))
def c1647 : List Lit := [(787, true), (40, false), (48, false)]
theorem step1647 (p : Nat → Bool) (h : Constraints p) : clause p c1647 = true :=
  Snake9.LocalRup.prove_clause [c558, c801, c802, c183, c26, c7] c1647 (by decide) p (sat_cons (step558 p h) (sat_cons (step801 p h) (sat_cons (step802 p h) (sat_cons (step183 p h) (sat_cons (step26 p h) (sat_cons (step7 p h) (sat_nil p)))))))
def c1648 : List Lit := [(21, false), (4, false)]
theorem step1648 (p : Nat → Bool) (h : Constraints p) : clause p c1648 = true :=
  Snake9.LocalRup.prove_clause [c566, c101, c102, c1477] c1648 (by decide) p (sat_cons (step566 p h) (sat_cons (step101 p h) (sat_cons (step102 p h) (sat_cons (step1477 p h) (sat_nil p)))))
def c1649 : List Lit := [(818, false), (24, false), (823, true), (803, false), (32, false), (889, false), (959, false)]
theorem step1649 (p : Nat → Bool) (h : Constraints p) : clause p c1649 = true :=
  Snake9.LocalRup.prove_clause [c1317, c865, c870, c912, c844, c1091, c841, c1314, c131, c1278, c1595] c1649 (by decide) p (sat_cons (step1317 p h) (sat_cons (step865 p h) (sat_cons (step870 p h) (sat_cons (step912 p h) (sat_cons (step844 p h) (sat_cons (step1091 p h) (sat_cons (step841 p h) (sat_cons (step1314 p h) (sat_cons (step131 p h) (sat_cons (step1278 p h) (sat_cons (step1595 p h) (sat_nil p))))))))))))
def c1650 : List Lit := [(15, false), (10, true), (72, false), (46, false)]
theorem step1650 (p : Nat → Bool) (h : Constraints p) : clause p c1650 = true :=
  Snake9.LocalRup.prove_clause [c563, c268, c82] c1650 (by decide) p (sat_cons (step563 p h) (sat_cons (step268 p h) (sat_cons (step82 p h) (sat_nil p))))
def c1651 : List Lit := [(1019, false), (803, false), (24, false), (814, false), (809, false), (32, false), (889, false), (951, false), (927, false)]
theorem step1651 (p : Nat → Bool) (h : Constraints p) : clause p c1651 = true :=
  Snake9.LocalRup.prove_clause [c1317, c855, c868, c911, c1083, c1313, c1129, c1181, c1278, c1285, c1314, c1187, c1091, c1134, c912, c1112, c869, c136, c858, c849] c1651 (by decide) p (sat_cons (step1317 p h) (sat_cons (step855 p h) (sat_cons (step868 p h) (sat_cons (step911 p h) (sat_cons (step1083 p h) (sat_cons (step1313 p h) (sat_cons (step1129 p h) (sat_cons (step1181 p h) (sat_cons (step1278 p h) (sat_cons (step1285 p h) (sat_cons (step1314 p h) (sat_cons (step1187 p h) (sat_cons (step1091 p h) (sat_cons (step1134 p h) (sat_cons (step912 p h) (sat_cons (step1112 p h) (sat_cons (step869 p h) (sat_cons (step136 p h) (sat_cons (step858 p h) (sat_cons (step849 p h) (sat_nil p)))))))))))))))))))))
def c1652 : List Lit := [(89, false), (24, false), (818, true), (28, true), (32, false)]
theorem step1652 (p : Nat → Bool) (h : Constraints p) : clause p c1652 = true :=
  Snake9.LocalRup.prove_clause [c140, c137, c854, c849, c859] c1652 (by decide) p (sat_cons (step140 p h) (sat_cons (step137 p h) (sat_cons (step854 p h) (sat_cons (step849 p h) (sat_cons (step859 p h) (sat_nil p))))))
def c1653 : List Lit := [(6, false), (24, false), (124, true), (32, false), (44, true)]
theorem step1653 (p : Nat → Bool) (h : Constraints p) : clause p c1653 = true :=
  Snake9.LocalRup.prove_clause [c559, c31, c118, c36] c1653 (by decide) p (sat_cons (step559 p h) (sat_cons (step31 p h) (sat_cons (step118 p h) (sat_cons (step36 p h) (sat_nil p)))))
def c1654 : List Lit := [(815, false), (823, true), (24, false), (818, true), (15, true), (32, false)]
theorem step1654 (p : Nat → Bool) (h : Constraints p) : clause p c1654 = true :=
  Snake9.LocalRup.prove_clause [c856, c859, c874, c849, c847, c124, c841] c1654 (by decide) p (sat_cons (step856 p h) (sat_cons (step859 p h) (sat_cons (step874 p h) (sat_cons (step849 p h) (sat_cons (step847 p h) (sat_cons (step124 p h) (sat_cons (step841 p h) (sat_nil p))))))))
def c1655 : List Lit := [(24, true), (1037, true), (72, false), (32, false), (951, false), (927, false)]
theorem step1655 (p : Nat → Bool) (h : Constraints p) : clause p c1655 = true :=
  Snake9.LocalRup.prove_clause [c596, c571, c487, c166, c1595, c423, c1285, c1112, c1187, c1134] c1655 (by decide) p (sat_cons (step596 p h) (sat_cons (step571 p h) (sat_cons (step487 p h) (sat_cons (step166 p h) (sat_cons (step1595 p h) (sat_cons (step423 p h) (sat_cons (step1285 p h) (sat_cons (step1112 p h) (sat_cons (step1187 p h) (sat_cons (step1134 p h) (sat_nil p)))))))))))
def c1656 : List Lit := [(89, false), (15, true), (28, true), (24, false), (890, false), (32, false), (794, false), (951, false), (927, false)]
theorem step1656 (p : Nat → Bool) (h : Constraints p) : clause p c1656 = true :=
  Snake9.LocalRup.prove_clause [c1317, c131, c121, c142, c1652, c841, c810, c1112, c847, c818, c1134, c875, c824, c1187, c899, c1563, c1092, c1315] c1656 (by decide) p (sat_cons (step1317 p h) (sat_cons (step131 p h) (sat_cons (step121 p h) (sat_cons (step142 p h) (sat_cons (step1652 p h) (sat_cons (step841 p h) (sat_cons (step810 p h) (sat_cons (step1112 p h) (sat_cons (step847 p h) (sat_cons (step818 p h) (sat_cons (step1134 p h) (sat_cons (step875 p h) (sat_cons (step824 p h) (sat_cons (step1187 p h) (sat_cons (step899 p h) (sat_cons (step1563 p h) (sat_cons (step1092 p h) (sat_cons (step1315 p h) (sat_nil p)))))))))))))))))))
def c1657 : List Lit := [(15, true), (28, true), (24, false), (1037, true), (890, false), (32, false), (794, false), (951, false), (927, false)]
theorem step1657 (p : Nat → Bool) (h : Constraints p) : clause p c1657 = true :=
  Snake9.LocalRup.prove_clause [c1317, c815, c823, c1129, c1181, c1656, c1595, c1278, c1285, c1314, c1187, c1084, c1134, c891, c1112, c136, c130, c139, c849, c841, c854, c847, c859, c875] c1657 (by decide) p (sat_cons (step1317 p h) (sat_cons (step815 p h) (sat_cons (step823 p h) (sat_cons (step1129 p h) (sat_cons (step1181 p h) (sat_cons (step1656 p h) (sat_cons (step1595 p h) (sat_cons (step1278 p h) (sat_cons (step1285 p h) (sat_cons (step1314 p h) (sat_cons (step1187 p h) (sat_cons (step1084 p h) (sat_cons (step1134 p h) (sat_cons (step891 p h) (sat_cons (step1112 p h) (sat_cons (step136 p h) (sat_cons (step130 p h) (sat_cons (step139 p h) (sat_cons (step849 p h) (sat_cons (step841 p h) (sat_cons (step854 p h) (sat_cons (step847 p h) (sat_cons (step859 p h) (sat_cons (step875 p h) (sat_nil p)))))))))))))))))))))))))
def c1658 : List Lit := [(89, false), (24, false), (795, false), (789, false), (28, true), (32, false), (889, false), (951, false), (927, false)]
theorem step1658 (p : Nat → Bool) (h : Constraints p) : clause p c1658 = true :=
  Snake9.LocalRup.prove_clause [c1317, c131, c121, c142, c1652, c841, c810, c1112, c844, c819, c1134, c870, c830, c1187, c913, c1563, c1098, c1315] c1658 (by decide) p (sat_cons (step1317 p h) (sat_cons (step131 p h) (sat_cons (step121 p h) (sat_cons (step142 p h) (sat_cons (step1652 p h) (sat_cons (step841 p h) (sat_cons (step810 p h) (sat_cons (step1112 p h) (sat_cons (step844 p h) (sat_cons (step819 p h) (sat_cons (step1134 p h) (sat_cons (step870 p h) (sat_cons (step830 p h) (sat_cons (step1187 p h) (sat_cons (step913 p h) (sat_cons (step1563 p h) (sat_cons (step1098 p h) (sat_cons (step1315 p h) (sat_nil p)))))))))))))))))))
def c1659 : List Lit := [(809, false), (1019, false), (24, false), (797, false), (1, true), (28, true), (72, false), (32, false), (1039, true), (889, false), (951, false), (927, false)]
theorem step1659 (p : Nat → Bool) (h : Constraints p) : clause p c1659 = true :=
  Snake9.LocalRup.prove_clause [c1317, c806, c829, c1129, c1181, c1278, c1314, c1091, c905, c852, c1651, c870, c834, c1637, c807, c1648, c801] c1659 (by decide) p (sat_cons (step1317 p h) (sat_cons (step806 p h) (sat_cons (step829 p h) (sat_cons (step1129 p h) (sat_cons (step1181 p h) (sat_cons (step1278 p h) (sat_cons (step1314 p h) (sat_cons (step1091 p h) (sat_cons (step905 p h) (sat_cons (step852 p h) (sat_cons (step1651 p h) (sat_cons (step870 p h) (sat_cons (step834 p h) (sat_cons (step1637 p h) (sat_cons (step807 p h) (sat_cons (step1648 p h) (sat_cons (step801 p h) (sat_nil p))))))))))))))))))
def c1660 : List Lit := [(24, false), (795, false), (1, true), (28, true), (72, false), (32, false), (1039, true), (889, false), (951, false), (927, false)]
theorem step1660 (p : Nat → Bool) (h : Constraints p) : clause p c1660 = true :=
  Snake9.LocalRup.prove_clause [c1317, c806, c816, c829, c1129, c1181, c1658, c1595, c1278, c1314, c1091, c905, c1659, c844, c841, c127, c124, c111, c854, c849, c810, c859, c819, c1649, c830] c1660 (by decide) p (sat_cons (step1317 p h) (sat_cons (step806 p h) (sat_cons (step816 p h) (sat_cons (step829 p h) (sat_cons (step1129 p h) (sat_cons (step1181 p h) (sat_cons (step1658 p h) (sat_cons (step1595 p h) (sat_cons (step1278 p h) (sat_cons (step1314 p h) (sat_cons (step1091 p h) (sat_cons (step905 p h) (sat_cons (step1659 p h) (sat_cons (step844 p h) (sat_cons (step841 p h) (sat_cons (step127 p h) (sat_cons (step124 p h) (sat_cons (step111 p h) (sat_cons (step854 p h) (sat_cons (step849 p h) (sat_cons (step810 p h) (sat_cons (step859 p h) (sat_cons (step819 p h) (sat_cons (step1649 p h) (sat_cons (step830 p h) (sat_nil p))))))))))))))))))))))))))
def c1661 : List Lit := [(15, false), (72, false), (32, false), (1039, true), (889, false), (951, false), (46, false)]
theorem step1661 (p : Nat → Bool) (h : Constraints p) : clause p c1661 = true :=
  Snake9.LocalRup.prove_clause [c559, c1317, c1617, c1650, c63, c61, c52, c58, c852, c806, c814, c1660, c30, c1632, c1655, c810, c849, c1313, c819, c858, c1083, c830, c864, c911] c1661 (by decide) p (sat_cons (step559 p h) (sat_cons (step1317 p h) (sat_cons (step1617 p h) (sat_cons (step1650 p h) (sat_cons (step63 p h) (sat_cons (step61 p h) (sat_cons (step52 p h) (sat_cons (step58 p h) (sat_cons (step852 p h) (sat_cons (step806 p h) (sat_cons (step814 p h) (sat_cons (step1660 p h) (sat_cons (step30 p h) (sat_cons (step1632 p h) (sat_cons (step1655 p h) (sat_cons (step810 p h) (sat_cons (step849 p h) (sat_cons (step1313 p h) (sat_cons (step819 p h) (sat_cons (step858 p h) (sat_cons (step1083 p h) (sat_cons (step830 p h) (sat_cons (step864 p h) (sat_cons (step911 p h) (sat_nil p)))))))))))))))))))))))))
def c1662 : List Lit := [(24, true), (1038, true), (72, false), (32, false), (940, false), (927, false)]
theorem step1662 (p : Nat → Bool) (h : Constraints p) : clause p c1662 = true :=
  Snake9.LocalRup.prove_clause [c596, c571, c594, c1164, c487, c166, c1206, c1595, c427, c423, c1217, c1291, c1235, c1112, c1551, c1134, c1553, c1187, c1188, c1286, c1165, c1258, c1261, c1157, c1554, c1220, c1156, c1241, c1207, c477, c1549, c1201, c498] c1662 (by decide) p (sat_cons (step596 p h) (sat_cons (step571 p h) (sat_cons (step594 p h) (sat_cons (step1164 p h) (sat_cons (step487 p h) (sat_cons (step166 p h) (sat_cons (step1206 p h) (sat_cons (step1595 p h) (sat_cons (step427 p h) (sat_cons (step423 p h) (sat_cons (step1217 p h) (sat_cons (step1291 p h) (sat_cons (step1235 p h) (sat_cons (step1112 p h) (sat_cons (step1551 p h) (sat_cons (step1134 p h) (sat_cons (step1553 p h) (sat_cons (step1187 p h) (sat_cons (step1188 p h) (sat_cons (step1286 p h) (sat_cons (step1165 p h) (sat_cons (step1258 p h) (sat_cons (step1261 p h) (sat_cons (step1157 p h) (sat_cons (step1554 p h) (sat_cons (step1220 p h) (sat_cons (step1156 p h) (sat_cons (step1241 p h) (sat_cons (step1207 p h) (sat_cons (step477 p h) (sat_cons (step1549 p h) (sat_cons (step1201 p h) (sat_cons (step498 p h) (sat_nil p))))))))))))))))))))))))))))))))))
def c1663 : List Lit := [(1002, false), (85, false), (1020, true), (89, true)]
theorem step1663 (p : Nat → Bool) (h : Constraints p) : clause p c1663 = true :=
  Snake9.LocalRup.prove_clause [c594, c477, c1206, c1217, c1258, c1554, c1551, c1241, c1553, c1549, c1261, c498, c1220, c1201, c1207] c1663 (by decide) p (sat_cons (step594 p h) (sat_cons (step477 p h) (sat_cons (step1206 p h) (sat_cons (step1217 p h) (sat_cons (step1258 p h) (sat_cons (step1554 p h) (sat_cons (step1551 p h) (sat_cons (step1241 p h) (sat_cons (step1553 p h) (sat_cons (step1549 p h) (sat_cons (step1261 p h) (sat_cons (step498 p h) (sat_cons (step1220 p h) (sat_cons (step1201 p h) (sat_cons (step1207 p h) (sat_nil p))))))))))))))))
def c1664 : List Lit := [(932, false), (89, true), (961, true), (1038, true), (72, false), (32, false), (940, false)]
theorem step1664 (p : Nat → Bool) (h : Constraints p) : clause p c1664 = true :=
  Snake9.LocalRup.prove_clause [c594, c593, c609, c602, c1206, c1217, c1164, c1187, c1188, c1286, c1165, c1258, c1157, c1158, c1156, c1152, c477, c471, c1663, c1235, c427, c549, c548, c541, c1549, c1240, c1248, c1546, c1225, c1226, c526, c523] c1664 (by decide) p (sat_cons (step594 p h) (sat_cons (step593 p h) (sat_cons (step609 p h) (sat_cons (step602 p h) (sat_cons (step1206 p h) (sat_cons (step1217 p h) (sat_cons (step1164 p h) (sat_cons (step1187 p h) (sat_cons (step1188 p h) (sat_cons (step1286 p h) (sat_cons (step1165 p h) (sat_cons (step1258 p h) (sat_cons (step1157 p h) (sat_cons (step1158 p h) (sat_cons (step1156 p h) (sat_cons (step1152 p h) (sat_cons (step477 p h) (sat_cons (step471 p h) (sat_cons (step1663 p h) (sat_cons (step1235 p h) (sat_cons (step427 p h) (sat_cons (step549 p h) (sat_cons (step548 p h) (sat_cons (step541 p h) (sat_cons (step1549 p h) (sat_cons (step1240 p h) (sat_cons (step1248 p h) (sat_cons (step1546 p h) (sat_cons (step1225 p h) (sat_cons (step1226 p h) (sat_cons (step526 p h) (sat_cons (step523 p h) (sat_nil p)))))))))))))))))))))))))))))))))
def c1665 : List Lit := [(62, false), (833, true), (24, false), (15, true), (32, false), (794, false)]
theorem step1665 (p : Nat → Bool) (h : Constraints p) : clause p c1665 = true :=
  Snake9.LocalRup.prove_clause [c120, c136, c130, c139, c810, c849, c841, c853, c818, c847, c858, c824, c874, c899, c905, c875, c829, c861, c804, c851, c801, c1648] c1665 (by decide) p (sat_cons (step120 p h) (sat_cons (step136 p h) (sat_cons (step130 p h) (sat_cons (step139 p h) (sat_cons (step810 p h) (sat_cons (step849 p h) (sat_cons (step841 p h) (sat_cons (step853 p h) (sat_cons (step818 p h) (sat_cons (step847 p h) (sat_cons (step858 p h) (sat_cons (step824 p h) (sat_cons (step874 p h) (sat_cons (step899 p h) (sat_cons (step905 p h) (sat_cons (step875 p h) (sat_cons (step829 p h) (sat_cons (step861 p h) (sat_cons (step804 p h) (sat_cons (step851 p h) (sat_cons (step801 p h) (sat_cons (step1648 p h) (sat_nil p)))))))))))))))))))))))
def c1666 : List Lit := [(1019, false), (15, true), (1038, true), (72, false), (32, false), (889, false), (794, false), (940, false), (927, false)]
theorem step1666 (p : Nat → Bool) (h : Constraints p) : clause p c1666 = true :=
  Snake9.LocalRup.prove_clause [c1317, c1662, c1129, c1164, c1181, c1278, c1291, c1314, c1091, c1665, c1112, c1134, c1187, c1664, c1285, c121, c1644, c1313, c810, c1083, c818, c898, c824] c1666 (by decide) p (sat_cons (step1317 p h) (sat_cons (step1662 p h) (sat_cons (step1129 p h) (sat_cons (step1164 p h) (sat_cons (step1181 p h) (sat_cons (step1278 p h) (sat_cons (step1291 p h) (sat_cons (step1314 p h) (sat_cons (step1091 p h) (sat_cons (step1665 p h) (sat_cons (step1112 p h) (sat_cons (step1134 p h) (sat_cons (step1187 p h) (sat_cons (step1664 p h) (sat_cons (step1285 p h) (sat_cons (step121 p h) (sat_cons (step1644 p h) (sat_cons (step1313 p h) (sat_cons (step810 p h) (sat_cons (step1083 p h) (sat_cons (step818 p h) (sat_cons (step898 p h) (sat_cons (step824 p h) (sat_nil p))))))))))))))))))))))))
def c1667 : List Lit := [(72, false), (32, false), (1039, true), (889, false), (794, false), (940, false), (47, true), (46, false)]
theorem step1667 (p : Nat → Bool) (h : Constraints p) : clause p c1667 = true :=
  Snake9.LocalRup.prove_clause [c596, c602, c1317, c1164, c1617, c1640, c1073, c1312, c1661, c1662, c1666, c1595, c1622, c486, c121, c142, c1644, c1546, c810, c1112, c1225, c1226, c818, c1134, c488, c523, c824, c1152, c519, c898, c1158, c1549, c1083, c1165, c1240, c1313, c1188, c1553, c1290, c1253] c1667 (by decide) p (sat_cons (step596 p h) (sat_cons (step602 p h) (sat_cons (step1317 p h) (sat_cons (step1164 p h) (sat_cons (step1617 p h) (sat_cons (step1640 p h) (sat_cons (step1073 p h) (sat_cons (step1312 p h) (sat_cons (step1661 p h) (sat_cons (step1662 p h) (sat_cons (step1666 p h) (sat_cons (step1595 p h) (sat_cons (step1622 p h) (sat_cons (step486 p h) (sat_cons (step121 p h) (sat_cons (step142 p h) (sat_cons (step1644 p h) (sat_cons (step1546 p h) (sat_cons (step810 p h) (sat_cons (step1112 p h) (sat_cons (step1225 p h) (sat_cons (step1226 p h) (sat_cons (step818 p h) (sat_cons (step1134 p h) (sat_cons (step488 p h) (sat_cons (step523 p h) (sat_cons (step824 p h) (sat_cons (step1152 p h) (sat_cons (step519 p h) (sat_cons (step898 p h) (sat_cons (step1158 p h) (sat_cons (step1549 p h) (sat_cons (step1083 p h) (sat_cons (step1165 p h) (sat_cons (step1240 p h) (sat_cons (step1313 p h) (sat_cons (step1188 p h) (sat_cons (step1553 p h) (sat_cons (step1290 p h) (sat_cons (step1253 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))
def c1668 : List Lit := [(932, false), (1038, true), (941, false)]
theorem step1668 (p : Nat → Bool) (h : Constraints p) : clause p c1668 = true :=
  Snake9.LocalRup.prove_clause [c596, c602, c1167, c1188, c1291, c1595, c1622, c486, c1546, c1225, c1226, c488, c523, c1152, c519, c1158, c1549, c1168, c1240, c1189, c1553, c1296, c1253] c1668 (by decide) p (sat_cons (step596 p h) (sat_cons (step602 p h) (sat_cons (step1167 p h) (sat_cons (step1188 p h) (sat_cons (step1291 p h) (sat_cons (step1595 p h) (sat_cons (step1622 p h) (sat_cons (step486 p h) (sat_cons (step1546 p h) (sat_cons (step1225 p h) (sat_cons (step1226 p h) (sat_cons (step488 p h) (sat_cons (step523 p h) (sat_cons (step1152 p h) (sat_cons (step519 p h) (sat_cons (step1158 p h) (sat_cons (step1549 p h) (sat_cons (step1168 p h) (sat_cons (step1240 p h) (sat_cons (step1189 p h) (sat_cons (step1553 p h) (sat_cons (step1296 p h) (sat_cons (step1253 p h) (sat_nil p))))))))))))))))))))))))
def c1669 : List Lit := [(89, false), (62, false), (32, false)]
theorem step1669 (p : Nat → Bool) (h : Constraints p) : clause p c1669 = true :=
  Snake9.LocalRup.prove_clause [c596, c487, c142] c1669 (by decide) p (sat_cons (step596 p h) (sat_cons (step487 p h) (sat_cons (step142 p h) (sat_nil p))))
def c1670 : List Lit := [(1038, true), (941, false), (32, false), (927, false)]
theorem step1670 (p : Nat → Bool) (h : Constraints p) : clause p c1670 = true :=
  Snake9.LocalRup.prove_clause [c594, c593, c609, c602, c1129, c1167, c1182, c1286, c1668, c1134, c1112, c1669, c1206, c1595, c1217, c1291, c1258, c1183, c1168, c1157, c1158, c1156, c1152, c477, c1663, c471, c1235, c425, c548, c549, c541, c1549, c1240, c1248, c1546, c1225, c1226, c526, c523] c1670 (by decide) p (sat_cons (step594 p h) (sat_cons (step593 p h) (sat_cons (step609 p h) (sat_cons (step602 p h) (sat_cons (step1129 p h) (sat_cons (step1167 p h) (sat_cons (step1182 p h) (sat_cons (step1286 p h) (sat_cons (step1668 p h) (sat_cons (step1134 p h) (sat_cons (step1112 p h) (sat_cons (step1669 p h) (sat_cons (step1206 p h) (sat_cons (step1595 p h) (sat_cons (step1217 p h) (sat_cons (step1291 p h) (sat_cons (step1258 p h) (sat_cons (step1183 p h) (sat_cons (step1168 p h) (sat_cons (step1157 p h) (sat_cons (step1158 p h) (sat_cons (step1156 p h) (sat_cons (step1152 p h) (sat_cons (step477 p h) (sat_cons (step1663 p h) (sat_cons (step471 p h) (sat_cons (step1235 p h) (sat_cons (step425 p h) (sat_cons (step548 p h) (sat_cons (step549 p h) (sat_cons (step541 p h) (sat_cons (step1549 p h) (sat_cons (step1240 p h) (sat_cons (step1248 p h) (sat_cons (step1546 p h) (sat_cons (step1225 p h) (sat_cons (step1226 p h) (sat_cons (step526 p h) (sat_cons (step523 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))
def c1671 : List Lit := [(36, true), (10, true), (1, false)]
theorem step1671 (p : Nat → Bool) (h : Constraints p) : clause p c1671 = true :=
  Snake9.LocalRup.prove_clause [c557, c2] c1671 (by decide) p (sat_cons (step557 p h) (sat_cons (step2 p h) (sat_nil p)))
def c1672 : List Lit := [(36, true), (3, true), (1, false)]
theorem step1672 (p : Nat → Bool) (h : Constraints p) : clause p c1672 = true :=
  Snake9.LocalRup.prove_clause [c557, c3] c1672 (by decide) p (sat_cons (step557 p h) (sat_cons (step3 p h) (sat_nil p)))
def c1673 : List Lit := [(3, true), (10, true), (1, false)]
theorem step1673 (p : Nat → Bool) (h : Constraints p) : clause p c1673 = true :=
  Snake9.LocalRup.prove_clause [c557, c4] c1673 (by decide) p (sat_cons (step557 p h) (sat_cons (step4 p h) (sat_nil p)))
def c1674 : List Lit := [(37, true), (20, true), (2, false)]
theorem step1674 (p : Nat → Bool) (h : Constraints p) : clause p c1674 = true :=
  Snake9.LocalRup.prove_clause [c558, c6] c1674 (by decide) p (sat_cons (step558 p h) (sat_cons (step6 p h) (sat_nil p)))
def c1675 : List Lit := [(37, true), (5, true), (2, false)]
theorem step1675 (p : Nat → Bool) (h : Constraints p) : clause p c1675 = true :=
  Snake9.LocalRup.prove_clause [c558, c7] c1675 (by decide) p (sat_cons (step558 p h) (sat_cons (step7 p h) (sat_nil p)))
def c1676 : List Lit := [(20, true), (2, false), (5, true)]
theorem step1676 (p : Nat → Bool) (h : Constraints p) : clause p c1676 = true :=
  Snake9.LocalRup.prove_clause [c558, c8] c1676 (by decide) p (sat_cons (step558 p h) (sat_cons (step8 p h) (sat_nil p)))
def c1677 : List Lit := [(6, false), (24, true)]
theorem step1677 (p : Nat → Bool) (h : Constraints p) : clause p c1677 = true :=
  Snake9.LocalRup.prove_clause [c559, c30] c1677 (by decide) p (sat_cons (step559 p h) (sat_cons (step30 p h) (sat_nil p)))
def c1678 : List Lit := [(6, false), (8, true)]
theorem step1678 (p : Nat → Bool) (h : Constraints p) : clause p c1678 = true :=
  Snake9.LocalRup.prove_clause [c559, c31] c1678 (by decide) p (sat_cons (step559 p h) (sat_cons (step31 p h) (sat_nil p)))
def c1679 : List Lit := [(25, true), (41, true), (7, false)]
theorem step1679 (p : Nat → Bool) (h : Constraints p) : clause p c1679 = true :=
  Snake9.LocalRup.prove_clause [c560, c32] c1679 (by decide) p (sat_cons (step560 p h) (sat_cons (step32 p h) (sat_nil p)))
def c1680 : List Lit := [(41, true), (9, true), (7, false)]
theorem step1680 (p : Nat → Bool) (h : Constraints p) : clause p c1680 = true :=
  Snake9.LocalRup.prove_clause [c560, c33] c1680 (by decide) p (sat_cons (step560 p h) (sat_cons (step33 p h) (sat_nil p)))
def c1681 : List Lit := [(25, true), (9, true), (7, false)]
theorem step1681 (p : Nat → Bool) (h : Constraints p) : clause p c1681 = true :=
  Snake9.LocalRup.prove_clause [c560, c34] c1681 (by decide) p (sat_cons (step560 p h) (sat_cons (step34 p h) (sat_nil p)))
def c1682 : List Lit := [(11, false), (10, true), (47, true)]
theorem step1682 (p : Nat → Bool) (h : Constraints p) : clause p c1682 = true :=
  Snake9.LocalRup.prove_clause [c561, c66] c1682 (by decide) p (sat_cons (step561 p h) (sat_cons (step66 p h) (sat_nil p)))
def c1683 : List Lit := [(11, false), (13, true), (10, true)]
theorem step1683 (p : Nat → Bool) (h : Constraints p) : clause p c1683 = true :=
  Snake9.LocalRup.prove_clause [c561, c67] c1683 (by decide) p (sat_cons (step561 p h) (sat_cons (step67 p h) (sat_nil p)))
def c1684 : List Lit := [(29, true), (14, true), (12, false)]
theorem step1684 (p : Nat → Bool) (h : Constraints p) : clause p c1684 = true :=
  Snake9.LocalRup.prove_clause [c562, c68] c1684 (by decide) p (sat_cons (step562 p h) (sat_cons (step68 p h) (sat_nil p)))
def c1685 : List Lit := [(29, true), (12, false), (10, true)]
theorem step1685 (p : Nat → Bool) (h : Constraints p) : clause p c1685 = true :=
  Snake9.LocalRup.prove_clause [c562, c69] c1685 (by decide) p (sat_cons (step562 p h) (sat_cons (step69 p h) (sat_nil p)))
def c1686 : List Lit := [(14, true), (10, true), (12, false)]
theorem step1686 (p : Nat → Bool) (h : Constraints p) : clause p c1686 = true :=
  Snake9.LocalRup.prove_clause [c562, c70] c1686 (by decide) p (sat_cons (step562 p h) (sat_cons (step70 p h) (sat_nil p)))
def c1687 : List Lit := [(17, true), (51, true), (15, false)]
theorem step1687 (p : Nat → Bool) (h : Constraints p) : clause p c1687 = true :=
  Snake9.LocalRup.prove_clause [c563, c81] c1687 (by decide) p (sat_cons (step563 p h) (sat_cons (step81 p h) (sat_nil p)))
def c1688 : List Lit := [(51, true), (10, true), (15, false)]
theorem step1688 (p : Nat → Bool) (h : Constraints p) : clause p c1688 = true :=
  Snake9.LocalRup.prove_clause [c563, c82] c1688 (by decide) p (sat_cons (step563 p h) (sat_cons (step82 p h) (sat_nil p)))
def c1689 : List Lit := [(17, true), (10, true), (15, false)]
theorem step1689 (p : Nat → Bool) (h : Constraints p) : clause p c1689 = true :=
  Snake9.LocalRup.prove_clause [c563, c83] c1689 (by decide) p (sat_cons (step563 p h) (sat_cons (step83 p h) (sat_nil p)))
def c1690 : List Lit := [(33, true), (53, true), (16, false)]
theorem step1690 (p : Nat → Bool) (h : Constraints p) : clause p c1690 = true :=
  Snake9.LocalRup.prove_clause [c564, c84] c1690 (by decide) p (sat_cons (step564 p h) (sat_cons (step84 p h) (sat_nil p)))
def c1691 : List Lit := [(53, true), (18, true), (16, false)]
theorem step1691 (p : Nat → Bool) (h : Constraints p) : clause p c1691 = true :=
  Snake9.LocalRup.prove_clause [c564, c85] c1691 (by decide) p (sat_cons (step564 p h) (sat_cons (step85 p h) (sat_nil p)))
def c1692 : List Lit := [(33, true), (18, true), (16, false)]
theorem step1692 (p : Nat → Bool) (h : Constraints p) : clause p c1692 = true :=
  Snake9.LocalRup.prove_clause [c564, c86] c1692 (by decide) p (sat_cons (step564 p h) (sat_cons (step86 p h) (sat_nil p)))
def c1693 : List Lit := [(57, true), (19, false), (24, true)]
theorem step1693 (p : Nat → Bool) (h : Constraints p) : clause p c1693 = true :=
  Snake9.LocalRup.prove_clause [c565, c95] c1693 (by decide) p (sat_cons (step565 p h) (sat_cons (step95 p h) (sat_nil p)))
def c1694 : List Lit := [(20, true), (57, true), (19, false)]
theorem step1694 (p : Nat → Bool) (h : Constraints p) : clause p c1694 = true :=
  Snake9.LocalRup.prove_clause [c565, c96] c1694 (by decide) p (sat_cons (step565 p h) (sat_cons (step96 p h) (sat_nil p)))
def c1695 : List Lit := [(19, false), (20, true), (24, true)]
theorem step1695 (p : Nat → Bool) (h : Constraints p) : clause p c1695 = true :=
  Snake9.LocalRup.prove_clause [c565, c97] c1695 (by decide) p (sat_cons (step565 p h) (sat_cons (step97 p h) (sat_nil p)))
def c1696 : List Lit := [(21, false), (22, true)]
theorem step1696 (p : Nat → Bool) (h : Constraints p) : clause p c1696 = true :=
  Snake9.LocalRup.prove_clause [c566, c101] c1696 (by decide) p (sat_cons (step566 p h) (sat_cons (step101 p h) (sat_nil p)))
def c1697 : List Lit := [(21, false), (3, true)]
theorem step1697 (p : Nat → Bool) (h : Constraints p) : clause p c1697 = true :=
  Snake9.LocalRup.prove_clause [c566, c102] c1697 (by decide) p (sat_cons (step566 p h) (sat_cons (step102 p h) (sat_nil p)))
def c1698 : List Lit := [(25, true), (23, false), (61, true)]
theorem step1698 (p : Nat → Bool) (h : Constraints p) : clause p c1698 = true :=
  Snake9.LocalRup.prove_clause [c567, c106] c1698 (by decide) p (sat_cons (step567 p h) (sat_cons (step106 p h) (sat_nil p)))
def c1699 : List Lit := [(23, false), (24, true), (61, true)]
theorem step1699 (p : Nat → Bool) (h : Constraints p) : clause p c1699 = true :=
  Snake9.LocalRup.prove_clause [c567, c107] c1699 (by decide) p (sat_cons (step567 p h) (sat_cons (step107 p h) (sat_nil p)))
def c1700 : List Lit := [(25, true), (23, false), (24, true)]
theorem step1700 (p : Nat → Bool) (h : Constraints p) : clause p c1700 = true :=
  Snake9.LocalRup.prove_clause [c567, c108] c1700 (by decide) p (sat_cons (step567 p h) (sat_cons (step108 p h) (sat_nil p)))
def c1701 : List Lit := [(27, true), (65, true), (26, false), (24, true)]
theorem step1701 (p : Nat → Bool) (h : Constraints p) : clause p c1701 = true :=
  Snake9.LocalRup.prove_clause [c568, c148] c1701 (by decide) p (sat_cons (step568 p h) (sat_cons (step148 p h) (sat_nil p)))
def c1702 : List Lit := [(65, true), (26, false), (8, true), (24, true)]
theorem step1702 (p : Nat → Bool) (h : Constraints p) : clause p c1702 = true :=
  Snake9.LocalRup.prove_clause [c568, c149] c1702 (by decide) p (sat_cons (step568 p h) (sat_cons (step149 p h) (sat_nil p)))
def c1703 : List Lit := [(27, true), (26, false), (24, true), (8, true)]
theorem step1703 (p : Nat → Bool) (h : Constraints p) : clause p c1703 = true :=
  Snake9.LocalRup.prove_clause [c568, c150] c1703 (by decide) p (sat_cons (step568 p h) (sat_cons (step150 p h) (sat_nil p)))
def c1704 : List Lit := [(29, true), (28, false), (67, true)]
theorem step1704 (p : Nat → Bool) (h : Constraints p) : clause p c1704 = true :=
  Snake9.LocalRup.prove_clause [c569, c153] c1704 (by decide) p (sat_cons (step569 p h) (sat_cons (step153 p h) (sat_nil p)))
def c1705 : List Lit := [(67, true), (10, true), (28, false)]
theorem step1705 (p : Nat → Bool) (h : Constraints p) : clause p c1705 = true :=
  Snake9.LocalRup.prove_clause [c569, c154] c1705 (by decide) p (sat_cons (step569 p h) (sat_cons (step154 p h) (sat_nil p)))
def c1706 : List Lit := [(29, true), (28, false), (10, true)]
theorem step1706 (p : Nat → Bool) (h : Constraints p) : clause p c1706 = true :=
  Snake9.LocalRup.prove_clause [c569, c155] c1706 (by decide) p (sat_cons (step569 p h) (sat_cons (step155 p h) (sat_nil p)))
def c1707 : List Lit := [(30, false), (31, true)]
theorem step1707 (p : Nat → Bool) (h : Constraints p) : clause p c1707 = true :=
  Snake9.LocalRup.prove_clause [c570, c160] c1707 (by decide) p (sat_cons (step570 p h) (sat_cons (step160 p h) (sat_nil p)))
def c1708 : List Lit := [(30, false), (13, true)]
theorem step1708 (p : Nat → Bool) (h : Constraints p) : clause p c1708 = true :=
  Snake9.LocalRup.prove_clause [c570, c161] c1708 (by decide) p (sat_cons (step570 p h) (sat_cons (step161 p h) (sat_nil p)))
def c1709 : List Lit := [(73, true), (33, true), (32, false)]
theorem step1709 (p : Nat → Bool) (h : Constraints p) : clause p c1709 = true :=
  Snake9.LocalRup.prove_clause [c571, c165] c1709 (by decide) p (sat_cons (step571 p h) (sat_cons (step165 p h) (sat_nil p)))
end B112E257
