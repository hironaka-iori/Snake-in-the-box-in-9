import B112E026Part0055
namespace B112E026
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c4986 : List Lit := [(1641, true)]
theorem step4986 (p : Nat → Bool) (h : Constraints p) : clause p c4986 = true :=
  Snake9.LocalRup.prove_clause [c4983, c4905, c1736] c4986 (by decide) p (sat_cons (step4983 p h) (sat_cons (step4905 p h) (sat_cons (step1736 p h) (sat_nil p))))
def c4987 : List Lit := [(1656, false)]
theorem step4987 (p : Nat → Bool) (h : Constraints p) : clause p c4987 = true :=
  Snake9.LocalRup.prove_clause [c4984, c4686, c1189] c4987 (by decide) p (sat_cons (step4984 p h) (sat_cons (step4686 p h) (sat_cons (step1189 p h) (sat_nil p))))
def c4988 : List Lit := [(105, true), (89, false)]
theorem step4988 (p : Nat → Bool) (h : Constraints p) : clause p c4988 = true :=
  Snake9.TreeRup.prove_clause [c4810, c4978, c4975, c4687, c4982, c4981, c4686, c4985, c4434, c4950, c4954, c4953, c4974, c4976, c4904, c4983, c4905, c4685, c4918, c1517, c4412, c1714, c4923, c1196, c1198, c1202, c1963, c1213, c4736, c1218, c1282, c1283, c3685, c1188, c1337, c2187, c1182, c3000, c1162, c1732, c3641, c1638, c1146, c1663, c3827, c1745, c1081, c1632, c1075, c2795, c1604, c602, c1244, c1253, c1247, c612, c1110, c1422, c1117, c1142, c1420, c1167, c1101, c1091, c1093, c1754, c1089, c1086, c830, c1683, c269, c1684, c825, c1615, c750, c804, c1613, c746, c802, c768, c742, c801, c769, c741, c797, c775, c736, c566, c781, c735, c2351, c1679, c4759, c382, c767, c422, c760, c1231, c756, c1240, c755, c1235, c253, c4845, c1593, c217] c4988 (by decide) p (sat_cons (step4810 p h) (sat_cons (step4978 p h) (sat_cons (step4975 p h) (sat_cons (step4687 p h) (sat_cons (step4982 p h) (sat_cons (step4981 p h) (sat_cons (step4686 p h) (sat_cons (step4985 p h) (sat_cons (step4434 p h) (sat_cons (step4950 p h) (sat_cons (step4954 p h) (sat_cons (step4953 p h) (sat_cons (step4974 p h) (sat_cons (step4976 p h) (sat_cons (step4904 p h) (sat_cons (step4983 p h) (sat_cons (step4905 p h) (sat_cons (step4685 p h) (sat_cons (step4918 p h) (sat_cons (step1517 p h) (sat_cons (step4412 p h) (sat_cons (step1714 p h) (sat_cons (step4923 p h) (sat_cons (step1196 p h) (sat_cons (step1198 p h) (sat_cons (step1202 p h) (sat_cons (step1963 p h) (sat_cons (step1213 p h) (sat_cons (step4736 p h) (sat_cons (step1218 p h) (sat_cons (step1282 p h) (sat_cons (step1283 p h) (sat_cons (step3685 p h) (sat_cons (step1188 p h) (sat_cons (step1337 p h) (sat_cons (step2187 p h) (sat_cons (step1182 p h) (sat_cons (step3000 p h) (sat_cons (step1162 p h) (sat_cons (step1732 p h) (sat_cons (step3641 p h) (sat_cons (step1638 p h) (sat_cons (step1146 p h) (sat_cons (step1663 p h) (sat_cons (step3827 p h) (sat_cons (step1745 p h) (sat_cons (step1081 p h) (sat_cons (step1632 p h) (sat_cons (step1075 p h) (sat_cons (step2795 p h) (sat_cons (step1604 p h) (sat_cons (step602 p h) (sat_cons (step1244 p h) (sat_cons (step1253 p h) (sat_cons (step1247 p h) (sat_cons (step612 p h) (sat_cons (step1110 p h) (sat_cons (step1422 p h) (sat_cons (step1117 p h) (sat_cons (step1142 p h) (sat_cons (step1420 p h) (sat_cons (step1167 p h) (sat_cons (step1101 p h) (sat_cons (step1091 p h) (sat_cons (step1093 p h) (sat_cons (step1754 p h) (sat_cons (step1089 p h) (sat_cons (step1086 p h) (sat_cons (step830 p h) (sat_cons (step1683 p h) (sat_cons (step269 p h) (sat_cons (step1684 p h) (sat_cons (step825 p h) (sat_cons (step1615 p h) (sat_cons (step750 p h) (sat_cons (step804 p h) (sat_cons (step1613 p h) (sat_cons (step746 p h) (sat_cons (step802 p h) (sat_cons (step768 p h) (sat_cons (step742 p h) (sat_cons (step801 p h) (sat_cons (step769 p h) (sat_cons (step741 p h) (sat_cons (step797 p h) (sat_cons (step775 p h) (sat_cons (step736 p h) (sat_cons (step566 p h) (sat_cons (step781 p h) (sat_cons (step735 p h) (sat_cons (step2351 p h) (sat_cons (step1679 p h) (sat_cons (step4759 p h) (sat_cons (step382 p h) (sat_cons (step767 p h) (sat_cons (step422 p h) (sat_cons (step760 p h) (sat_cons (step1231 p h) (sat_cons (step756 p h) (sat_cons (step1240 p h) (sat_cons (step755 p h) (sat_cons (step1235 p h) (sat_cons (step253 p h) (sat_cons (step4845 p h) (sat_cons (step1593 p h) (sat_cons (step217 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c4989 : List Lit := [(89, false)]
theorem step4989 (p : Nat → Bool) (h : Constraints p) : clause p c4989 = true :=
  Snake9.LocalRup.prove_clause [c4810, c4986, c4904, c4950, c4975, c4974, c4686, c4918, c1517, c4402, c4412, c1713, c1714, c1326, c1325, c4988, c2419, c1528, c3659] c4989 (by decide) p (sat_cons (step4810 p h) (sat_cons (step4986 p h) (sat_cons (step4904 p h) (sat_cons (step4950 p h) (sat_cons (step4975 p h) (sat_cons (step4974 p h) (sat_cons (step4686 p h) (sat_cons (step4918 p h) (sat_cons (step1517 p h) (sat_cons (step4402 p h) (sat_cons (step4412 p h) (sat_cons (step1713 p h) (sat_cons (step1714 p h) (sat_cons (step1326 p h) (sat_cons (step1325 p h) (sat_cons (step4988 p h) (sat_cons (step2419 p h) (sat_cons (step1528 p h) (sat_cons (step3659 p h) (sat_nil p))))))))))))))))))))
def c4990 : List Lit := [(1642, true)]
theorem step4990 (p : Nat → Bool) (h : Constraints p) : clause p c4990 = true :=
  Snake9.LocalRup.prove_clause [c4989, c4982, c4983, c4974, c4975, c4906] c4990 (by decide) p (sat_cons (step4989 p h) (sat_cons (step4982 p h) (sat_cons (step4983 p h) (sat_cons (step4974 p h) (sat_cons (step4975 p h) (sat_cons (step4906 p h) (sat_nil p)))))))
def c4991 : List Lit := [(1682, false), (95, false)]
theorem step4991 (p : Nat → Bool) (h : Constraints p) : clause p c4991 = true :=
  Snake9.LocalRup.prove_clause [c4810, c4983, c4990, c4989, c4982, c4974, c4434, c4986, c3624, c4907, c1714, c1517, c4412] c4991 (by decide) p (sat_cons (step4810 p h) (sat_cons (step4983 p h) (sat_cons (step4990 p h) (sat_cons (step4989 p h) (sat_cons (step4982 p h) (sat_cons (step4974 p h) (sat_cons (step4434 p h) (sat_cons (step4986 p h) (sat_cons (step3624 p h) (sat_cons (step4907 p h) (sat_cons (step1714 p h) (sat_cons (step1517 p h) (sat_cons (step4412 p h) (sat_nil p))))))))))))))
def c4992 : List Lit := [(1682, false)]
theorem step4992 (p : Nat → Bool) (h : Constraints p) : clause p c4992 = true :=
  Snake9.LocalRup.prove_clause [c4950, c4686, c4975, c1528, c4991] c4992 (by decide) p (sat_cons (step4950 p h) (sat_cons (step4686 p h) (sat_cons (step4975 p h) (sat_cons (step1528 p h) (sat_cons (step4991 p h) (sat_nil p))))))
def c4993 : List Lit := [(1678, false)]
theorem step4993 (p : Nat → Bool) (h : Constraints p) : clause p c4993 = true :=
  Snake9.LocalRup.prove_clause [c4992, c1242] c4993 (by decide) p (sat_cons (step4992 p h) (sat_cons (step1242 p h) (sat_nil p)))
def c4994 : List Lit := [(102, false), (95, false)]
theorem step4994 (p : Nat → Bool) (h : Constraints p) : clause p c4994 = true :=
  Snake9.LocalRup.prove_clause [c4977, c4950, c4686, c4976, c4987, c1397, c1886, c3962, c2187, c1188, c1283, c1217] c4994 (by decide) p (sat_cons (step4977 p h) (sat_cons (step4950 p h) (sat_cons (step4686 p h) (sat_cons (step4976 p h) (sat_cons (step4987 p h) (sat_cons (step1397 p h) (sat_cons (step1886 p h) (sat_cons (step3962 p h) (sat_cons (step2187 p h) (sat_cons (step1188 p h) (sat_cons (step1283 p h) (sat_cons (step1217 p h) (sat_nil p)))))))))))))
def c4995 : List Lit := [(95, false)]
theorem step4995 (p : Nat → Bool) (h : Constraints p) : clause p c4995 = true :=
  Snake9.LocalRup.prove_clause [c4950, c4976, c4981, c4975, c4736, c1202, c1197, c4994] c4995 (by decide) p (sat_cons (step4950 p h) (sat_cons (step4976 p h) (sat_cons (step4981 p h) (sat_cons (step4975 p h) (sat_cons (step4736 p h) (sat_cons (step1202 p h) (sat_cons (step1197 p h) (sat_cons (step4994 p h) (sat_nil p)))))))))
def c4996 : List Lit := [(1627, true)]
theorem step4996 (p : Nat → Bool) (h : Constraints p) : clause p c4996 = true :=
  Snake9.LocalRup.prove_clause [c4995, c4987, c4976, c4434, c4989, c3089] c4996 (by decide) p (sat_cons (step4995 p h) (sat_cons (step4987 p h) (sat_cons (step4976 p h) (sat_cons (step4434 p h) (sat_cons (step4989 p h) (sat_cons (step3089 p h) (sat_nil p)))))))
def c4997 : List Lit := [(1671, true), (1728, true)]
theorem step4997 (p : Nat → Bool) (h : Constraints p) : clause p c4997 = true :=
  Snake9.LocalRup.prove_clause [c4975, c4977, c4686, c4989, c4974, c4951, c4987, c4995, c4904, c4980, c1914, c1217, c1188, c1182, c4770, c1732, c1337, c2187, c1278] c4997 (by decide) p (sat_cons (step4975 p h) (sat_cons (step4977 p h) (sat_cons (step4686 p h) (sat_cons (step4989 p h) (sat_cons (step4974 p h) (sat_cons (step4951 p h) (sat_cons (step4987 p h) (sat_cons (step4995 p h) (sat_cons (step4904 p h) (sat_cons (step4980 p h) (sat_cons (step1914 p h) (sat_cons (step1217 p h) (sat_cons (step1188 p h) (sat_cons (step1182 p h) (sat_cons (step4770 p h) (sat_cons (step1732 p h) (sat_cons (step1337 p h) (sat_cons (step2187 p h) (sat_cons (step1278 p h) (sat_nil p))))))))))))))))))))
def c4998 : List Lit := [(84, true), (31, true), (96, false), (105, false)]
theorem step4998 (p : Nat → Bool) (h : Constraints p) : clause p c4998 = true :=
  Snake9.TreeRup.prove_clause [c4987, c4951, c4974, c4982, c4990, c4105, c4981, c4904, c4992, c4950, c4976, c4434, c4989, c4996, c4983, c4810, c4995, c4685, c930, c2131, c1502, c413, c1517, c4412, c1714, c4997, c1283, c2187, c1732, c1663, c1282, c1337, c3827, c1745, c3078, c1330, c1715, c1062, c1691, c4770, c2418, c1197, c1829, c1634, c1633, c519, c2795, c1122, c602, c1133, c1244, c1125, c1253, c4463, c1247, c1690, c924, c612, c1058, c4680, c1110, c4664, c4678, c1422, c987, c1142, c997, c1167, c989, c1101, c4873, c1754, c3021, c830, c870, c1684, c4066, c3170, c752, c1553, c713, c84, c712, c695, c699, c698] c4998 (by decide) p (sat_cons (step4987 p h) (sat_cons (step4951 p h) (sat_cons (step4974 p h) (sat_cons (step4982 p h) (sat_cons (step4990 p h) (sat_cons (step4105 p h) (sat_cons (step4981 p h) (sat_cons (step4904 p h) (sat_cons (step4992 p h) (sat_cons (step4950 p h) (sat_cons (step4976 p h) (sat_cons (step4434 p h) (sat_cons (step4989 p h) (sat_cons (step4996 p h) (sat_cons (step4983 p h) (sat_cons (step4810 p h) (sat_cons (step4995 p h) (sat_cons (step4685 p h) (sat_cons (step930 p h) (sat_cons (step2131 p h) (sat_cons (step1502 p h) (sat_cons (step413 p h) (sat_cons (step1517 p h) (sat_cons (step4412 p h) (sat_cons (step1714 p h) (sat_cons (step4997 p h) (sat_cons (step1283 p h) (sat_cons (step2187 p h) (sat_cons (step1732 p h) (sat_cons (step1663 p h) (sat_cons (step1282 p h) (sat_cons (step1337 p h) (sat_cons (step3827 p h) (sat_cons (step1745 p h) (sat_cons (step3078 p h) (sat_cons (step1330 p h) (sat_cons (step1715 p h) (sat_cons (step1062 p h) (sat_cons (step1691 p h) (sat_cons (step4770 p h) (sat_cons (step2418 p h) (sat_cons (step1197 p h) (sat_cons (step1829 p h) (sat_cons (step1634 p h) (sat_cons (step1633 p h) (sat_cons (step519 p h) (sat_cons (step2795 p h) (sat_cons (step1122 p h) (sat_cons (step602 p h) (sat_cons (step1133 p h) (sat_cons (step1244 p h) (sat_cons (step1125 p h) (sat_cons (step1253 p h) (sat_cons (step4463 p h) (sat_cons (step1247 p h) (sat_cons (step1690 p h) (sat_cons (step924 p h) (sat_cons (step612 p h) (sat_cons (step1058 p h) (sat_cons (step4680 p h) (sat_cons (step1110 p h) (sat_cons (step4664 p h) (sat_cons (step4678 p h) (sat_cons (step1422 p h) (sat_cons (step987 p h) (sat_cons (step1142 p h) (sat_cons (step997 p h) (sat_cons (step1167 p h) (sat_cons (step989 p h) (sat_cons (step1101 p h) (sat_cons (step4873 p h) (sat_cons (step1754 p h) (sat_cons (step3021 p h) (sat_cons (step830 p h) (sat_cons (step870 p h) (sat_cons (step1684 p h) (sat_cons (step4066 p h) (sat_cons (step3170 p h) (sat_cons (step752 p h) (sat_cons (step1553 p h) (sat_cons (step713 p h) (sat_cons (step84 p h) (sat_cons (step712 p h) (sat_cons (step695 p h) (sat_cons (step699 p h) (sat_cons (step698 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c4999 : List Lit := [(84, false), (96, false), (1628, true)]
theorem step4999 (p : Nat → Bool) (h : Constraints p) : clause p c4999 = true :=
  Snake9.LocalRup.prove_clause [c4904, c4434, c4989, c342, c343, c1122, c1125, c1133] c4999 (by decide) p (sat_cons (step4904 p h) (sat_cons (step4434 p h) (sat_cons (step4989 p h) (sat_cons (step342 p h) (sat_cons (step343 p h) (sat_cons (step1122 p h) (sat_cons (step1125 p h) (sat_cons (step1133 p h) (sat_nil p)))))))))
def c5000 : List Lit := [(96, false), (105, false)]
theorem step5000 (p : Nat → Bool) (h : Constraints p) : clause p c5000 = true :=
  Snake9.TreeRup.prove_clause [c4950, c4983, c4990, c4985, c4996, c4981, c4987, c4951, c4974, c4904, c4982, c4434, c4995, c4989, c4810, c4976, c4992, c2131, c1502, c413, c1517, c4412, c1714, c4997, c1282, c1337, c4770, c2418, c1197, c1162, c1146, c1330, c1715, c3827, c1829, c1283, c2187, c1732, c1745, c1663, c4999, c1634, c1633, c4998, c519, c2795, c558, c1122, c602, c1637, c1133, c1244, c1125, c1253, c4463, c391, c379, c1247, c1690, c1232, c987, c612, c1058, c1240, c1110, c4664, c1235, c1117, c997, c1420, c989, c268, c449, c1590] c5000 (by decide) p (sat_cons (step4950 p h) (sat_cons (step4983 p h) (sat_cons (step4990 p h) (sat_cons (step4985 p h) (sat_cons (step4996 p h) (sat_cons (step4981 p h) (sat_cons (step4987 p h) (sat_cons (step4951 p h) (sat_cons (step4974 p h) (sat_cons (step4904 p h) (sat_cons (step4982 p h) (sat_cons (step4434 p h) (sat_cons (step4995 p h) (sat_cons (step4989 p h) (sat_cons (step4810 p h) (sat_cons (step4976 p h) (sat_cons (step4992 p h) (sat_cons (step2131 p h) (sat_cons (step1502 p h) (sat_cons (step413 p h) (sat_cons (step1517 p h) (sat_cons (step4412 p h) (sat_cons (step1714 p h) (sat_cons (step4997 p h) (sat_cons (step1282 p h) (sat_cons (step1337 p h) (sat_cons (step4770 p h) (sat_cons (step2418 p h) (sat_cons (step1197 p h) (sat_cons (step1162 p h) (sat_cons (step1146 p h) (sat_cons (step1330 p h) (sat_cons (step1715 p h) (sat_cons (step3827 p h) (sat_cons (step1829 p h) (sat_cons (step1283 p h) (sat_cons (step2187 p h) (sat_cons (step1732 p h) (sat_cons (step1745 p h) (sat_cons (step1663 p h) (sat_cons (step4999 p h) (sat_cons (step1634 p h) (sat_cons (step1633 p h) (sat_cons (step4998 p h) (sat_cons (step519 p h) (sat_cons (step2795 p h) (sat_cons (step558 p h) (sat_cons (step1122 p h) (sat_cons (step602 p h) (sat_cons (step1637 p h) (sat_cons (step1133 p h) (sat_cons (step1244 p h) (sat_cons (step1125 p h) (sat_cons (step1253 p h) (sat_cons (step4463 p h) (sat_cons (step391 p h) (sat_cons (step379 p h) (sat_cons (step1247 p h) (sat_cons (step1690 p h) (sat_cons (step1232 p h) (sat_cons (step987 p h) (sat_cons (step612 p h) (sat_cons (step1058 p h) (sat_cons (step1240 p h) (sat_cons (step1110 p h) (sat_cons (step4664 p h) (sat_cons (step1235 p h) (sat_cons (step1117 p h) (sat_cons (step997 p h) (sat_cons (step1420 p h) (sat_cons (step989 p h) (sat_cons (step268 p h) (sat_cons (step449 p h) (sat_cons (step1590 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c5001 : List Lit := [(50, false), (105, false)]
theorem step5001 (p : Nat → Bool) (h : Constraints p) : clause p c5001 = true :=
  Snake9.LocalRup.prove_clause [c4995, c4987, c4951, c4974, c4989, c4982, c4950, c4996, c4981, c4904, c4992, c4810, c4983, c4434, c2131, c1502, c413, c1517, c4412, c1714, c4997, c1282, c1337, c1283, c2187, c1255, c4770, c2418, c5000, c1184, c2016, c1246, c1245, c1253, c1247, c1248, c629, c1670, c613, c1110, c1422, c1142, c1167, c1101, c1754, c830, c1684, c750, c746, c743, c733, c729, c728, c325, c3526] c5001 (by decide) p (sat_cons (step4995 p h) (sat_cons (step4987 p h) (sat_cons (step4951 p h) (sat_cons (step4974 p h) (sat_cons (step4989 p h) (sat_cons (step4982 p h) (sat_cons (step4950 p h) (sat_cons (step4996 p h) (sat_cons (step4981 p h) (sat_cons (step4904 p h) (sat_cons (step4992 p h) (sat_cons (step4810 p h) (sat_cons (step4983 p h) (sat_cons (step4434 p h) (sat_cons (step2131 p h) (sat_cons (step1502 p h) (sat_cons (step413 p h) (sat_cons (step1517 p h) (sat_cons (step4412 p h) (sat_cons (step1714 p h) (sat_cons (step4997 p h) (sat_cons (step1282 p h) (sat_cons (step1337 p h) (sat_cons (step1283 p h) (sat_cons (step2187 p h) (sat_cons (step1255 p h) (sat_cons (step4770 p h) (sat_cons (step2418 p h) (sat_cons (step5000 p h) (sat_cons (step1184 p h) (sat_cons (step2016 p h) (sat_cons (step1246 p h) (sat_cons (step1245 p h) (sat_cons (step1253 p h) (sat_cons (step1247 p h) (sat_cons (step1248 p h) (sat_cons (step629 p h) (sat_cons (step1670 p h) (sat_cons (step613 p h) (sat_cons (step1110 p h) (sat_cons (step1422 p h) (sat_cons (step1142 p h) (sat_cons (step1167 p h) (sat_cons (step1101 p h) (sat_cons (step1754 p h) (sat_cons (step830 p h) (sat_cons (step1684 p h) (sat_cons (step750 p h) (sat_cons (step746 p h) (sat_cons (step743 p h) (sat_cons (step733 p h) (sat_cons (step729 p h) (sat_cons (step728 p h) (sat_cons (step325 p h) (sat_cons (step3526 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c5002 : List Lit := [(105, false)]
theorem step5002 (p : Nat → Bool) (h : Constraints p) : clause p c5002 = true :=
  Snake9.LocalRup.prove_clause [c4992, c4904, c4981, c4990, c4983, c4810, c4995, c4811, c4434, c4989, c2131, c1502, c413, c1517, c4412, c1714, c4997, c1282, c1337, c1330, c1829, c1715, c5001, c4107, c1058, c1690, c3114, c3794] c5002 (by decide) p (sat_cons (step4992 p h) (sat_cons (step4904 p h) (sat_cons (step4981 p h) (sat_cons (step4990 p h) (sat_cons (step4983 p h) (sat_cons (step4810 p h) (sat_cons (step4995 p h) (sat_cons (step4811 p h) (sat_cons (step4434 p h) (sat_cons (step4989 p h) (sat_cons (step2131 p h) (sat_cons (step1502 p h) (sat_cons (step413 p h) (sat_cons (step1517 p h) (sat_cons (step4412 p h) (sat_cons (step1714 p h) (sat_cons (step4997 p h) (sat_cons (step1282 p h) (sat_cons (step1337 p h) (sat_cons (step1330 p h) (sat_cons (step1829 p h) (sat_cons (step1715 p h) (sat_cons (step5001 p h) (sat_cons (step4107 p h) (sat_cons (step1058 p h) (sat_cons (step1690 p h) (sat_cons (step3114 p h) (sat_cons (step3794 p h) (sat_nil p)))))))))))))))))))))))))))))
def c5003 : List Lit := [(1663, true)]
theorem step5003 (p : Nat → Bool) (h : Constraints p) : clause p c5003 = true :=
  Snake9.LocalRup.prove_clause [c5002, c1196] c5003 (by decide) p (sat_cons (step5002 p h) (sat_cons (step1196 p h) (sat_nil p)))
def c5004 : List Lit := [(102, true)]
theorem step5004 (p : Nat → Bool) (h : Constraints p) : clause p c5004 = true :=
  Snake9.LocalRup.prove_clause [c5002, c4978, c1198] c5004 (by decide) p (sat_cons (step5002 p h) (sat_cons (step4978 p h) (sat_cons (step1198 p h) (sat_nil p))))
def c5005 : List Lit := [(1666, true)]
theorem step5005 (p : Nat → Bool) (h : Constraints p) : clause p c5005 = true :=
  Snake9.LocalRup.prove_clause [c5003, c4975, c1202] c5005 (by decide) p (sat_cons (step5003 p h) (sat_cons (step4975 p h) (sat_cons (step1202 p h) (sat_nil p))))
def c5006 : List Lit := [(1671, true)]
theorem step5006 (p : Nat → Bool) (h : Constraints p) : clause p c5006 = true :=
  Snake9.LocalRup.prove_clause [c5005, c4687, c1213] c5006 (by decide) p (sat_cons (step5005 p h) (sat_cons (step4687 p h) (sat_cons (step1213 p h) (sat_nil p))))
def c5007 : List Lit := [(1658, false)]
theorem step5007 (p : Nat → Bool) (h : Constraints p) : clause p c5007 = true :=
  Snake9.LocalRup.prove_clause [c5005, c4982, c1218] c5007 (by decide) p (sat_cons (step5005 p h) (sat_cons (step4982 p h) (sat_cons (step1218 p h) (sat_nil p))))
def c5008 : List Lit := [(1705, true)]
theorem step5008 (p : Nat → Bool) (h : Constraints p) : clause p c5008 = true :=
  Snake9.LocalRup.prove_clause [c5006, c4981, c1282] c5008 (by decide) p (sat_cons (step5006 p h) (sat_cons (step4981 p h) (sat_cons (step1282 p h) (sat_nil p))))
def c5009 : List Lit := [(1655, false)]
theorem step5009 (p : Nat → Bool) (h : Constraints p) : clause p c5009 = true :=
  Snake9.LocalRup.prove_clause [c5007, c4686, c1188] c5009 (by decide) p (sat_cons (step5007 p h) (sat_cons (step4686 p h) (sat_cons (step1188 p h) (sat_nil p))))
def c5010 : List Lit := [(1645, false)]
theorem step5010 (p : Nat → Bool) (h : Constraints p) : clause p c5010 = true :=
  Snake9.LocalRup.prove_clause [c5008, c4723, c1346] c5010 (by decide) p (sat_cons (step5008 p h) (sat_cons (step4723 p h) (sat_cons (step1346 p h) (sat_nil p))))
def c5011 : List Lit := [(94, true)]
theorem step5011 (p : Nat → Bool) (h : Constraints p) : clause p c5011 = true :=
  Snake9.LocalRup.prove_clause [c5009, c1183] c5011 (by decide) p (sat_cons (step5009 p h) (sat_cons (step1183 p h) (sat_nil p)))
def c5012 : List Lit := [(97, false)]
theorem step5012 (p : Nat → Bool) (h : Constraints p) : clause p c5012 = true :=
  Snake9.LocalRup.prove_clause [c5009, c4976, c3000] c5012 (by decide) p (sat_cons (step5009 p h) (sat_cons (step4976 p h) (sat_cons (step3000 p h) (sat_nil p))))
def c5013 : List Lit := [(87, true)]
theorem step5013 (p : Nat → Bool) (h : Constraints p) : clause p c5013 = true :=
  Snake9.LocalRup.prove_clause [c5012, c4995, c4976, c1638] c5013 (by decide) p (sat_cons (step5012 p h) (sat_cons (step4995 p h) (sat_cons (step4976 p h) (sat_cons (step1638 p h) (sat_nil p)))))
def c5014 : List Lit := [(1728, true)]
theorem step5014 (p : Nat → Bool) (h : Constraints p) : clause p c5014 = true :=
  Snake9.LocalRup.prove_clause [c5008, c5009, c4989, c4974, c4951, c4987, c4995, c4904, c1337, c4770] c5014 (by decide) p (sat_cons (step5008 p h) (sat_cons (step5009 p h) (sat_cons (step4989 p h) (sat_cons (step4974 p h) (sat_cons (step4951 p h) (sat_cons (step4987 p h) (sat_cons (step4995 p h) (sat_cons (step4904 p h) (sat_cons (step1337 p h) (sat_cons (step4770 p h) (sat_nil p)))))))))))
def c5015 : List Lit := [(1576, false)]
theorem step5015 (p : Nat → Bool) (h : Constraints p) : clause p c5015 = true :=
  Snake9.LocalRup.prove_clause [c5014, c1714] c5015 (by decide) p (sat_cons (step5014 p h) (sat_cons (step1714 p h) (sat_nil p)))
def c5016 : List Lit := [(1539, false)]
theorem step5016 (p : Nat → Bool) (h : Constraints p) : clause p c5016 = true :=
  Snake9.LocalRup.prove_clause [c5015, c4810, c4412] c5016 (by decide) p (sat_cons (step5015 p h) (sat_cons (step4810 p h) (sat_cons (step4412 p h) (sat_nil p))))
def c5017 : List Lit := [(53, true)]
theorem step5017 (p : Nat → Bool) (h : Constraints p) : clause p c5017 = true :=
  Snake9.LocalRup.prove_clause [c5016, c1517] c5017 (by decide) p (sat_cons (step5016 p h) (sat_cons (step1517 p h) (sat_nil p)))
def c5018 : List Lit := [(88, true)]
theorem step5018 (p : Nat → Bool) (h : Constraints p) : clause p c5018 = true :=
  Snake9.LocalRup.prove_clause [c5017, c1588] c5018 (by decide) p (sat_cons (step5017 p h) (sat_cons (step1588 p h) (sat_nil p)))
def c5019 : List Lit := [(108, false)]
theorem step5019 (p : Nat → Bool) (h : Constraints p) : clause p c5019 = true :=
  Snake9.LocalRup.prove_clause [c5017, c4904, c5018, c413] c5019 (by decide) p (sat_cons (step5017 p h) (sat_cons (step4904 p h) (sat_cons (step5018 p h) (sat_cons (step413 p h) (sat_nil p)))))
def c5020 : List Lit := [(1677, true)]
theorem step5020 (p : Nat → Bool) (h : Constraints p) : clause p c5020 = true :=
  Snake9.LocalRup.prove_clause [c5019, c1231] c5020 (by decide) p (sat_cons (step5019 p h) (sat_cons (step1231 p h) (sat_nil p)))
def c5021 : List Lit := [(86, false)]
theorem step5021 (p : Nat → Bool) (h : Constraints p) : clause p c5021 = true :=
  Snake9.LocalRup.prove_clause [c5019, c4976, c4992, c4745] c5021 (by decide) p (sat_cons (step5019 p h) (sat_cons (step4976 p h) (sat_cons (step4992 p h) (sat_cons (step4745 p h) (sat_nil p)))))
def c5022 : List Lit := [(107, true)]
theorem step5022 (p : Nat → Bool) (h : Constraints p) : clause p c5022 = true :=
  Snake9.LocalRup.prove_clause [c5019, c4993, c1233] c5022 (by decide) p (sat_cons (step5019 p h) (sat_cons (step4993 p h) (sat_cons (step1233 p h) (sat_nil p))))
def c5023 : List Lit := [(1679, false)]
theorem step5023 (p : Nat → Bool) (h : Constraints p) : clause p c5023 = true :=
  Snake9.LocalRup.prove_clause [c5020, c4992, c1240] c5023 (by decide) p (sat_cons (step5020 p h) (sat_cons (step4992 p h) (sat_cons (step1240 p h) (sat_nil p))))
def c5024 : List Lit := [(1624, true)]
theorem step5024 (p : Nat → Bool) (h : Constraints p) : clause p c5024 = true :=
  Snake9.LocalRup.prove_clause [c5021, c4989, c1125] c5024 (by decide) p (sat_cons (step5021 p h) (sat_cons (step4989 p h) (sat_cons (step1125 p h) (sat_nil p))))
def c5025 : List Lit := [(85, false)]
theorem step5025 (p : Nat → Bool) (h : Constraints p) : clause p c5025 = true :=
  Snake9.LocalRup.prove_clause [c5022, c4976, c5011, c4995, c4913] c5025 (by decide) p (sat_cons (step5022 p h) (sat_cons (step4976 p h) (sat_cons (step5011 p h) (sat_cons (step4995 p h) (sat_cons (step4913 p h) (sat_nil p))))))
def c5026 : List Lit := [(52, false)]
theorem step5026 (p : Nat → Bool) (h : Constraints p) : clause p c5026 = true :=
  Snake9.LocalRup.prove_clause [c5022, c5013, c4976, c382] c5026 (by decide) p (sat_cons (step5022 p h) (sat_cons (step5013 p h) (sat_cons (step4976 p h) (sat_cons (step382 p h) (sat_nil p)))))
def c5027 : List Lit := [(110, true)]
theorem step5027 (p : Nat → Bool) (h : Constraints p) : clause p c5027 = true :=
  Snake9.LocalRup.prove_clause [c5023, c1235] c5027 (by decide) p (sat_cons (step5023 p h) (sat_cons (step1235 p h) (sat_nil p)))
def c5028 : List Lit := [(1622, true)]
theorem step5028 (p : Nat → Bool) (h : Constraints p) : clause p c5028 = true :=
  Snake9.LocalRup.prove_clause [c5025, c4434, c1122] c5028 (by decide) p (sat_cons (step5025 p h) (sat_cons (step4434 p h) (sat_cons (step1122 p h) (sat_nil p))))
def c5029 : List Lit := [(1534, true)]
theorem step5029 (p : Nat → Bool) (h : Constraints p) : clause p c5029 = true :=
  Snake9.LocalRup.prove_clause [c5026, c986] c5029 (by decide) p (sat_cons (step5026 p h) (sat_cons (step986 p h) (sat_nil p)))
def c5030 : List Lit := [(1628, true)]
theorem step5030 (p : Nat → Bool) (h : Constraints p) : clause p c5030 = true :=
  Snake9.LocalRup.prove_clause [c5028, c5024, c1133] c5030 (by decide) p (sat_cons (step5028 p h) (sat_cons (step5024 p h) (sat_cons (step1133 p h) (sat_nil p))))
def c5031 : List Lit := [(1536, false)]
theorem step5031 (p : Nat → Bool) (h : Constraints p) : clause p c5031 = true :=
  Snake9.LocalRup.prove_clause [c5029, c5016, c994] c5031 (by decide) p (sat_cons (step5029 p h) (sat_cons (step5016 p h) (sat_cons (step994 p h) (sat_nil p))))
def c5032 : List Lit := [(54, true)]
theorem step5032 (p : Nat → Bool) (h : Constraints p) : clause p c5032 = true :=
  Snake9.LocalRup.prove_clause [c5031, c989] c5032 (by decide) p (sat_cons (step5031 p h) (sat_cons (step989 p h) (sat_nil p)))
def c5033 : List Lit := [(90, false)]
theorem step5033 (p : Nat → Bool) (h : Constraints p) : clause p c5033 = true :=
  Snake9.LocalRup.prove_clause [c5032, c5004, c5027, c449] c5033 (by decide) p (sat_cons (step5032 p h) (sat_cons (step5004 p h) (sat_cons (step5027 p h) (sat_cons (step449 p h) (sat_nil p)))))
def c5034 : List Lit := [(71, true)]
theorem step5034 (p : Nat → Bool) (h : Constraints p) : clause p c5034 = true :=
  Snake9.LocalRup.prove_clause [c5033, c5032, c1590] c5034 (by decide) p (sat_cons (step5033 p h) (sat_cons (step5032 p h) (sat_cons (step1590 p h) (sat_nil p))))
def c5035 : List Lit := [(1601, true)]
theorem step5035 (p : Nat → Bool) (h : Constraints p) : clause p c5035 = true :=
  Snake9.LocalRup.prove_clause [c5034, c5032, c4873] c5035 (by decide) p (sat_cons (step5034 p h) (sat_cons (step5032 p h) (sat_cons (step4873 p h) (sat_nil p))))
def c5036 : List Lit := [(79, false)]
theorem step5036 (p : Nat → Bool) (h : Constraints p) : clause p c5036 = true :=
  Snake9.LocalRup.prove_clause [c5034, c5027, c5032, c268] c5036 (by decide) p (sat_cons (step5034 p h) (sat_cons (step5027 p h) (sat_cons (step5032 p h) (sat_cons (step268 p h) (sat_nil p)))))
def c5037 : List Lit := [(67, false)]
theorem step5037 (p : Nat → Bool) (h : Constraints p) : clause p c5037 = true :=
  Snake9.LocalRup.prove_clause [c5034, c5027, c5032, c266] c5037 (by decide) p (sat_cons (step5034 p h) (sat_cons (step5027 p h) (sat_cons (step5032 p h) (sat_cons (step266 p h) (sat_nil p)))))
def c5038 : List Lit := [(1606, true)]
theorem step5038 (p : Nat → Bool) (h : Constraints p) : clause p c5038 = true :=
  Snake9.LocalRup.prove_clause [c5035, c4983, c1101] c5038 (by decide) p (sat_cons (step5035 p h) (sat_cons (step4983 p h) (sat_cons (step1101 p h) (sat_nil p))))
def c5039 : List Lit := [(1616, true)]
theorem step5039 (p : Nat → Bool) (h : Constraints p) : clause p c5039 = true :=
  Snake9.LocalRup.prove_clause [c5036, c1420] c5039 (by decide) p (sat_cons (step5036 p h) (sat_cons (step1420 p h) (sat_nil p)))
def c5040 : List Lit := [(1635, false)]
theorem step5040 (p : Nat → Bool) (h : Constraints p) : clause p c5040 = true :=
  Snake9.LocalRup.prove_clause [c5038, c5010, c1169] c5040 (by decide) p (sat_cons (step5038 p h) (sat_cons (step5010 p h) (sat_cons (step1169 p h) (sat_nil p))))
def c5041 : List Lit := []
theorem step5041 (p : Nat → Bool) (h : Constraints p) : clause p c5041 = true :=
  Snake9.LocalRup.prove_clause [c5039, c5040, c5030, c5037, c4983, c5010, c1524] c5041 (by decide) p (sat_cons (step5039 p h) (sat_cons (step5040 p h) (sat_cons (step5030 p h) (sat_cons (step5037 p h) (sat_cons (step4983 p h) (sat_cons (step5010 p h) (sat_cons (step1524 p h) (sat_nil p))))))))
end B112E026
