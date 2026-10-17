import B112E040Part0066
namespace B112E040
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c5813 : List Lit := [(80, true), (1594, false), (1647, false), (1473, false), (1456, false), (115, true), (37, true), (1463, false)]
theorem step5813 (p : Nat → Bool) (h : Constraints p) : clause p c5813 = true :=
  Snake9.LocalRup.prove_clause [c5234, c3554] c5813 (by decide) p (sat_cons (step5234 p h) (sat_cons (step3554 p h) (sat_nil p)))
def c5814 : List Lit := [(1456, false), (80, true), (25, true), (26, false), (21, true), (115, true), (1594, false), (37, true), (1647, false)]
theorem step5814 (p : Nat → Bool) (h : Constraints p) : clause p c5814 = true :=
  Snake9.LocalRup.prove_clause [c5234, c3545] c5814 (by decide) p (sat_cons (step5234 p h) (sat_cons (step3545 p h) (sat_nil p)))
def c5815 : List Lit := [(1456, false), (80, true), (16, true), (1647, false), (115, true), (1463, false), (1473, false), (37, true)]
theorem step5815 (p : Nat → Bool) (h : Constraints p) : clause p c5815 = true :=
  Snake9.LocalRup.prove_clause [c5234, c3569] c5815 (by decide) p (sat_cons (step5234 p h) (sat_cons (step3569 p h) (sat_nil p)))
def c5816 : List Lit := [(80, true), (1474, false), (1455, false), (6, false), (1647, false), (16, true), (37, true)]
theorem step5816 (p : Nat → Bool) (h : Constraints p) : clause p c5816 = true :=
  Snake9.LocalRup.prove_clause [c5234, c3433] c5816 (by decide) p (sat_cons (step5234 p h) (sat_cons (step3433 p h) (sat_nil p)))
def c5817 : List Lit := [(1490, false), (18, false), (1647, false), (80, true), (1594, false), (115, true)]
theorem step5817 (p : Nat → Bool) (h : Constraints p) : clause p c5817 = true :=
  Snake9.LocalRup.prove_clause [c5234, c3616] c5817 (by decide) p (sat_cons (step5234 p h) (sat_cons (step3616 p h) (sat_nil p)))
def c5818 : List Lit := [(80, true), (1665, false), (26, true), (1647, false), (16, false), (115, true), (1448, false), (37, false), (1490, false), (6, true), (25, false)]
theorem step5818 (p : Nat → Bool) (h : Constraints p) : clause p c5818 = true :=
  Snake9.LocalRup.prove_clause [c5234, c3607] c5818 (by decide) p (sat_cons (step5234 p h) (sat_cons (step3607 p h) (sat_nil p)))
def c5819 : List Lit := [(3, false), (111, true), (1594, true), (37, true)]
theorem step5819 (p : Nat → Bool) (h : Constraints p) : clause p c5819 = true :=
  Snake9.LocalRup.prove_clause [c5234, c4352] c5819 (by decide) p (sat_cons (step5234 p h) (sat_cons (step4352 p h) (sat_nil p)))
def c5820 : List Lit := [(1492, false), (111, true), (1647, false), (80, false), (115, true)]
theorem step5820 (p : Nat → Bool) (h : Constraints p) : clause p c5820 = true :=
  Snake9.LocalRup.prove_clause [c5236, c3987] c5820 (by decide) p (sat_cons (step5236 p h) (sat_cons (step3987 p h) (sat_nil p)))
def c5821 : List Lit := [(111, true), (1456, false), (115, true), (63, false), (1590, true), (37, true), (71, false), (25, false), (1647, true)]
theorem step5821 (p : Nat → Bool) (h : Constraints p) : clause p c5821 = true :=
  Snake9.LocalRup.prove_clause [c5234, c4351] c5821 (by decide) p (sat_cons (step5234 p h) (sat_cons (step4351 p h) (sat_nil p)))
def c5822 : List Lit := [(1681, false), (24, false), (1517, true), (30, false), (1651, false), (1480, true), (16, true), (26, true), (37, true), (21, true), (70, false), (1489, false), (1463, false)]
theorem step5822 (p : Nat → Bool) (h : Constraints p) : clause p c5822 = true :=
  Snake9.LocalRup.prove_clause [c5234, c3931] c5822 (by decide) p (sat_cons (step5234 p h) (sat_cons (step3931 p h) (sat_nil p)))
def c5823 : List Lit := [(73, false), (1516, true), (37, true)]
theorem step5823 (p : Nat → Bool) (h : Constraints p) : clause p c5823 = true :=
  Snake9.LocalRup.prove_clause [c5234, c3540] c5823 (by decide) p (sat_cons (step5234 p h) (sat_cons (step3540 p h) (sat_nil p)))
def c5824 : List Lit := [(1570, true), (73, false), (29, true), (23, true), (70, false), (18, false), (1456, false), (1465, false), (37, true)]
theorem step5824 (p : Nat → Bool) (h : Constraints p) : clause p c5824 = true :=
  Snake9.LocalRup.prove_clause [c5234, c3476] c5824 (by decide) p (sat_cons (step5234 p h) (sat_cons (step3476 p h) (sat_nil p)))
def c5825 : List Lit := [(1570, true), (73, false), (1473, false), (1456, false), (37, true), (1465, false)]
theorem step5825 (p : Nat → Bool) (h : Constraints p) : clause p c5825 = true :=
  Snake9.LocalRup.prove_clause [c5234, c4333] c5825 (by decide) p (sat_cons (step5234 p h) (sat_cons (step4333 p h) (sat_nil p)))
def c5826 : List Lit := [(43, true), (18, false), (1552, true), (5, true), (55, true), (37, true), (111, false)]
theorem step5826 (p : Nat → Bool) (h : Constraints p) : clause p c5826 = true :=
  Snake9.LocalRup.prove_clause [c5234, c4229] c5826 (by decide) p (sat_cons (step5234 p h) (sat_cons (step4229 p h) (sat_nil p)))
def c5827 : List Lit := [(1570, true), (1540, false), (26, false), (1456, false), (1455, false)]
theorem step5827 (p : Nat → Bool) (h : Constraints p) : clause p c5827 = true :=
  Snake9.LocalRup.prove_clause [c5234, c4107] c5827 (by decide) p (sat_cons (step5234 p h) (sat_cons (step4107 p h) (sat_nil p)))
def c5828 : List Lit := [(1540, false), (1552, true), (1571, true), (1455, false), (1473, false), (37, true)]
theorem step5828 (p : Nat → Bool) (h : Constraints p) : clause p c5828 = true :=
  Snake9.LocalRup.prove_clause [c5234, c4217] c5828 (by decide) p (sat_cons (step5234 p h) (sat_cons (step4217 p h) (sat_nil p)))
def c5829 : List Lit := [(1456, false), (80, false), (1463, false), (37, true), (1594, false), (111, true), (115, true), (16, true), (1647, false)]
theorem step5829 (p : Nat → Bool) (h : Constraints p) : clause p c5829 = true :=
  Snake9.LocalRup.prove_clause [c5234, c4092] c5829 (by decide) p (sat_cons (step5234 p h) (sat_cons (step4092 p h) (sat_nil p)))
def c5830 : List Lit := [(1456, false), (1594, false), (37, true), (80, false), (1465, false), (1473, false), (115, true), (111, true), (1647, false)]
theorem step5830 (p : Nat → Bool) (h : Constraints p) : clause p c5830 = true :=
  Snake9.LocalRup.prove_clause [c5234, c4040] c5830 (by decide) p (sat_cons (step5234 p h) (sat_cons (step4040 p h) (sat_nil p)))
def c5831 : List Lit := [(1456, false), (1570, true), (37, true), (1473, false), (111, false), (1463, false)]
theorem step5831 (p : Nat → Bool) (h : Constraints p) : clause p c5831 = true :=
  Snake9.LocalRup.prove_clause [c5234, c3511] c5831 (by decide) p (sat_cons (step5234 p h) (sat_cons (step3511 p h) (sat_nil p)))
def c5832 : List Lit := [(1681, false), (1570, true), (16, true), (70, false), (25, true), (1455, false), (1481, true), (1651, false), (26, true), (37, true)]
theorem step5832 (p : Nat → Bool) (h : Constraints p) : clause p c5832 = true :=
  Snake9.LocalRup.prove_clause [c5234, c3935] c5832 (by decide) p (sat_cons (step5234 p h) (sat_cons (step3935 p h) (sat_nil p)))
def c5833 : List Lit := [(80, false), (1570, true), (1463, false), (115, true), (1594, false), (1647, false), (1474, false), (1455, false), (37, true)]
theorem step5833 (p : Nat → Bool) (h : Constraints p) : clause p c5833 = true :=
  Snake9.LocalRup.prove_clause [c5234, c3719] c5833 (by decide) p (sat_cons (step5234 p h) (sat_cons (step3719 p h) (sat_nil p)))
def c5834 : List Lit := [(1570, true), (1474, false), (1455, false), (1463, false), (37, true), (111, false)]
theorem step5834 (p : Nat → Bool) (h : Constraints p) : clause p c5834 = true :=
  Snake9.LocalRup.prove_clause [c5234, c4262] c5834 (by decide) p (sat_cons (step5234 p h) (sat_cons (step4262 p h) (sat_nil p)))
def c5835 : List Lit := [(1456, false), (1474, false), (1571, true), (111, false), (37, true), (1463, false)]
theorem step5835 (p : Nat → Bool) (h : Constraints p) : clause p c5835 = true :=
  Snake9.LocalRup.prove_clause [c5234, c4255] c5835 (by decide) p (sat_cons (step5234 p h) (sat_cons (step4255 p h) (sat_nil p)))
def c5836 : List Lit := [(1456, false), (1570, true), (1463, false), (1474, false), (37, true)]
theorem step5836 (p : Nat → Bool) (h : Constraints p) : clause p c5836 = true :=
  Snake9.LocalRup.prove_clause [c5234, c4250] c5836 (by decide) p (sat_cons (step5234 p h) (sat_cons (step4250 p h) (sat_nil p)))
def c5837 : List Lit := [(1570, true), (1520, false), (1455, false), (1474, false), (37, true), (1463, false)]
theorem step5837 (p : Nat → Bool) (h : Constraints p) : clause p c5837 = true :=
  Snake9.LocalRup.prove_clause [c5234, c4260] c5837 (by decide) p (sat_cons (step5234 p h) (sat_cons (step4260 p h) (sat_nil p)))
def c5838 : List Lit := [(1570, true), (1456, false), (16, true), (1474, false), (1463, false)]
theorem step5838 (p : Nat → Bool) (h : Constraints p) : clause p c5838 = true :=
  Snake9.LocalRup.prove_clause [c5234, c3591] c5838 (by decide) p (sat_cons (step5234 p h) (sat_cons (step3591 p h) (sat_nil p)))
def c5839 : List Lit := [(29, true), (24, false), (1570, true), (1480, true), (26, false), (1456, false), (1594, true), (16, true), (25, true), (37, true)]
theorem step5839 (p : Nat → Bool) (h : Constraints p) : clause p c5839 = true :=
  Snake9.LocalRup.prove_clause [c5234, c3580] c5839 (by decide) p (sat_cons (step5234 p h) (sat_cons (step3580 p h) (sat_nil p)))
def c5840 : List Lit := [(1516, true), (18, false), (37, true)]
theorem step5840 (p : Nat → Bool) (h : Constraints p) : clause p c5840 = true :=
  Snake9.LocalRup.prove_clause [c5234, c3430] c5840 (by decide) p (sat_cons (step5234 p h) (sat_cons (step3430 p h) (sat_nil p)))
def c5841 : List Lit := [(1456, false), (80, false), (5, true), (25, true), (26, false), (30, false), (115, true), (1594, true), (21, true), (16, false), (1647, false), (111, true)]
theorem step5841 (p : Nat → Bool) (h : Constraints p) : clause p c5841 = true :=
  Snake9.LocalRup.prove_clause [c5234, c4033] c5841 (by decide) p (sat_cons (step5234 p h) (sat_cons (step4033 p h) (sat_nil p)))
def c5842 : List Lit := [(1665, false), (80, false), (5, true), (71, false), (1469, false), (1479, true), (1456, false), (115, true), (1465, false), (37, true), (1474, true), (16, false), (1647, false), (55, true)]
theorem step5842 (p : Nat → Bool) (h : Constraints p) : clause p c5842 = true :=
  Snake9.LocalRup.prove_clause [c5234, c4032] c5842 (by decide) p (sat_cons (step5234 p h) (sat_cons (step4032 p h) (sat_nil p)))
def c5843 : List Lit := [(57, true), (18, false), (112, false), (1551, true), (111, false), (37, true)]
theorem step5843 (p : Nat → Bool) (h : Constraints p) : clause p c5843 = true :=
  Snake9.LocalRup.prove_clause [c5234, c4319] c5843 (by decide) p (sat_cons (step5234 p h) (sat_cons (step4319 p h) (sat_nil p)))
def c5844 : List Lit := [(31, true), (20, true), (1516, true), (1480, true), (26, true), (25, true), (37, true)]
theorem step5844 (p : Nat → Bool) (h : Constraints p) : clause p c5844 = true :=
  Snake9.LocalRup.prove_clause [c5234, c4233] c5844 (by decide) p (sat_cons (step5234 p h) (sat_cons (step4233 p h) (sat_nil p)))
def c5845 : List Lit := [(1570, true), (1455, false), (1488, false), (1538, false), (37, true), (1473, false), (111, false)]
theorem step5845 (p : Nat → Bool) (h : Constraints p) : clause p c5845 = true :=
  Snake9.LocalRup.prove_clause [c5234, c4290] c5845 (by decide) p (sat_cons (step5234 p h) (sat_cons (step4290 p h) (sat_nil p)))
def c5846 : List Lit := [(1571, true), (1455, false), (1463, false), (37, true), (16, true), (1538, false), (111, false), (1473, false)]
theorem step5846 (p : Nat → Bool) (h : Constraints p) : clause p c5846 = true :=
  Snake9.LocalRup.prove_clause [c5234, c4322] c5846 (by decide) p (sat_cons (step5234 p h) (sat_cons (step4322 p h) (sat_nil p)))
def c5847 : List Lit := [(44, true), (1538, false), (1455, false), (26, true), (70, false), (1571, true), (37, true), (30, true), (25, true), (1549, false)]
theorem step5847 (p : Nat → Bool) (h : Constraints p) : clause p c5847 = true :=
  Snake9.LocalRup.prove_clause [c5234, c3691] c5847 (by decide) p (sat_cons (step5234 p h) (sat_cons (step3691 p h) (sat_nil p)))
def c5848 : List Lit := [(26, true), (1455, false), (25, true), (80, false), (115, true), (16, true), (1594, true), (37, true), (1647, false)]
theorem step5848 (p : Nat → Bool) (h : Constraints p) : clause p c5848 = true :=
  Snake9.LocalRup.prove_clause [c5234, c3948] c5848 (by decide) p (sat_cons (step5234 p h) (sat_cons (step3948 p h) (sat_nil p)))
def c5849 : List Lit := [(1456, false), (1594, false), (1463, false), (111, true), (1473, false), (80, false), (16, true), (115, true), (1647, false)]
theorem step5849 (p : Nat → Bool) (h : Constraints p) : clause p c5849 = true :=
  Snake9.LocalRup.prove_clause [c5234, c4094] c5849 (by decide) p (sat_cons (step5234 p h) (sat_cons (step4094 p h) (sat_nil p)))
def c5850 : List Lit := [(1570, true), (80, false), (37, true), (1594, false), (115, true), (1490, false), (1647, false)]
theorem step5850 (p : Nat → Bool) (h : Constraints p) : clause p c5850 = true :=
  Snake9.LocalRup.prove_clause [c5234, c3712] c5850 (by decide) p (sat_cons (step5234 p h) (sat_cons (step3712 p h) (sat_nil p)))
def c5851 : List Lit := [(109, false), (1665, false), (1657, false), (116, false), (37, true), (111, false), (115, true), (25, true), (1474, false)]
theorem step5851 (p : Nat → Bool) (h : Constraints p) : clause p c5851 = true :=
  Snake9.LocalRup.prove_clause [c5234, c4563] c5851 (by decide) p (sat_cons (step5234 p h) (sat_cons (step4563 p h) (sat_nil p)))
def c5852 : List Lit := [(100, false), (96, true), (1570, true), (26, false), (1594, true), (37, true), (65, false), (111, false)]
theorem step5852 (p : Nat → Bool) (h : Constraints p) : clause p c5852 = true :=
  Snake9.LocalRup.prove_clause [c5234, c4598] c5852 (by decide) p (sat_cons (step5234 p h) (sat_cons (step4598 p h) (sat_nil p)))
def c5853 : List Lit := [(1570, true), (1538, false), (37, true), (1473, false), (1463, false), (111, false), (16, true)]
theorem step5853 (p : Nat → Bool) (h : Constraints p) : clause p c5853 = true :=
  Snake9.LocalRup.prove_clause [c5234, c4601] c5853 (by decide) p (sat_cons (step5234 p h) (sat_cons (step4601 p h) (sat_nil p)))
def c5854 : List Lit := [(55, true), (1516, true), (28, false), (1470, true), (30, false), (21, false), (37, true), (1595, true), (5, true), (16, false), (25, true)]
theorem step5854 (p : Nat → Bool) (h : Constraints p) : clause p c5854 = true :=
  Snake9.LocalRup.prove_clause [c5234, c4622] c5854 (by decide) p (sat_cons (step5234 p h) (sat_cons (step4622 p h) (sat_nil p)))
def c5855 : List Lit := [(1657, false), (1550, true), (115, true), (1712, true), (1594, false), (80, true), (111, false)]
theorem step5855 (p : Nat → Bool) (h : Constraints p) : clause p c5855 = true :=
  Snake9.LocalRup.prove_clause [c5234, c4702] c5855 (by decide) p (sat_cons (step5234 p h) (sat_cons (step4702 p h) (sat_nil p)))
def c5856 : List Lit := [(1540, false), (1571, true), (16, true), (111, false), (1463, false), (1455, false)]
theorem step5856 (p : Nat → Bool) (h : Constraints p) : clause p c5856 = true :=
  Snake9.LocalRup.prove_clause [c5234, c4711] c5856 (by decide) p (sat_cons (step5234 p h) (sat_cons (step4711 p h) (sat_nil p)))
def c5857 : List Lit := [(1570, true), (1540, true), (1455, false), (1473, false), (1463, false), (115, false)]
theorem step5857 (p : Nat → Bool) (h : Constraints p) : clause p c5857 = true :=
  Snake9.LocalRup.prove_clause [c5234, c4807] c5857 (by decide) p (sat_cons (step5234 p h) (sat_cons (step4807 p h) (sat_nil p)))
def c5858 : List Lit := [(1474, false), (1455, false), (1647, false), (16, true), (115, true), (80, false), (111, true), (1594, false), (1463, false)]
theorem step5858 (p : Nat → Bool) (h : Constraints p) : clause p c5858 = true :=
  Snake9.LocalRup.prove_clause [c5234, c4831] c5858 (by decide) p (sat_cons (step5234 p h) (sat_cons (step4831 p h) (sat_nil p)))
def c5859 : List Lit := [(1481, true), (1594, true), (21, false), (111, false)]
theorem step5859 (p : Nat → Bool) (h : Constraints p) : clause p c5859 = true :=
  Snake9.LocalRup.prove_clause [c5738, c1880, c5739, c1326, c5692, c4264, c5709, c1373, c1377, c5716, c1881, c5694, c990, c1325, c2552, c5373, c4282, c1451, c1851, c5712, c5696, c1910, c5501, c1774, c567, c4317, c1361, c1603, c938, c5520, c5725, c1369, c2123, c1360, c1094, c597, c2126, c1592, c3457, c1291, c1923, c5377, c1312, c5376] c5859 (by decide) p (sat_cons (step5738 p h) (sat_cons (step1880 p h) (sat_cons (step5739 p h) (sat_cons (step1326 p h) (sat_cons (step5692 p h) (sat_cons (step4264 p h) (sat_cons (step5709 p h) (sat_cons (step1373 p h) (sat_cons (step1377 p h) (sat_cons (step5716 p h) (sat_cons (step1881 p h) (sat_cons (step5694 p h) (sat_cons (step990 p h) (sat_cons (step1325 p h) (sat_cons (step2552 p h) (sat_cons (step5373 p h) (sat_cons (step4282 p h) (sat_cons (step1451 p h) (sat_cons (step1851 p h) (sat_cons (step5712 p h) (sat_cons (step5696 p h) (sat_cons (step1910 p h) (sat_cons (step5501 p h) (sat_cons (step1774 p h) (sat_cons (step567 p h) (sat_cons (step4317 p h) (sat_cons (step1361 p h) (sat_cons (step1603 p h) (sat_cons (step938 p h) (sat_cons (step5520 p h) (sat_cons (step5725 p h) (sat_cons (step1369 p h) (sat_cons (step2123 p h) (sat_cons (step1360 p h) (sat_cons (step1094 p h) (sat_cons (step597 p h) (sat_cons (step2126 p h) (sat_cons (step1592 p h) (sat_cons (step3457 p h) (sat_cons (step1291 p h) (sat_cons (step1923 p h) (sat_cons (step5377 p h) (sat_cons (step1312 p h) (sat_cons (step5376 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))
def c5860 : List Lit := [(1594, true), (21, false), (111, false)]
theorem step5860 (p : Nat → Bool) (h : Constraints p) : clause p c5860 = true :=
  Snake9.TreeRup.prove_clause [c5738, c1880, c5713, c5712, c5709, c1373, c1377, c5702, c5692, c5694, c990, c4835, c5765, c1834, c2136, c5716, c1881, c1209, c5696, c1822, c1603, c1910, c938, c939, c12, c5739, c1325, c1326, c4264, c4317, c5501, c2552, c1361, c1774, c5373, c567, c4282, c1451, c1851, c5859, c1020, c1821, c5510, c1201, c970, c1835, c1158, c980, c5795, c2123, c1013, c5541, c1094, c994, c2126, c985, c1592, c3457, c4202, c5535, c1291, c1352, c1791, c1311, c5377, c569, c5521, c1314, c1388, c1323, c1369, c1313, c1360, c5376] c5860 (by decide) p (sat_cons (step5738 p h) (sat_cons (step1880 p h) (sat_cons (step5713 p h) (sat_cons (step5712 p h) (sat_cons (step5709 p h) (sat_cons (step1373 p h) (sat_cons (step1377 p h) (sat_cons (step5702 p h) (sat_cons (step5692 p h) (sat_cons (step5694 p h) (sat_cons (step990 p h) (sat_cons (step4835 p h) (sat_cons (step5765 p h) (sat_cons (step1834 p h) (sat_cons (step2136 p h) (sat_cons (step5716 p h) (sat_cons (step1881 p h) (sat_cons (step1209 p h) (sat_cons (step5696 p h) (sat_cons (step1822 p h) (sat_cons (step1603 p h) (sat_cons (step1910 p h) (sat_cons (step938 p h) (sat_cons (step939 p h) (sat_cons (step12 p h) (sat_cons (step5739 p h) (sat_cons (step1325 p h) (sat_cons (step1326 p h) (sat_cons (step4264 p h) (sat_cons (step4317 p h) (sat_cons (step5501 p h) (sat_cons (step2552 p h) (sat_cons (step1361 p h) (sat_cons (step1774 p h) (sat_cons (step5373 p h) (sat_cons (step567 p h) (sat_cons (step4282 p h) (sat_cons (step1451 p h) (sat_cons (step1851 p h) (sat_cons (step5859 p h) (sat_cons (step1020 p h) (sat_cons (step1821 p h) (sat_cons (step5510 p h) (sat_cons (step1201 p h) (sat_cons (step970 p h) (sat_cons (step1835 p h) (sat_cons (step1158 p h) (sat_cons (step980 p h) (sat_cons (step5795 p h) (sat_cons (step2123 p h) (sat_cons (step1013 p h) (sat_cons (step5541 p h) (sat_cons (step1094 p h) (sat_cons (step994 p h) (sat_cons (step2126 p h) (sat_cons (step985 p h) (sat_cons (step1592 p h) (sat_cons (step3457 p h) (sat_cons (step4202 p h) (sat_cons (step5535 p h) (sat_cons (step1291 p h) (sat_cons (step1352 p h) (sat_cons (step1791 p h) (sat_cons (step1311 p h) (sat_cons (step5377 p h) (sat_cons (step569 p h) (sat_cons (step5521 p h) (sat_cons (step1314 p h) (sat_cons (step1388 p h) (sat_cons (step1323 p h) (sat_cons (step1369 p h) (sat_cons (step1313 p h) (sat_cons (step1360 p h) (sat_cons (step5376 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c5861 : List Lit := [(21, false), (111, false)]
theorem step5861 (p : Nat → Bool) (h : Constraints p) : clause p c5861 = true :=
  Snake9.LocalRup.prove_clause [c5692, c4835, c5765, c5709, c5738, c1880, c5860, c5428, c5599, c2451, c3093, c1881, c5792, c1094, c1821, c2123, c5725] c5861 (by decide) p (sat_cons (step5692 p h) (sat_cons (step4835 p h) (sat_cons (step5765 p h) (sat_cons (step5709 p h) (sat_cons (step5738 p h) (sat_cons (step1880 p h) (sat_cons (step5860 p h) (sat_cons (step5428 p h) (sat_cons (step5599 p h) (sat_cons (step2451 p h) (sat_cons (step3093 p h) (sat_cons (step1881 p h) (sat_cons (step5792 p h) (sat_cons (step1094 p h) (sat_cons (step1821 p h) (sat_cons (step2123 p h) (sat_cons (step5725 p h) (sat_nil p))))))))))))))))))
def c5862 : List Lit := [(1657, true), (98, false), (1664, true), (80, false), (1647, false), (25, true)]
theorem step5862 (p : Nat → Bool) (h : Constraints p) : clause p c5862 = true :=
  Snake9.LocalRup.prove_clause [c1999, c5715] c5862 (by decide) p (sat_cons (step1999 p h) (sat_cons (step5715 p h) (sat_nil p)))
def c5863 : List Lit := [(98, false), (115, true), (1691, true), (1658, true), (1594, false), (80, false), (1647, false), (111, false)]
theorem step5863 (p : Nat → Bool) (h : Constraints p) : clause p c5863 = true :=
  Snake9.LocalRup.prove_clause [c2278, c1406, c1373, c1377, c1388, c1369, c5692, c5590, c1879, c5862, c4078, c1411, c4548, c1773, c2131, c1610] c5863 (by decide) p (sat_cons (step2278 p h) (sat_cons (step1406 p h) (sat_cons (step1373 p h) (sat_cons (step1377 p h) (sat_cons (step1388 p h) (sat_cons (step1369 p h) (sat_cons (step5692 p h) (sat_cons (step5590 p h) (sat_cons (step1879 p h) (sat_cons (step5862 p h) (sat_cons (step4078 p h) (sat_cons (step1411 p h) (sat_cons (step4548 p h) (sat_cons (step1773 p h) (sat_cons (step2131 p h) (sat_cons (step1610 p h) (sat_nil p)))))))))))))))))
def c5864 : List Lit := [(1657, false), (1675, false), (1594, false), (1711, true), (111, false)]
theorem step5864 (p : Nat → Bool) (h : Constraints p) : clause p c5864 = true :=
  Snake9.LocalRup.prove_clause [c1381, c1853, c1443, c1410, c1411, c1451, c1384, c1301, c1596] c5864 (by decide) p (sat_cons (step1381 p h) (sat_cons (step1853 p h) (sat_cons (step1443 p h) (sat_cons (step1410 p h) (sat_cons (step1411 p h) (sat_cons (step1451 p h) (sat_cons (step1384 p h) (sat_cons (step1301 p h) (sat_cons (step1596 p h) (sat_nil p))))))))))
def c5865 : List Lit := [(115, true), (1594, false), (80, false), (1647, false), (1711, true), (111, false)]
theorem step5865 (p : Nat → Bool) (h : Constraints p) : clause p c5865 = true :=
  Snake9.LocalRup.prove_clause [c1853, c1443, c4363, c2278, c1333, c1373, c1377, c1381, c1404, c1457, c1302, c5863, c5864, c3467, c1624, c1349, c1327, c618, c1318, c1791, c569, c1314, c1316, c1317, c1320, c1345, c1311, c1334, c5526, c5314, c1329, c1301, c1451, c1626, c1405, c1608, c1610, c1264, c1358, c1593, c4554] c5865 (by decide) p (sat_cons (step1853 p h) (sat_cons (step1443 p h) (sat_cons (step4363 p h) (sat_cons (step2278 p h) (sat_cons (step1333 p h) (sat_cons (step1373 p h) (sat_cons (step1377 p h) (sat_cons (step1381 p h) (sat_cons (step1404 p h) (sat_cons (step1457 p h) (sat_cons (step1302 p h) (sat_cons (step5863 p h) (sat_cons (step5864 p h) (sat_cons (step3467 p h) (sat_cons (step1624 p h) (sat_cons (step1349 p h) (sat_cons (step1327 p h) (sat_cons (step618 p h) (sat_cons (step1318 p h) (sat_cons (step1791 p h) (sat_cons (step569 p h) (sat_cons (step1314 p h) (sat_cons (step1316 p h) (sat_cons (step1317 p h) (sat_cons (step1320 p h) (sat_cons (step1345 p h) (sat_cons (step1311 p h) (sat_cons (step1334 p h) (sat_cons (step5526 p h) (sat_cons (step5314 p h) (sat_cons (step1329 p h) (sat_cons (step1301 p h) (sat_cons (step1451 p h) (sat_cons (step1626 p h) (sat_cons (step1405 p h) (sat_cons (step1608 p h) (sat_cons (step1610 p h) (sat_cons (step1264 p h) (sat_cons (step1358 p h) (sat_cons (step1593 p h) (sat_cons (step4554 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))
def c5866 : List Lit := [(1657, true), (1594, false), (80, false), (1647, false), (1711, true), (111, false)]
theorem step5866 (p : Nat → Bool) (h : Constraints p) : clause p c5866 = true :=
  Snake9.LocalRup.prove_clause [c2278, c5865, c1796, c643, c1361, c1364, c1383, c1404, c1457, c1302, c1853, c1443, c1406, c1390, c1370, c1333, c5692, c3467, c1624, c1349, c5862, c1327, c618, c1791, c569, c1314, c1320, c1311, c1312, c5526, c1301, c1451, c1405, c1384, c1610, c1377, c1358, c1359, c1372, c1602, c2332, c5573] c5866 (by decide) p (sat_cons (step2278 p h) (sat_cons (step5865 p h) (sat_cons (step1796 p h) (sat_cons (step643 p h) (sat_cons (step1361 p h) (sat_cons (step1364 p h) (sat_cons (step1383 p h) (sat_cons (step1404 p h) (sat_cons (step1457 p h) (sat_cons (step1302 p h) (sat_cons (step1853 p h) (sat_cons (step1443 p h) (sat_cons (step1406 p h) (sat_cons (step1390 p h) (sat_cons (step1370 p h) (sat_cons (step1333 p h) (sat_cons (step5692 p h) (sat_cons (step3467 p h) (sat_cons (step1624 p h) (sat_cons (step1349 p h) (sat_cons (step5862 p h) (sat_cons (step1327 p h) (sat_cons (step618 p h) (sat_cons (step1791 p h) (sat_cons (step569 p h) (sat_cons (step1314 p h) (sat_cons (step1320 p h) (sat_cons (step1311 p h) (sat_cons (step1312 p h) (sat_cons (step5526 p h) (sat_cons (step1301 p h) (sat_cons (step1451 p h) (sat_cons (step1405 p h) (sat_cons (step1384 p h) (sat_cons (step1610 p h) (sat_cons (step1377 p h) (sat_cons (step1358 p h) (sat_cons (step1359 p h) (sat_cons (step1372 p h) (sat_cons (step1602 p h) (sat_cons (step2332 p h) (sat_cons (step5573 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))
def c5867 : List Lit := [(1594, false), (80, false), (1647, false), (1711, true), (111, false)]
theorem step5867 (p : Nat → Bool) (h : Constraints p) : clause p c5867 = true :=
  Snake9.LocalRup.prove_clause [c1853, c1443, c5865, c1796, c643, c1361, c1364, c1383, c5866, c1410, c1411, c3926, c5864, c1451, c1610, c1377, c1301, c1359, c1372, c1642, c2332] c5867 (by decide) p (sat_cons (step1853 p h) (sat_cons (step1443 p h) (sat_cons (step5865 p h) (sat_cons (step1796 p h) (sat_cons (step643 p h) (sat_cons (step1361 p h) (sat_cons (step1364 p h) (sat_cons (step1383 p h) (sat_cons (step5866 p h) (sat_cons (step1410 p h) (sat_cons (step1411 p h) (sat_cons (step3926 p h) (sat_cons (step5864 p h) (sat_cons (step1451 p h) (sat_cons (step1610 p h) (sat_cons (step1377 p h) (sat_cons (step1301 p h) (sat_cons (step1359 p h) (sat_cons (step1372 p h) (sat_cons (step1642 p h) (sat_cons (step2332 p h) (sat_nil p))))))))))))))))))))))
def c5868 : List Lit := [(1675, true), (109, false), (1657, false), (1594, true), (80, false), (111, false)]
theorem step5868 (p : Nat → Bool) (h : Constraints p) : clause p c5868 = true :=
  Snake9.LocalRup.prove_clause [c2637, c5692, c1376, c1377, c1375, c1372, c1373, c4551, c664, c1796, c643, c4854, c5071, c1642, c1799, c1361, c1850, c4557, c1364, c982, c1383, c990, c1410, c5500, c1442, c1881] c5868 (by decide) p (sat_cons (step2637 p h) (sat_cons (step5692 p h) (sat_cons (step1376 p h) (sat_cons (step1377 p h) (sat_cons (step1375 p h) (sat_cons (step1372 p h) (sat_cons (step1373 p h) (sat_cons (step4551 p h) (sat_cons (step664 p h) (sat_cons (step1796 p h) (sat_cons (step643 p h) (sat_cons (step4854 p h) (sat_cons (step5071 p h) (sat_cons (step1642 p h) (sat_cons (step1799 p h) (sat_cons (step1361 p h) (sat_cons (step1850 p h) (sat_cons (step4557 p h) (sat_cons (step1364 p h) (sat_cons (step982 p h) (sat_cons (step1383 p h) (sat_cons (step990 p h) (sat_cons (step1410 p h) (sat_cons (step5500 p h) (sat_cons (step1442 p h) (sat_cons (step1881 p h) (sat_nil p)))))))))))))))))))))))))))
def c5869 : List Lit := [(1680, true), (1657, false), (80, false), (1647, false), (1711, true), (111, false)]
theorem step5869 (p : Nat → Bool) (h : Constraints p) : clause p c5869 = true :=
  Snake9.LocalRup.prove_clause [c5867, c5861, c5692, c4835, c1382, c1610, c1359, c5868, c1384, c3682, c1364, c1596, c1881, c1361, c1850, c1795, c643, c2126, c1443, c1373, c5576, c1612, c5723, c1094, c1378, c969, c1821, c2123, c1375, c1799, c4557, c982, c5848, c990, c5667, c1016, c973, c978, c981, c1011, c970, c1820, c5766, c1193, c1164] c5869 (by decide) p (sat_cons (step5867 p h) (sat_cons (step5861 p h) (sat_cons (step5692 p h) (sat_cons (step4835 p h) (sat_cons (step1382 p h) (sat_cons (step1610 p h) (sat_cons (step1359 p h) (sat_cons (step5868 p h) (sat_cons (step1384 p h) (sat_cons (step3682 p h) (sat_cons (step1364 p h) (sat_cons (step1596 p h) (sat_cons (step1881 p h) (sat_cons (step1361 p h) (sat_cons (step1850 p h) (sat_cons (step1795 p h) (sat_cons (step643 p h) (sat_cons (step2126 p h) (sat_cons (step1443 p h) (sat_cons (step1373 p h) (sat_cons (step5576 p h) (sat_cons (step1612 p h) (sat_cons (step5723 p h) (sat_cons (step1094 p h) (sat_cons (step1378 p h) (sat_cons (step969 p h) (sat_cons (step1821 p h) (sat_cons (step2123 p h) (sat_cons (step1375 p h) (sat_cons (step1799 p h) (sat_cons (step4557 p h) (sat_cons (step982 p h) (sat_cons (step5848 p h) (sat_cons (step990 p h) (sat_cons (step5667 p h) (sat_cons (step1016 p h) (sat_cons (step973 p h) (sat_cons (step978 p h) (sat_cons (step981 p h) (sat_cons (step1011 p h) (sat_cons (step970 p h) (sat_cons (step1820 p h) (sat_cons (step5766 p h) (sat_cons (step1193 p h) (sat_cons (step1164 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))
def c5870 : List Lit := [(110, false), (1618, true), (1658, true), (80, false), (1647, false)]
theorem step5870 (p : Nat → Bool) (h : Constraints p) : clause p c5870 = true :=
  Snake9.LocalRup.prove_clause [c1848, c4360, c1264, c1333, c1353, c5578, c1322, c1323, c1350, c1314, c1315, c1334, c537, c1329, c4554] c5870 (by decide) p (sat_cons (step1848 p h) (sat_cons (step4360 p h) (sat_cons (step1264 p h) (sat_cons (step1333 p h) (sat_cons (step1353 p h) (sat_cons (step5578 p h) (sat_cons (step1322 p h) (sat_cons (step1323 p h) (sat_cons (step1350 p h) (sat_cons (step1314 p h) (sat_cons (step1315 p h) (sat_cons (step1334 p h) (sat_cons (step537 p h) (sat_cons (step1329 p h) (sat_cons (step4554 p h) (sat_nil p))))))))))))))))
def c5871 : List Lit := [(1668, true), (110, true), (1672, true), (88, false), (80, false), (111, false)]
theorem step5871 (p : Nat → Bool) (h : Constraints p) : clause p c5871 = true :=
  Snake9.LocalRup.prove_clause [c1358, c1369, c1360, c1367, c4551, c1361, c1374, c1795, c643] c5871 (by decide) p (sat_cons (step1358 p h) (sat_cons (step1369 p h) (sat_cons (step1360 p h) (sat_cons (step1367 p h) (sat_cons (step4551 p h) (sat_cons (step1361 p h) (sat_cons (step1374 p h) (sat_cons (step1795 p h) (sat_cons (step643 p h) (sat_nil p))))))))))
def c5872 : List Lit := [(1657, false), (80, false), (1647, false), (1711, true), (111, false)]
theorem step5872 (p : Nat → Bool) (h : Constraints p) : clause p c5872 = true :=
  Snake9.LocalRup.prove_clause [c5867, c1871, c1412, c1390, c5869, c1417, c1411, c1443, c1850, c1642, c1596, c1385, c1379, c5870, c5871, c1388, c1377, c5868, c1373, c1360, c1796, c643, c1370, c1361] c5872 (by decide) p (sat_cons (step5867 p h) (sat_cons (step1871 p h) (sat_cons (step1412 p h) (sat_cons (step1390 p h) (sat_cons (step5869 p h) (sat_cons (step1417 p h) (sat_cons (step1411 p h) (sat_cons (step1443 p h) (sat_cons (step1850 p h) (sat_cons (step1642 p h) (sat_cons (step1596 p h) (sat_cons (step1385 p h) (sat_cons (step1379 p h) (sat_cons (step5870 p h) (sat_cons (step5871 p h) (sat_cons (step1388 p h) (sat_cons (step1377 p h) (sat_cons (step5868 p h) (sat_cons (step1373 p h) (sat_cons (step1360 p h) (sat_cons (step1796 p h) (sat_cons (step643 p h) (sat_cons (step1370 p h) (sat_cons (step1361 p h) (sat_nil p)))))))))))))))))))))))))
def c5873 : List Lit := [(115, false), (1664, false), (98, false), (71, false), (80, false), (1656, false), (111, false)]
theorem step5873 (p : Nat → Bool) (h : Constraints p) : clause p c5873 = true :=
  Snake9.LocalRup.prove_clause [c5692, c2136, c1796, c643, c4854, c5071, c1361, c1370, c1390, c1406, c1870, c1881, c5256, c5856, c990, c1910, c982] c5873 (by decide) p (sat_cons (step5692 p h) (sat_cons (step2136 p h) (sat_cons (step1796 p h) (sat_cons (step643 p h) (sat_cons (step4854 p h) (sat_cons (step5071 p h) (sat_cons (step1361 p h) (sat_cons (step1370 p h) (sat_cons (step1390 p h) (sat_cons (step1406 p h) (sat_cons (step1870 p h) (sat_cons (step1881 p h) (sat_cons (step5256 p h) (sat_cons (step5856 p h) (sat_cons (step990 p h) (sat_cons (step1910 p h) (sat_cons (step982 p h) (sat_nil p))))))))))))))))))
def c5874 : List Lit := [(16, true), (1468, true), (1571, true), (26, true), (57, true), (112, false), (115, true), (1594, true), (80, false), (1647, false), (111, false)]
theorem step5874 (p : Nat → Bool) (h : Constraints p) : clause p c5874 = true :=
  Snake9.LocalRup.prove_clause [c982, c990, c5861, c5692, c4835, c969, c5848, c5667, c973, c978, c981, c1011, c970, c1820, c5843, c1193] c5874 (by decide) p (sat_cons (step982 p h) (sat_cons (step990 p h) (sat_cons (step5861 p h) (sat_cons (step5692 p h) (sat_cons (step4835 p h) (sat_cons (step969 p h) (sat_cons (step5848 p h) (sat_cons (step5667 p h) (sat_cons (step973 p h) (sat_cons (step978 p h) (sat_cons (step981 p h) (sat_cons (step1011 p h) (sat_cons (step970 p h) (sat_cons (step1820 p h) (sat_cons (step5843 p h) (sat_cons (step1193 p h) (sat_nil p)))))))))))))))))
def c5875 : List Lit := [(1618, true), (1657, true), (1594, true), (80, false), (1682, true), (1647, false), (111, false)]
theorem step5875 (p : Nat → Bool) (h : Constraints p) : clause p c5875 = true :=
  Snake9.TreeRup.prove_clause [c1624, c4520, c1333, c1349, c3467, c2637, c2278, c5692, c4835, c5765, c1642, c4364, c5526, c615, c1311, c1791, c1761, c1320, c1314, c569, c1327, c5862, c1773, c1774, c1369, c596, c1389, c1379, c5873, c1373, c1374, c4621, c1377, c1378, c1794, c1795, c2126, c1388, c1375, c656, c659, c486, c1094, c1406, c1799, c2123, c1870, c4557, c1158, c1881, c982, c568, c1201, c990, c5094, c838, c1821, c5312, c1016, c839, c1186, c1810, c1160, c846, c841, c5874, c267, c3807, c1783, c3806, c574] c5875 (by decide) p (sat_cons (step1624 p h) (sat_cons (step4520 p h) (sat_cons (step1333 p h) (sat_cons (step1349 p h) (sat_cons (step3467 p h) (sat_cons (step2637 p h) (sat_cons (step2278 p h) (sat_cons (step5692 p h) (sat_cons (step4835 p h) (sat_cons (step5765 p h) (sat_cons (step1642 p h) (sat_cons (step4364 p h) (sat_cons (step5526 p h) (sat_cons (step615 p h) (sat_cons (step1311 p h) (sat_cons (step1791 p h) (sat_cons (step1761 p h) (sat_cons (step1320 p h) (sat_cons (step1314 p h) (sat_cons (step569 p h) (sat_cons (step1327 p h) (sat_cons (step5862 p h) (sat_cons (step1773 p h) (sat_cons (step1774 p h) (sat_cons (step1369 p h) (sat_cons (step596 p h) (sat_cons (step1389 p h) (sat_cons (step1379 p h) (sat_cons (step5873 p h) (sat_cons (step1373 p h) (sat_cons (step1374 p h) (sat_cons (step4621 p h) (sat_cons (step1377 p h) (sat_cons (step1378 p h) (sat_cons (step1794 p h) (sat_cons (step1795 p h) (sat_cons (step2126 p h) (sat_cons (step1388 p h) (sat_cons (step1375 p h) (sat_cons (step656 p h) (sat_cons (step659 p h) (sat_cons (step486 p h) (sat_cons (step1094 p h) (sat_cons (step1406 p h) (sat_cons (step1799 p h) (sat_cons (step2123 p h) (sat_cons (step1870 p h) (sat_cons (step4557 p h) (sat_cons (step1158 p h) (sat_cons (step1881 p h) (sat_cons (step982 p h) (sat_cons (step568 p h) (sat_cons (step1201 p h) (sat_cons (step990 p h) (sat_cons (step5094 p h) (sat_cons (step838 p h) (sat_cons (step1821 p h) (sat_cons (step5312 p h) (sat_cons (step1016 p h) (sat_cons (step839 p h) (sat_cons (step1186 p h) (sat_cons (step1810 p h) (sat_cons (step1160 p h) (sat_cons (step846 p h) (sat_cons (step841 p h) (sat_cons (step5874 p h) (sat_cons (step267 p h) (sat_cons (step3807 p h) (sat_cons (step1783 p h) (sat_cons (step3806 p h) (sat_cons (step574 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c5876 : List Lit := [(16, false), (26, true), (1571, true), (1538, false), (108, true), (97, true), (106, false), (71, false), (80, false), (111, false)]
theorem step5876 (p : Nat → Bool) (h : Constraints p) : clause p c5876 = true :=
  Snake9.LocalRup.prove_clause [c5692, c4835, c5765, c982, c5094, c990, c5312, c1186, c1160, c1158, c1201, c1044, c5775, c5440, c5478, c267, c3807, c968, c1783, c5826, c1681, c3806, c4251, c3439, c82] c5876 (by decide) p (sat_cons (step5692 p h) (sat_cons (step4835 p h) (sat_cons (step5765 p h) (sat_cons (step982 p h) (sat_cons (step5094 p h) (sat_cons (step990 p h) (sat_cons (step5312 p h) (sat_cons (step1186 p h) (sat_cons (step1160 p h) (sat_cons (step1158 p h) (sat_cons (step1201 p h) (sat_cons (step1044 p h) (sat_cons (step5775 p h) (sat_cons (step5440 p h) (sat_cons (step5478 p h) (sat_cons (step267 p h) (sat_cons (step3807 p h) (sat_cons (step968 p h) (sat_cons (step1783 p h) (sat_cons (step5826 p h) (sat_cons (step1681 p h) (sat_cons (step3806 p h) (sat_cons (step4251 p h) (sat_cons (step3439 p h) (sat_cons (step82 p h) (sat_nil p))))))))))))))))))))))))))
end B112E040
