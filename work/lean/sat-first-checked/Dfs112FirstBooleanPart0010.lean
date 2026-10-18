import Dfs112FirstBooleanPart0009
namespace Dfs112FirstBoolean
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem step1948 (p : Nat → Bool) (h : Constraints p) : p 62 = false ∨ p 61 = false ∨ p 56 = false ∨ p 59 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 62 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 61 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 56 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 59 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 57 = false := (Or.elim (step210 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u2 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u3 l2))) (fun r2 => (False.elim (bool_contra u0 r2))))))))
  have t1 : p 63 = true := (Or.elim (step1764 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => (False.elim (bool_contra u0 r1))))))
  exact (Or.elim (step235 p h) (fun l0 => (bool_contra t1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u3 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra u1 l2)) (fun r2 => (bool_contra u0 r2)))))))

theorem step1949 (p : Nat → Bool) (h : Constraints p) : p 73 = false ∨ p 75 = true ∨ p 1681 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 73 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 75 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1681 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 104 = true := (Or.elim (step1331 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u2))))
  have t1 : p 105 = true := (Or.elim (step1330 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u2))))
  have t2 : p 106 = false := (Or.elim (step573 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u0 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t0 l2))) (fun r2 => (False.elim (bool_contra t1 r2))))))))
  exact (Or.elim (step1778 p h) (fun l0 => (bool_contra l0 u1)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t2)) (fun r1 => (bool_contra u0 r1)))))

theorem step1950 (p : Nat → Bool) (h : Constraints p) : p 1615 = true ∨ p 58 = false ∨ p 66 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1615 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 58 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 66 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 69 = true := (Or.elim (step1201 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t1 : p 68 = true := (Or.elim (step1202 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t2 : p 71 = true := (Or.elim (step1774 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => r0))
  exact (Or.elim (step258 p h) (fun l0 => (bool_contra t1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u1 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra u2 l2)) (fun r2 => (bool_contra t2 r2)))))))

theorem step1951 (p : Nat → Bool) (h : Constraints p) : p 1703 = true ∨ p 106 = true ∨ p 105 = false ∨ p 94 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1703 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 106 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 105 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 94 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 117 = true := (Or.elim (step1378 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t1 : p 116 = true := (Or.elim (step1379 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t2 : p 115 = false := (Or.elim (step624 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u2 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t1 l2))) (fun r2 => (False.elim (bool_contra t0 r2))))))))
  exact (Or.elim (step1843 p h) (fun l0 => (bool_contra l0 t2)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 u3)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t1 l2)) (fun r2 => (bool_contra r2 u1)))))))

theorem step1952 (p : Nat → Bool) (h : Constraints p) : p 116 = false ∨ p 117 = false ∨ p 106 = true ∨ p 105 = false ∨ p 94 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 116 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 117 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 106 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 105 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 94 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr hl)))))
  have t0 : p 115 = true := (Or.elim (step1843 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u4))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u0 l2))) (fun r2 => (False.elim (bool_contra r2 u2))))))))
  exact (Or.elim (step624 p h) (fun l0 => (bool_contra t0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u3 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra u0 l2)) (fun r2 => (bool_contra u1 r2)))))))

theorem step1953 (p : Nat → Bool) (h : Constraints p) : p 1544 = true ∨ p 1533 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1544 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1533 = false := bool_false_of_not_true (fun hl => hc (Or.inr hl))
  have t0 : p 45 = true := (Or.elim (step1071 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t1 : p 41 = false := (Or.elim (step1630 p h) (fun l0 => (False.elim (bool_contra l0 u0))) (fun r0 => r0))
  have t2 : p 42 = false := (Or.elim (step1612 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => r0))
  have t3 : p 1528 = true := (Or.elim (step1044 p h) (fun l0 => (False.elim (bool_contra l0 t1))) (fun r0 => r0))
  have t4 : p 1530 = true := (Or.elim (step1048 p h) (fun l0 => (False.elim (bool_contra l0 t2))) (fun r0 => r0))
  exact (Or.elim (step1053 p h) (fun l0 => (bool_contra t3 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t4 l1)) (fun r1 => (bool_contra r1 u1)))))

theorem step1954 (p : Nat → Bool) (h : Constraints p) : p 1570 = true ∨ p 1544 = false ∨ p 1524 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1570 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1544 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1524 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 1548 = true := (Or.elim (step1078 p h) (fun l0 => (False.elim (bool_contra u1 l0))) (fun r0 => r0))
  have t1 : p 1560 = true := (Or.elim (step1102 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => r0))
  have t2 : p 1536 = true := (Or.elim (step1061 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => r0))
  have t3 : p 1561 = false := (Or.elim (step1121 p h) (fun l0 => (False.elim (bool_contra t2 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t4 : p 1537 = false := (Or.elim (step1126 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t1 l1))) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t5 : p 1549 = false := (Or.elim (step1107 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t3))))
  have t6 : p 1556 = false := (Or.elim (step1103 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t3))))))
  have t7 : p 1532 = false := (Or.elim (step1062 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t4))))))
  have t8 : p 1546 = false := (Or.elim (step1079 p h) (fun l0 => (False.elim (bool_contra u1 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t5))))))
  have t9 : p 1552 = false := (Or.elim (step1092 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t6))))
  have t10 : p 1530 = false := (Or.elim (step1050 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t7))))
  have t11 : p 1528 = false := (Or.elim (step1052 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t7))))
  have t12 : p 50 = true := (Or.elim (step1073 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t8))))
  have t13 : p 53 = true := (Or.elim (step1085 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t9))))
  have t14 : p 43 = true := (Or.elim (step1047 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t10))))
  have t15 : p 42 = true := (Or.elim (step1048 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t10))))
  have t16 : p 39 = true := (Or.elim (step1045 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t11))))
  have t17 : p 38 = false := (Or.elim (step132 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t16 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t15 l2))) (fun r2 => (False.elim (bool_contra t14 r2))))))))
  exact (Or.elim (step1596 p h) (fun l0 => (bool_contra t13 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t12 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 t17)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra t16 l3)) (fun r3 => (bool_contra t14 r3)))))))))

theorem step1955 (p : Nat → Bool) (h : Constraints p) : p 43 = false ∨ p 42 = false ∨ p 53 = false ∨ p 1546 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 43 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 42 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 53 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 1546 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 49 = true := (Or.elim (step1074 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u3))))
  have t1 : p 54 = true := (Or.elim (step1747 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => r0))
  have t2 : p 50 = true := (Or.elim (step1073 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u3))))
  have t3 : p 52 = false := (Or.elim (step175 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u0 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t2 l2))) (fun r2 => (False.elim (bool_contra u2 r2))))))))
  have t4 : p 51 = true := (Or.elim (step1751 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t3))) (fun r1 => (False.elim (bool_contra t2 r1))))))
  have t5 : p 44 = false := (Or.elim (step177 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t4 l2))) (fun r2 => (False.elim (bool_contra t1 r2))))))))
  have t6 : p 38 = true := (Or.elim (step1742 p h) (fun l0 => (False.elim (bool_contra l0 t3))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u0 l2))) (fun r2 => (False.elim (bool_contra r2 t5))))))))
  have t7 : p 46 = true := (Or.elim (step1741 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t3))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra l2 t5))) (fun r2 => (False.elim (bool_contra u0 r2))))))))
  exact (Or.elim (step1517 p h) (fun l0 => (bool_contra t6 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u1 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra u0 l2)) (fun r2 => (bool_contra t7 r2)))))))

theorem step1956 (p : Nat → Bool) (h : Constraints p) : p 110 = false ∨ p 101 = false ∨ p 44 = true ∨ p 61 = false ∨ p 106 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 110 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 101 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 44 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 61 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 106 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr hl)))))
  have t0 : p 89 = false := (Or.elim (step439 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u3 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u1 l2))) (fun r2 => (False.elim (bool_contra u0 r2))))))))
  exact (Or.elim (step1833 p h) (fun l0 => (bool_contra l0 u2)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u0 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 t0)) (fun r2 => (bool_contra r2 u4)))))))

theorem step1957 (p : Nat → Bool) (h : Constraints p) : p 1508 = true ∨ p 7 = false ∨ p 61 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1508 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 7 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 61 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 1475 = true := (step1931 p h)
  have t1 : p 1476 = false := (Or.elim (step1874 p h) (fun l0 => (False.elim (bool_contra l0 u0))) (fun r0 => r0))
  have t2 : p 1498 = false := (Or.elim (step1012 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t3 : p 1494 = false := (Or.elim (step995 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t2))))
  have t4 : p 1485 = false := (Or.elim (step1868 p h) (fun l0 => (False.elim (bool_contra l0 t2))) (fun r0 => r0))
  have t5 : p 1481 = false := (Or.elim (step975 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t4))))
  have t6 : p 15 = true := (Or.elim (step968 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t5))))
  have t7 : p 26 = false := (Or.elim (step40 p h) (fun l0 => (False.elim (bool_contra u1 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t6 l1))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra u2 r2))))))))
  have t8 : p 6 = false := (Or.elim (step38 p h) (fun l0 => (False.elim (bool_contra u1 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t6 l2))) (fun r2 => (False.elim (bool_contra u2 r2))))))))
  have t9 : p 2 = false := (Or.elim (step35 p h) (fun l0 => (False.elim (bool_contra u1 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t6 l2))) (fun r2 => (False.elim (bool_contra u2 r2))))))))
  have t10 : p 1491 = true := (Or.elim (step985 p h) (fun l0 => (False.elim (bool_contra l0 t7))) (fun r0 => r0))
  have t11 : p 1461 = true := (Or.elim (step928 p h) (fun l0 => (False.elim (bool_contra l0 t8))) (fun r0 => r0))
  have t12 : p 1489 = false := (Or.elim (step990 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t10 l1))) (fun r1 => (False.elim (bool_contra r1 t3))))))
  have t13 : p 1464 = true := (Or.elim (step934 p h) (fun l0 => (False.elim (bool_contra l0 t9))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t11 l1))) (fun r1 => r1))))
  have t14 : p 24 = true := (Or.elim (step981 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t12))))
  have t15 : p 1470 = false := (Or.elim (step960 p h) (fun l0 => (False.elim (bool_contra t13 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t1))))))
  have t16 : p 1468 = false := (Or.elim (step942 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t15))))
  have t17 : p 1466 = false := (Or.elim (step944 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t15))))
  have t18 : p 13 = true := (Or.elim (step939 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t16))))
  have t19 : p 8 = true := (Or.elim (step937 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t17))))
  have t20 : p 5 = true := (Or.elim (step1708 p h) (fun l0 => (False.elim (bool_contra t18 l0))) (fun r0 => r0))
  exact (Or.elim (step21 p h) (fun l0 => (bool_contra t20 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t19 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t18 l2)) (fun r2 => (bool_contra t14 r2)))))))

theorem step1958 (p : Nat → Bool) (h : Constraints p) : p 1485 = true ∨ p 1661 = true ∨ p 1639 = false ∨ p 1612 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1485 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1661 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1639 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 1612 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 1483 = false := (Or.elim (step973 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t1 : p 1481 = false := (Or.elim (step975 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t2 : p 19 = true := (Or.elim (step971 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t0))))
  have t3 : p 18 = true := (Or.elim (step967 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t1))))
  have t4 : p 73 = false := (Or.elim (step1682 p h) (fun l0 => (False.elim (bool_contra t2 l0))) (fun r0 => r0))
  have t5 : p 72 = false := (Or.elim (step1781 p h) (fun l0 => (False.elim (bool_contra t3 l0))) (fun r0 => r0))
  have t6 : p 77 = false := (Or.elim (step1782 p h) (fun l0 => (False.elim (bool_contra t3 l0))) (fun r0 => r0))
  have t7 : p 1618 = true := (Or.elim (step1206 p h) (fun l0 => (False.elim (bool_contra l0 t5))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t4))) (fun r1 => r1))))
  have t8 : p 1631 = true := (Or.elim (step1234 p h) (fun l0 => (False.elim (bool_contra l0 t6))) (fun r0 => r0))
  have t9 : p 1620 = true := (Or.elim (step1208 p h) (fun l0 => (False.elim (bool_contra t7 l0))) (fun r0 => r0))
  have t10 : p 1649 = true := (Or.elim (step1648 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u2 l1))) (fun r1 => (False.elim (bool_contra t8 r1))))))
  have t11 : p 1626 = true := (Or.elim (step1225 p h) (fun l0 => (False.elim (bool_contra u3 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t9 l1))) (fun r1 => r1))))
  exact (Or.elim (step1302 p h) (fun l0 => (bool_contra t11 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t10 l1)) (fun r1 => (bool_contra r1 u1)))))

theorem step1959 (p : Nat → Bool) (h : Constraints p) : p 1509 = true ∨ p 18 = true ∨ p 1481 = false ∨ p 1498 = false ∨ p 7 = false ∨ p 61 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1509 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 18 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1481 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 1498 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 7 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 61 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl))))))
  have t0 : p 1475 = true := (step1931 p h)
  have t1 : p 1499 = false := (Or.elim (step1013 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t2 : p 1476 = false := (Or.elim (step1017 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u3 l1))) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t3 : p 1486 = false := (Or.elim (step1869 p h) (fun l0 => (False.elim (bool_contra l0 t1))) (fun r0 => r0))
  have t4 : p 24 = true := (Or.elim (step1917 p h) (fun l0 => (False.elim (bool_contra l0 t1))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra u2 r1))))))
  have t5 : p 1482 = false := (Or.elim (step978 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t3))))
  have t6 : p 15 = true := (Or.elim (step969 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u1))) (fun r1 => (False.elim (bool_contra r1 t5))))))
  have t7 : p 6 = false := (Or.elim (step38 p h) (fun l0 => (False.elim (bool_contra u4 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t6 l2))) (fun r2 => (False.elim (bool_contra u5 r2))))))))
  have t8 : p 2 = false := (Or.elim (step35 p h) (fun l0 => (False.elim (bool_contra u4 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t6 l2))) (fun r2 => (False.elim (bool_contra u5 r2))))))))
  have t9 : p 1461 = true := (Or.elim (step928 p h) (fun l0 => (False.elim (bool_contra l0 t7))) (fun r0 => r0))
  have t10 : p 1464 = true := (Or.elim (step934 p h) (fun l0 => (False.elim (bool_contra l0 t8))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t9 l1))) (fun r1 => r1))))
  have t11 : p 1470 = false := (Or.elim (step960 p h) (fun l0 => (False.elim (bool_contra t10 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t2))))))
  have t12 : p 1468 = false := (Or.elim (step942 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t11))))
  have t13 : p 1466 = false := (Or.elim (step944 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t11))))
  have t14 : p 13 = true := (Or.elim (step939 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t12))))
  have t15 : p 8 = true := (Or.elim (step937 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t13))))
  have t16 : p 5 = true := (Or.elim (step1708 p h) (fun l0 => (False.elim (bool_contra t14 l0))) (fun r0 => r0))
  exact (Or.elim (step21 p h) (fun l0 => (bool_contra t16 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t15 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t14 l2)) (fun r2 => (bool_contra t4 r2)))))))

theorem step1960 (p : Nat → Bool) (h : Constraints p) : p 1570 = true ∨ p 1524 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1570 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1524 = true := bool_true_of_not_false (fun hl => hc (Or.inr hl))
  have t0 : p 1538 = false := (Or.elim (step1132 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t1 : p 1544 = false := (Or.elim (step1954 p h) (fun l0 => (False.elim (bool_contra l0 u0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra u1 r1))))))
  have t2 : p 1533 = false := (Or.elim (step1063 p h) (fun l0 => (False.elim (bool_contra u1 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t0))))))
  exact (Or.elim (step1953 p h) (fun l0 => (bool_contra l0 t1)) (fun r0 => (bool_contra r0 t2)))

theorem step1961 (p : Nat → Bool) (h : Constraints p) : p 1510 = true ∨ p 1617 = true ∨ p 7 = false ∨ p 61 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1510 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1617 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 7 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 61 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 1475 = true := (step1931 p h)
  have t1 : p 73 = true := (Or.elim (step1204 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u1))))
  have t2 : p 19 = false := (Or.elim (step1682 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra t1 r0))))
  have t3 : p 1483 = true := (Or.elim (step971 p h) (fun l0 => (False.elim (bool_contra l0 t2))) (fun r0 => r0))
  have t4 : p 1486 = true := (Or.elim (step1574 p h) (fun l0 => (False.elim (bool_contra l0 u1))) (fun r0 => r0))
  have t5 : p 1499 = true := (Or.elim (step1869 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra t4 r0))))
  have t6 : p 72 = true := (Or.elim (step1205 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u1))))
  have t7 : p 18 = false := (Or.elim (step1781 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra t6 r0))))
  have t8 : p 1500 = false := (Or.elim (step1014 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t9 : p 1476 = false := (Or.elim (step1018 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t5 l1))) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t10 : p 1487 = false := (Or.elim (step1870 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t8))))
  have t11 : p 1494 = false := (Or.elim (step1002 p h) (fun l0 => (False.elim (bool_contra t4 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t8))))))
  have t12 : p 1482 = false := (Or.elim (step979 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t3 l1))) (fun r1 => (False.elim (bool_contra r1 t10))))))
  have t13 : p 15 = true := (Or.elim (step969 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t7))) (fun r1 => (False.elim (bool_contra r1 t12))))))
  have t14 : p 26 = false := (Or.elim (step40 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t13 l1))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra u3 r2))))))))
  have t15 : p 6 = false := (Or.elim (step38 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t13 l2))) (fun r2 => (False.elim (bool_contra u3 r2))))))))
  have t16 : p 2 = false := (Or.elim (step35 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t13 l2))) (fun r2 => (False.elim (bool_contra u3 r2))))))))
  have t17 : p 1491 = true := (Or.elim (step985 p h) (fun l0 => (False.elim (bool_contra l0 t14))) (fun r0 => r0))
  have t18 : p 1461 = true := (Or.elim (step928 p h) (fun l0 => (False.elim (bool_contra l0 t15))) (fun r0 => r0))
  have t19 : p 1489 = false := (Or.elim (step990 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t17 l1))) (fun r1 => (False.elim (bool_contra r1 t11))))))
  have t20 : p 1464 = true := (Or.elim (step934 p h) (fun l0 => (False.elim (bool_contra l0 t16))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t18 l1))) (fun r1 => r1))))
  have t21 : p 24 = true := (Or.elim (step981 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t19))))
  have t22 : p 1470 = false := (Or.elim (step960 p h) (fun l0 => (False.elim (bool_contra t20 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t9))))))
  have t23 : p 1468 = false := (Or.elim (step942 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t22))))
  have t24 : p 1466 = false := (Or.elim (step944 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t22))))
  have t25 : p 13 = true := (Or.elim (step939 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t23))))
  have t26 : p 8 = true := (Or.elim (step937 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t24))))
  have t27 : p 5 = true := (Or.elim (step1708 p h) (fun l0 => (False.elim (bool_contra t25 l0))) (fun r0 => r0))
  exact (Or.elim (step21 p h) (fun l0 => (bool_contra t27 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t26 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t25 l2)) (fun r2 => (bool_contra t21 r2)))))))

theorem step1962 (p : Nat → Bool) (h : Constraints p) : p 1476 = true ∨ p 2 = true ∨ p 6 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1476 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 2 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 6 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 1461 = true := (Or.elim (step928 p h) (fun l0 => (False.elim (bool_contra l0 u2))) (fun r0 => r0))
  have t1 : p 1464 = true := (Or.elim (step934 p h) (fun l0 => (False.elim (bool_contra l0 u1))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t0 l1))) (fun r1 => r1))))
  have t2 : p 1465 = false := (Or.elim (step964 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t3 : p 1470 = false := (Or.elim (step960 p h) (fun l0 => (False.elim (bool_contra t1 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t4 : p 1462 = false := (Or.elim (step935 p h) (fun l0 => (False.elim (bool_contra l0 u1))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t2))))))
  have t5 : p 1468 = false := (Or.elim (step942 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t3))))
  have t6 : p 1466 = false := (Or.elim (step944 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t3))))
  have t7 : p 4 = true := (Or.elim (step930 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u2))) (fun r1 => (False.elim (bool_contra r1 t4))))))
  have t8 : p 12 = true := (Or.elim (step940 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t5))))
  have t9 : p 10 = true := (Or.elim (step936 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t6))))
  exact (Or.elim (step1609 p h) (fun l0 => (bool_contra t8 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t7 l1)) (fun r1 => (bool_contra t9 r1)))))

theorem step1963 (p : Nat → Bool) (h : Constraints p) : p 1471 = true ∨ p 4 = false ∨ p 1555 = true ∨ p 75 = false ∨ p 1468 = false ∨ p 63 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1471 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 4 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1555 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 75 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 1468 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 63 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl))))))
  have t0 : p 1469 = false := (Or.elim (step943 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t1 : p 1466 = false := (Or.elim (step945 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u4 l1))) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t2 : p 10 = true := (Or.elim (step936 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t1))))
  have t3 : p 8 = true := (Or.elim (step937 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t1))))
  have t4 : p 12 = false := (Or.elim (step1609 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u1 l1))) (fun r1 => (False.elim (bool_contra t2 r1))))))
  have t5 : p 3 = false := (Or.elim (step6 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u1 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t3 l2))) (fun r2 => (False.elim (bool_contra t2 r2))))))))
  have t6 : p 13 = true := (Or.elim (step941 p h) (fun l0 => (False.elim (bool_contra l0 t4))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t0))))))
  have t7 : p 5 = true := (Or.elim (step1703 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t5))) (fun r1 => (False.elim (bool_contra t3 r1))))))
  have t8 : p 57 = true := (Or.elim (step1697 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t5))) (fun r1 => (False.elim (bool_contra u1 r1))))))
  have t9 : p 60 = false := (Or.elim (step22 p h) (fun l0 => (False.elim (bool_contra t7 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t3 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t6 l2))) (fun r2 => r2))))))
  have t10 : p 59 = false := (Or.elim (step218 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t8 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u5 l2))) (fun r2 => (False.elim (bool_contra u3 r2))))))))
  exact (Or.elim (step1089 p h) (fun l0 => (bool_contra l0 t10)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t9)) (fun r1 => (bool_contra r1 u2)))))

theorem step1964 (p : Nat → Bool) (h : Constraints p) : p 1463 = true ∨ p 7 = false ∨ p 61 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1463 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 7 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 61 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 1461 = false := (Or.elim (step931 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t1 : p 2 = true := (Or.elim (step933 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t2 : p 6 = true := (Or.elim (step928 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t0))))
  exact (Or.elim (step33 p h) (fun l0 => (bool_contra u1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t1 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t2 l2)) (fun r2 => (bool_contra u2 r2)))))))

theorem step1965 (p : Nat → Bool) (h : Constraints p) : p 1476 = true ∨ p 1555 = true ∨ p 75 = false ∨ p 1468 = false ∨ p 89 = true ∨ p 61 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1476 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1555 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 75 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 1468 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 89 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 61 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl))))))
  have t0 : p 1470 = true := (Or.elim (step942 p h) (fun l0 => (False.elim (bool_contra u3 l0))) (fun r0 => r0))
  have t1 : p 7 = true := (Or.elim (step1760 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u4))) (fun r1 => (False.elim (bool_contra u5 r1))))))
  have t2 : p 1463 = true := (Or.elim (step1964 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t1 l1))) (fun r1 => (False.elim (bool_contra u5 r1))))))
  have t3 : p 63 = true := (Or.elim (step1759 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u4))) (fun r1 => (False.elim (bool_contra u5 r1))))))
  have t4 : p 1464 = false := (Or.elim (step960 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t0 l1))) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t5 : p 1471 = false := (Or.elim (step956 p h) (fun l0 => (False.elim (bool_contra t2 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t6 : p 4 = true := (Or.elim (step1646 p h) (fun l0 => (False.elim (bool_contra l0 t4))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t1 l2))) (fun r2 => (False.elim (bool_contra u5 r2))))))))
  exact (Or.elim (step1963 p h) (fun l0 => (bool_contra l0 t5)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t6 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u1)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra u2 l3)) (fun r3 => (Or.elim r3 (fun l4 => (bool_contra u3 l4)) (fun r4 => (bool_contra t3 r4)))))))))))

theorem step1966 (p : Nat → Bool) (h : Constraints p) : p 1476 = true ∨ p 15 = true ∨ p 7 = false ∨ p 61 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1476 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 15 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 7 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 61 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 1468 = true := (Or.elim (step1691 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u1))))
  have t1 : p 1470 = true := (Or.elim (step942 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => r0))
  have t2 : p 1463 = true := (Or.elim (step1964 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u2 l1))) (fun r1 => (False.elim (bool_contra u3 r1))))))
  have t3 : p 1464 = false := (Or.elim (step960 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t1 l1))) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t4 : p 1471 = false := (Or.elim (step956 p h) (fun l0 => (False.elim (bool_contra t2 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t5 : p 4 = true := (Or.elim (step1646 p h) (fun l0 => (False.elim (bool_contra l0 t3))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u2 l2))) (fun r2 => (False.elim (bool_contra u3 r2))))))))
  have t6 : p 1469 = false := (Or.elim (step943 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t4))))
  have t7 : p 1466 = false := (Or.elim (step945 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t0 l1))) (fun r1 => (False.elim (bool_contra r1 t4))))))
  have t8 : p 10 = true := (Or.elim (step936 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t7))))
  have t9 : p 8 = true := (Or.elim (step937 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t7))))
  have t10 : p 12 = false := (Or.elim (step1609 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t5 l1))) (fun r1 => (False.elim (bool_contra t8 r1))))))
  have t11 : p 3 = false := (Or.elim (step6 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t5 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t9 l2))) (fun r2 => (False.elim (bool_contra t8 r2))))))))
  have t12 : p 13 = true := (Or.elim (step941 p h) (fun l0 => (False.elim (bool_contra l0 t10))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t6))))))
  have t13 : p 9 = true := (Or.elim (step1702 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t11))) (fun r1 => (False.elim (bool_contra t9 r1))))))
  have t14 : p 6 = false := (Or.elim (step1692 p h) (fun l0 => (False.elim (bool_contra l0 t11))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra t9 r1))))))
  have t15 : p 14 = true := (Or.elim (step1707 p h) (fun l0 => (False.elim (bool_contra t12 l0))) (fun r0 => r0))
  have t16 : p 131 = true := (Or.elim (step46 p h) (fun l0 => (False.elim (bool_contra t13 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t14))))))
  have t17 : p 136 = true := (Or.elim (step57 p h) (fun l0 => (False.elim (bool_contra t15 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u1))))))
  have t18 : p 257 = true := (Or.elim (step734 p h) (fun l0 => (False.elim (bool_contra t16 l0))) (fun r0 => r0))
  have t19 : p 265 = true := (Or.elim (step738 p h) (fun l0 => (False.elim (bool_contra t17 l0))) (fun r0 => r0))
  have t20 : p 261 = true := (Or.elim (step737 p h) (fun l0 => (False.elim (bool_contra t18 l0))) (fun r0 => r0))
  have t21 : p 267 = true := (Or.elim (step739 p h) (fun l0 => (False.elim (bool_contra t19 l0))) (fun r0 => r0))
  exact (Or.elim (step1851 p h) (fun l0 => (bool_contra t20 l0)) (fun r0 => (bool_contra t21 r0)))

theorem step1967 (p : Nat → Bool) (h : Constraints p) : p 1659 = true ∨ p 73 = true ∨ p 1612 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1659 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 73 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1612 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 1617 = true := (Or.elim (step1204 p h) (fun l0 => (False.elim (bool_contra l0 u1))) (fun r0 => r0))
  have t1 : p 1619 = true := (Or.elim (step1207 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => r0))
  have t2 : p 1625 = true := (Or.elim (step1224 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t1 l1))) (fun r1 => r1))))
  have t3 : p 1626 = false := (Or.elim (step1883 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t4 : p 1648 = false := (Or.elim (step1294 p h) (fun l0 => (False.elim (bool_contra t2 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t5 : p 1620 = false := (Or.elim (step1225 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t3))))))
  have t6 : p 1635 = false := (Or.elim (step1878 p h) (fun l0 => (False.elim (bool_contra l0 t4))) (fun r0 => r0))
  have t7 : p 1618 = false := (Or.elim (step1208 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t5))))
  have t8 : p 1631 = false := (Or.elim (step1240 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t6))))
  have t9 : p 72 = true := (Or.elim (step1206 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u1))) (fun r1 => (False.elim (bool_contra r1 t7))))))
  have t10 : p 77 = true := (Or.elim (step1234 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t8))))
  exact (Or.elim (step1783 p h) (fun l0 => (bool_contra t9 l0)) (fun r0 => (bool_contra t10 r0)))

theorem step1968 (p : Nat → Bool) (h : Constraints p) : p 111 = false ∨ p 84 = false ∨ p 104 = false ∨ p 112 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 111 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 84 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 104 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 112 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 107 = true := (Or.elim (step1836 p h) (fun l0 => (False.elim (bool_contra l0 u3))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u0 l1))) (fun r1 => r1))))
  exact (Or.elim (step587 p h) (fun l0 => (bool_contra t0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u1 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra u2 l2)) (fun r2 => (bool_contra u0 r2)))))))

theorem step1969 (p : Nat → Bool) (h : Constraints p) : p 1476 = true ∨ p 7 = false ∨ p 61 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1476 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 7 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 61 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 15 = true := (Or.elim (step1966 p h) (fun l0 => (False.elim (bool_contra l0 u0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u1 l2))) (fun r2 => (False.elim (bool_contra u2 r2))))))))
  have t1 : p 6 = false := (Or.elim (step38 p h) (fun l0 => (False.elim (bool_contra u1 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t0 l2))) (fun r2 => (False.elim (bool_contra u2 r2))))))))
  have t2 : p 2 = false := (Or.elim (step35 p h) (fun l0 => (False.elim (bool_contra u1 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t0 l2))) (fun r2 => (False.elim (bool_contra u2 r2))))))))
  exact (Or.elim (step1962 p h) (fun l0 => (bool_contra l0 u0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t2)) (fun r1 => (bool_contra r1 t1)))))

theorem step1970 (p : Nat → Bool) (h : Constraints p) : p 68 = false ∨ p 71 = true ∨ p 1609 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 68 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 71 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1609 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 64 = true := (Or.elim (step1191 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u2))))
  have t1 : p 67 = true := (Or.elim (step1190 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u2))))
  have t2 : p 66 = true := (Or.elim (step1771 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u0 l1))) (fun r1 => (False.elim (bool_contra r1 u1))))))
  exact (Or.elim (step251 p h) (fun l0 => (bool_contra t2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t0 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t1 l2)) (fun r2 => (bool_contra u0 r2)))))))

theorem step1971 (p : Nat → Bool) (h : Constraints p) : p 59 = true ∨ p 1557 = true ∨ p 1609 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 59 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1557 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1609 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 1555 = false := (Or.elim (step1091 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u1))))
  have t1 : p 1554 = true := (Or.elim (step1088 p h) (fun l0 => (False.elim (bool_contra l0 u0))) (fun r0 => r0))
  have t2 : p 60 = true := (Or.elim (step1089 p h) (fun l0 => (False.elim (bool_contra l0 u0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t0))))))
  have t3 : p 1552 = false := (Or.elim (step1093 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t1 l1))) (fun r1 => (False.elim (bool_contra r1 u1))))))
  have t4 : p 56 = false := (Or.elim (step1944 p h) (fun l0 => (False.elim (bool_contra l0 u2))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t2 l1))) (fun r1 => r1))))
  exact (Or.elim (step1084 p h) (fun l0 => (bool_contra l0 t4)) (fun r0 => (bool_contra r0 t3)))

theorem step1972 (p : Nat → Bool) (h : Constraints p) : p 1636 = true ∨ p 80 = true ∨ p 59 = false ∨ p 1486 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1636 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 80 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 59 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 1486 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 1633 = true := (Or.elim (step1235 p h) (fun l0 => (False.elim (bool_contra l0 u1))) (fun r0 => r0))
  have t1 : p 1634 = false := (Or.elim (step1239 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t2 : p 1631 = false := (Or.elim (step1241 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t0 l1))) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t3 : p 79 = true := (Or.elim (step1237 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u1))) (fun r1 => (False.elim (bool_contra r1 t1))))))
  have t4 : p 77 = true := (Or.elim (step1234 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t2))))
  have t5 : p 75 = true := (Or.elim (step1788 p h) (fun l0 => (False.elim (bool_contra t3 l0))) (fun r0 => r0))
  have t6 : p 19 = false := (Or.elim (step281 p h) (fun l0 => (False.elim (bool_contra t5 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u2 l2))) (fun r2 => (False.elim (bool_contra t3 r2))))))))
  have t7 : p 18 = false := (Or.elim (step1782 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra t4 r0))))
  have t8 : p 1483 = true := (Or.elim (step971 p h) (fun l0 => (False.elim (bool_contra l0 t6))) (fun r0 => r0))
  have t9 : p 1481 = true := (Or.elim (step967 p h) (fun l0 => (False.elim (bool_contra l0 t7))) (fun r0 => r0))
  exact (Or.elim (step976 p h) (fun l0 => (bool_contra t9 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t8 l1)) (fun r1 => (bool_contra r1 u3)))))

theorem step1973 (p : Nat → Bool) (h : Constraints p) : p 1644 = true ∨ p 88 = true ∨ p 85 = false ∨ p 92 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1644 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 88 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 85 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 92 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 1641 = true := (Or.elim (step1247 p h) (fun l0 => (False.elim (bool_contra l0 u1))) (fun r0 => r0))
  have t1 : p 1642 = false := (Or.elim (step1250 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t2 : p 1639 = false := (Or.elim (step1252 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t0 l1))) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t3 : p 90 = true := (Or.elim (step1248 p h) (fun l0 => (False.elim (bool_contra l0 u1))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t1))))))
  have t4 : p 84 = true := (Or.elim (step1244 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t2))))
  have t5 : p 91 = false := (Or.elim (step449 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u2 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t3 l2))) (fun r2 => (False.elim (bool_contra u3 r2))))))))
  have t6 : p 83 = false := (Or.elim (step340 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t4 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u2 l2))) (fun r2 => (False.elim (bool_contra t3 r2))))))))
  exact (Or.elim (step1802 p h) (fun l0 => (bool_contra l0 t6)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t3 l1)) (fun r1 => (bool_contra r1 t5)))))

theorem step1974 (p : Nat → Bool) (h : Constraints p) : p 53 = true ∨ p 1557 = true ∨ p 1609 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 53 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1557 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1609 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 1553 = false := (Or.elim (step1095 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u1))))
  have t1 : p 1552 = true := (Or.elim (step1085 p h) (fun l0 => (False.elim (bool_contra l0 u0))) (fun r0 => r0))
  have t2 : p 56 = true := (Or.elim (step1086 p h) (fun l0 => (False.elim (bool_contra l0 u0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t0))))))
  have t3 : p 1554 = false := (Or.elim (step1093 p h) (fun l0 => (False.elim (bool_contra t1 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u1))))))
  have t4 : p 60 = false := (Or.elim (step1944 p h) (fun l0 => (False.elim (bool_contra l0 u2))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra t2 r1))))))
  exact (Or.elim (step1087 p h) (fun l0 => (bool_contra l0 t4)) (fun r0 => (bool_contra r0 t3)))

theorem step1975 (p : Nat → Bool) (h : Constraints p) : p 1572 = true ∨ p 1524 = false ∨ p 50 = true ∨ p 1556 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1572 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1524 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 50 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 1556 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 1546 = true := (Or.elim (step1073 p h) (fun l0 => (False.elim (bool_contra l0 u2))) (fun r0 => r0))
  have t1 : p 1548 = true := (Or.elim (step1076 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => r0))
  have t2 : p 1561 = true := (Or.elim (step1103 p h) (fun l0 => (False.elim (bool_contra t1 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u3 l1))) (fun r1 => r1))))
  have t3 : p 1536 = true := (Or.elim (step1061 p h) (fun l0 => (False.elim (bool_contra u1 l0))) (fun r0 => r0))
  have t4 : p 1538 = false := (Or.elim (step1134 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t2 l1))) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t5 : p 1563 = false := (Or.elim (step1123 p h) (fun l0 => (False.elim (bool_contra t3 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t6 : p 1533 = false := (Or.elim (step1063 p h) (fun l0 => (False.elim (bool_contra u1 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t4))))))
  have t7 : p 1550 = false := (Or.elim (step1113 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u3 l1))) (fun r1 => (False.elim (bool_contra r1 t5))))))
  have t8 : p 1544 = true := (Or.elim (step1953 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t6))))
  have t9 : p 1547 = false := (Or.elim (step1080 p h) (fun l0 => (False.elim (bool_contra t8 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t7))))))
  have t10 : p 1545 = false := (Or.elim (step1082 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t0 l1))) (fun r1 => (False.elim (bool_contra r1 t7))))))
  have t11 : p 1549 = true := (Or.elim (step1079 p h) (fun l0 => (False.elim (bool_contra t8 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t0 l1))) (fun r1 => r1))))
  have t12 : p 49 = true := (Or.elim (step1075 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u2))) (fun r1 => (False.elim (bool_contra r1 t9))))))
  have t13 : p 1562 = true := (Or.elim (step1108 p h) (fun l0 => (False.elim (bool_contra t11 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u3 l1))) (fun r1 => r1))))
  have t14 : p 48 = true := (Or.elim (step1748 p h) (fun l0 => (False.elim (bool_contra t12 l0))) (fun r0 => r0))
  have t15 : p 1537 = false := (Or.elim (step1128 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t13 l1))) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t16 : p 1532 = false := (Or.elim (step1062 p h) (fun l0 => (False.elim (bool_contra u1 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t15))))))
  have t17 : p 1530 = false := (Or.elim (step1050 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t16))))
  have t18 : p 1528 = false := (Or.elim (step1052 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t16))))
  have t19 : p 42 = true := (Or.elim (step1048 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t17))))
  have t20 : p 41 = true := (Or.elim (step1044 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t18))))
  have t21 : p 45 = false := (Or.elim (step1612 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra t19 r0))))
  have t22 : p 47 = false := (Or.elim (step163 p h) (fun l0 => (False.elim (bool_contra t14 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t20 l1))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra t12 r2))))))))
  exact (Or.elim (step1072 p h) (fun l0 => (bool_contra l0 t21)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t22)) (fun r1 => (bool_contra r1 t10)))))

theorem step1976 (p : Nat → Bool) (h : Constraints p) : p 31 = false ∨ p 92 = true ∨ p 1690 = true ∨ p 1724 = true ∨ p 1609 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 31 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 92 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1690 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 1724 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 1609 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr hl)))))
  have t0 : p 94 = true := (Or.elim (step1645 p h) (fun l0 => (False.elim (bool_contra l0 u4))) (fun r0 => r0))
  have t1 : p 67 = true := (Or.elim (step1190 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u4))))
  have t2 : p 97 = false := (Or.elim (step468 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u0 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t1 l2))) (fun r2 => r2))))))
  have t3 : p 101 = false := (Or.elim (step469 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u0 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t1 l2))) (fun r2 => r2))))))
  have t4 : p 93 = false := (Or.elim (step467 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u0 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t1 l2))) (fun r2 => r2))))))
  have t5 : p 1673 = true := (Or.elim (step1316 p h) (fun l0 => (False.elim (bool_contra l0 t2))) (fun r0 => r0))
  have t6 : p 1679 = true := (Or.elim (step1327 p h) (fun l0 => (False.elim (bool_contra l0 t3))) (fun r0 => r0))
  have t7 : p 1672 = true := (Or.elim (step1315 p h) (fun l0 => (False.elim (bool_contra l0 u1))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t4))) (fun r1 => r1))))
  have t8 : p 98 = true := (Or.elim (step1925 p h) (fun l0 => (False.elim (bool_contra l0 u2))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t0 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t1 l2))) (fun r2 => (Or.elim r2 (fun l3 => (False.elim (bool_contra t5 l3))) (fun r3 => (Or.elim r3 (fun l4 => (False.elim (bool_contra l4 u1))) (fun r4 => r4))))))))))
  have t9 : p 1677 = true := (Or.elim (step1325 p h) (fun l0 => (False.elim (bool_contra t7 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t5 l1))) (fun r1 => r1))))
  exact (Or.elim (step1664 p h) (fun l0 => (bool_contra t9 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 u3)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t6 l2)) (fun r2 => (bool_contra t8 r2)))))))

theorem step1977 (p : Nat → Bool) (h : Constraints p) : p 1676 = true ∨ p 92 = true ∨ p 1609 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1676 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 92 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1609 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 1671 = true := (Or.elim (step1314 p h) (fun l0 => (False.elim (bool_contra l0 u1))) (fun r0 => r0))
  have t1 : p 94 = true := (Or.elim (step1645 p h) (fun l0 => (False.elim (bool_contra l0 u2))) (fun r0 => r0))
  have t2 : p 67 = true := (Or.elim (step1190 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u2))))
  have t3 : p 1672 = false := (Or.elim (step1324 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t4 : p 1673 = false := (Or.elim (step1322 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t5 : p 93 = true := (Or.elim (step1315 p h) (fun l0 => (False.elim (bool_contra l0 u1))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t3))))))
  have t6 : p 97 = true := (Or.elim (step1316 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t4))))
  exact (Or.elim (step477 p h) (fun l0 => (bool_contra t1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t2 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t5 l2)) (fun r2 => (bool_contra t6 r2)))))))

theorem step1978 (p : Nat → Bool) (h : Constraints p) : p 1675 = true ∨ p 1609 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1675 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1609 = false := bool_false_of_not_true (fun hl => hc (Or.inr hl))
  have t0 : p 94 = true := (Or.elim (step1645 p h) (fun l0 => (False.elim (bool_contra l0 u1))) (fun r0 => r0))
  have t1 : p 67 = true := (Or.elim (step1190 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u1))))
  have t2 : p 1673 = false := (Or.elim (step1319 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t3 : p 1671 = false := (Or.elim (step1321 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t4 : p 97 = true := (Or.elim (step1316 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t2))))
  have t5 : p 93 = true := (Or.elim (step1313 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t3))))
  exact (Or.elim (step477 p h) (fun l0 => (bool_contra t0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t1 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t5 l2)) (fun r2 => (bool_contra t4 r2)))))))

theorem step1979 (p : Nat → Bool) (h : Constraints p) : p 93 = false ∨ p 1699 = false ∨ p 1724 = true ∨ p 1676 = false ∨ p 1609 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 93 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 1699 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1724 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 1676 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 1609 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr hl)))))
  have t0 : p 94 = true := (Or.elim (step1645 p h) (fun l0 => (False.elim (bool_contra l0 u4))) (fun r0 => r0))
  have t1 : p 67 = true := (Or.elim (step1190 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u4))))
  have t2 : p 101 = false := (Or.elim (step478 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t1 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u0 l2))) (fun r2 => r2))))))
  have t3 : p 116 = false := (Or.elim (step479 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t1 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u0 l2))) (fun r2 => r2))))))
  have t4 : p 1679 = true := (Or.elim (step1327 p h) (fun l0 => (False.elim (bool_contra l0 t2))) (fun r0 => r0))
  have t5 : p 1703 = true := (Or.elim (step1379 p h) (fun l0 => (False.elim (bool_contra l0 t3))) (fun r0 => r0))
  have t6 : p 1683 = true := (Or.elim (step1335 p h) (fun l0 => (False.elim (bool_contra t4 l0))) (fun r0 => r0))
  have t7 : p 1707 = true := (Or.elim (step1386 p h) (fun l0 => (False.elim (bool_contra t5 l0))) (fun r0 => r0))
  have t8 : p 1689 = true := (Or.elim (step1351 p h) (fun l0 => (False.elim (bool_contra u3 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t6 l1))) (fun r1 => r1))))
  have t9 : p 1713 = false := (Or.elim (step1425 p h) (fun l0 => (False.elim (bool_contra t8 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u2))))))
  have t10 : p 1700 = false := (Or.elim (step1402 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t7 l1))) (fun r1 => (False.elim (bool_contra r1 t9))))))
  have t11 : p 1708 = false := (Or.elim (step1398 p h) (fun l0 => (False.elim (bool_contra u1 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t9))))))
  have t12 : p 1705 = false := (Or.elim (step1387 p h) (fun l0 => (False.elim (bool_contra t5 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t11))))))
  have t13 : p 122 = true := (Or.elim (step1381 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t12))))
  have t14 : p 119 = true := (Or.elim (step1382 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t12))))
  exact (Or.elim (step1618 p h) (fun l0 => (bool_contra l0 t10)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t14 l1)) (fun r1 => (bool_contra t13 r1)))))

theorem step1980 (p : Nat → Bool) (h : Constraints p) : p 1724 = true ∨ p 1673 = false ∨ p 1712 = false ∨ p 7 = true ∨ p 61 = false ∨ p 1609 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1724 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1673 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1712 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 7 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 61 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 1609 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl))))))
  have t0 : p 89 = true := (Or.elim (step1760 p h) (fun l0 => (False.elim (bool_contra l0 u3))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra u4 r1))))))
  have t1 : p 63 = true := (Or.elim (step1761 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u3))) (fun r1 => (False.elim (bool_contra u4 r1))))))
  have t2 : p 92 = false := (Or.elim (step1524 p h) (fun l0 => (False.elim (bool_contra u4 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t1 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t0 l2))) (fun r2 => r2))))))
  have t3 : p 1676 = true := (Or.elim (step1977 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t2))) (fun r1 => (False.elim (bool_contra r1 u5))))))
  have t4 : p 94 = true := (Or.elim (step1645 p h) (fun l0 => (False.elim (bool_contra l0 u5))) (fun r0 => r0))
  have t5 : p 67 = true := (Or.elim (step1190 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u5))))
  have t6 : p 1690 = false := (Or.elim (step1429 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u2 l1))) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t7 : p 1684 = false := (Or.elim (step1352 p h) (fun l0 => (False.elim (bool_contra t3 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t6))))))
  have t8 : p 98 = true := (Or.elim (step1925 p h) (fun l0 => (False.elim (bool_contra l0 t6))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t4 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t5 l2))) (fun r2 => (Or.elim r2 (fun l3 => (False.elim (bool_contra u1 l3))) (fun r3 => (Or.elim r3 (fun l4 => (False.elim (bool_contra l4 t2))) (fun r4 => r4))))))))))
  have t9 : p 1682 = false := (Or.elim (step1334 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t7))))
  have t10 : p 1699 = true := (Or.elim (step1665 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t9))) (fun r1 => (False.elim (bool_contra t8 r1))))))
  have t11 : p 93 = false := (Or.elim (step1979 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t10 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra l2 u0))) (fun r2 => (Or.elim r2 (fun l3 => (False.elim (bool_contra t3 l3))) (fun r3 => (False.elim (bool_contra r3 u5))))))))))
  have t12 : p 1672 = true := (Or.elim (step1315 p h) (fun l0 => (False.elim (bool_contra l0 t2))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t11))) (fun r1 => r1))))
  have t13 : p 1677 = true := (Or.elim (step1325 p h) (fun l0 => (False.elim (bool_contra t12 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u1 l1))) (fun r1 => r1))))
  have t14 : p 1689 = true := (Or.elim (step1355 p h) (fun l0 => (False.elim (bool_contra t13 l0))) (fun r0 => r0))
  have t15 : p 1679 = false := (Or.elim (step1664 p h) (fun l0 => (False.elim (bool_contra t13 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u0))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra t8 r2))))))))
  have t16 : p 1713 = false := (Or.elim (step1425 p h) (fun l0 => (False.elim (bool_contra t14 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t17 : p 101 = true := (Or.elim (step1327 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t15))))
  have t18 : p 116 = false := (Or.elim (step482 p h) (fun l0 => (False.elim (bool_contra t4 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t5 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t17 l2))) (fun r2 => r2))))))
  have t19 : p 110 = false := (Or.elim (step439 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u4 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t17 l2))) (fun r2 => r2))))))
  have t20 : p 99 = false := (Or.elim (step512 p h) (fun l0 => (False.elim (bool_contra t17 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t0 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t4 l2))) (fun r2 => r2))))))
  have t21 : p 100 = false := (Or.elim (step513 p h) (fun l0 => (False.elim (bool_contra t17 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t0 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t4 l2))) (fun r2 => r2))))))
  have t22 : p 1703 = true := (Or.elim (step1379 p h) (fun l0 => (False.elim (bool_contra l0 t18))) (fun r0 => r0))
  have t23 : p 87 = true := (Or.elim (step1814 p h) (fun l0 => (False.elim (bool_contra l0 t21))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t8 l2))) (fun r2 => (False.elim (bool_contra r2 t20))))))))
  have t24 : p 118 = true := (Or.elim (step1811 p h) (fun l0 => (False.elim (bool_contra l0 t21))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t8 l2))) (fun r2 => (False.elim (bool_contra r2 t20))))))))
  have t25 : p 1707 = true := (Or.elim (step1386 p h) (fun l0 => (False.elim (bool_contra t22 l0))) (fun r0 => r0))
  have t26 : p 109 = false := (Or.elim (step1536 p h) (fun l0 => (False.elim (bool_contra t23 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t8 l1))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra t24 r2))))))))
  have t27 : p 1700 = false := (Or.elim (step1402 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t25 l1))) (fun r1 => (False.elim (bool_contra r1 t16))))))
  have t28 : p 1696 = true := (Or.elim (step1366 p h) (fun l0 => (False.elim (bool_contra l0 t26))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t19))) (fun r1 => r1))))
  exact (Or.elim (step1375 p h) (fun l0 => (bool_contra t28 l0)) (fun r0 => (bool_contra r0 t27)))

theorem step1981 (p : Nat → Bool) (h : Constraints p) : p 1592 = true ∨ p 1524 = false ∨ p 79 = false ∨ p 50 = true ∨ p 1609 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1592 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1524 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 79 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 50 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 1609 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr hl)))))
  have t0 : p 1507 = true := (step1932 p h)
  have t1 : p 1475 = true := (step1931 p h)
  have t2 : p 55 = true := (Or.elim (step1913 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u4))))
  have t3 : p 64 = true := (Or.elim (step1191 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u4))))
  have t4 : p 1556 = true := (Or.elim (step1905 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t2 l1))) (fun r1 => (False.elim (bool_contra t3 r1))))))
  have t5 : p 1572 = true := (Or.elim (step1975 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u1 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra l2 u3))) (fun r2 => (False.elim (bool_contra t4 r2))))))))
  have t6 : p 1536 = true := (Or.elim (step1061 p h) (fun l0 => (False.elim (bool_contra u1 l0))) (fun r0 => r0))
  have t7 : p 75 = true := (Or.elim (step1788 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => r0))
  have t8 : p 1546 = true := (Or.elim (step1073 p h) (fun l0 => (False.elim (bool_contra l0 u3))) (fun r0 => r0))
  have t9 : p 1573 = false := (Or.elim (step1152 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t10 : p 1508 = false := (Or.elim (step1158 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t5 l1))) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t11 : p 1564 = false := (Or.elim (step1124 p h) (fun l0 => (False.elim (bool_contra t6 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t9))))))
  have t12 : p 1498 = false := (Or.elim (step1012 p h) (fun l0 => (False.elim (bool_contra t1 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t10))))))
  have t13 : p 1485 = false := (Or.elim (step1868 p h) (fun l0 => (False.elim (bool_contra l0 t12))) (fun r0 => r0))
  have t14 : p 1483 = false := (Or.elim (step973 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t13))))
  have t15 : p 1481 = false := (Or.elim (step975 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t13))))
  have t16 : p 19 = true := (Or.elim (step971 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t14))))
  have t17 : p 18 = true := (Or.elim (step967 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t15))))
  have t18 : p 59 = false := (Or.elim (step281 p h) (fun l0 => (False.elim (bool_contra t7 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t16 l1))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra u2 r2))))))))
  have t19 : p 1544 = true := (Or.elim (step1583 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra t17 r0))))
  have t20 : p 1557 = true := (Or.elim (step1971 p h) (fun l0 => (False.elim (bool_contra l0 t18))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u4))))))
  have t21 : p 1549 = true := (Or.elim (step1079 p h) (fun l0 => (False.elim (bool_contra t19 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t8 l1))) (fun r1 => r1))))
  have t22 : p 1550 = false := (Or.elim (step1114 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t20 l1))) (fun r1 => (False.elim (bool_contra r1 t11))))))
  have t23 : p 1563 = true := (Or.elim (step1109 p h) (fun l0 => (False.elim (bool_contra t21 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t20 l1))) (fun r1 => r1))))
  have t24 : p 1547 = false := (Or.elim (step1080 p h) (fun l0 => (False.elim (bool_contra t19 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t22))))))
  have t25 : p 1545 = false := (Or.elim (step1082 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t8 l1))) (fun r1 => (False.elim (bool_contra r1 t22))))))
  have t26 : p 1537 = false := (Or.elim (step1129 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t23 l1))) (fun r1 => (False.elim (bool_contra r1 t9))))))
  have t27 : p 49 = true := (Or.elim (step1075 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u3))) (fun r1 => (False.elim (bool_contra r1 t24))))))
  have t28 : p 1532 = false := (Or.elim (step1062 p h) (fun l0 => (False.elim (bool_contra u1 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t26))))))
  have t29 : p 48 = true := (Or.elim (step1748 p h) (fun l0 => (False.elim (bool_contra t27 l0))) (fun r0 => r0))
  have t30 : p 1530 = false := (Or.elim (step1050 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t28))))
  have t31 : p 1528 = false := (Or.elim (step1052 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t28))))
  have t32 : p 42 = true := (Or.elim (step1048 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t30))))
  have t33 : p 41 = true := (Or.elim (step1044 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t31))))
  have t34 : p 45 = false := (Or.elim (step1612 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra t32 r0))))
  have t35 : p 47 = false := (Or.elim (step163 p h) (fun l0 => (False.elim (bool_contra t29 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t33 l1))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra t27 r2))))))))
  exact (Or.elim (step1072 p h) (fun l0 => (bool_contra l0 t34)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t35)) (fun r1 => (bool_contra r1 t25)))))

theorem step1982 (p : Nat → Bool) (h : Constraints p) : p 1712 = false ∨ p 1724 = true ∨ p 7 = true ∨ p 61 = false ∨ p 1609 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1712 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 1724 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 7 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 61 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 1609 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr hl)))))
  have t0 : p 89 = true := (Or.elim (step1760 p h) (fun l0 => (False.elim (bool_contra l0 u2))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra u3 r1))))))
  have t1 : p 63 = true := (Or.elim (step1761 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u2))) (fun r1 => (False.elim (bool_contra u3 r1))))))
  have t2 : p 92 = false := (Or.elim (step1524 p h) (fun l0 => (False.elim (bool_contra u3 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t1 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t0 l2))) (fun r2 => r2))))))
  have t3 : p 1676 = true := (Or.elim (step1977 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t2))) (fun r1 => (False.elim (bool_contra r1 u4))))))
  have t4 : p 94 = true := (Or.elim (step1645 p h) (fun l0 => (False.elim (bool_contra l0 u4))) (fun r0 => r0))
  have t5 : p 67 = true := (Or.elim (step1190 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u4))))
  have t6 : p 1690 = false := (Or.elim (step1429 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u0 l1))) (fun r1 => (False.elim (bool_contra r1 u1))))))
  have t7 : p 1673 = false := (Or.elim (step1980 p h) (fun l0 => (False.elim (bool_contra l0 u1))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u0 l2))) (fun r2 => (Or.elim r2 (fun l3 => (False.elim (bool_contra l3 u2))) (fun r3 => (Or.elim r3 (fun l4 => (False.elim (bool_contra u3 l4))) (fun r4 => (False.elim (bool_contra r4 u4))))))))))))
  have t8 : p 1684 = false := (Or.elim (step1352 p h) (fun l0 => (False.elim (bool_contra t3 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t6))))))
  have t9 : p 97 = true := (Or.elim (step1316 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t7))))
  have t10 : p 1682 = false := (Or.elim (step1334 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t8))))
  have t11 : p 1680 = false := (Or.elim (step1338 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t8))))
  have t12 : p 101 = false := (Or.elim (step480 p h) (fun l0 => (False.elim (bool_contra t4 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t5 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t9 l2))) (fun r2 => r2))))))
  have t13 : p 116 = false := (Or.elim (step481 p h) (fun l0 => (False.elim (bool_contra t4 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t5 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t9 l2))) (fun r2 => r2))))))
  have t14 : p 98 = true := (Or.elim (step1329 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t12))) (fun r1 => (False.elim (bool_contra r1 t11))))))
  have t15 : p 1679 = true := (Or.elim (step1327 p h) (fun l0 => (False.elim (bool_contra l0 t12))) (fun r0 => r0))
  have t16 : p 1703 = true := (Or.elim (step1379 p h) (fun l0 => (False.elim (bool_contra l0 t13))) (fun r0 => r0))
  have t17 : p 1699 = true := (Or.elim (step1665 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t10))) (fun r1 => (False.elim (bool_contra t14 r1))))))
  have t18 : p 1683 = true := (Or.elim (step1335 p h) (fun l0 => (False.elim (bool_contra t15 l0))) (fun r0 => r0))
  have t19 : p 1707 = true := (Or.elim (step1386 p h) (fun l0 => (False.elim (bool_contra t16 l0))) (fun r0 => r0))
  have t20 : p 1689 = true := (Or.elim (step1351 p h) (fun l0 => (False.elim (bool_contra t3 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t18 l1))) (fun r1 => r1))))
  have t21 : p 1713 = false := (Or.elim (step1425 p h) (fun l0 => (False.elim (bool_contra t20 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u1))))))
  have t22 : p 1708 = false := (Or.elim (step1398 p h) (fun l0 => (False.elim (bool_contra t17 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t21))))))
  have t23 : p 1700 = false := (Or.elim (step1402 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t19 l1))) (fun r1 => (False.elim (bool_contra r1 t21))))))
  have t24 : p 1705 = false := (Or.elim (step1387 p h) (fun l0 => (False.elim (bool_contra t16 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t22))))))
  have t25 : p 122 = true := (Or.elim (step1381 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t24))))
  have t26 : p 119 = true := (Or.elim (step1382 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t24))))
  exact (Or.elim (step1618 p h) (fun l0 => (bool_contra l0 t23)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t26 l1)) (fun r1 => (bool_contra t25 r1)))))

theorem step1983 (p : Nat → Bool) (h : Constraints p) : p 1724 = true ∨ p 7 = true ∨ p 61 = false ∨ p 1609 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1724 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 7 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 61 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 1609 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 89 = true := (Or.elim (step1760 p h) (fun l0 => (False.elim (bool_contra l0 u1))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra u2 r1))))))
  have t1 : p 63 = true := (Or.elim (step1761 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u1))) (fun r1 => (False.elim (bool_contra u2 r1))))))
  have t2 : p 92 = false := (Or.elim (step1524 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t1 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t0 l2))) (fun r2 => r2))))))
  have t3 : p 1676 = true := (Or.elim (step1977 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t2))) (fun r1 => (False.elim (bool_contra r1 u3))))))
  have t4 : p 94 = true := (Or.elim (step1645 p h) (fun l0 => (False.elim (bool_contra l0 u3))) (fun r0 => r0))
  have t5 : p 67 = true := (Or.elim (step1190 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u3))))
  have t6 : p 1712 = false := (Or.elim (step1982 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u0))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra l2 u1))) (fun r2 => (Or.elim r2 (fun l3 => (False.elim (bool_contra u2 l3))) (fun r3 => (False.elim (bool_contra r3 u3))))))))))
  have t7 : p 1691 = false := (Or.elim (step1888 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t8 : p 1708 = false := (Or.elim (step1393 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t6))))
  have t9 : p 1700 = false := (Or.elim (step1401 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t6))))
  have t10 : p 1673 = false := (Or.elim (step1904 p h) (fun l0 => (False.elim (bool_contra l0 t7))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t4 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t5 l2))) (fun r2 => (Or.elim r2 (fun l3 => (False.elim (bool_contra t3 l3))) (fun r3 => (Or.elim r3 (fun l4 => l4) (fun r4 => (False.elim (bool_contra r4 t6))))))))))))
  have t11 : p 97 = true := (Or.elim (step1316 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t10))))
  have t12 : p 116 = false := (Or.elim (step481 p h) (fun l0 => (False.elim (bool_contra t4 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t5 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t11 l2))) (fun r2 => r2))))))
  have t13 : p 1703 = true := (Or.elim (step1379 p h) (fun l0 => (False.elim (bool_contra l0 t12))) (fun r0 => r0))
  have t14 : p 1705 = false := (Or.elim (step1387 p h) (fun l0 => (False.elim (bool_contra t13 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t8))))))
  have t15 : p 122 = true := (Or.elim (step1381 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t14))))
  have t16 : p 119 = true := (Or.elim (step1382 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t14))))
  exact (Or.elim (step1618 p h) (fun l0 => (bool_contra l0 t9)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t16 l1)) (fun r1 => (bool_contra t15 r1)))))

theorem step1984 (p : Nat → Bool) (h : Constraints p) : p 1705 = true ∨ p 1700 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1705 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1700 = false := bool_false_of_not_true (fun hl => hc (Or.inr hl))
  have t0 : p 122 = true := (Or.elim (step1381 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t1 : p 119 = true := (Or.elim (step1382 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  exact (Or.elim (step1618 p h) (fun l0 => (bool_contra l0 u1)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t1 l1)) (fun r1 => (bool_contra t0 r1)))))

theorem step1985 (p : Nat → Bool) (h : Constraints p) : p 1485 = true ∨ p 1660 = true ∨ p 1645 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1485 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1660 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1645 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 1483 = false := (Or.elim (step973 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t1 : p 1481 = false := (Or.elim (step975 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t2 : p 19 = true := (Or.elim (step971 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t0))))
  have t3 : p 18 = true := (Or.elim (step967 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t1))))
  have t4 : p 73 = false := (Or.elim (step1682 p h) (fun l0 => (False.elim (bool_contra t2 l0))) (fun r0 => r0))
  have t5 : p 72 = false := (Or.elim (step1781 p h) (fun l0 => (False.elim (bool_contra t3 l0))) (fun r0 => r0))
  have t6 : p 77 = false := (Or.elim (step1782 p h) (fun l0 => (False.elim (bool_contra t3 l0))) (fun r0 => r0))
  have t7 : p 1618 = true := (Or.elim (step1206 p h) (fun l0 => (False.elim (bool_contra l0 t5))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t4))) (fun r1 => r1))))
  have t8 : p 1631 = true := (Or.elim (step1234 p h) (fun l0 => (False.elim (bool_contra l0 t6))) (fun r0 => r0))
  have t9 : p 1620 = true := (Or.elim (step1208 p h) (fun l0 => (False.elim (bool_contra t7 l0))) (fun r0 => r0))
  have t10 : p 1635 = true := (Or.elim (step1240 p h) (fun l0 => (False.elim (bool_contra t8 l0))) (fun r0 => r0))
  have t11 : p 1624 = true := (Or.elim (step1215 p h) (fun l0 => (False.elim (bool_contra t9 l0))) (fun r0 => r0))
  have t12 : p 1650 = true := (Or.elim (step1263 p h) (fun l0 => (False.elim (bool_contra t10 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u2 l1))) (fun r1 => r1))))
  exact (Or.elim (step1289 p h) (fun l0 => (bool_contra t11 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t12 l1)) (fun r1 => (bool_contra r1 u1)))))

theorem step1986 (p : Nat → Bool) (h : Constraints p) : p 1650 = false ∨ p 200 = true ∨ p 72 = true ∨ p 1660 = true ∨ p 1574 = false ∨ p 79 = false ∨ p 1724 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1650 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 200 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 72 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 1660 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 1574 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 79 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))
  have u6 : p 1724 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl)))))))
  have t0 : p 1475 = true := (step1931 p h)
  have t1 : p 1617 = true := (Or.elim (step1205 p h) (fun l0 => (False.elim (bool_contra l0 u2))) (fun r0 => r0))
  have t2 : p 1619 = true := (Or.elim (step1207 p h) (fun l0 => (False.elim (bool_contra t1 l0))) (fun r0 => r0))
  have t3 : p 1623 = true := (Or.elim (step1214 p h) (fun l0 => (False.elim (bool_contra t2 l0))) (fun r0 => r0))
  have t4 : p 1624 = false := (Or.elim (step1289 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u0 l1))) (fun r1 => (False.elim (bool_contra r1 u3))))))
  have t5 : p 1620 = false := (Or.elim (step1215 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t4))))
  have t6 : p 1618 = false := (Or.elim (step1208 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t5))))
  have t7 : p 73 = true := (Or.elim (step1206 p h) (fun l0 => (False.elim (bool_contra l0 u2))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t6))))))
  have t8 : p 1499 = true := (Or.elim (step1653 p h) (fun l0 => (False.elim (bool_contra u5 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t7 l2))) (fun r2 => (False.elim (bool_contra r2 u1))))))))
  have t9 : p 1509 = true := (Or.elim (step1013 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t8 l1))) (fun r1 => r1))))
  have t10 : p 1659 = true := (Or.elim (step1283 p h) (fun l0 => (False.elim (bool_contra t3 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u0 l1))) (fun r1 => r1))))
  have t11 : p 1595 = true := (Or.elim (step1168 p h) (fun l0 => (False.elim (bool_contra t9 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u4 l1))) (fun r1 => r1))))
  have t12 : p 1745 = true := (Or.elim (step1463 p h) (fun l0 => (False.elim (bool_contra t10 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u6 l1))) (fun r1 => r1))))
  exact (Or.elim (step1899 p h) (fun l0 => (bool_contra t11 l0)) (fun r0 => (bool_contra t12 r0)))

theorem step1987 (p : Nat → Bool) (h : Constraints p) : p 1650 = true ∨ p 1640 = false ∨ p 87 = false ∨ p 88 = true ∨ p 109 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1650 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1640 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 87 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 88 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 109 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr hl)))))
  have t0 : p 1641 = true := (Or.elim (step1247 p h) (fun l0 => (False.elim (bool_contra l0 u3))) (fun r0 => r0))
  have t1 : p 1645 = true := (Or.elim (step1255 p h) (fun l0 => (False.elim (bool_contra u1 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t0 l1))) (fun r1 => r1))))
  have t2 : p 1646 = false := (Or.elim (step1260 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t3 : p 1635 = false := (Or.elim (step1263 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t1 l1))) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t4 : p 1642 = false := (Or.elim (step1256 p h) (fun l0 => (False.elim (bool_contra u1 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t2))))))
  have t5 : p 1633 = false := (Or.elim (step1238 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t3))))
  have t6 : p 90 = true := (Or.elim (step1248 p h) (fun l0 => (False.elim (bool_contra l0 u3))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t4))))))
  have t7 : p 80 = true := (Or.elim (step1235 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t5))))
  exact (Or.elim (step412 p h) (fun l0 => (bool_contra u2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t7 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t6 l2)) (fun r2 => (bool_contra u4 r2)))))))

end Dfs112FirstBoolean
