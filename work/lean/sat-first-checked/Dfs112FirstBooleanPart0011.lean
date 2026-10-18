import Dfs112FirstBooleanPart0010
namespace Dfs112FirstBoolean
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem step1988 (p : Nat → Bool) (h : Constraints p) : p 59 = false ∨ p 72 = true ∨ p 79 = false ∨ p 1626 = true ∨ p 63 = false ∨ p 61 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 59 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 72 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 79 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 1626 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 63 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 61 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl))))))
  have t0 : p 75 = true := (Or.elim (step1788 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => r0))
  have t1 : p 73 = false := (Or.elim (step283 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u0 l1))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra u2 r2))))))))
  have t2 : p 62 = false := (Or.elim (step235 p h) (fun l0 => (False.elim (bool_contra u4 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u0 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u5 l2))) (fun r2 => r2))))))
  have t3 : p 58 = false := (Or.elim (step220 p h) (fun l0 => (False.elim (bool_contra u0 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u4 l2))) (fun r2 => (False.elim (bool_contra t0 r2))))))))
  have t4 : p 1618 = true := (Or.elim (step1206 p h) (fun l0 => (False.elim (bool_contra l0 u1))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t1))) (fun r1 => r1))))
  have t5 : p 1607 = true := (Or.elim (step1187 p h) (fun l0 => (False.elim (bool_contra l0 t2))) (fun r0 => r0))
  exact (Or.elim (step1924 p h) (fun l0 => (bool_contra l0 u3)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t4 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t5 l2)) (fun r2 => (bool_contra r2 t3)))))))

theorem step1989 (p : Nat → Bool) (h : Constraints p) : p 1525 = true ∨ p 31 = true ∨ p 95 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1525 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 31 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 95 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 1520 = true := (Or.elim (step1034 p h) (fun l0 => (False.elim (bool_contra l0 u1))) (fun r0 => r0))
  have t1 : p 1521 = false := (Or.elim (step1043 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t2 : p 1522 = false := (Or.elim (step1042 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t3 : p 33 = true := (Or.elim (step1035 p h) (fun l0 => (False.elim (bool_contra l0 u1))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t1))))))
  exact (Or.elim (step1628 p h) (fun l0 => (bool_contra t3 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t2)) (fun r1 => (bool_contra u2 r1)))))

theorem step1990 (p : Nat → Bool) (h : Constraints p) : p 1574 = true ∨ p 1562 = false ∨ p 1554 = false ∨ p 1538 = false ∨ p 50 = true ∨ p 1525 = false ∨ p 122 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1574 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1562 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1554 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 1538 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 50 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 1525 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))
  have u6 : p 122 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl)))))))
  have t0 : p 1563 = false := (Or.elim (step1136 p h) (fun l0 => (False.elim (bool_contra u3 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t1 : p 1539 = false := (Or.elim (step1141 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u1 l1))) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t2 : p 1544 = false := (Or.elim (step1676 p h) (fun l0 => (False.elim (bool_contra l0 u4))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (Or.elim r2 (fun l3 => (False.elim (bool_contra u6 l3))) (fun r3 => (False.elim (bool_contra u2 r3))))))))))
  have t3 : p 1533 = false := (Or.elim (step1068 p h) (fun l0 => (False.elim (bool_contra u5 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t1))))))
  exact (Or.elim (step1953 p h) (fun l0 => (bool_contra l0 t2)) (fun r0 => (bool_contra r0 t3)))

theorem step1991 (p : Nat → Bool) (h : Constraints p) : p 1485 = false ∨ p 1645 = false ∨ p 1574 = false ∨ p 1623 = false ∨ p 1725 = false ∨ p 87 = false ∨ p 1491 = false ∨ p 109 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1485 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 1645 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1574 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 1623 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 1725 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 87 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))
  have u6 : p 1491 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))))
  have u7 : p 109 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl))))))))
  have t0 : p 1475 = true := (step1931 p h)
  have t1 : p 1649 = true := (Or.elim (step1259 p h) (fun l0 => (False.elim (bool_contra u1 l0))) (fun r0 => r0))
  have t2 : p 1658 = true := (Or.elim (step1282 p h) (fun l0 => (False.elim (bool_contra u3 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t1 l1))) (fun r1 => r1))))
  have t3 : p 1745 = true := (Or.elim (step1457 p h) (fun l0 => (False.elim (bool_contra t2 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u4 l1))) (fun r1 => r1))))
  have t4 : p 1595 = false := (Or.elim (step1899 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra t3 r0))))
  have t5 : p 1509 = false := (Or.elim (step1168 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u2 l1))) (fun r1 => (False.elim (bool_contra r1 t4))))))
  have t6 : p 1499 = false := (Or.elim (step1013 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t5))))))
  have t7 : p 1498 = true := (Or.elim (step1868 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra u0 r0))))
  have t8 : p 1508 = true := (Or.elim (step1012 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t7 l1))) (fun r1 => r1))))
  have t9 : p 1594 = true := (Or.elim (step1160 p h) (fun l0 => (False.elim (bool_contra t8 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u2 l1))) (fun r1 => r1))))
  have t10 : p 1746 = false := (Or.elim (step1898 p h) (fun l0 => (False.elim (bool_contra t9 l0))) (fun r0 => r0))
  have t11 : p 1494 = false := (Or.elim (step999 p h) (fun l0 => (False.elim (bool_contra u0 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t6))))))
  have t12 : p 1659 = false := (Or.elim (step1464 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u4 l1))) (fun r1 => (False.elim (bool_contra r1 t10))))))
  have t13 : p 1489 = false := (Or.elim (step990 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u6 l1))) (fun r1 => (False.elim (bool_contra r1 t11))))))
  have t14 : p 1650 = false := (Or.elim (step1283 p h) (fun l0 => (False.elim (bool_contra u3 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t12))))))
  have t15 : p 24 = true := (Or.elim (step981 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t13))))
  have t16 : p 1635 = false := (Or.elim (step1263 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u1 l1))) (fun r1 => (False.elim (bool_contra r1 t14))))))
  have t17 : p 80 = false := (Or.elim (step391 p h) (fun l0 => (False.elim (bool_contra u5 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t15 l1))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra u7 r2))))))))
  have t18 : p 1633 = false := (Or.elim (step1238 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t16))))
  exact (Or.elim (step1235 p h) (fun l0 => (bool_contra l0 t17)) (fun r0 => (bool_contra r0 t18)))

theorem step1992 (p : Nat → Bool) (h : Constraints p) : p 1645 = false ∨ p 1574 = false ∨ p 1623 = false ∨ p 1725 = false ∨ p 87 = false ∨ p 1491 = false ∨ p 109 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1645 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 1574 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1623 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 1725 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 87 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 1491 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))
  have u6 : p 109 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl)))))))
  have t0 : p 1507 = true := (step1932 p h)
  have t1 : p 1593 = true := (Or.elim (step1153 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u1 l1))) (fun r1 => r1))))
  have t2 : p 1747 = false := (Or.elim (step1897 p h) (fun l0 => (False.elim (bool_contra t1 l0))) (fun r0 => r0))
  have t3 : p 1660 = false := (Or.elim (step1471 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u3 l1))) (fun r1 => (False.elim (bool_contra r1 t2))))))
  have t4 : p 1485 = false := (Or.elim (step1991 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u0 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u1 l2))) (fun r2 => (Or.elim r2 (fun l3 => (False.elim (bool_contra u2 l3))) (fun r3 => (Or.elim r3 (fun l4 => (False.elim (bool_contra u3 l4))) (fun r4 => (Or.elim r4 (fun l5 => (False.elim (bool_contra u4 l5))) (fun r5 => (Or.elim r5 (fun l6 => (False.elim (bool_contra u5 l6))) (fun r6 => (False.elim (bool_contra u6 r6))))))))))))))))
  exact (Or.elim (step1985 p h) (fun l0 => (bool_contra l0 t4)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t3)) (fun r1 => (bool_contra u0 r1)))))

theorem step1993 (p : Nat → Bool) (h : Constraints p) : p 1574 = false ∨ p 1623 = false ∨ p 1725 = false ∨ p 87 = false ∨ p 1491 = false ∨ p 88 = true ∨ p 109 = false ∨ p 1639 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1574 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 1623 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1725 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 87 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 1491 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 88 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))
  have u6 : p 109 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))))
  have u7 : p 1639 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl))))))))
  have t0 : p 1475 = true := (step1931 p h)
  have t1 : p 1641 = true := (Or.elim (step1247 p h) (fun l0 => (False.elim (bool_contra l0 u5))) (fun r0 => r0))
  have t2 : p 1644 = true := (Or.elim (step1252 p h) (fun l0 => (False.elim (bool_contra u7 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t1 l1))) (fun r1 => r1))))
  have t3 : p 1645 = false := (Or.elim (step1992 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u0 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u1 l2))) (fun r2 => (Or.elim r2 (fun l3 => (False.elim (bool_contra u2 l3))) (fun r3 => (Or.elim r3 (fun l4 => (False.elim (bool_contra u3 l4))) (fun r4 => (Or.elim r4 (fun l5 => (False.elim (bool_contra u4 l5))) (fun r5 => (False.elim (bool_contra u6 r5))))))))))))))
  have t4 : p 1642 = false := (Or.elim (step1253 p h) (fun l0 => (False.elim (bool_contra u7 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t3))))))
  have t5 : p 90 = true := (Or.elim (step1248 p h) (fun l0 => (False.elim (bool_contra l0 u5))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t4))))))
  have t6 : p 80 = false := (Or.elim (step412 p h) (fun l0 => (False.elim (bool_contra u3 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t5 l2))) (fun r2 => (False.elim (bool_contra u6 r2))))))))
  have t7 : p 24 = false := (Or.elim (step396 p h) (fun l0 => (False.elim (bool_contra u3 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t5 l2))) (fun r2 => (False.elim (bool_contra u6 r2))))))))
  have t8 : p 1633 = true := (Or.elim (step1235 p h) (fun l0 => (False.elim (bool_contra l0 t6))) (fun r0 => r0))
  have t9 : p 1489 = true := (Or.elim (step981 p h) (fun l0 => (False.elim (bool_contra l0 t7))) (fun r0 => r0))
  have t10 : p 1635 = true := (Or.elim (step1238 p h) (fun l0 => (False.elim (bool_contra t8 l0))) (fun r0 => r0))
  have t11 : p 1649 = true := (Or.elim (step1262 p h) (fun l0 => (False.elim (bool_contra t10 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t2 l1))) (fun r1 => r1))))
  have t12 : p 1658 = true := (Or.elim (step1282 p h) (fun l0 => (False.elim (bool_contra u1 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t11 l1))) (fun r1 => r1))))
  have t13 : p 1745 = true := (Or.elim (step1457 p h) (fun l0 => (False.elim (bool_contra t12 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u2 l1))) (fun r1 => r1))))
  have t14 : p 1595 = false := (Or.elim (step1899 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra t13 r0))))
  have t15 : p 1509 = false := (Or.elim (step1168 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u0 l1))) (fun r1 => (False.elim (bool_contra r1 t14))))))
  have t16 : p 1499 = false := (Or.elim (step1013 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t15))))))
  have t17 : p 1494 = true := (Or.elim (step990 p h) (fun l0 => (False.elim (bool_contra t9 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u4 l1))) (fun r1 => r1))))
  have t18 : p 1481 = false := (Or.elim (step1917 p h) (fun l0 => (False.elim (bool_contra l0 t16))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t7))) (fun r1 => r1))))
  have t19 : p 1498 = true := (Or.elim (step995 p h) (fun l0 => (False.elim (bool_contra t17 l0))) (fun r0 => r0))
  have t20 : p 18 = true := (Or.elim (step967 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t18))))
  have t21 : p 1508 = true := (Or.elim (step1012 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t19 l1))) (fun r1 => r1))))
  have t22 : p 77 = false := (Or.elim (step1782 p h) (fun l0 => (False.elim (bool_contra t20 l0))) (fun r0 => r0))
  have t23 : p 1594 = true := (Or.elim (step1160 p h) (fun l0 => (False.elim (bool_contra t21 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u0 l1))) (fun r1 => r1))))
  have t24 : p 1631 = true := (Or.elim (step1234 p h) (fun l0 => (False.elim (bool_contra l0 t22))) (fun r0 => r0))
  have t25 : p 1746 = false := (Or.elim (step1898 p h) (fun l0 => (False.elim (bool_contra t23 l0))) (fun r0 => r0))
  have t26 : p 1636 = true := (Or.elim (step1241 p h) (fun l0 => (False.elim (bool_contra t24 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t8 l1))) (fun r1 => r1))))
  have t27 : p 1659 = false := (Or.elim (step1464 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u2 l1))) (fun r1 => (False.elim (bool_contra r1 t25))))))
  have t28 : p 1650 = true := (Or.elim (step1267 p h) (fun l0 => (False.elim (bool_contra t26 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t2 l1))) (fun r1 => r1))))
  exact (Or.elim (step1283 p h) (fun l0 => (bool_contra u1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t28 l1)) (fun r1 => (bool_contra r1 t27)))))

theorem step1994 (p : Nat → Bool) (h : Constraints p) : p 1533 = true ∨ p 44 = false ∨ p 41 = true ∨ p 110 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1533 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 44 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 41 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 110 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 1528 = true := (Or.elim (step1044 p h) (fun l0 => (False.elim (bool_contra l0 u2))) (fun r0 => r0))
  have t1 : p 1529 = false := (Or.elim (step1055 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t2 : p 1530 = false := (Or.elim (step1053 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t3 : p 39 = true := (Or.elim (step1046 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u2))) (fun r1 => (False.elim (bool_contra r1 t1))))))
  have t4 : p 43 = true := (Or.elim (step1047 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t2))))
  exact (Or.elim (step153 p h) (fun l0 => (bool_contra u1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t3 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t4 l2)) (fun r2 => (bool_contra u3 r2)))))))

theorem step1995 (p : Nat → Bool) (h : Constraints p) : p 53 = false ∨ p 49 = false ∨ p 122 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 53 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 49 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 122 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 54 = false := (Or.elim (step180 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u1 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u0 l2))) (fun r2 => (False.elim (bool_contra u2 r2))))))))
  exact (Or.elim (step1747 p h) (fun l0 => (bool_contra u1 l0)) (fun r0 => (bool_contra r0 t0)))

theorem step1996 (p : Nat → Bool) (h : Constraints p) : p 1562 = true ∨ p 50 = true ∨ p 122 = false ∨ p 1609 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1562 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 50 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 122 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 1609 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 1546 = true := (Or.elim (step1073 p h) (fun l0 => (False.elim (bool_contra l0 u1))) (fun r0 => r0))
  have t1 : p 1548 = true := (Or.elim (step1076 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => r0))
  have t2 : p 55 = true := (Or.elim (step1913 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u3))))
  have t3 : p 64 = true := (Or.elim (step1191 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u3))))
  have t4 : p 1556 = true := (Or.elim (step1905 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t2 l1))) (fun r1 => (False.elim (bool_contra t3 r1))))))
  have t5 : p 1549 = false := (Or.elim (step1108 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t4 l1))) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t6 : p 1557 = false := (Or.elim (step1104 p h) (fun l0 => (False.elim (bool_contra t1 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t7 : p 1547 = false := (Or.elim (step1077 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t5))))
  have t8 : p 53 = true := (Or.elim (step1974 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t6))) (fun r1 => (False.elim (bool_contra r1 u3))))))
  have t9 : p 49 = true := (Or.elim (step1075 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u1))) (fun r1 => (False.elim (bool_contra r1 t7))))))
  exact (Or.elim (step1995 p h) (fun l0 => (bool_contra t8 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t9 l1)) (fun r1 => (bool_contra u2 r1)))))

theorem step1997 (p : Nat → Bool) (h : Constraints p) : p 1681 = true ∨ p 103 = false ∨ p 109 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1681 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 103 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 109 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 105 = true := (Or.elim (step1330 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t1 : p 104 = true := (Or.elim (step1331 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  exact (Or.elim (step544 p h) (fun l0 => (bool_contra u1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t1 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t0 l2)) (fun r2 => (bool_contra u2 r2)))))))

theorem step1998 (p : Nat → Bool) (h : Constraints p) : p 1650 = false ∨ p 72 = true ∨ p 1623 = false ∨ p 1725 = false ∨ p 1574 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1650 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 72 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1623 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 1725 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 1574 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr hl)))))
  have t0 : p 1507 = true := (step1932 p h)
  have t1 : p 1475 = true := (step1931 p h)
  have t2 : p 1593 = true := (Or.elim (step1153 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u4 l1))) (fun r1 => r1))))
  have t3 : p 1747 = false := (Or.elim (step1897 p h) (fun l0 => (False.elim (bool_contra t2 l0))) (fun r0 => r0))
  have t4 : p 1660 = false := (Or.elim (step1471 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u3 l1))) (fun r1 => (False.elim (bool_contra r1 t3))))))
  have t5 : p 1659 = true := (Or.elim (step1283 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u0 l1))) (fun r1 => r1))))
  have t6 : p 1624 = false := (Or.elim (step1289 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u0 l1))) (fun r1 => (False.elim (bool_contra r1 t4))))))
  have t7 : p 1746 = true := (Or.elim (step1464 p h) (fun l0 => (False.elim (bool_contra t5 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u3 l1))) (fun r1 => r1))))
  have t8 : p 1620 = false := (Or.elim (step1215 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t6))))
  have t9 : p 1594 = false := (Or.elim (step1898 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra t7 r0))))
  have t10 : p 1618 = false := (Or.elim (step1208 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t8))))
  have t11 : p 1508 = false := (Or.elim (step1160 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u4 l1))) (fun r1 => (False.elim (bool_contra r1 t9))))))
  have t12 : p 73 = true := (Or.elim (step1206 p h) (fun l0 => (False.elim (bool_contra l0 u1))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t10))))))
  have t13 : p 1498 = false := (Or.elim (step1012 p h) (fun l0 => (False.elim (bool_contra t1 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t11))))))
  have t14 : p 19 = false := (Or.elim (step1682 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra t12 r0))))
  have t15 : p 1485 = false := (Or.elim (step1868 p h) (fun l0 => (False.elim (bool_contra l0 t13))) (fun r0 => r0))
  have t16 : p 1483 = true := (Or.elim (step971 p h) (fun l0 => (False.elim (bool_contra l0 t14))) (fun r0 => r0))
  exact (Or.elim (step973 p h) (fun l0 => (bool_contra t16 l0)) (fun r0 => (bool_contra r0 t15)))

theorem step1999 (p : Nat → Bool) (h : Constraints p) : p 88 = true ∨ p 87 = true ∨ p 1673 = true ∨ p 1645 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 88 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 87 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1673 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 1645 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 1639 = true := (Or.elim (step1680 p h) (fun l0 => (False.elim (bool_contra l0 u2))) (fun r0 => r0))
  have t1 : p 1642 = false := (Or.elim (step1253 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u3))))))
  have t2 : p 95 = true := (Or.elim (step1317 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u2))))
  have t3 : p 90 = true := (Or.elim (step1248 p h) (fun l0 => (False.elim (bool_contra l0 u0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t1))))))
  have t4 : p 83 = true := (Or.elim (step1803 p h) (fun l0 => (False.elim (bool_contra l0 u1))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra t3 r1))))))
  have t5 : p 84 = true := (Or.elim (step1915 p h) (fun l0 => (False.elim (bool_contra l0 u0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u3))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (Or.elim r2 (fun l3 => (False.elim (bool_contra t4 l3))) (fun r3 => (False.elim (bool_contra t2 r3))))))))))
  exact (Or.elim (step342 p h) (fun l0 => (bool_contra t4 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t5 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t3 l2)) (fun r2 => (bool_contra t2 r2)))))))

theorem step2000 (p : Nat → Bool) (h : Constraints p) : p 1725 = false ∨ p 1644 = false ∨ p 80 = true ∨ p 1633 = false ∨ p 72 = true ∨ p 1574 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1725 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 1644 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 80 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 1633 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 72 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 1574 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl))))))
  have t0 : p 1475 = true := (step1931 p h)
  have t1 : p 1617 = true := (Or.elim (step1205 p h) (fun l0 => (False.elim (bool_contra l0 u4))) (fun r0 => r0))
  have t2 : p 1619 = true := (Or.elim (step1207 p h) (fun l0 => (False.elim (bool_contra t1 l0))) (fun r0 => r0))
  have t3 : p 1623 = true := (Or.elim (step1214 p h) (fun l0 => (False.elim (bool_contra t2 l0))) (fun r0 => r0))
  have t4 : p 1635 = true := (Or.elim (step1238 p h) (fun l0 => (False.elim (bool_contra u3 l0))) (fun r0 => r0))
  have t5 : p 1649 = true := (Or.elim (step1262 p h) (fun l0 => (False.elim (bool_contra t4 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u1 l1))) (fun r1 => r1))))
  have t6 : p 1658 = true := (Or.elim (step1282 p h) (fun l0 => (False.elim (bool_contra t3 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t5 l1))) (fun r1 => r1))))
  have t7 : p 1650 = false := (Or.elim (step1998 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u4))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t3 l2))) (fun r2 => (Or.elim r2 (fun l3 => (False.elim (bool_contra u0 l3))) (fun r3 => (False.elim (bool_contra u5 r3))))))))))
  have t8 : p 1745 = true := (Or.elim (step1457 p h) (fun l0 => (False.elim (bool_contra t6 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u0 l1))) (fun r1 => r1))))
  have t9 : p 1636 = false := (Or.elim (step1267 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u1 l1))) (fun r1 => (False.elim (bool_contra r1 t7))))))
  have t10 : p 1595 = false := (Or.elim (step1899 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra t8 r0))))
  have t11 : p 1634 = false := (Or.elim (step1239 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t9))))
  have t12 : p 1631 = false := (Or.elim (step1241 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u3 l1))) (fun r1 => (False.elim (bool_contra r1 t9))))))
  have t13 : p 1509 = false := (Or.elim (step1168 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u5 l1))) (fun r1 => (False.elim (bool_contra r1 t10))))))
  have t14 : p 79 = true := (Or.elim (step1237 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u2))) (fun r1 => (False.elim (bool_contra r1 t11))))))
  have t15 : p 77 = true := (Or.elim (step1234 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t12))))
  have t16 : p 1499 = false := (Or.elim (step1013 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t13))))))
  have t17 : p 200 = false := (Or.elim (step293 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t15 l1))) (fun r1 => (False.elim (bool_contra t14 r1))))))
  have t18 : p 18 = false := (Or.elim (step1782 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra t15 r0))))
  have t19 : p 73 = false := (Or.elim (step1653 p h) (fun l0 => (False.elim (bool_contra t14 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t16))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra r2 t17))))))))
  have t20 : p 1481 = true := (Or.elim (step967 p h) (fun l0 => (False.elim (bool_contra l0 t18))) (fun r0 => r0))
  have t21 : p 1618 = true := (Or.elim (step1206 p h) (fun l0 => (False.elim (bool_contra l0 u4))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t19))) (fun r1 => r1))))
  have t22 : p 1485 = true := (Or.elim (step975 p h) (fun l0 => (False.elim (bool_contra t20 l0))) (fun r0 => r0))
  have t23 : p 1620 = true := (Or.elim (step1208 p h) (fun l0 => (False.elim (bool_contra t21 l0))) (fun r0 => r0))
  have t24 : p 1498 = true := (Or.elim (step1868 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra t22 r0))))
  have t25 : p 1624 = true := (Or.elim (step1215 p h) (fun l0 => (False.elim (bool_contra t23 l0))) (fun r0 => r0))
  have t26 : p 1508 = true := (Or.elim (step1012 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t24 l1))) (fun r1 => r1))))
  have t27 : p 1659 = true := (Or.elim (step1288 p h) (fun l0 => (False.elim (bool_contra t25 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t5 l1))) (fun r1 => r1))))
  have t28 : p 1594 = true := (Or.elim (step1160 p h) (fun l0 => (False.elim (bool_contra t26 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u5 l1))) (fun r1 => r1))))
  have t29 : p 1746 = true := (Or.elim (step1464 p h) (fun l0 => (False.elim (bool_contra t27 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u0 l1))) (fun r1 => r1))))
  exact (Or.elim (step1898 p h) (fun l0 => (bool_contra t28 l0)) (fun r0 => (bool_contra t29 r0)))

theorem step2001 (p : Nat → Bool) (h : Constraints p) : p 1572 = true ∨ p 1558 = false ∨ p 1536 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1572 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1558 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1536 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 1562 = true := (Or.elim (step1100 p h) (fun l0 => (False.elim (bool_contra u1 l0))) (fun r0 => r0))
  have t1 : p 1563 = false := (Or.elim (step1123 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t2 : p 1537 = false := (Or.elim (step1128 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t0 l1))) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t3 : p 1548 = false := (Or.elim (step1105 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u1 l1))) (fun r1 => (False.elim (bool_contra r1 t1))))))
  have t4 : p 1533 = false := (Or.elim (step1059 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t2))))
  have t5 : p 1544 = false := (Or.elim (step1078 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t3))))
  exact (Or.elim (step1953 p h) (fun l0 => (bool_contra l0 t5)) (fun r0 => (bool_contra r0 t4)))

theorem step2002 (p : Nat → Bool) (h : Constraints p) : p 1499 = true ∨ p 80 = false ∨ p 19 = true ∨ p 26 = true ∨ p 87 = true ∨ p 85 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1499 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 80 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 19 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 26 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 87 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 85 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl))))))
  have t0 : p 1483 = true := (Or.elim (step971 p h) (fun l0 => (False.elim (bool_contra l0 u2))) (fun r0 => r0))
  have t1 : p 1485 = true := (Or.elim (step973 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => r0))
  have t2 : p 1486 = false := (Or.elim (step1869 p h) (fun l0 => (False.elim (bool_contra l0 u0))) (fun r0 => r0))
  have t3 : p 1494 = false := (Or.elim (step999 p h) (fun l0 => (False.elim (bool_contra t1 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t4 : p 1484 = false := (Or.elim (step974 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t2))))
  have t5 : p 1492 = false := (Or.elim (step988 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t3))))
  have t6 : p 24 = true := (Or.elim (step1918 p h) (fun l0 => (False.elim (bool_contra l0 t3))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u5 l1))) (fun r1 => r1))))
  have t7 : p 21 = true := (Or.elim (step972 p h) (fun l0 => (False.elim (bool_contra l0 u2))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t4))))))
  have t8 : p 27 = true := (Or.elim (step986 p h) (fun l0 => (False.elim (bool_contra l0 u3))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t5))))))
  have t9 : p 20 = false := (Or.elim (step73 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t7 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t6 l2))) (fun r2 => (False.elim (bool_contra u1 r2))))))))
  have t10 : p 25 = false := (Or.elim (step92 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t7 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t6 l2))) (fun r2 => (False.elim (bool_contra t8 r2))))))))
  exact (Or.elim (step1721 p h) (fun l0 => (bool_contra l0 t9)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 u4)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 t10)) (fun r2 => (bool_contra t6 r2)))))))

theorem step2003 (p : Nat → Bool) (h : Constraints p) : p 79 = false ∨ p 59 = false ∨ p 73 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 79 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 59 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 73 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 75 = true := (Or.elim (step1788 p h) (fun l0 => (False.elim (bool_contra u0 l0))) (fun r0 => r0))
  exact (Or.elim (step283 p h) (fun l0 => (bool_contra t0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u1 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra u2 l2)) (fun r2 => (bool_contra u0 r2)))))))

theorem step2004 (p : Nat → Bool) (h : Constraints p) : p 62 = true ∨ p 1617 = false ∨ p 1626 = true ∨ p 68 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 62 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1617 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1626 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 68 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 1607 = true := (Or.elim (step1187 p h) (fun l0 => (False.elim (bool_contra l0 u0))) (fun r0 => r0))
  have t1 : p 1611 = true := (Or.elim (step1195 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => r0))
  have t2 : p 1621 = false := (Or.elim (step1221 p h) (fun l0 => (False.elim (bool_contra t1 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u2))))))
  have t3 : p 1616 = false := (Or.elim (step1212 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u1 l1))) (fun r1 => (False.elim (bool_contra r1 t2))))))
  have t4 : p 69 = true := (Or.elim (step1203 p h) (fun l0 => (False.elim (bool_contra l0 u3))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t3))))))
  have t5 : p 71 = true := (Or.elim (step1774 p h) (fun l0 => (False.elim (bool_contra t4 l0))) (fun r0 => r0))
  have t6 : p 70 = true := (Or.elim (step1775 p h) (fun l0 => (False.elim (bool_contra t4 l0))) (fun r0 => r0))
  have t7 : p 193 = true := (Or.elim (step269 p h) (fun l0 => (False.elim (bool_contra t5 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u3))))))
  have t8 : p 192 = true := (Or.elim (step266 p h) (fun l0 => (False.elim (bool_contra t6 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u0))))))
  exact (Or.elim (step1858 p h) (fun l0 => (bool_contra t8 l0)) (fun r0 => (bool_contra t7 r0)))

theorem step2005 (p : Nat → Bool) (h : Constraints p) : p 1609 = true ∨ p 92 = true ∨ p 1689 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1609 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 92 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1689 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 1677 = false := (Or.elim (step1355 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u2))))
  have t1 : p 67 = true := (Or.elim (step1190 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t2 : p 94 = true := (Or.elim (step1645 p h) (fun l0 => (False.elim (bool_contra l0 u0))) (fun r0 => r0))
  have t3 : p 1676 = true := (Or.elim (step1977 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u1))) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t4 : p 1683 = false := (Or.elim (step1351 p h) (fun l0 => (False.elim (bool_contra t3 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u2))))))
  have t5 : p 1679 = false := (Or.elim (step1335 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t4))))
  have t6 : p 101 = true := (Or.elim (step1327 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t5))))
  have t7 : p 93 = false := (Or.elim (step478 p h) (fun l0 => (False.elim (bool_contra t2 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t1 l1))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra t6 r2))))))))
  have t8 : p 97 = false := (Or.elim (step480 p h) (fun l0 => (False.elim (bool_contra t2 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t1 l1))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra t6 r2))))))))
  have t9 : p 1672 = true := (Or.elim (step1315 p h) (fun l0 => (False.elim (bool_contra l0 u1))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t7))) (fun r1 => r1))))
  have t10 : p 1673 = true := (Or.elim (step1316 p h) (fun l0 => (False.elim (bool_contra l0 t8))) (fun r0 => r0))
  exact (Or.elim (step1325 p h) (fun l0 => (bool_contra t9 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t10 l1)) (fun r1 => (bool_contra r1 t0)))))

theorem step2006 (p : Nat → Bool) (h : Constraints p) : p 1644 = true ∨ p 95 = false ∨ p 98 = false ∨ p 84 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1644 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 95 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 98 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 84 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 1639 = true := (Or.elim (step1244 p h) (fun l0 => (False.elim (bool_contra l0 u3))) (fun r0 => r0))
  have t1 : p 1641 = false := (Or.elim (step1252 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t2 : p 83 = false := (Or.elim (step1911 p h) (fun l0 => (False.elim (bool_contra l0 u0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u3))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra u1 r2))))))))
  have t3 : p 90 = true := (Or.elim (step1246 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t1))))
  have t4 : p 88 = true := (Or.elim (step1247 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t1))))
  have t5 : p 87 = false := (Or.elim (step414 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t4 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t3 l2))) (fun r2 => (False.elim (bool_contra u2 r2))))))))
  exact (Or.elim (step1803 p h) (fun l0 => (bool_contra l0 t5)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t2)) (fun r1 => (bool_contra t3 r1)))))

theorem step2007 (p : Nat → Bool) (h : Constraints p) : p 1641 = true ∨ p 98 = false ∨ p 85 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1641 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 98 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 85 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 90 = true := (Or.elim (step1246 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t1 : p 88 = true := (Or.elim (step1247 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t2 : p 87 = false := (Or.elim (step414 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t1 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t0 l2))) (fun r2 => (False.elim (bool_contra u1 r2))))))))
  have t3 : p 91 = true := (Or.elim (step1801 p h) (fun l0 => (False.elim (bool_contra l0 t2))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t0 l1))) (fun r1 => r1))))
  exact (Or.elim (step447 p h) (fun l0 => (bool_contra t3 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u2 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t1 l2)) (fun r2 => (bool_contra t0 r2)))))))

theorem step2008 (p : Nat → Bool) (h : Constraints p) : p 87 = true ∨ p 90 = false ∨ p 85 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 87 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 90 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 85 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 83 = true := (Or.elim (step1803 p h) (fun l0 => (False.elim (bool_contra l0 u0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra u1 r1))))))
  have t1 : p 91 = true := (Or.elim (step1801 p h) (fun l0 => (False.elim (bool_contra l0 u0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u1 l1))) (fun r1 => r1))))
  exact (Or.elim (step1531 p h) (fun l0 => (bool_contra t0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u2 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra u1 l2)) (fun r2 => (bool_contra t1 r2)))))))

theorem step2009 (p : Nat → Bool) (h : Constraints p) : p 1530 = true ∨ p 1550 = true ∨ p 18 = false ∨ p 1525 = true ∨ p 53 = false ∨ p 95 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1530 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1550 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 18 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 1525 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 53 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 95 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl))))))
  have t0 : p 43 = true := (Or.elim (step1047 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t1 : p 42 = true := (Or.elim (step1048 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t2 : p 45 = false := (Or.elim (step1612 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra t1 r0))))
  have t3 : p 1546 = true := (Or.elim (step1955 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t1 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u4 l2))) (fun r2 => r2))))))
  have t4 : p 1545 = false := (Or.elim (step1082 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t3 l1))) (fun r1 => (False.elim (bool_contra r1 u1))))))
  have t5 : p 47 = true := (Or.elim (step1072 p h) (fun l0 => (False.elim (bool_contra l0 t2))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t4))))))
  have t6 : p 40 = false := (Or.elim (step142 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u2 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t1 l2))) (fun r2 => (False.elim (bool_contra t5 r2))))))))
  have t7 : p 32 = true := (Or.elim (step1746 p h) (fun l0 => (False.elim (bool_contra l0 t6))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t5 l1))) (fun r1 => r1))))
  have t8 : p 35 = false := (Or.elim (step121 p h) (fun l0 => (False.elim (bool_contra t7 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t5 l2))) (fun r2 => (False.elim (bool_contra u5 r2))))))))
  have t9 : p 33 = false := (Or.elim (step120 p h) (fun l0 => (False.elim (bool_contra t7 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t5 l2))) (fun r2 => (False.elim (bool_contra u5 r2))))))))
  have t10 : p 1522 = true := (Or.elim (step1036 p h) (fun l0 => (False.elim (bool_contra l0 t8))) (fun r0 => r0))
  have t11 : p 1520 = true := (Or.elim (step1033 p h) (fun l0 => (False.elim (bool_contra l0 t9))) (fun r0 => r0))
  exact (Or.elim (step1042 p h) (fun l0 => (bool_contra t11 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t10 l1)) (fun r1 => (bool_contra r1 u3)))))

theorem step2010 (p : Nat → Bool) (h : Constraints p) : p 47 = false ∨ p 40 = true ∨ p 1525 = true ∨ p 95 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 47 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 40 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1525 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 95 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 32 = true := (Or.elim (step1746 p h) (fun l0 => (False.elim (bool_contra l0 u1))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u0 l1))) (fun r1 => r1))))
  have t1 : p 35 = false := (Or.elim (step121 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u0 l2))) (fun r2 => (False.elim (bool_contra u3 r2))))))))
  have t2 : p 33 = false := (Or.elim (step120 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u0 l2))) (fun r2 => (False.elim (bool_contra u3 r2))))))))
  have t3 : p 1522 = true := (Or.elim (step1036 p h) (fun l0 => (False.elim (bool_contra l0 t1))) (fun r0 => r0))
  have t4 : p 1520 = true := (Or.elim (step1033 p h) (fun l0 => (False.elim (bool_contra l0 t2))) (fun r0 => r0))
  exact (Or.elim (step1042 p h) (fun l0 => (bool_contra t4 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t3 l1)) (fun r1 => (bool_contra r1 u2)))))

theorem step2011 (p : Nat → Bool) (h : Constraints p) : p 1476 = true ∨ p 2 = true ∨ p 3 = false ∨ p 18 = false ∨ p 10 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1476 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 2 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 3 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 18 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 10 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr hl)))))
  have t0 : p 1463 = true := (Or.elim (step933 p h) (fun l0 => (False.elim (bool_contra l0 u1))) (fun r0 => r0))
  have t1 : p 1466 = true := (Or.elim (step936 p h) (fun l0 => (False.elim (bool_contra l0 u4))) (fun r0 => r0))
  have t2 : p 1470 = true := (Or.elim (step944 p h) (fun l0 => (False.elim (bool_contra t1 l0))) (fun r0 => r0))
  have t3 : p 1464 = false := (Or.elim (step960 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t2 l1))) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t4 : p 1471 = false := (Or.elim (step956 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t5 : p 1461 = false := (Or.elim (step934 p h) (fun l0 => (False.elim (bool_contra l0 u1))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t3))))))
  have t6 : p 1467 = false := (Or.elim (step947 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t4))))
  have t7 : p 4 = true := (Or.elim (step929 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t5))))
  have t8 : p 8 = true := (Or.elim (step938 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u4))) (fun r1 => (False.elim (bool_contra r1 t6))))))
  exact (Or.elim (step7 p h) (fun l0 => (bool_contra u2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t7 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t8 l2)) (fun r2 => (bool_contra u3 r2)))))))

theorem step2012 (p : Nat → Bool) (h : Constraints p) : p 24 = true ∨ p 1494 = true ∨ p 21 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 24 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1494 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 21 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 1490 = false := (Or.elim (step992 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u1))))
  have t1 : p 1489 = true := (Or.elim (step981 p h) (fun l0 => (False.elim (bool_contra l0 u0))) (fun r0 => r0))
  have t2 : p 23 = true := (Or.elim (step983 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u0))) (fun r1 => (False.elim (bool_contra r1 t0))))))
  have t3 : p 1491 = false := (Or.elim (step990 p h) (fun l0 => (False.elim (bool_contra t1 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u1))))))
  have t4 : p 27 = true := (Or.elim (step984 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t3))))
  have t5 : p 26 = true := (Or.elim (step985 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t3))))
  have t6 : p 28 = false := (Or.elim (step102 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t2 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t5 l2))) (fun r2 => (False.elim (bool_contra t4 r2))))))))
  have t7 : p 25 = false := (Or.elim (step93 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u2 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t5 l2))) (fun r2 => (False.elim (bool_contra t4 r2))))))))
  exact (Or.elim (step1727 p h) (fun l0 => (bool_contra l0 t7)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t4 l1)) (fun r1 => (bool_contra r1 t6)))))

theorem step2013 (p : Nat → Bool) (h : Constraints p) : p 1676 = true ∨ p 31 = false ∨ p 92 = true ∨ p 21 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1676 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 31 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 92 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 21 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 1671 = true := (Or.elim (step1314 p h) (fun l0 => (False.elim (bool_contra l0 u2))) (fun r0 => r0))
  have t1 : p 1672 = false := (Or.elim (step1324 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t2 : p 1673 = false := (Or.elim (step1322 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t3 : p 93 = true := (Or.elim (step1315 p h) (fun l0 => (False.elim (bool_contra l0 u2))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t1))))))
  have t4 : p 97 = true := (Or.elim (step1316 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t2))))
  have t5 : p 94 = false := (Or.elim (step471 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u1 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t3 l2))) (fun r2 => (False.elim (bool_contra t4 r2))))))))
  have t6 : p 29 = false := (Or.elim (step106 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u3 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u1 l2))) (fun r2 => (False.elim (bool_contra t3 r2))))))))
  exact (Or.elim (step1729 p h) (fun l0 => (bool_contra l0 t6)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t5)) (fun r1 => (bool_contra u1 r1)))))

theorem step2014 (p : Nat → Bool) (h : Constraints p) : p 1641 = true ∨ p 1644 = true ∨ p 24 = false ∨ p 95 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1641 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1644 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 24 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 95 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 90 = true := (Or.elim (step1246 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t1 : p 88 = true := (Or.elim (step1247 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t2 : p 87 = false := (Or.elim (step392 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u2 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t1 l2))) (fun r2 => (False.elim (bool_contra t0 r2))))))))
  have t3 : p 83 = true := (Or.elim (step1803 p h) (fun l0 => (False.elim (bool_contra l0 t2))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra t0 r1))))))
  have t4 : p 84 = true := (Or.elim (step1911 p h) (fun l0 => (False.elim (bool_contra l0 u1))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t3 l2))) (fun r2 => (False.elim (bool_contra u3 r2))))))))
  exact (Or.elim (step342 p h) (fun l0 => (bool_contra t3 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t4 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t0 l2)) (fun r2 => (bool_contra u3 r2)))))))

theorem step2015 (p : Nat → Bool) (h : Constraints p) : p 1609 = true ∨ p 1724 = true ∨ p 31 = false ∨ p 92 = true ∨ p 1676 = false ∨ p 1673 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1609 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1724 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 31 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 92 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 1676 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 1673 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl))))))
  have t0 : p 1691 = false := (Or.elim (step1888 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u1))))
  have t1 : p 67 = true := (Or.elim (step1190 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t2 : p 94 = true := (Or.elim (step1645 p h) (fun l0 => (False.elim (bool_contra l0 u0))) (fun r0 => r0))
  have t3 : p 1690 = true := (Or.elim (step1976 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u3))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (Or.elim r2 (fun l3 => (False.elim (bool_contra l3 u1))) (fun r3 => (False.elim (bool_contra r3 u0))))))))))
  have t4 : p 1712 = true := (Or.elim (step1904 p h) (fun l0 => (False.elim (bool_contra l0 t0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t2 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t1 l2))) (fun r2 => (Or.elim r2 (fun l3 => (False.elim (bool_contra u4 l3))) (fun r3 => (Or.elim r3 (fun l4 => (False.elim (bool_contra u5 l4))) (fun r4 => r4))))))))))
  exact (Or.elim (step1429 p h) (fun l0 => (bool_contra t3 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t4 l1)) (fun r1 => (bool_contra r1 u1)))))

theorem step2016 (p : Nat → Bool) (h : Constraints p) : p 1712 = true ∨ p 1684 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1712 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1684 = false := bool_false_of_not_true (fun hl => hc (Or.inr hl))
  have t0 : p 1682 = false := (Or.elim (step1334 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u1))))
  have t1 : p 1708 = false := (Or.elim (step1393 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t2 : p 1700 = false := (Or.elim (step1401 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t3 : p 1699 = false := (Or.elim (step1643 p h) (fun l0 => (False.elim (bool_contra l0 u0))) (fun r0 => r0))
  have t4 : p 1705 = true := (Or.elim (step1984 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t2))))
  have t5 : p 1697 = false := (Or.elim (step1370 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t3))))
  have t6 : p 1695 = false := (Or.elim (step1372 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t3))))
  have t7 : p 98 = false := (Or.elim (step1665 p h) (fun l0 => (False.elim (bool_contra l0 t3))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => r1))))
  have t8 : p 1703 = false := (Or.elim (step1387 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t4 l1))) (fun r1 => (False.elim (bool_contra r1 t1))))))
  have t9 : p 113 = true := (Or.elim (step1367 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t5))))
  have t10 : p 110 = true := (Or.elim (step1364 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t6))))
  have t11 : p 1679 = true := (Or.elim (step1328 p h) (fun l0 => (False.elim (bool_contra l0 t7))) (fun r0 => r0))
  have t12 : p 116 = true := (Or.elim (step1379 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t8))))
  have t13 : p 1681 = false := (Or.elim (step1336 p h) (fun l0 => (False.elim (bool_contra t11 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u1))))))
  have t14 : p 106 = false := (Or.elim (step1620 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t10 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra l2 t0))) (fun r2 => (False.elim (bool_contra t12 r2))))))))
  have t15 : p 105 = true := (Or.elim (step1330 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t13))))
  have t16 : p 104 = true := (Or.elim (step1331 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t13))))
  exact (Or.elim (step1589 p h) (fun l0 => (bool_contra l0 t8)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t14)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t16 l2)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra t15 l3)) (fun r3 => (bool_contra t9 r3)))))))))

theorem step2017 (p : Nat → Bool) (h : Constraints p) : p 1649 = false ∨ p 1609 = false ∨ p 1704 = false ∨ p 119 = true ∨ p 106 = true ∨ p 101 = false ∨ p 1689 = false ∨ p 110 = false ∨ p 111 = false ∨ p 1745 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1649 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 1609 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1704 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 119 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 106 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 101 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))
  have u6 : p 1689 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))))
  have u7 : p 110 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))))
  have u8 : p 111 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))))))
  have u9 : p 1745 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl))))))))))
  have t0 : p 1611 = true := (Or.elim (step1193 p h) (fun l0 => (False.elim (bool_contra u1 l0))) (fun r0 => r0))
  have t1 : p 1623 = true := (Or.elim (step1218 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => r0))
  have t2 : p 1705 = true := (Or.elim (step1382 p h) (fun l0 => (False.elim (bool_contra l0 u3))) (fun r0 => r0))
  have t3 : p 1709 = true := (Or.elim (step1390 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t2 l1))) (fun r1 => r1))))
  have t4 : p 1713 = true := (Or.elim (step1394 p h) (fun l0 => (False.elim (bool_contra t3 l0))) (fun r0 => r0))
  have t5 : p 1724 = true := (Or.elim (step1425 p h) (fun l0 => (False.elim (bool_contra u6 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t4 l1))) (fun r1 => r1))))
  have t6 : p 1659 = false := (Or.elim (step1463 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t5 l1))) (fun r1 => (False.elim (bool_contra r1 u9))))))
  have t7 : p 1658 = true := (Or.elim (step1282 p h) (fun l0 => (False.elim (bool_contra t1 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u0 l1))) (fun r1 => r1))))
  have t8 : p 1624 = false := (Or.elim (step1288 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u0 l1))) (fun r1 => (False.elim (bool_contra r1 t6))))))
  have t9 : p 1725 = false := (Or.elim (step1457 p h) (fun l0 => (False.elim (bool_contra t7 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u9))))))
  have t10 : p 1612 = false := (Or.elim (step1223 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t8))))
  have t11 : p 1714 = false := (Or.elim (step1426 p h) (fun l0 => (False.elim (bool_contra u6 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t9))))))
  have t12 : p 1607 = false := (Or.elim (step1196 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u1 l1))) (fun r1 => (False.elim (bool_contra r1 t10))))))
  have t13 : p 1710 = false := (Or.elim (step1395 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t11))))
  have t14 : p 61 = true := (Or.elim (step1188 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t12))))
  have t15 : p 1706 = false := (Or.elim (step1391 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t13))))))
  have t16 : p 89 = false := (Or.elim (step439 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t14 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u5 l2))) (fun r2 => (False.elim (bool_contra u7 r2))))))))
  have t17 : p 122 = true := (Or.elim (step1383 p h) (fun l0 => (False.elim (bool_contra l0 u3))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t15))))))
  have t18 : p 112 = true := (Or.elim (step1830 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u7 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra l2 t16))) (fun r2 => (False.elim (bool_contra r2 u4))))))))
  exact (Or.elim (step609 p h) (fun l0 => (bool_contra t18 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u7 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra u8 l2)) (fun r2 => (bool_contra t17 r2)))))))

theorem step2018 (p : Nat → Bool) (h : Constraints p) : p 1641 = true ∨ p 87 = false ∨ p 109 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1641 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 87 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 109 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 90 = true := (Or.elim (step1246 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t1 : p 88 = true := (Or.elim (step1247 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  exact (Or.elim (step415 p h) (fun l0 => (bool_contra u1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t1 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t0 l2)) (fun r2 => (bool_contra u2 r2)))))))

theorem step2019 (p : Nat → Bool) (h : Constraints p) : p 1699 = true ∨ p 1673 = false ∨ p 1690 = true ∨ p 92 = true ∨ p 1745 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1699 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1673 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1690 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 92 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 1745 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr hl)))))
  have t0 : p 1671 = true := (Or.elim (step1314 p h) (fun l0 => (False.elim (bool_contra l0 u3))) (fun r0 => r0))
  have t1 : p 1676 = true := (Or.elim (step1322 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u1 l1))) (fun r1 => r1))))
  have t2 : p 1684 = false := (Or.elim (step1352 p h) (fun l0 => (False.elim (bool_contra t1 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u2))))))
  have t3 : p 1680 = false := (Or.elim (step1338 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t2))))
  have t4 : p 1682 = false := (Or.elim (step1334 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t2))))
  have t5 : p 1697 = false := (Or.elim (step1370 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t6 : p 1695 = false := (Or.elim (step1372 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t7 : p 1683 = true := (Or.elim (step1587 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t8 : p 98 = false := (Or.elim (step1665 p h) (fun l0 => (False.elim (bool_contra l0 u0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t4))) (fun r1 => r1))))
  have t9 : p 113 = true := (Or.elim (step1367 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t5))))
  have t10 : p 111 = true := (Or.elim (step1368 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t5))))
  have t11 : p 110 = true := (Or.elim (step1364 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t6))))
  have t12 : p 109 = true := (Or.elim (step1365 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t6))))
  have t13 : p 1677 = false := (Or.elim (step1356 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t7 l1))) (fun r1 => (False.elim (bool_contra r1 u2))))))
  have t14 : p 1689 = true := (Or.elim (step1351 p h) (fun l0 => (False.elim (bool_contra t1 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t7 l1))) (fun r1 => r1))))
  have t15 : p 1679 = true := (Or.elim (step1328 p h) (fun l0 => (False.elim (bool_contra l0 t8))) (fun r0 => r0))
  have t16 : p 101 = true := (Or.elim (step1329 p h) (fun l0 => (False.elim (bool_contra l0 t8))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t3))))))
  have t17 : p 1672 = false := (Or.elim (step1325 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u1 l1))) (fun r1 => (False.elim (bool_contra r1 t13))))))
  have t18 : p 1681 = false := (Or.elim (step1336 p h) (fun l0 => (False.elim (bool_contra t15 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t2))))))
  have t19 : p 93 = true := (Or.elim (step1315 p h) (fun l0 => (False.elim (bool_contra l0 u3))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t17))))))
  have t20 : p 105 = true := (Or.elim (step1330 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t18))))
  have t21 : p 104 = true := (Or.elim (step1331 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t18))))
  have t22 : p 103 = false := (Or.elim (step1997 p h) (fun l0 => (False.elim (bool_contra l0 t18))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra t12 r1))))))
  have t23 : p 114 = false := (Or.elim (step616 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t19 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t21 l2))) (fun r2 => (False.elim (bool_contra t9 r2))))))))
  have t24 : p 106 = false := (Or.elim (step579 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t21 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t20 l2))) (fun r2 => (False.elim (bool_contra t11 r2))))))))
  have t25 : p 87 = true := (Or.elim (step1829 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t12 l1))) (fun r1 => (False.elim (bool_contra r1 t22))))))
  have t26 : p 118 = true := (Or.elim (step1827 p h) (fun l0 => (False.elim (bool_contra t12 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t22))))))
  have t27 : p 81 = true := (Or.elim (step1823 p h) (fun l0 => (False.elim (bool_contra l0 t23))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t22))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra l2 t24))) (fun r2 => (Or.elim r2 (fun l3 => l3) (fun r3 => (False.elim (bool_contra t21 r3))))))))))
  have t28 : p 115 = true := (Or.elim (step1840 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t23))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra l2 t22))) (fun r2 => (False.elim (bool_contra t9 r2))))))))
  have t29 : p 119 = false := (Or.elim (step645 p h) (fun l0 => (False.elim (bool_contra t26 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t12 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t9 l2))) (fun r2 => r2))))))
  have t30 : p 80 = false := (Or.elim (step327 p h) (fun l0 => (False.elim (bool_contra t27 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t19 l2))) (fun r2 => (False.elim (bool_contra t21 r2))))))))
  have t31 : p 84 = false := (Or.elim (step328 p h) (fun l0 => (False.elim (bool_contra t27 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t19 l2))) (fun r2 => (False.elim (bool_contra t21 r2))))))))
  have t32 : p 116 = false := (Or.elim (step622 p h) (fun l0 => (False.elim (bool_contra t28 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t20 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t9 l2))) (fun r2 => r2))))))
  have t33 : p 117 = false := (Or.elim (step623 p h) (fun l0 => (False.elim (bool_contra t28 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t20 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t9 l2))) (fun r2 => r2))))))
  have t34 : p 1633 = true := (Or.elim (step1235 p h) (fun l0 => (False.elim (bool_contra l0 t30))) (fun r0 => r0))
  have t35 : p 1639 = true := (Or.elim (step1244 p h) (fun l0 => (False.elim (bool_contra l0 t31))) (fun r0 => r0))
  have t36 : p 1704 = true := (Or.elim (step1380 p h) (fun l0 => (False.elim (bool_contra l0 t32))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t33))) (fun r1 => r1))))
  have t37 : p 1635 = true := (Or.elim (step1238 p h) (fun l0 => (False.elim (bool_contra t34 l0))) (fun r0 => r0))
  have t38 : p 1641 = true := (Or.elim (step2018 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t25 l1))) (fun r1 => (False.elim (bool_contra t12 r1))))))
  have t39 : p 1644 = true := (Or.elim (step1252 p h) (fun l0 => (False.elim (bool_contra t35 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t38 l1))) (fun r1 => r1))))
  have t40 : p 1649 = true := (Or.elim (step1262 p h) (fun l0 => (False.elim (bool_contra t37 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t39 l1))) (fun r1 => r1))))
  have t41 : p 1609 = false := (Or.elim (step2017 p h) (fun l0 => (False.elim (bool_contra t40 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t36 l2))) (fun r2 => (Or.elim r2 (fun l3 => (False.elim (bool_contra l3 t29))) (fun r3 => (Or.elim r3 (fun l4 => (False.elim (bool_contra l4 t24))) (fun r4 => (Or.elim r4 (fun l5 => (False.elim (bool_contra t16 l5))) (fun r5 => (Or.elim r5 (fun l6 => (False.elim (bool_contra t14 l6))) (fun r6 => (Or.elim r6 (fun l7 => (False.elim (bool_contra t11 l7))) (fun r7 => (Or.elim r7 (fun l8 => (False.elim (bool_contra t10 l8))) (fun r8 => (False.elim (bool_contra r8 u4))))))))))))))))))))
  have t42 : p 67 = true := (Or.elim (step1190 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t41))))
  have t43 : p 94 = true := (Or.elim (step1645 p h) (fun l0 => (False.elim (bool_contra l0 t41))) (fun r0 => r0))
  exact (Or.elim (step478 p h) (fun l0 => (bool_contra t43 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t42 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t19 l2)) (fun r2 => (bool_contra t16 r2)))))))

theorem step2020 (p : Nat → Bool) (h : Constraints p) : p 1609 = true ∨ p 93 = false ∨ p 101 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1609 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 93 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 101 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 67 = true := (Or.elim (step1190 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t1 : p 94 = true := (Or.elim (step1645 p h) (fun l0 => (False.elim (bool_contra l0 u0))) (fun r0 => r0))
  exact (Or.elim (step478 p h) (fun l0 => (bool_contra t1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t0 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra u1 l2)) (fun r2 => (bool_contra u2 r2)))))))

theorem step2021 (p : Nat → Bool) (h : Constraints p) : p 1704 = false ∨ p 1709 = true ∨ p 1714 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1704 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 1709 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1714 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 1708 = true := (Or.elim (step1389 p h) (fun l0 => (False.elim (bool_contra u0 l0))) (fun r0 => r0))
  have t1 : p 1705 = false := (Or.elim (step1390 p h) (fun l0 => (False.elim (bool_contra u0 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u1))))))
  have t2 : p 1700 = false := (Or.elim (step1403 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t0 l1))) (fun r1 => (False.elim (bool_contra r1 u2))))))
  exact (Or.elim (step1984 p h) (fun l0 => (bool_contra l0 t1)) (fun r0 => (bool_contra r0 t2)))

theorem step2022 (p : Nat → Bool) (h : Constraints p) : p 121 = true ∨ p 117 = false ∨ p 105 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 121 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 117 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 105 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 108 = true := (Or.elim (step1846 p h) (fun l0 => (False.elim (bool_contra u1 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u0))) (fun r1 => r1))))
  have t1 : p 115 = true := (Or.elim (step1845 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u1 l1))) (fun r1 => (False.elim (bool_contra r1 u0))))))
  exact (Or.elim (step1544 p h) (fun l0 => (bool_contra u2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t0 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t1 l2)) (fun r2 => (bool_contra u1 r2)))))))

theorem step2023 (p : Nat → Bool) (h : Constraints p) : p 1659 = true ∨ p 67 = true ∨ p 1649 = false ∨ p 1644 = false ∨ p 1611 = false ∨ p 103 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1659 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 67 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1649 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 1644 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 1611 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 103 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl))))))
  have t0 : p 1623 = true := (Or.elim (step1218 p h) (fun l0 => (False.elim (bool_contra u4 l0))) (fun r0 => r0))
  have t1 : p 1624 = false := (Or.elim (step1288 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u2 l1))) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t2 : p 1650 = false := (Or.elim (step1283 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t3 : p 1612 = false := (Or.elim (step1223 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t1))))
  have t4 : p 1619 = false := (Or.elim (step1219 p h) (fun l0 => (False.elim (bool_contra u4 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t1))))))
  have t5 : p 1636 = false := (Or.elim (step1267 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u3 l1))) (fun r1 => (False.elim (bool_contra r1 t2))))))
  have t6 : p 1610 = false := (Or.elim (step1194 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t3))))
  have t7 : p 1617 = false := (Or.elim (step1207 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t4))))
  have t8 : p 64 = true := (Or.elim (step1192 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u1))) (fun r1 => (False.elim (bool_contra r1 t6))))))
  have t9 : p 72 = true := (Or.elim (step1205 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t7))))
  have t10 : p 55 = true := (Or.elim (step1777 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u5))) (fun r1 => (False.elim (bool_contra t9 r1))))))
  exact (Or.elim (step1683 p h) (fun l0 => (bool_contra t9 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t5)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t10 l2)) (fun r2 => (bool_contra t8 r2)))))))

theorem step2024 (p : Nat → Bool) (h : Constraints p) : p 1713 = true ∨ p 1703 = false ∨ p 1699 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1713 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1703 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1699 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 1707 = true := (Or.elim (step1386 p h) (fun l0 => (False.elim (bool_contra u1 l0))) (fun r0 => r0))
  have t1 : p 1700 = false := (Or.elim (step1402 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t0 l1))) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t2 : p 1708 = false := (Or.elim (step1398 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t3 : p 1705 = true := (Or.elim (step1984 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t1))))
  exact (Or.elim (step1387 p h) (fun l0 => (bool_contra u1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t3 l1)) (fun r1 => (bool_contra r1 t2)))))

theorem step2025 (p : Nat → Bool) (h : Constraints p) : p 1639 = true ∨ p 93 = false ∨ p 1674 = true ∨ p 101 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1639 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 93 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1674 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 101 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 85 = true := (Or.elim (step1243 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t1 : p 84 = true := (Or.elim (step1244 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t2 : p 95 = false := (Or.elim (step1681 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u0))) (fun r1 => (False.elim (bool_contra u1 r1))))))
  have t3 : p 97 = true := (Or.elim (step1318 p h) (fun l0 => (False.elim (bool_contra l0 t2))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u2))))))
  have t4 : p 96 = false := (Or.elim (step491 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t1 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u1 l2))) (fun r2 => (False.elim (bool_contra t3 r2))))))))
  have t5 : p 86 = false := (Or.elim (step379 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t1 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t0 l2))) (fun r2 => (False.elim (bool_contra t3 r2))))))))
  have t6 : p 94 = false := (Or.elim (step483 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u1 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t3 l2))) (fun r2 => (False.elim (bool_contra u3 r2))))))))
  exact (Or.elim (step1810 p h) (fun l0 => (bool_contra l0 t6)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t4)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 t5)) (fun r2 => (bool_contra t3 r2)))))))

theorem step2026 (p : Nat → Bool) (h : Constraints p) : p 1658 = true ∨ p 1639 = false ∨ p 1611 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1658 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1639 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1611 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 1648 = true := (Or.elim (step1910 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra u1 r0))))
  have t1 : p 1623 = true := (Or.elim (step1218 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => r0))
  have t2 : p 1624 = false := (Or.elim (step1287 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t0 l1))) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t3 : p 1649 = false := (Or.elim (step1282 p h) (fun l0 => (False.elim (bool_contra t1 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t4 : p 1619 = false := (Or.elim (step1219 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t2))))))
  have t5 : p 1631 = false := (Or.elim (step1648 p h) (fun l0 => (False.elim (bool_contra l0 t3))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u1 l1))) (fun r1 => r1))))
  have t6 : p 1617 = false := (Or.elim (step1207 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t4))))
  have t7 : p 77 = true := (Or.elim (step1234 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t5))))
  have t8 : p 72 = true := (Or.elim (step1205 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t6))))
  exact (Or.elim (step1783 p h) (fun l0 => (bool_contra t8 l0)) (fun r0 => (bool_contra t7 r0)))

theorem step2027 (p : Nat → Bool) (h : Constraints p) : p 1631 = false ∨ p 1650 = true ∨ p 88 = true ∨ p 87 = false ∨ p 98 = false ∨ p 1639 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1631 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 1650 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 88 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 87 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 98 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 1639 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl))))))
  have t0 : p 1641 = true := (Or.elim (step1247 p h) (fun l0 => (False.elim (bool_contra l0 u2))) (fun r0 => r0))
  have t1 : p 1644 = true := (Or.elim (step1252 p h) (fun l0 => (False.elim (bool_contra u5 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t0 l1))) (fun r1 => r1))))
  have t2 : p 1636 = false := (Or.elim (step1267 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t1 l1))) (fun r1 => (False.elim (bool_contra r1 u1))))))
  have t3 : p 1635 = true := (Or.elim (step1240 p h) (fun l0 => (False.elim (bool_contra u0 l0))) (fun r0 => r0))
  have t4 : p 1633 = false := (Or.elim (step1241 p h) (fun l0 => (False.elim (bool_contra u0 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t2))))))
  have t5 : p 1645 = false := (Or.elim (step1263 p h) (fun l0 => (False.elim (bool_contra t3 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u1))))))
  have t6 : p 80 = true := (Or.elim (step1235 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t4))))
  have t7 : p 1642 = false := (Or.elim (step1253 p h) (fun l0 => (False.elim (bool_contra u5 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t5))))))
  have t8 : p 90 = false := (Or.elim (step411 p h) (fun l0 => (False.elim (bool_contra u3 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t6 l1))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra u4 r2))))))))
  exact (Or.elim (step1248 p h) (fun l0 => (bool_contra l0 u2)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t8)) (fun r1 => (bool_contra r1 t7)))))

end Dfs112FirstBoolean
