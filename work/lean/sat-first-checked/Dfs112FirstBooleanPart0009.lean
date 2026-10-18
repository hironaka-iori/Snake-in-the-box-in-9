import Dfs112FirstBooleanPart0008
namespace Dfs112FirstBoolean
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem step1908 (p : Nat → Bool) (h : Constraints p) : p 117 = false ∨ p 116 = false ∨ p 113 = false ∨ p 121 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 117 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 116 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 113 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 121 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 115 = true := (Or.elim (step1845 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u0 l1))) (fun r1 => (False.elim (bool_contra r1 u3))))))
  exact (Or.elim (step625 p h) (fun l0 => (bool_contra t0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u2 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra u1 l2)) (fun r2 => (bool_contra u0 r2)))))))

theorem step1909 (p : Nat → Bool) (h : Constraints p) : p 107 = true ∨ p 242 = true ∨ p 1699 = true ∨ p 119 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 107 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 242 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1699 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 119 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 1695 = false := (Or.elim (step1372 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u2))))
  have t1 : p 110 = true := (Or.elim (step1364 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t0))))
  have t2 : p 1697 = false := (Or.elim (step1370 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u2))))
  have t3 : p 111 = true := (Or.elim (step1368 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t2))))
  have t4 : p 112 = true := (Or.elim (step1836 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t3 l1))) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t5 : p 120 = true := (Or.elim (step1835 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t3 l1))) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t6 : p 122 = false := (Or.elim (step609 p h) (fun l0 => (False.elim (bool_contra t4 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t1 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t3 l2))) (fun r2 => r2))))))
  exact (Or.elim (step653 p h) (fun l0 => (bool_contra t5 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 u1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u3)) (fun r2 => (bool_contra r2 t6)))))))

theorem step1910 (p : Nat → Bool) (h : Constraints p) : p 1648 = true ∨ p 1639 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1648 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1639 = true := bool_true_of_not_false (fun hl => hc (Or.inr hl))
  have t0 : p 1644 = false := (Or.elim (step1258 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t1 : p 1635 = false := (Or.elim (step1878 p h) (fun l0 => (False.elim (bool_contra l0 u0))) (fun r0 => r0))
  have t2 : p 1640 = false := (Or.elim (step1254 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t0))))
  have t3 : p 1641 = false := (Or.elim (step1252 p h) (fun l0 => (False.elim (bool_contra u1 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t0))))))
  have t4 : p 1633 = false := (Or.elim (step1238 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t1))))
  have t5 : p 80 = false := (Or.elim (step1602 p h) (fun l0 => (False.elim (bool_contra l0 t3))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t2))) (fun r1 => r1))))
  exact (Or.elim (step1235 p h) (fun l0 => (bool_contra l0 t5)) (fun r0 => (bool_contra r0 t4)))

theorem step1911 (p : Nat → Bool) (h : Constraints p) : p 1644 = true ∨ p 84 = true ∨ p 83 = false ∨ p 95 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1644 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 84 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 83 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 95 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 1639 = true := (Or.elim (step1244 p h) (fun l0 => (False.elim (bool_contra l0 u1))) (fun r0 => r0))
  have t1 : p 1640 = false := (Or.elim (step1254 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t2 : p 1641 = false := (Or.elim (step1252 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t3 : p 85 = true := (Or.elim (step1245 p h) (fun l0 => (False.elim (bool_contra l0 u1))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t1))))))
  have t4 : p 90 = true := (Or.elim (step1246 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t2))))
  exact (Or.elim (step343 p h) (fun l0 => (bool_contra u2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t3 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t4 l2)) (fun r2 => (bool_contra u3 r2)))))))

theorem step1912 (p : Nat → Bool) (h : Constraints p) : p 1649 = true ∨ p 1644 = false ∨ p 1639 = false ∨ p 83 = false ∨ p 87 = false ∨ p 109 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1649 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1644 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1639 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 83 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 87 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 109 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl))))))
  have t0 : p 1645 = false := (Or.elim (step1259 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t1 : p 1642 = false := (Or.elim (step1253 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t0))))))
  have t2 : p 1635 = false := (Or.elim (step1262 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u1 l1))) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t3 : p 1633 = false := (Or.elim (step1238 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t2))))
  have t4 : p 80 = true := (Or.elim (step1235 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t3))))
  have t5 : p 90 = false := (Or.elim (step1527 p h) (fun l0 => (False.elim (bool_contra t4 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u3 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u4 l2))) (fun r2 => r2))))))
  have t6 : p 88 = false := (Or.elim (step410 p h) (fun l0 => (False.elim (bool_contra u4 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t4 l1))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra u5 r2))))))))
  exact (Or.elim (step1248 p h) (fun l0 => (bool_contra l0 t6)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t5)) (fun r1 => (bool_contra r1 t1)))))

theorem step1913 (p : Nat → Bool) (h : Constraints p) : p 55 = true ∨ p 1609 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 55 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1609 = false := bool_false_of_not_true (fun hl => hc (Or.inr hl))
  have t0 : p 64 = true := (Or.elim (step1191 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u1))))
  have t1 : p 67 = true := (Or.elim (step1190 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u1))))
  have t2 : p 66 = true := (Or.elim (step1766 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u0))) (fun r1 => (False.elim (bool_contra t0 r1))))))
  have t3 : p 65 = true := (Or.elim (step1767 p h) (fun l0 => (False.elim (bool_contra l0 u0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra t0 r1))))))
  exact (Or.elim (step1525 p h) (fun l0 => (bool_contra t0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t3 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t2 l2)) (fun r2 => (bool_contra t1 r2)))))))

theorem step1914 (p : Nat → Bool) (h : Constraints p) : p 1499 = true ∨ p 1489 = false ∨ p 88 = false ∨ p 61 = false ∨ p 18 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1499 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1489 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 88 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 61 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 18 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr hl)))))
  have t0 : p 1481 = true := (Or.elim (step967 p h) (fun l0 => (False.elim (bool_contra l0 u4))) (fun r0 => r0))
  have t1 : p 1485 = true := (Or.elim (step975 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => r0))
  have t2 : p 1486 = false := (Or.elim (step1869 p h) (fun l0 => (False.elim (bool_contra l0 u0))) (fun r0 => r0))
  have t3 : p 1494 = false := (Or.elim (step999 p h) (fun l0 => (False.elim (bool_contra t1 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t4 : p 1482 = false := (Or.elim (step978 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t2))))
  have t5 : p 1491 = false := (Or.elim (step990 p h) (fun l0 => (False.elim (bool_contra u1 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t3))))))
  have t6 : p 15 = true := (Or.elim (step969 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u4))) (fun r1 => (False.elim (bool_contra r1 t4))))))
  have t7 : p 26 = true := (Or.elim (step985 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t5))))
  exact (Or.elim (step1580 p h) (fun l0 => (bool_contra u3 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u2 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t7 l2)) (fun r2 => (bool_contra t6 r2)))))))

theorem step1915 (p : Nat → Bool) (h : Constraints p) : p 88 = true ∨ p 1645 = true ∨ p 84 = true ∨ p 83 = false ∨ p 95 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 88 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1645 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 84 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 83 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 95 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr hl)))))
  have t0 : p 1639 = true := (Or.elim (step1244 p h) (fun l0 => (False.elim (bool_contra l0 u2))) (fun r0 => r0))
  have t1 : p 1642 = false := (Or.elim (step1253 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u1))))))
  have t2 : p 1641 = true := (Or.elim (step1247 p h) (fun l0 => (False.elim (bool_contra l0 u0))) (fun r0 => r0))
  have t3 : p 90 = true := (Or.elim (step1248 p h) (fun l0 => (False.elim (bool_contra l0 u0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t1))))))
  have t4 : p 1640 = false := (Or.elim (step1255 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t2 l1))) (fun r1 => (False.elim (bool_contra r1 u1))))))
  have t5 : p 85 = false := (Or.elim (step343 p h) (fun l0 => (False.elim (bool_contra u3 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t3 l2))) (fun r2 => (False.elim (bool_contra u4 r2))))))))
  exact (Or.elim (step1245 p h) (fun l0 => (bool_contra l0 u2)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t5)) (fun r1 => (bool_contra r1 t4)))))

theorem step1916 (p : Nat → Bool) (h : Constraints p) : p 1571 = true ∨ p 1556 = false ∨ p 1524 = false ∨ p 1546 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1571 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1556 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1524 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 1546 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 1548 = true := (Or.elim (step1076 p h) (fun l0 => (False.elim (bool_contra u3 l0))) (fun r0 => r0))
  have t1 : p 1561 = true := (Or.elim (step1103 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u1 l1))) (fun r1 => r1))))
  have t2 : p 1536 = true := (Or.elim (step1061 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => r0))
  have t3 : p 1562 = false := (Or.elim (step1122 p h) (fun l0 => (False.elim (bool_contra t2 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t4 : p 1537 = false := (Or.elim (step1127 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t1 l1))) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t5 : p 1549 = false := (Or.elim (step1108 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u1 l1))) (fun r1 => (False.elim (bool_contra r1 t3))))))
  have t6 : p 1532 = false := (Or.elim (step1062 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t4))))))
  have t7 : p 1544 = false := (Or.elim (step1079 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u3 l1))) (fun r1 => (False.elim (bool_contra r1 t5))))))
  have t8 : p 1528 = false := (Or.elim (step1052 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t6))))
  have t9 : p 41 = false := (Or.elim (step1630 p h) (fun l0 => (False.elim (bool_contra l0 t7))) (fun r0 => r0))
  exact (Or.elim (step1044 p h) (fun l0 => (bool_contra l0 t9)) (fun r0 => (bool_contra r0 t8)))

theorem step1917 (p : Nat → Bool) (h : Constraints p) : p 1499 = true ∨ p 24 = true ∨ p 1481 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1499 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 24 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1481 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 1489 = true := (Or.elim (step981 p h) (fun l0 => (False.elim (bool_contra l0 u1))) (fun r0 => r0))
  have t1 : p 1485 = true := (Or.elim (step975 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => r0))
  have t2 : p 1486 = false := (Or.elim (step1869 p h) (fun l0 => (False.elim (bool_contra l0 u0))) (fun r0 => r0))
  have t3 : p 1494 = false := (Or.elim (step999 p h) (fun l0 => (False.elim (bool_contra t1 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t4 : p 1483 = false := (Or.elim (step976 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t2))))))
  have t5 : p 1490 = false := (Or.elim (step992 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t3))))
  have t6 : p 1491 = false := (Or.elim (step990 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t3))))))
  have t7 : p 21 = true := (Or.elim (step970 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t4))))
  have t8 : p 23 = true := (Or.elim (step983 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u1))) (fun r1 => (False.elim (bool_contra r1 t5))))))
  have t9 : p 27 = true := (Or.elim (step984 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t6))))
  have t10 : p 26 = true := (Or.elim (step985 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t6))))
  have t11 : p 28 = false := (Or.elim (step102 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t8 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t10 l2))) (fun r2 => (False.elim (bool_contra t9 r2))))))))
  have t12 : p 25 = true := (Or.elim (step1727 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t9 l1))) (fun r1 => (False.elim (bool_contra r1 t11))))))
  exact (Or.elim (step93 p h) (fun l0 => (bool_contra t12 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t7 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t10 l2)) (fun r2 => (bool_contra t9 r2)))))))

theorem step1918 (p : Nat → Bool) (h : Constraints p) : p 1494 = true ∨ p 85 = false ∨ p 24 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1494 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 85 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 24 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 1489 = true := (Or.elim (step981 p h) (fun l0 => (False.elim (bool_contra l0 u2))) (fun r0 => r0))
  have t1 : p 1490 = false := (Or.elim (step992 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t2 : p 1491 = false := (Or.elim (step990 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t3 : p 23 = true := (Or.elim (step983 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u2))) (fun r1 => (False.elim (bool_contra r1 t1))))))
  have t4 : p 27 = true := (Or.elim (step984 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t2))))
  have t5 : p 26 = true := (Or.elim (step985 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t2))))
  have t6 : p 28 = false := (Or.elim (step102 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t3 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t5 l2))) (fun r2 => (False.elim (bool_contra t4 r2))))))))
  have t7 : p 86 = true := (Or.elim (step1718 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t3 l1))) (fun r1 => (False.elim (bool_contra r1 t6))))))
  have t8 : p 22 = true := (Or.elim (step1720 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t3 l1))) (fun r1 => (False.elim (bool_contra r1 t6))))))
  exact (Or.elim (step1512 p h) (fun l0 => (bool_contra t8 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t3 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra u1 l2)) (fun r2 => (bool_contra t7 r2)))))))

theorem step1919 (p : Nat → Bool) (h : Constraints p) : p 28 = true ∨ p 23 = false ∨ p 85 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 28 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 23 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 85 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 86 = true := (Or.elim (step1718 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u1 l1))) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t1 : p 22 = true := (Or.elim (step1720 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u1 l1))) (fun r1 => (False.elim (bool_contra r1 u0))))))
  exact (Or.elim (step1512 p h) (fun l0 => (bool_contra t1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u1 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra u2 l2)) (fun r2 => (bool_contra t0 r2)))))))

theorem step1920 (p : Nat → Bool) (h : Constraints p) : p 1703 = true ∨ p 108 = true ∨ p 113 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1703 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 108 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 113 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 117 = true := (Or.elim (step1378 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t1 : p 116 = true := (Or.elim (step1379 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t2 : p 115 = false := (Or.elim (step625 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u2 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t1 l2))) (fun r2 => (False.elim (bool_contra t0 r2))))))))
  exact (Or.elim (step1847 p h) (fun l0 => (bool_contra l0 t2)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t0 l1)) (fun r1 => (bool_contra r1 u1)))))

theorem step1921 (p : Nat → Bool) (h : Constraints p) : p 117 = false ∨ p 116 = false ∨ p 108 = true ∨ p 113 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 117 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 116 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 108 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 113 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 115 = false := (Or.elim (step625 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u3 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u1 l2))) (fun r2 => (False.elim (bool_contra u0 r2))))))))
  exact (Or.elim (step1847 p h) (fun l0 => (bool_contra l0 t0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u0 l1)) (fun r1 => (bool_contra r1 u2)))))

theorem step1922 (p : Nat → Bool) (h : Constraints p) : p 114 = false ∨ p 116 = false ∨ p 1691 = true ∨ p 1673 = false ∨ p 92 = true ∨ p 1679 = false ∨ p 113 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 114 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 116 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1691 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 1673 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 92 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 1679 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))
  have u6 : p 113 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl)))))))
  have t0 : p 104 = false := (Or.elim (step619 p h) (fun l0 => (False.elim (bool_contra u0 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u6 l2))) (fun r2 => (False.elim (bool_contra u1 r2))))))))
  have t1 : p 93 = false := (Or.elim (step618 p h) (fun l0 => (False.elim (bool_contra u0 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u6 l2))) (fun r2 => (False.elim (bool_contra u1 r2))))))))
  have t2 : p 1681 = true := (Or.elim (step1331 p h) (fun l0 => (False.elim (bool_contra l0 t0))) (fun r0 => r0))
  have t3 : p 1672 = true := (Or.elim (step1315 p h) (fun l0 => (False.elim (bool_contra l0 u4))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t1))) (fun r1 => r1))))
  have t4 : p 1684 = true := (Or.elim (step1336 p h) (fun l0 => (False.elim (bool_contra u5 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t2 l1))) (fun r1 => r1))))
  have t5 : p 1677 = true := (Or.elim (step1325 p h) (fun l0 => (False.elim (bool_contra t3 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u3 l1))) (fun r1 => r1))))
  exact (Or.elim (step1357 p h) (fun l0 => (bool_contra t5 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t4 l1)) (fun r1 => (bool_contra r1 u2)))))

theorem step1923 (p : Nat → Bool) (h : Constraints p) : p 1713 = true ∨ p 44 = true ∨ p 89 = true ∨ p 1703 = false ∨ p 119 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1713 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 44 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 89 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 1703 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 119 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr hl)))))
  have t0 : p 1705 = true := (Or.elim (step1382 p h) (fun l0 => (False.elim (bool_contra l0 u4))) (fun r0 => r0))
  have t1 : p 1708 = true := (Or.elim (step1387 p h) (fun l0 => (False.elim (bool_contra u3 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t0 l1))) (fun r1 => r1))))
  have t2 : p 1709 = false := (Or.elim (step1394 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t3 : p 1699 = false := (Or.elim (step1398 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t1 l1))) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t4 : p 1706 = false := (Or.elim (step1388 p h) (fun l0 => (False.elim (bool_contra u3 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t2))))))
  have t5 : p 1697 = false := (Or.elim (step1370 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t3))))
  have t6 : p 1695 = false := (Or.elim (step1372 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t3))))
  have t7 : p 122 = true := (Or.elim (step1383 p h) (fun l0 => (False.elim (bool_contra l0 u4))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t4))))))
  have t8 : p 111 = true := (Or.elim (step1368 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t5))))
  have t9 : p 110 = true := (Or.elim (step1364 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t6))))
  have t10 : p 112 = false := (Or.elim (step609 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t9 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t8 l2))) (fun r2 => (False.elim (bool_contra t7 r2))))))))
  exact (Or.elim (step1832 p h) (fun l0 => (bool_contra l0 u1)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t10)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u2)) (fun r2 => (bool_contra t9 r2)))))))

theorem step1924 (p : Nat → Bool) (h : Constraints p) : p 1626 = true ∨ p 1618 = false ∨ p 1607 = false ∨ p 58 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1626 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1618 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1607 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 58 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 1620 = true := (Or.elim (step1208 p h) (fun l0 => (False.elim (bool_contra u1 l0))) (fun r0 => r0))
  have t1 : p 1611 = true := (Or.elim (step1195 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => r0))
  have t2 : p 1621 = false := (Or.elim (step1221 p h) (fun l0 => (False.elim (bool_contra t1 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t3 : p 1612 = false := (Or.elim (step1225 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t0 l1))) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t4 : p 1615 = false := (Or.elim (step1211 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u1 l1))) (fun r1 => (False.elim (bool_contra r1 t2))))))
  have t5 : p 1609 = false := (Or.elim (step1196 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t3))))))
  have t6 : p 68 = true := (Or.elim (step1202 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t4))))
  have t7 : p 67 = true := (Or.elim (step1190 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t5))))
  have t8 : p 64 = true := (Or.elim (step1191 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t5))))
  have t9 : p 66 = true := (Or.elim (step1773 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t6 l1))) (fun r1 => (False.elim (bool_contra r1 u3))))))
  exact (Or.elim (step251 p h) (fun l0 => (bool_contra t9 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t8 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t7 l2)) (fun r2 => (bool_contra t6 r2)))))))

theorem step1925 (p : Nat → Bool) (h : Constraints p) : p 1690 = true ∨ p 94 = false ∨ p 67 = false ∨ p 1673 = false ∨ p 92 = true ∨ p 98 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1690 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 94 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 67 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 1673 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 92 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 98 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl))))))
  have t0 : p 1671 = true := (Or.elim (step1314 p h) (fun l0 => (False.elim (bool_contra l0 u4))) (fun r0 => r0))
  have t1 : p 1676 = true := (Or.elim (step1322 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u3 l1))) (fun r1 => r1))))
  have t2 : p 1679 = true := (Or.elim (step1328 p h) (fun l0 => (False.elim (bool_contra l0 u5))) (fun r0 => r0))
  have t3 : p 1683 = true := (Or.elim (step1335 p h) (fun l0 => (False.elim (bool_contra t2 l0))) (fun r0 => r0))
  have t4 : p 1684 = false := (Or.elim (step1352 p h) (fun l0 => (False.elim (bool_contra t1 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t5 : p 1677 = false := (Or.elim (step1356 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t3 l1))) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t6 : p 1680 = false := (Or.elim (step1338 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t4))))
  have t7 : p 1672 = false := (Or.elim (step1325 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u3 l1))) (fun r1 => (False.elim (bool_contra r1 t5))))))
  have t8 : p 101 = true := (Or.elim (step1329 p h) (fun l0 => (False.elim (bool_contra l0 u5))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t6))))))
  have t9 : p 93 = true := (Or.elim (step1315 p h) (fun l0 => (False.elim (bool_contra l0 u4))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t7))))))
  exact (Or.elim (step478 p h) (fun l0 => (bool_contra u1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u2 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t9 l2)) (fun r2 => (bool_contra t8 r2)))))))

theorem step1926 (p : Nat → Bool) (h : Constraints p) : p 67 = false ∨ p 64 = false ∨ p 1690 = true ∨ p 1673 = false ∨ p 92 = true ∨ p 98 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 67 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 64 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1690 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 1673 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 92 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 98 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl))))))
  have t0 : p 1679 = true := (Or.elim (step1328 p h) (fun l0 => (False.elim (bool_contra l0 u5))) (fun r0 => r0))
  have t1 : p 1683 = true := (Or.elim (step1335 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => r0))
  have t2 : p 1677 = false := (Or.elim (step1356 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t1 l1))) (fun r1 => (False.elim (bool_contra r1 u2))))))
  have t3 : p 1672 = false := (Or.elim (step1325 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u3 l1))) (fun r1 => (False.elim (bool_contra r1 t2))))))
  have t4 : p 93 = true := (Or.elim (step1315 p h) (fun l0 => (False.elim (bool_contra l0 u4))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t3))))))
  have t5 : p 94 = false := (Or.elim (step1925 p h) (fun l0 => (False.elim (bool_contra l0 u2))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u0 l2))) (fun r2 => (Or.elim r2 (fun l3 => (False.elim (bool_contra u3 l3))) (fun r3 => (Or.elim r3 (fun l4 => (False.elim (bool_contra l4 u4))) (fun r4 => (False.elim (bool_contra r4 u5))))))))))))
  have t6 : p 65 = true := (Or.elim (step1769 p h) (fun l0 => (False.elim (bool_contra l0 t5))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra u0 r1))))))
  exact (Or.elim (step248 p h) (fun l0 => (bool_contra t6 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u1 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra u0 l2)) (fun r2 => (bool_contra t4 r2)))))))

theorem step1927 (p : Nat → Bool) (h : Constraints p) : p 117 = false ∨ p 121 = true ∨ p 42 = false ∨ p 85 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 117 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 121 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 42 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 85 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 108 = false := (Or.elim (step589 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u2 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u3 l2))) (fun r2 => (False.elim (bool_contra u0 r2))))))))
  exact (Or.elim (step1846 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 u1)) (fun r1 => (bool_contra r1 t0)))))

theorem step1928 (p : Nat → Bool) (h : Constraints p) : p 61 = false ∨ p 88 = false ∨ p 26 = false ∨ p 1464 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 61 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 88 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 26 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 1464 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 89 = false := (Or.elim (step425 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u2 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u0 l2))) (fun r2 => (False.elim (bool_contra u1 r2))))))))
  have t1 : p 7 = true := (Or.elim (step1760 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => (False.elim (bool_contra u0 r1))))))
  have t2 : p 2 = false := (Or.elim (step36 p h) (fun l0 => (False.elim (bool_contra t1 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u2 l2))) (fun r2 => (False.elim (bool_contra u0 r2))))))))
  have t3 : p 6 = false := (Or.elim (step39 p h) (fun l0 => (False.elim (bool_contra t1 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u2 l2))) (fun r2 => (False.elim (bool_contra u0 r2))))))))
  have t4 : p 1461 = false := (Or.elim (step934 p h) (fun l0 => (False.elim (bool_contra l0 t2))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u3))))))
  exact (Or.elim (step928 p h) (fun l0 => (bool_contra l0 t3)) (fun r0 => (bool_contra r0 t4)))

theorem step1929 (p : Nat → Bool) (h : Constraints p) : p 6 = true ∨ p 1475 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 6 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1475 = false := bool_false_of_not_true (fun hl => hc (Or.inr hl))
  have t0 : p 1464 = false := (Or.elim (step959 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u1))))
  have t1 : p 1462 = false := (Or.elim (step932 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t0))))
  have t2 : p 10 = true := (Or.elim (step1644 p h) (fun l0 => (False.elim (bool_contra l0 u1))) (fun r0 => r0))
  have t3 : p 1461 = true := (Or.elim (step928 p h) (fun l0 => (False.elim (bool_contra l0 u0))) (fun r0 => r0))
  have t4 : p 4 = true := (Or.elim (step930 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u0))) (fun r1 => (False.elim (bool_contra r1 t1))))))
  have t5 : p 1463 = true := (Or.elim (step931 p h) (fun l0 => (False.elim (bool_contra t3 l0))) (fun r0 => r0))
  have t6 : p 12 = false := (Or.elim (step1609 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t4 l1))) (fun r1 => (False.elim (bool_contra t2 r1))))))
  have t7 : p 1470 = false := (Or.elim (step955 p h) (fun l0 => (False.elim (bool_contra t5 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u1))))))
  have t8 : p 1468 = true := (Or.elim (step940 p h) (fun l0 => (False.elim (bool_contra l0 t6))) (fun r0 => r0))
  exact (Or.elim (step942 p h) (fun l0 => (bool_contra t8 l0)) (fun r0 => (bool_contra r0 t7)))

theorem step1930 (p : Nat → Bool) (h : Constraints p) : p 1470 = true ∨ p 6 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1470 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 6 = true := bool_true_of_not_false (fun hl => hc (Or.inr hl))
  have t0 : p 1468 = false := (Or.elim (step942 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t1 : p 1466 = false := (Or.elim (step944 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t2 : p 13 = true := (Or.elim (step939 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t0))))
  have t3 : p 8 = true := (Or.elim (step937 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t1))))
  have t4 : p 5 = true := (Or.elim (step1708 p h) (fun l0 => (False.elim (bool_contra t2 l0))) (fun r0 => r0))
  exact (Or.elim (step15 p h) (fun l0 => (bool_contra t4 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u1 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t3 l2)) (fun r2 => (bool_contra t2 r2)))))))

theorem step1931 (p : Nat → Bool) (h : Constraints p) : p 1475 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1475 = false := bool_false_of_not_true (fun hl => hc hl)
  have t0 : p 1471 = false := (Or.elim (step951 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t1 : p 10 = true := (Or.elim (step1644 p h) (fun l0 => (False.elim (bool_contra l0 u0))) (fun r0 => r0))
  have t2 : p 1469 = false := (Or.elim (step943 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t0))))
  have t3 : p 6 = true := (Or.elim (step1929 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t4 : p 1470 = true := (Or.elim (step1930 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra t3 r0))))
  have t5 : p 1463 = false := (Or.elim (step955 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t4 l1))) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t6 : p 1461 = false := (Or.elim (step931 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t5))))
  have t7 : p 4 = true := (Or.elim (step929 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t6))))
  have t8 : p 12 = false := (Or.elim (step1609 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t7 l1))) (fun r1 => (False.elim (bool_contra t1 r1))))))
  have t9 : p 1468 = true := (Or.elim (step940 p h) (fun l0 => (False.elim (bool_contra l0 t8))) (fun r0 => r0))
  have t10 : p 13 = true := (Or.elim (step941 p h) (fun l0 => (False.elim (bool_contra l0 t8))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t2))))))
  have t11 : p 1466 = false := (Or.elim (step945 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t9 l1))) (fun r1 => (False.elim (bool_contra r1 t0))))))
  have t12 : p 5 = true := (Or.elim (step1708 p h) (fun l0 => (False.elim (bool_contra t10 l0))) (fun r0 => r0))
  have t13 : p 8 = false := (Or.elim (step15 p h) (fun l0 => (False.elim (bool_contra t12 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t3 l1))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra t10 r2))))))))
  exact (Or.elim (step937 p h) (fun l0 => (bool_contra l0 t13)) (fun r0 => (bool_contra r0 t11)))

theorem step1932 (p : Nat → Bool) (h : Constraints p) : p 1507 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1507 = false := bool_false_of_not_true (fun hl => hc hl)
  have t0 : p 1475 = true := (step1931 p h)
  exact (Or.elim (step1873 p h) (fun l0 => (bool_contra t0 l0)) (fun r0 => (bool_contra r0 u0)))

theorem step1933 (p : Nat → Bool) (h : Constraints p) : p 1564 = true ∨ p 1555 = false ∨ p 1545 = false ∨ p 38 = true ∨ p 39 = false ∨ p 43 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1564 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1555 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1545 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 38 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 39 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 43 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl))))))
  have t0 : p 1557 = true := (Or.elim (step1091 p h) (fun l0 => (False.elim (bool_contra u1 l0))) (fun r0 => r0))
  have t1 : p 1549 = true := (Or.elim (step1081 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => r0))
  have t2 : p 1558 = false := (Or.elim (step1110 p h) (fun l0 => (False.elim (bool_contra t1 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t3 : p 1550 = false := (Or.elim (step1114 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t0 l1))) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t4 : p 1552 = false := (Or.elim (step1094 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u1 l1))) (fun r1 => (False.elim (bool_contra r1 t2))))))
  have t5 : p 1546 = false := (Or.elim (step1082 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t3))))))
  have t6 : p 53 = true := (Or.elim (step1085 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t4))))
  have t7 : p 50 = true := (Or.elim (step1073 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t5))))
  exact (Or.elim (step1596 p h) (fun l0 => (bool_contra t6 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t7 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u3)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra u4 l3)) (fun r3 => (bool_contra u5 r3)))))))))

theorem step1934 (p : Nat → Bool) (h : Constraints p) : p 1723 = true ∨ p 1681 = false ∨ p 1676 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1723 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1681 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1676 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 1683 = true := (Or.elim (step1333 p h) (fun l0 => (False.elim (bool_contra u1 l0))) (fun r0 => r0))
  have t1 : p 1689 = true := (Or.elim (step1351 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t0 l1))) (fun r1 => r1))))
  have t2 : p 1690 = false := (Or.elim (step1887 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t3 : p 1712 = false := (Or.elim (step1424 p h) (fun l0 => (False.elim (bool_contra t1 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t4 : p 1684 = false := (Or.elim (step1352 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t2))))))
  have t5 : p 1699 = false := (Or.elim (step1643 p h) (fun l0 => (False.elim (bool_contra l0 t3))) (fun r0 => r0))
  have t6 : p 1682 = false := (Or.elim (step1334 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t4))))
  have t7 : p 1679 = false := (Or.elim (step1336 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u1 l1))) (fun r1 => (False.elim (bool_contra r1 t4))))))
  have t8 : p 98 = false := (Or.elim (step1665 p h) (fun l0 => (False.elim (bool_contra l0 t5))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t6))) (fun r1 => r1))))
  exact (Or.elim (step1328 p h) (fun l0 => (bool_contra l0 t8)) (fun r0 => (bool_contra r0 t7)))

theorem step1935 (p : Nat → Bool) (h : Constraints p) : p 1571 = true ∨ p 1556 = false ∨ p 48 = false ∨ p 41 = false ∨ p 1524 = false ∨ p 1536 = false ∨ p 45 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1571 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1556 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 48 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 41 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 1524 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 1536 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))
  have u6 : p 45 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl)))))))
  have t0 : p 1562 = false := (Or.elim (step1122 p h) (fun l0 => (False.elim (bool_contra u5 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t1 : p 1546 = false := (Or.elim (step1916 p h) (fun l0 => (False.elim (bool_contra l0 u0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u1 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u4 l2))) (fun r2 => r2))))))
  have t2 : p 1549 = false := (Or.elim (step1108 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u1 l1))) (fun r1 => (False.elim (bool_contra r1 t0))))))
  have t3 : p 49 = true := (Or.elim (step1074 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t1))))
  have t4 : p 1545 = false := (Or.elim (step1081 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t2))))
  have t5 : p 47 = false := (Or.elim (step163 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u3 l1))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra t3 r2))))))))
  exact (Or.elim (step1072 p h) (fun l0 => (bool_contra l0 u6)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t5)) (fun r1 => (bool_contra r1 t4)))))

theorem step1936 (p : Nat → Bool) (h : Constraints p) : p 87 = false ∨ p 1639 = false ∨ p 1650 = true ∨ p 109 = false ∨ p 98 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 87 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 1639 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1650 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 109 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 98 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr hl)))))
  have t0 : p 1642 = true := (Or.elim (step1636 p h) (fun l0 => (False.elim (bool_contra u0 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u4 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u3 l2))) (fun r2 => r2))))))
  have t1 : p 80 = false := (Or.elim (step413 p h) (fun l0 => (False.elim (bool_contra u0 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u4 l2))) (fun r2 => (False.elim (bool_contra u3 r2))))))))
  have t2 : p 1645 = true := (Or.elim (step1253 p h) (fun l0 => (False.elim (bool_contra u1 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t0 l1))) (fun r1 => r1))))
  have t3 : p 1633 = true := (Or.elim (step1235 p h) (fun l0 => (False.elim (bool_contra l0 t1))) (fun r0 => r0))
  have t4 : p 1635 = false := (Or.elim (step1263 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t2 l1))) (fun r1 => (False.elim (bool_contra r1 u2))))))
  exact (Or.elim (step1238 p h) (fun l0 => (bool_contra t3 l0)) (fun r0 => (bool_contra r0 t4)))

theorem step1937 (p : Nat → Bool) (h : Constraints p) : p 88 = false ∨ p 82 = true ∨ p 89 = true ∨ p 87 = true ∨ p 1679 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 88 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 82 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 89 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 87 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 1679 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr hl)))))
  have t0 : p 98 = true := (Or.elim (step1328 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u4))))
  have t1 : p 101 = true := (Or.elim (step1327 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u4))))
  have t2 : p 100 = false := (Or.elim (step510 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u0 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t0 l2))) (fun r2 => (False.elim (bool_contra t1 r2))))))))
  exact (Or.elim (step1799 p h) (fun l0 => (bool_contra l0 t2)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u0 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u1)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u3)) (fun r3 => (bool_contra r3 u2)))))))))

theorem step1938 (p : Nat → Bool) (h : Constraints p) : p 1532 = true ∨ p 44 = false ∨ p 110 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1532 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 44 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 110 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 1530 = false := (Or.elim (step1050 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t1 : p 1528 = false := (Or.elim (step1052 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t2 : p 43 = true := (Or.elim (step1047 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t0))))
  have t3 : p 39 = true := (Or.elim (step1045 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t1))))
  exact (Or.elim (step153 p h) (fun l0 => (bool_contra u1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t3 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t2 l2)) (fun r2 => (bool_contra u2 r2)))))))

theorem step1939 (p : Nat → Bool) (h : Constraints p) : p 1572 = true ∨ p 1528 = false ∨ p 44 = false ∨ p 110 = false ∨ p 1525 = false ∨ p 1548 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1572 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1528 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 44 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 110 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 1525 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 1548 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl))))))
  have t0 : p 1532 = true := (Or.elim (step1938 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u2 l1))) (fun r1 => (False.elim (bool_contra u3 r1))))))
  have t1 : p 1538 = true := (Or.elim (step1067 p h) (fun l0 => (False.elim (bool_contra u4 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t0 l1))) (fun r1 => r1))))
  have t2 : p 1560 = true := (Or.elim (step1102 p h) (fun l0 => (False.elim (bool_contra u5 l0))) (fun r0 => r0))
  have t3 : p 1539 = false := (Or.elim (step1139 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t2 l1))) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t4 : p 1561 = false := (Or.elim (step1134 p h) (fun l0 => (False.elim (bool_contra t1 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t5 : p 1533 = false := (Or.elim (step1068 p h) (fun l0 => (False.elim (bool_contra u4 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t3))))))
  have t6 : p 1556 = false := (Or.elim (step1103 p h) (fun l0 => (False.elim (bool_contra u5 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t4))))))
  have t7 : p 1530 = false := (Or.elim (step1053 p h) (fun l0 => (False.elim (bool_contra u1 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t5))))))
  have t8 : p 1552 = false := (Or.elim (step1092 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t6))))
  have t9 : p 43 = true := (Or.elim (step1047 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t7))))
  have t10 : p 53 = true := (Or.elim (step1085 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t8))))
  exact (Or.elim (step155 p h) (fun l0 => (bool_contra u2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t9 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t10 l2)) (fun r2 => (bool_contra u3 r2)))))))

theorem step1940 (p : Nat → Bool) (h : Constraints p) : p 1573 = false ∨ p 1649 = false ∨ p 1494 = false ∨ p 1724 = false ∨ p 1509 = false ∨ p 1481 = false ∨ p 72 = true ∨ p 1611 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1573 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 1649 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1494 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 1724 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 1509 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 1481 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))
  have u6 : p 72 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))))
  have u7 : p 1611 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl))))))))
  have t0 : p 1475 = true := (step1931 p h)
  have t1 : p 1617 = true := (Or.elim (step1205 p h) (fun l0 => (False.elim (bool_contra l0 u6))) (fun r0 => r0))
  have t2 : p 1619 = true := (Or.elim (step1207 p h) (fun l0 => (False.elim (bool_contra t1 l0))) (fun r0 => r0))
  have t3 : p 1624 = true := (Or.elim (step1219 p h) (fun l0 => (False.elim (bool_contra u7 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t2 l1))) (fun r1 => r1))))
  have t4 : p 1659 = true := (Or.elim (step1288 p h) (fun l0 => (False.elim (bool_contra t3 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u1 l1))) (fun r1 => r1))))
  have t5 : p 1745 = true := (Or.elim (step1463 p h) (fun l0 => (False.elim (bool_contra t4 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u3 l1))) (fun r1 => r1))))
  have t6 : p 1595 = false := (Or.elim (step1899 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra t5 r0))))
  have t7 : p 1594 = true := (Or.elim (step1167 p h) (fun l0 => (False.elim (bool_contra u4 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u0 l1))) (fun r1 => r1))))
  have t8 : p 1510 = false := (Or.elim (step1174 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u0 l1))) (fun r1 => (False.elim (bool_contra r1 t6))))))
  have t9 : p 1746 = false := (Or.elim (step1898 p h) (fun l0 => (False.elim (bool_contra t7 l0))) (fun r0 => r0))
  have t10 : p 1500 = false := (Or.elim (step1014 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t8))))))
  have t11 : p 1660 = false := (Or.elim (step1470 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u3 l1))) (fun r1 => (False.elim (bool_contra r1 t9))))))
  have t12 : p 1486 = false := (Or.elim (step1002 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u2 l1))) (fun r1 => (False.elim (bool_contra r1 t10))))))
  have t13 : p 1625 = false := (Or.elim (step1295 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u1 l1))) (fun r1 => (False.elim (bool_contra r1 t11))))))
  have t14 : p 1483 = false := (Or.elim (step976 p h) (fun l0 => (False.elim (bool_contra u5 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t12))))))
  have t15 : p 1620 = false := (Or.elim (step1220 p h) (fun l0 => (False.elim (bool_contra u7 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t13))))))
  have t16 : p 19 = true := (Or.elim (step971 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t14))))
  have t17 : p 1618 = false := (Or.elim (step1208 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t15))))
  have t18 : p 73 = false := (Or.elim (step1682 p h) (fun l0 => (False.elim (bool_contra t16 l0))) (fun r0 => r0))
  exact (Or.elim (step1206 p h) (fun l0 => (bool_contra l0 u6)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t18)) (fun r1 => (bool_contra r1 t17)))))

theorem step1941 (p : Nat → Bool) (h : Constraints p) : p 1573 = true ∨ p 1548 = false ∨ p 1525 = false ∨ p 44 = false ∨ p 1554 = false ∨ p 110 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1573 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1548 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1525 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 44 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 1554 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 110 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl))))))
  have t0 : p 1556 = true := (Or.elim (step1090 p h) (fun l0 => (False.elim (bool_contra u4 l0))) (fun r0 => r0))
  have t1 : p 1561 = true := (Or.elim (step1103 p h) (fun l0 => (False.elim (bool_contra u1 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t0 l1))) (fun r1 => r1))))
  have t2 : p 1532 = true := (Or.elim (step1938 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u3 l1))) (fun r1 => (False.elim (bool_contra u5 r1))))))
  have t3 : p 1538 = true := (Or.elim (step1067 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t2 l1))) (fun r1 => r1))))
  have t4 : p 1562 = false := (Or.elim (step1135 p h) (fun l0 => (False.elim (bool_contra t3 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t5 : p 1539 = false := (Or.elim (step1140 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t1 l1))) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t6 : p 1557 = false := (Or.elim (step1104 p h) (fun l0 => (False.elim (bool_contra u1 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t4))))))
  have t7 : p 1533 = false := (Or.elim (step1068 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t5))))))
  have t8 : p 1552 = false := (Or.elim (step1093 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u4 l1))) (fun r1 => (False.elim (bool_contra r1 t6))))))
  have t9 : p 53 = true := (Or.elim (step1085 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t8))))
  have t10 : p 43 = false := (Or.elim (step155 p h) (fun l0 => (False.elim (bool_contra u3 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t9 l2))) (fun r2 => (False.elim (bool_contra u5 r2))))))))
  have t11 : p 39 = false := (Or.elim (step154 p h) (fun l0 => (False.elim (bool_contra u3 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t9 l2))) (fun r2 => (False.elim (bool_contra u5 r2))))))))
  have t12 : p 1530 = true := (Or.elim (step1047 p h) (fun l0 => (False.elim (bool_contra l0 t10))) (fun r0 => r0))
  have t13 : p 1528 = true := (Or.elim (step1045 p h) (fun l0 => (False.elim (bool_contra l0 t11))) (fun r0 => r0))
  exact (Or.elim (step1053 p h) (fun l0 => (bool_contra t13 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t12 l1)) (fun r1 => (bool_contra r1 t7)))))

theorem step1942 (p : Nat → Bool) (h : Constraints p) : p 1554 = false ∨ p 1548 = false ∨ p 1525 = false ∨ p 44 = false ∨ p 110 = false ∨ p 1574 = true ∨ p 1562 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1554 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 1548 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1525 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 44 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 110 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 1574 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))
  have u6 : p 1562 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl)))))))
  have t0 : p 1557 = false := (Or.elim (step1104 p h) (fun l0 => (False.elim (bool_contra u1 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u6))))))
  have t1 : p 1556 = true := (Or.elim (step1090 p h) (fun l0 => (False.elim (bool_contra u0 l0))) (fun r0 => r0))
  have t2 : p 1552 = false := (Or.elim (step1093 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u0 l1))) (fun r1 => (False.elim (bool_contra r1 t0))))))
  have t3 : p 1549 = false := (Or.elim (step1108 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t1 l1))) (fun r1 => (False.elim (bool_contra r1 u6))))))
  have t4 : p 1561 = true := (Or.elim (step1103 p h) (fun l0 => (False.elim (bool_contra u1 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t1 l1))) (fun r1 => r1))))
  have t5 : p 53 = true := (Or.elim (step1085 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t2))))
  have t6 : p 1545 = false := (Or.elim (step1081 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t3))))
  have t7 : p 1540 = false := (Or.elim (step1147 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t4 l1))) (fun r1 => (False.elim (bool_contra r1 u5))))))
  have t8 : p 43 = false := (Or.elim (step155 p h) (fun l0 => (False.elim (bool_contra u3 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t5 l2))) (fun r2 => (False.elim (bool_contra u4 r2))))))))
  have t9 : p 39 = false := (Or.elim (step154 p h) (fun l0 => (False.elim (bool_contra u3 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t5 l2))) (fun r2 => (False.elim (bool_contra u4 r2))))))))
  have t10 : p 1534 = false := (Or.elim (step1069 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t7))))))
  have t11 : p 1530 = true := (Or.elim (step1047 p h) (fun l0 => (False.elim (bool_contra l0 t8))) (fun r0 => r0))
  have t12 : p 1528 = true := (Or.elim (step1045 p h) (fun l0 => (False.elim (bool_contra l0 t9))) (fun r0 => r0))
  have t13 : p 1529 = false := (Or.elim (step1056 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t11 l1))) (fun r1 => (False.elim (bool_contra r1 t10))))))
  have t14 : p 1531 = false := (Or.elim (step1054 p h) (fun l0 => (False.elim (bool_contra t12 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t10))))))
  have t15 : p 41 = true := (Or.elim (step1046 p h) (fun l0 => (False.elim (bool_contra l0 t9))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t13))))))
  have t16 : p 42 = true := (Or.elim (step1049 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t8))) (fun r1 => (False.elim (bool_contra r1 t14))))))
  have t17 : p 1544 = true := (Or.elim (step1630 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra t15 r0))))
  have t18 : p 45 = false := (Or.elim (step1612 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra t16 r0))))
  have t19 : p 1546 = false := (Or.elim (step1079 p h) (fun l0 => (False.elim (bool_contra t17 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t3))))))
  have t20 : p 47 = true := (Or.elim (step1072 p h) (fun l0 => (False.elim (bool_contra l0 t18))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t6))))))
  have t21 : p 49 = true := (Or.elim (step1074 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t19))))
  have t22 : p 40 = false := (Or.elim (step144 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t15 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t16 l2))) (fun r2 => (False.elim (bool_contra t20 r2))))))))
  have t23 : p 48 = true := (Or.elim (step1745 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t20 l1))) (fun r1 => (False.elim (bool_contra r1 t22))))))
  exact (Or.elim (step163 p h) (fun l0 => (bool_contra t23 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t15 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t20 l2)) (fun r2 => (bool_contra t21 r2)))))))

theorem step1943 (p : Nat → Bool) (h : Constraints p) : p 1524 = true ∨ p 47 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1524 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 47 = true := bool_true_of_not_false (fun hl => hc (Or.inr hl))
  have t0 : p 1522 = false := (Or.elim (step1039 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t1 : p 1520 = false := (Or.elim (step1041 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t2 : p 35 = true := (Or.elim (step1036 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t0))))
  have t3 : p 34 = true := (Or.elim (step1037 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t0))))
  have t4 : p 33 = true := (Or.elim (step1033 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t1))))
  have t5 : p 37 = false := (Or.elim (step131 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t4 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t3 l2))) (fun r2 => (False.elim (bool_contra t2 r2))))))))
  have t6 : p 32 = false := (Or.elim (step118 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t4 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t2 l2))) (fun r2 => (False.elim (bool_contra u1 r2))))))))
  exact (Or.elim (step1734 p h) (fun l0 => (bool_contra l0 t5)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t2 l1)) (fun r1 => (bool_contra r1 t6)))))

theorem step1944 (p : Nat → Bool) (h : Constraints p) : p 1609 = true ∨ p 60 = false ∨ p 56 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1609 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 60 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 56 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 64 = true := (Or.elim (step1191 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t1 : p 55 = true := (Or.elim (step1913 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  exact (Or.elim (step182 p h) (fun l0 => (bool_contra t1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u2 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra u1 l2)) (fun r2 => (bool_contra t0 r2)))))))

theorem step1945 (p : Nat → Bool) (h : Constraints p) : p 87 = false ∨ p 1642 = true ∨ p 109 = false ∨ p 60 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 87 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 1642 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 109 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 60 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 88 = false := (Or.elim (step404 p h) (fun l0 => (False.elim (bool_contra u0 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u3 l1))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra u2 r2))))))))
  have t1 : p 90 = false := (Or.elim (step406 p h) (fun l0 => (False.elim (bool_contra u0 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u3 l1))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra u2 r2))))))))
  exact (Or.elim (step1248 p h) (fun l0 => (bool_contra l0 t0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t1)) (fun r1 => (bool_contra r1 u1)))))

theorem step1946 (p : Nat → Bool) (h : Constraints p) : p 84 = false ∨ p 1689 = true ∨ p 83 = false ∨ p 92 = true ∨ p 90 = false ∨ p 59 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 84 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 1689 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 83 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 92 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 90 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 59 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl))))))
  have t0 : p 1671 = true := (Or.elim (step1314 p h) (fun l0 => (False.elim (bool_contra l0 u3))) (fun r0 => r0))
  have t1 : p 1677 = false := (Or.elim (step1355 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u1))))
  have t2 : p 1674 = false := (Or.elim (step1323 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t1))))))
  have t3 : p 95 = false := (Or.elim (step342 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u0 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u4 l2))) (fun r2 => r2))))))
  have t4 : p 1673 = true := (Or.elim (step1317 p h) (fun l0 => (False.elim (bool_contra l0 t3))) (fun r0 => r0))
  have t5 : p 97 = true := (Or.elim (step1318 p h) (fun l0 => (False.elim (bool_contra l0 t3))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t2))))))
  have t6 : p 1676 = true := (Or.elim (step1322 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t4 l1))) (fun r1 => r1))))
  have t7 : p 1672 = false := (Or.elim (step1325 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t4 l1))) (fun r1 => (False.elim (bool_contra r1 t1))))))
  have t8 : p 86 = false := (Or.elim (step375 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u5 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u0 l2))) (fun r2 => (False.elim (bool_contra t5 r2))))))))
  have t9 : p 1683 = false := (Or.elim (step1351 p h) (fun l0 => (False.elim (bool_contra t6 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u1))))))
  have t10 : p 93 = true := (Or.elim (step1315 p h) (fun l0 => (False.elim (bool_contra l0 u3))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t7))))))
  have t11 : p 1679 = false := (Or.elim (step1335 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t9))))
  have t12 : p 96 = false := (Or.elim (step491 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u0 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t10 l2))) (fun r2 => (False.elim (bool_contra t5 r2))))))))
  have t13 : p 101 = true := (Or.elim (step1327 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t11))))
  have t14 : p 94 = true := (Or.elim (step1810 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t12))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra l2 t8))) (fun r2 => (False.elim (bool_contra t5 r2))))))))
  exact (Or.elim (step483 p h) (fun l0 => (bool_contra t14 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t10 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t5 l2)) (fun r2 => (bool_contra t13 r2)))))))

theorem step1947 (p : Nat → Bool) (h : Constraints p) : p 1607 = true ∨ p 56 = false ∨ p 59 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1607 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 56 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 59 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 62 = true := (Or.elim (step1187 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t1 : p 61 = true := (Or.elim (step1188 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t2 : p 57 = false := (Or.elim (step210 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u1 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u2 l2))) (fun r2 => (False.elim (bool_contra t0 r2))))))))
  have t3 : p 63 = true := (Or.elim (step1764 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t2))) (fun r1 => (False.elim (bool_contra t0 r1))))))
  exact (Or.elim (step235 p h) (fun l0 => (bool_contra t3 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u2 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t1 l2)) (fun r2 => (bool_contra t0 r2)))))))

end Dfs112FirstBoolean
