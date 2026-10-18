import Dfs112FirstBooleanPart0001
namespace Dfs112FirstBoolean
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem step1628 (p : Nat → Bool) (h : Constraints p) : p 33 = false ∨ p 1522 = true ∨ p 95 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 33 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 1522 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 95 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 157 = false := (step679 p h)
  have t1 : p 34 = true := (Or.elim (step1037 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u1))))
  have t2 : p 35 = true := (Or.elim (step1036 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u1))))
  have t3 : p 32 = false := (Or.elim (step119 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u0 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t2 l2))) (fun r2 => (False.elim (bool_contra u2 r2))))))))
  have t4 : p 37 = false := (Or.elim (step131 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u0 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t1 l2))) (fun r2 => (False.elim (bool_contra t2 r2))))))))
  exact (Or.elim (step128 p h) (fun l0 => (bool_contra t2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 t3)) (fun r2 => (bool_contra r2 t4)))))))

theorem step1629 (p : Nat → Bool) (h : Constraints p) : p 47 = false ∨ p 45 = false ∨ p 41 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 47 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 45 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 41 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 167 = false := (step684 p h)
  have t1 : p 40 = false := (Or.elim (step145 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u2 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u1 l2))) (fun r2 => (False.elim (bool_contra u0 r2))))))))
  exact (Or.elim (step157 p h) (fun l0 => (bool_contra u1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (bool_contra r1 t1)))))

theorem step1630 (p : Nat → Bool) (h : Constraints p) : p 1544 = true ∨ p 41 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1544 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 41 = true := bool_true_of_not_false (fun hl => hc (Or.inr hl))
  have t0 : p 47 = true := (Or.elim (step1070 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t1 : p 45 = true := (Or.elim (step1071 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  exact (Or.elim (step1629 p h) (fun l0 => (bool_contra t0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t1 l1)) (fun r1 => (bool_contra u1 r1)))))

theorem step1631 (p : Nat → Bool) (h : Constraints p) : p 61 = false ∨ p 62 = false ∨ p 89 = true ∨ p 92 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 61 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 62 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 89 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 92 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 183 = false := (step692 p h)
  have t1 : p 63 = true := (Or.elim (step228 p h) (fun l0 => (False.elim (bool_contra u0 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra r2 u2))))))))
  exact (Or.elim (step238 p h) (fun l0 => (bool_contra t1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u0 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra u1 l2)) (fun r2 => (bool_contra u3 r2)))))))

theorem step1632 (p : Nat → Bool) (h : Constraints p) : p 1524 = true ∨ p 95 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1524 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 95 = true := bool_true_of_not_false (fun hl => hc (Or.inr hl))
  have t0 : p 1522 = false := (Or.elim (step1039 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t1 : p 1520 = false := (Or.elim (step1041 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t2 : p 33 = false := (Or.elim (step1628 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => (False.elim (bool_contra u1 r1))))))
  exact (Or.elim (step1033 p h) (fun l0 => (bool_contra l0 t2)) (fun r0 => (bool_contra r0 t1)))

theorem step1633 (p : Nat → Bool) (h : Constraints p) : p 1574 = true ∨ p 1530 = false ∨ p 39 = true ∨ p 1547 = false ∨ p 1524 = false ∨ p 1556 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1574 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1530 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 39 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 1547 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 1524 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 1556 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl))))))
  have t0 : p 1528 = true := (Or.elim (step1045 p h) (fun l0 => (False.elim (bool_contra l0 u2))) (fun r0 => r0))
  have t1 : p 1533 = true := (Or.elim (step1053 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u1 l1))) (fun r1 => r1))))
  have t2 : p 1538 = true := (Or.elim (step1063 p h) (fun l0 => (False.elim (bool_contra u4 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t1 l1))) (fun r1 => r1))))
  have t3 : p 1549 = true := (Or.elim (step1077 p h) (fun l0 => (False.elim (bool_contra u3 l0))) (fun r0 => r0))
  have t4 : p 1562 = true := (Or.elim (step1108 p h) (fun l0 => (False.elim (bool_contra t3 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u5 l1))) (fun r1 => r1))))
  have t5 : p 1539 = false := (Or.elim (step1141 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t4 l1))) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t6 : p 1534 = false := (Or.elim (step1064 p h) (fun l0 => (False.elim (bool_contra u4 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t5))))))
  have t7 : p 1563 = false := (Or.elim (step1136 p h) (fun l0 => (False.elim (bool_contra t2 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t8 : p 1529 = false := (Or.elim (step1056 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u1 l1))) (fun r1 => (False.elim (bool_contra r1 t6))))))
  have t9 : p 1550 = false := (Or.elim (step1113 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u5 l1))) (fun r1 => (False.elim (bool_contra r1 t7))))))
  have t10 : p 41 = true := (Or.elim (step1046 p h) (fun l0 => (False.elim (bool_contra l0 u2))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t8))))))
  have t11 : p 1544 = false := (Or.elim (step1080 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u3 l1))) (fun r1 => (False.elim (bool_contra r1 t9))))))
  exact (Or.elim (step1630 p h) (fun l0 => (bool_contra l0 t11)) (fun r0 => (bool_contra t10 r0)))

theorem step1634 (p : Nat → Bool) (h : Constraints p) : p 1646 = false ∨ p 1662 = true ∨ p 73 = true ∨ p 1612 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1646 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 1662 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 73 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 1612 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 74 = true := (step1548 p h)
  have t1 : p 76 = true := (step289 p h)
  have t2 : p 1617 = true := (Or.elim (step1204 p h) (fun l0 => (False.elim (bool_contra l0 u2))) (fun r0 => r0))
  have t3 : p 1619 = true := (Or.elim (step1207 p h) (fun l0 => (False.elim (bool_contra t2 l0))) (fun r0 => r0))
  have t4 : p 1625 = true := (Or.elim (step1224 p h) (fun l0 => (False.elim (bool_contra u3 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t3 l1))) (fun r1 => r1))))
  have t5 : p 1651 = false := (Or.elim (step1297 p h) (fun l0 => (False.elim (bool_contra t4 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u1))))))
  have t6 : p 1650 = true := (Or.elim (step1260 p h) (fun l0 => (False.elim (bool_contra u0 l0))) (fun r0 => r0))
  have t7 : p 1635 = false := (Or.elim (step1264 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u0 l1))) (fun r1 => (False.elim (bool_contra r1 t5))))))
  have t8 : p 1626 = false := (Or.elim (step1303 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t6 l1))) (fun r1 => (False.elim (bool_contra r1 u1))))))
  have t9 : p 1631 = false := (Or.elim (step1240 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t7))))
  have t10 : p 1620 = false := (Or.elim (step1225 p h) (fun l0 => (False.elim (bool_contra u3 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t8))))))
  have t11 : p 77 = true := (Or.elim (step1234 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t9))))
  have t12 : p 1618 = false := (Or.elim (step1208 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t10))))
  have t13 : p 72 = false := (Or.elim (step278 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t1 l2))) (fun r2 => (False.elim (bool_contra t11 r2))))))))
  exact (Or.elim (step1206 p h) (fun l0 => (bool_contra l0 t13)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 u2)) (fun r1 => (bool_contra r1 t12)))))

theorem step1635 (p : Nat → Bool) (h : Constraints p) : p 1626 = false ∨ p 1571 = false ∨ p 1646 = false ∨ p 1495 = false ∨ p 1633 = false ∨ p 1723 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1626 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 1571 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1646 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 1495 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 1633 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 1723 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl))))))
  have t0 : p 1780 = false := (step1504 p h)
  have t1 : p 74 = true := (step1548 p h)
  have t2 : p 76 = true := (step289 p h)
  have t3 : p 1474 = true := (step1576 p h)
  have t4 : p 1499 = true := (Or.elim (step996 p h) (fun l0 => (False.elim (bool_contra u3 l0))) (fun r0 => r0))
  have t5 : p 1508 = true := (Or.elim (step1009 p h) (fun l0 => (False.elim (bool_contra t3 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t4 l1))) (fun r1 => r1))))
  have t6 : p 1591 = true := (Or.elim (step1157 p h) (fun l0 => (False.elim (bool_contra t5 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u1 l1))) (fun r1 => r1))))
  have t7 : p 1749 = false := (Or.elim (step1497 p h) (fun l0 => (False.elim (bool_contra t6 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t0))))))
  have t8 : p 1664 = false := (Or.elim (step1494 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u5 l1))) (fun r1 => (False.elim (bool_contra r1 t7))))))
  have t9 : p 1635 = true := (Or.elim (step1238 p h) (fun l0 => (False.elim (bool_contra u4 l0))) (fun r0 => r0))
  have t10 : p 1651 = true := (Or.elim (step1264 p h) (fun l0 => (False.elim (bool_contra t9 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u2 l1))) (fun r1 => r1))))
  have t11 : p 1652 = false := (Or.elim (step1305 p h) (fun l0 => (False.elim (bool_contra u0 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t8))))))
  have t12 : p 1663 = true := (Or.elim (step1304 p h) (fun l0 => (False.elim (bool_contra u0 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t10 l1))) (fun r1 => r1))))
  have t13 : p 1636 = false := (Or.elim (step1269 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u2 l1))) (fun r1 => (False.elim (bool_contra r1 t11))))))
  have t14 : p 1748 = true := (Or.elim (step1489 p h) (fun l0 => (False.elim (bool_contra t12 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u5 l1))) (fun r1 => r1))))
  have t15 : p 1631 = false := (Or.elim (step1241 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u4 l1))) (fun r1 => (False.elim (bool_contra r1 t13))))))
  have t16 : p 1592 = false := (Or.elim (step1498 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t14 l1))) (fun r1 => (False.elim (bool_contra r1 t0))))))
  have t17 : p 77 = true := (Or.elim (step1234 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t15))))
  have t18 : p 1509 = false := (Or.elim (step1165 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u1 l1))) (fun r1 => (False.elim (bool_contra r1 t16))))))
  have t19 : p 18 = false := (Or.elim (step277 p h) (fun l0 => (False.elim (bool_contra t1 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t2 l2))) (fun r2 => (False.elim (bool_contra t17 r2))))))))
  have t20 : p 1500 = false := (Or.elim (step1010 p h) (fun l0 => (False.elim (bool_contra t3 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t18))))))
  have t21 : p 1481 = true := (Or.elim (step967 p h) (fun l0 => (False.elim (bool_contra l0 t19))) (fun r0 => r0))
  have t22 : p 1485 = false := (Or.elim (step1000 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u3 l1))) (fun r1 => (False.elim (bool_contra r1 t20))))))
  exact (Or.elim (step975 p h) (fun l0 => (bool_contra t21 l0)) (fun r0 => (bool_contra r0 t22)))

theorem step1636 (p : Nat → Bool) (h : Constraints p) : p 87 = false ∨ p 98 = false ∨ p 109 = false ∨ p 1642 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 87 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 98 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 109 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 1642 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 90 = false := (Or.elim (step417 p h) (fun l0 => (False.elim (bool_contra u0 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u1 l2))) (fun r2 => (False.elim (bool_contra u2 r2))))))))
  have t1 : p 88 = false := (Or.elim (step416 p h) (fun l0 => (False.elim (bool_contra u0 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u1 l2))) (fun r2 => (False.elim (bool_contra u2 r2))))))))
  exact (Or.elim (step1248 p h) (fun l0 => (bool_contra l0 t1)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (bool_contra r1 u3)))))

theorem step1637 (p : Nat → Bool) (h : Constraints p) : p 1546 = true ∨ p 118 = true ∨ p 122 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1546 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 118 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 122 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 172 = false := (step687 p h)
  have t1 : p 171 = false := (step686 p h)
  have t2 : p 358 = false := (step1558 p h)
  have t3 : p 50 = true := (Or.elim (step1073 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t4 : p 49 = true := (Or.elim (step1074 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t5 : p 52 = true := (Or.elim (step167 p h) (fun l0 => (False.elim (bool_contra t3 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra r2 u1))))))))
  have t6 : p 51 = true := (Or.elim (step168 p h) (fun l0 => (False.elim (bool_contra t3 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra r2 u1))))))))
  have t7 : p 54 = true := (Or.elim (step165 p h) (fun l0 => (False.elim (bool_contra t4 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t1))) (fun r1 => r1))))
  have t8 : p 53 = false := (Or.elim (step179 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t6 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t5 l2))) (fun r2 => (False.elim (bool_contra t7 r2))))))))
  have t9 : p 176 = true := (Or.elim (step181 p h) (fun l0 => (False.elim (bool_contra t7 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra l2 t8))) (fun r2 => (False.elim (bool_contra r2 u2))))))))
  have t10 : p 173 = true := (Or.elim (step171 p h) (fun l0 => (False.elim (bool_contra t6 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t8))))))
  have t11 : p 343 = true := (Or.elim (step800 p h) (fun l0 => (False.elim (bool_contra t9 l0))) (fun r0 => r0))
  have t12 : p 337 = true := (Or.elim (step793 p h) (fun l0 => (False.elim (bool_contra t10 l0))) (fun r0 => r0))
  have t13 : p 347 = true := (Or.elim (step803 p h) (fun l0 => (False.elim (bool_contra t11 l0))) (fun r0 => r0))
  have t14 : p 339 = true := (Or.elim (step795 p h) (fun l0 => (False.elim (bool_contra t12 l0))) (fun r0 => r0))
  have t15 : p 355 = true := (Or.elim (step807 p h) (fun l0 => (False.elim (bool_contra t13 l0))) (fun r0 => r0))
  have t16 : p 341 = true := (Or.elim (step797 p h) (fun l0 => (False.elim (bool_contra t14 l0))) (fun r0 => r0))
  exact (Or.elim (step812 p h) (fun l0 => (bool_contra t16 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t15 l1)) (fun r1 => (bool_contra r1 t2)))))

theorem step1638 (p : Nat → Bool) (h : Constraints p) : p 1524 = true ∨ p 94 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1524 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 94 = false := bool_false_of_not_true (fun hl => hc (Or.inr hl))
  have t0 : p 153 = false := (step676 p h)
  have t1 : p 1522 = false := (Or.elim (step1039 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t2 : p 1520 = false := (Or.elim (step1041 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t3 : p 34 = true := (Or.elim (step1037 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t1))))
  have t4 : p 33 = true := (Or.elim (step1033 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t2))))
  have t5 : p 31 = true := (Or.elim (step1034 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t2))))
  have t6 : p 30 = false := (Or.elim (step109 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t5 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t4 l2))) (fun r2 => (False.elim (bool_contra t3 r2))))))))
  exact (Or.elim (step111 p h) (fun l0 => (bool_contra t5 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 t6)) (fun r2 => (bool_contra r2 u1)))))))

theorem step1639 (p : Nat → Bool) (h : Constraints p) : p 1525 = true ∨ p 34 = true ∨ p 32 = false ∨ p 95 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1525 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 34 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 32 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 95 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 1522 = true := (Or.elim (step1037 p h) (fun l0 => (False.elim (bool_contra l0 u1))) (fun r0 => r0))
  have t1 : p 1523 = false := (Or.elim (step1040 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t2 : p 1520 = false := (Or.elim (step1042 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t0 l1))) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t3 : p 35 = true := (Or.elim (step1038 p h) (fun l0 => (False.elim (bool_contra l0 u1))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t1))))))
  have t4 : p 33 = true := (Or.elim (step1033 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t2))))
  exact (Or.elim (step119 p h) (fun l0 => (bool_contra u2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t4 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t3 l2)) (fun r2 => (bool_contra u3 r2)))))))

theorem step1640 (p : Nat → Bool) (h : Constraints p) : p 1650 = true ∨ p 87 = true ∨ p 88 = true ∨ p 1640 = false ∨ p 95 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1650 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 87 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 88 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 1640 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 95 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr hl)))))
  have t0 : p 212 = false := (step706 p h)
  have t1 : p 1641 = true := (Or.elim (step1247 p h) (fun l0 => (False.elim (bool_contra l0 u2))) (fun r0 => r0))
  have t2 : p 1645 = true := (Or.elim (step1255 p h) (fun l0 => (False.elim (bool_contra u3 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t1 l1))) (fun r1 => r1))))
  have t3 : p 1646 = false := (Or.elim (step1260 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t4 : p 1635 = false := (Or.elim (step1263 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t2 l1))) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t5 : p 1642 = false := (Or.elim (step1256 p h) (fun l0 => (False.elim (bool_contra u3 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t3))))))
  have t6 : p 1633 = false := (Or.elim (step1238 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t4))))
  have t7 : p 90 = true := (Or.elim (step1248 p h) (fun l0 => (False.elim (bool_contra l0 u2))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t5))))))
  have t8 : p 80 = true := (Or.elim (step1235 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t6))))
  have t9 : p 83 = true := (Or.elim (step446 p h) (fun l0 => (False.elim (bool_contra t7 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra r2 u1))))))))
  exact (Or.elim (step339 p h) (fun l0 => (bool_contra t9 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t8 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t7 l2)) (fun r2 => (bool_contra u4 r2)))))))

theorem step1641 (p : Nat → Bool) (h : Constraints p) : p 1650 = true ∨ p 98 = false ∨ p 88 = true ∨ p 1640 = false ∨ p 95 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1650 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 98 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 88 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 1640 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 95 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr hl)))))
  have t0 : p 1641 = true := (Or.elim (step1247 p h) (fun l0 => (False.elim (bool_contra l0 u2))) (fun r0 => r0))
  have t1 : p 1645 = true := (Or.elim (step1255 p h) (fun l0 => (False.elim (bool_contra u3 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t0 l1))) (fun r1 => r1))))
  have t2 : p 1646 = false := (Or.elim (step1260 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t3 : p 1635 = false := (Or.elim (step1263 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t1 l1))) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t4 : p 87 = true := (Or.elim (step1640 p h) (fun l0 => (False.elim (bool_contra l0 u0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra l2 u2))) (fun r2 => (Or.elim r2 (fun l3 => (False.elim (bool_contra u3 l3))) (fun r3 => (False.elim (bool_contra u4 r3))))))))))
  have t5 : p 1642 = false := (Or.elim (step1256 p h) (fun l0 => (False.elim (bool_contra u3 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t2))))))
  have t6 : p 1633 = false := (Or.elim (step1238 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t3))))
  have t7 : p 90 = true := (Or.elim (step1248 p h) (fun l0 => (False.elim (bool_contra l0 u2))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t5))))))
  have t8 : p 80 = true := (Or.elim (step1235 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t6))))
  exact (Or.elim (step411 p h) (fun l0 => (bool_contra t4 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t8 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t7 l2)) (fun r2 => (bool_contra u1 r2)))))))

theorem step1642 (p : Nat → Bool) (h : Constraints p) : p 1548 = true ∨ p 32 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1548 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 32 = true := bool_true_of_not_false (fun hl => hc (Or.inr hl))
  have t0 : p 171 = false := (step686 p h)
  have t1 : p 167 = false := (step684 p h)
  have t2 : p 1546 = false := (Or.elim (step1076 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t3 : p 1544 = false := (Or.elim (step1078 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t4 : p 49 = true := (Or.elim (step1074 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t2))))
  have t5 : p 47 = true := (Or.elim (step1070 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t3))))
  have t6 : p 45 = true := (Or.elim (step1071 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t3))))
  have t7 : p 48 = true := (Or.elim (step166 p h) (fun l0 => (False.elim (bool_contra t4 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => r1))))
  have t8 : p 40 = false := (Or.elim (step160 p h) (fun l0 => (False.elim (bool_contra t5 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u1 l1))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra t7 r2))))))))
  exact (Or.elim (step157 p h) (fun l0 => (bool_contra t6 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t1)) (fun r1 => (bool_contra r1 t8)))))

theorem step1643 (p : Nat → Bool) (h : Constraints p) : p 1712 = true ∨ p 1699 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1712 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1699 = true := bool_true_of_not_false (fun hl => hc (Or.inr hl))
  have t0 : p 1700 = false := (Or.elim (step1401 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t1 : p 1707 = false := (Or.elim (step1397 p h) (fun l0 => (False.elim (bool_contra u1 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t2 : p 1705 = false := (Or.elim (step1384 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t1))))
  have t3 : p 122 = true := (Or.elim (step1381 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t2))))
  have t4 : p 119 = true := (Or.elim (step1382 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t2))))
  exact (Or.elim (step1618 p h) (fun l0 => (bool_contra l0 t0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t4 l1)) (fun r1 => (bool_contra t3 r1)))))

theorem step1644 (p : Nat → Bool) (h : Constraints p) : p 1475 = true ∨ p 10 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1475 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 10 = false := bool_false_of_not_true (fun hl => hc (Or.inr hl))
  have t0 : p 135 = false := (step667 p h)
  have t1 : p 1466 = true := (Or.elim (step936 p h) (fun l0 => (False.elim (bool_contra l0 u1))) (fun r0 => r0))
  have t2 : p 1470 = true := (Or.elim (step944 p h) (fun l0 => (False.elim (bool_contra t1 l0))) (fun r0 => r0))
  have t3 : p 1471 = false := (Or.elim (step951 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t4 : p 1463 = false := (Or.elim (step955 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t2 l1))) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t5 : p 1467 = false := (Or.elim (step947 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t3))))
  have t6 : p 1468 = false := (Or.elim (step945 p h) (fun l0 => (False.elim (bool_contra t1 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t3))))))
  have t7 : p 1461 = false := (Or.elim (step931 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t4))))
  have t8 : p 8 = true := (Or.elim (step938 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u1))) (fun r1 => (False.elim (bool_contra r1 t5))))))
  have t9 : p 13 = true := (Or.elim (step939 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t6))))
  have t10 : p 6 = true := (Or.elim (step928 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t7))))
  have t11 : p 5 = true := (Or.elim (step56 p h) (fun l0 => (False.elim (bool_contra t9 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => r1))))
  exact (Or.elim (step15 p h) (fun l0 => (bool_contra t11 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t10 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t8 l2)) (fun r2 => (bool_contra t9 r2)))))))

theorem step1645 (p : Nat → Bool) (h : Constraints p) : p 1609 = true ∨ p 94 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1609 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 94 = false := bool_false_of_not_true (fun hl => hc (Or.inr hl))
  have t0 : p 189 = false := (step695 p h)
  have t1 : p 67 = true := (Or.elim (step1190 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t2 : p 64 = true := (Or.elim (step1191 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t3 : p 66 = true := (Or.elim (step255 p h) (fun l0 => (False.elim (bool_contra t1 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra r2 u1))))))))
  have t4 : p 65 = true := (Or.elim (step256 p h) (fun l0 => (False.elim (bool_contra t1 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra r2 u1))))))))
  exact (Or.elim (step1525 p h) (fun l0 => (bool_contra t2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t4 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t3 l2)) (fun r2 => (bool_contra t1 r2)))))))

theorem step1646 (p : Nat → Bool) (h : Constraints p) : p 1464 = true ∨ p 4 = true ∨ p 7 = false ∨ p 61 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1464 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 4 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 7 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 61 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 1461 = true := (Or.elim (step929 p h) (fun l0 => (False.elim (bool_contra l0 u1))) (fun r0 => r0))
  have t1 : p 1462 = false := (Or.elim (step932 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t2 : p 2 = true := (Or.elim (step934 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t0 l1))) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t3 : p 6 = true := (Or.elim (step930 p h) (fun l0 => (False.elim (bool_contra l0 u1))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t1))))))
  exact (Or.elim (step33 p h) (fun l0 => (bool_contra u2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t2 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t3 l2)) (fun r2 => (bool_contra u3 r2)))))))

theorem step1647 (p : Nat → Bool) (h : Constraints p) : p 1675 = false ∨ p 1721 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1675 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 1721 = false := bool_false_of_not_true (fun hl => hc (Or.inr hl))
  have t0 : p 1711 = true := (step1586 p h)
  have t1 : p 1688 = false := (Or.elim (step1417 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t0 l1))) (fun r1 => (False.elim (bool_contra r1 u1))))))
  have t2 : p 1687 = true := (Or.elim (step1345 p h) (fun l0 => (False.elim (bool_contra u0 l0))) (fun r0 => r0))
  have t3 : p 1683 = false := (Or.elim (step1346 p h) (fun l0 => (False.elim (bool_contra u0 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t1))))))
  have t4 : p 1712 = false := (Or.elim (step1412 p h) (fun l0 => (False.elim (bool_contra t2 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u1))))))
  have t5 : p 1699 = true := (Or.elim (step1587 p h) (fun l0 => (False.elim (bool_contra l0 t3))) (fun r0 => r0))
  exact (Or.elim (step1643 p h) (fun l0 => (bool_contra l0 t4)) (fun r0 => (bool_contra t5 r0)))

theorem step1648 (p : Nat → Bool) (h : Constraints p) : p 1649 = true ∨ p 1639 = false ∨ p 1631 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1649 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1639 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1631 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 1643 = true := (step1579 p h)
  have t1 : p 1635 = true := (Or.elim (step1240 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => r0))
  have t2 : p 1636 = false := (Or.elim (step1266 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t0 l1))) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t3 : p 1644 = false := (Or.elim (step1262 p h) (fun l0 => (False.elim (bool_contra t1 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t4 : p 1633 = false := (Or.elim (step1241 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t2))))))
  have t5 : p 1640 = false := (Or.elim (step1254 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t3))))
  have t6 : p 1641 = false := (Or.elim (step1252 p h) (fun l0 => (False.elim (bool_contra u1 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t3))))))
  have t7 : p 80 = true := (Or.elim (step1235 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t4))))
  exact (Or.elim (step1602 p h) (fun l0 => (bool_contra l0 t6)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t5)) (fun r1 => (bool_contra t7 r1)))))

theorem step1649 (p : Nat → Bool) (h : Constraints p) : p 1675 = true ∨ p 23 = false ∨ p 27 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1675 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 23 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 27 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 145 = false := (step672 p h)
  have t1 : p 1673 = false := (Or.elim (step1319 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t2 : p 1671 = false := (Or.elim (step1321 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t3 : p 97 = true := (Or.elim (step1316 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t1))))
  have t4 : p 92 = true := (Or.elim (step1314 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t2))))
  have t5 : p 86 = false := (Or.elim (step373 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u1 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t4 l2))) (fun r2 => (False.elim (bool_contra t3 r2))))))))
  have t6 : p 28 = false := (Or.elim (step104 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u1 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u2 l2))) (fun r2 => (False.elim (bool_contra t4 r2))))))))
  exact (Or.elim (step82 p h) (fun l0 => (bool_contra u1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 t6)) (fun r2 => (bool_contra r2 t5)))))))

theorem step1650 (p : Nat → Bool) (h : Constraints p) : p 1641 = true ∨ p 80 = false ∨ p 92 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1641 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 80 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 92 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 212 = false := (step706 p h)
  have t1 : p 90 = true := (Or.elim (step1246 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t2 : p 88 = true := (Or.elim (step1247 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t3 : p 87 = false := (Or.elim (step408 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u1 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t2 l2))) (fun r2 => (False.elim (bool_contra t1 r2))))))))
  have t4 : p 91 = false := (Or.elim (step450 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t2 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t1 l2))) (fun r2 => (False.elim (bool_contra u2 r2))))))))
  exact (Or.elim (step444 p h) (fun l0 => (bool_contra t1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 t3)) (fun r2 => (bool_contra r2 t4)))))))

theorem step1651 (p : Nat → Bool) (h : Constraints p) : p 90 = false ∨ p 87 = true ∨ p 88 = false ∨ p 92 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 90 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 87 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 88 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 92 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 212 = false := (step706 p h)
  have t1 : p 91 = false := (Or.elim (step450 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u2 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u0 l2))) (fun r2 => (False.elim (bool_contra u3 r2))))))))
  exact (Or.elim (step444 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u1)) (fun r2 => (bool_contra r2 t1)))))))

theorem step1652 (p : Nat → Bool) (h : Constraints p) : p 1699 = true ∨ p 87 = true ∨ p 80 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1699 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 87 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 80 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 231 = false := (step715 p h)
  have t1 : p 1697 = false := (Or.elim (step1370 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t2 : p 1695 = false := (Or.elim (step1372 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t3 : p 113 = true := (Or.elim (step1367 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t1))))
  have t4 : p 109 = true := (Or.elim (step1365 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t2))))
  have t5 : p 103 = false := (Or.elim (step543 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u2 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t4 l2))) (fun r2 => (False.elim (bool_contra t3 r2))))))))
  exact (Or.elim (step595 p h) (fun l0 => (bool_contra t4 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u1)) (fun r2 => (bool_contra r2 t5)))))))

theorem step1653 (p : Nat → Bool) (h : Constraints p) : p 79 = false ∨ p 1499 = true ∨ p 73 = false ∨ p 200 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 79 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 1499 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 73 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 200 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 201 = false := (step701 p h)
  have t1 : p 74 = true := (step1548 p h)
  have t2 : p 76 = true := (step289 p h)
  have t3 : p 1487 = false := (Or.elim (step1004 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u1))))
  have t4 : p 78 = true := (Or.elim (step296 p h) (fun l0 => (False.elim (bool_contra u0 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => r1))))
  have t5 : p 75 = true := (Or.elim (step297 p h) (fun l0 => (False.elim (bool_contra u0 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => r1))))
  have t6 : p 19 = false := (Or.elim (step282 p h) (fun l0 => (False.elim (bool_contra t5 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u2 l2))) (fun r2 => (False.elim (bool_contra u0 r2))))))))
  have t7 : p 77 = true := (Or.elim (step295 p h) (fun l0 => (False.elim (bool_contra t4 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u3))) (fun r1 => r1))))
  have t8 : p 1483 = true := (Or.elim (step971 p h) (fun l0 => (False.elim (bool_contra l0 t6))) (fun r0 => r0))
  have t9 : p 18 = false := (Or.elim (step277 p h) (fun l0 => (False.elim (bool_contra t1 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t2 l2))) (fun r2 => (False.elim (bool_contra t7 r2))))))))
  have t10 : p 1481 = true := (Or.elim (step967 p h) (fun l0 => (False.elim (bool_contra l0 t9))) (fun r0 => r0))
  have t11 : p 1486 = true := (Or.elim (step976 p h) (fun l0 => (False.elim (bool_contra t10 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t8 l1))) (fun r1 => r1))))
  have t12 : p 1484 = false := (Or.elim (step977 p h) (fun l0 => (False.elim (bool_contra t10 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t3))))))
  have t13 : p 1493 = false := (Or.elim (step1001 p h) (fun l0 => (False.elim (bool_contra t11 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u1))))))
  have t14 : p 21 = true := (Or.elim (step972 p h) (fun l0 => (False.elim (bool_contra l0 t6))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t12))))))
  exact (Or.elim (step1575 p h) (fun l0 => (bool_contra l0 t13)) (fun r0 => (bool_contra t14 r0)))

theorem step1654 (p : Nat → Bool) (h : Constraints p) : p 1536 = true ∨ p 22 = false ∨ p 23 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1536 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 22 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 23 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 1532 = false := (Or.elim (step1058 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t1 : p 1524 = false := (Or.elim (step1061 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t2 : p 1530 = false := (Or.elim (step1050 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t0))))
  have t3 : p 1520 = false := (Or.elim (step1041 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t1))))
  have t4 : p 42 = true := (Or.elim (step1048 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t2))))
  have t5 : p 33 = true := (Or.elim (step1033 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t3))))
  exact (Or.elim (step78 p h) (fun l0 => (bool_contra u1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u2 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t5 l2)) (fun r2 => (bool_contra t4 r2)))))))

theorem step1655 (p : Nat → Bool) (h : Constraints p) : p 1493 = true ∨ p 28 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1493 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 28 = false := bool_false_of_not_true (fun hl => hc (Or.inr hl))
  have t0 : p 149 = false := (step675 p h)
  have t1 : p 1491 = false := (Or.elim (step987 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t2 : p 1489 = false := (Or.elim (step989 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t3 : p 27 = true := (Or.elim (step984 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t1))))
  have t4 : p 26 = true := (Or.elim (step985 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t1))))
  have t5 : p 24 = true := (Or.elim (step981 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t2))))
  have t6 : p 25 = true := (Or.elim (step101 p h) (fun l0 => (False.elim (bool_contra t3 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra r2 u1))))))))
  exact (Or.elim (step94 p h) (fun l0 => (bool_contra t6 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t5 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t4 l2)) (fun r2 => (bool_contra t3 r2)))))))

theorem step1656 (p : Nat → Bool) (h : Constraints p) : p 1677 = true ∨ p 86 = false ∨ p 1524 = true ∨ p 23 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1677 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 86 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1524 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 23 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 153 = false := (step676 p h)
  have t1 : p 1520 = false := (Or.elim (step1041 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u2))))
  have t2 : p 31 = true := (Or.elim (step1034 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t1))))
  have t3 : p 94 = true := (Or.elim (step1638 p h) (fun l0 => (False.elim (bool_contra l0 u2))) (fun r0 => r0))
  have t4 : p 33 = true := (Or.elim (step1033 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t1))))
  have t5 : p 1522 = false := (Or.elim (step1039 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u2))))
  have t6 : p 34 = true := (Or.elim (step1037 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t5))))
  have t7 : p 30 = false := (Or.elim (step109 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t2 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t4 l2))) (fun r2 => (False.elim (bool_contra t6 r2))))))))
  have t8 : p 29 = true := (Or.elim (step113 p h) (fun l0 => (False.elim (bool_contra t2 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra r2 t7))))))))
  have t9 : p 93 = false := (Or.elim (step1515 p h) (fun l0 => (False.elim (bool_contra t8 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t2 l1))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra t3 r2))))))))
  have t10 : p 1671 = true := (Or.elim (step1313 p h) (fun l0 => (False.elim (bool_contra l0 t9))) (fun r0 => r0))
  have t11 : p 95 = false := (Or.elim (step1632 p h) (fun l0 => (False.elim (bool_contra l0 u2))) (fun r0 => r0))
  have t12 : p 1673 = true := (Or.elim (step1317 p h) (fun l0 => (False.elim (bool_contra l0 t11))) (fun r0 => r0))
  have t13 : p 1672 = false := (Or.elim (step1325 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t12 l1))) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t14 : p 1674 = false := (Or.elim (step1323 p h) (fun l0 => (False.elim (bool_contra t10 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t15 : p 92 = true := (Or.elim (step1315 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t9))) (fun r1 => (False.elim (bool_contra r1 t13))))))
  have t16 : p 97 = true := (Or.elim (step1318 p h) (fun l0 => (False.elim (bool_contra l0 t11))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t14))))))
  exact (Or.elim (step373 p h) (fun l0 => (bool_contra u1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u3 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t15 l2)) (fun r2 => (bool_contra t16 r2)))))))

theorem step1657 (p : Nat → Bool) (h : Constraints p) : p 1679 = true ∨ p 1524 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1679 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1524 = false := bool_false_of_not_true (fun hl => hc (Or.inr hl))
  have t0 : p 156 = false := (step678 p h)
  have t1 : p 1522 = false := (Or.elim (step1039 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u1))))
  have t2 : p 35 = true := (Or.elim (step1036 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t1))))
  have t3 : p 1520 = false := (Or.elim (step1041 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u1))))
  have t4 : p 33 = true := (Or.elim (step1033 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t3))))
  have t5 : p 34 = true := (Or.elim (step1037 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t1))))
  have t6 : p 37 = false := (Or.elim (step131 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t4 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t5 l2))) (fun r2 => (False.elim (bool_contra t2 r2))))))))
  have t7 : p 31 = true := (Or.elim (step1034 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t3))))
  have t8 : p 30 = false := (Or.elim (step109 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t7 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t4 l2))) (fun r2 => (False.elim (bool_contra t5 r2))))))))
  have t9 : p 100 = true := (Or.elim (step126 p h) (fun l0 => (False.elim (bool_contra t5 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra l2 t8))) (fun r2 => (Or.elim r2 (fun l3 => (False.elim (bool_contra l3 t6))) (fun r3 => r3))))))))
  have t10 : p 101 = true := (Or.elim (step1327 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t11 : p 98 = true := (Or.elim (step1328 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  exact (Or.elim (step509 p h) (fun l0 => (bool_contra t9 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t5 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t11 l2)) (fun r2 => (bool_contra t10 r2)))))))

theorem step1658 (p : Nat → Bool) (h : Constraints p) : p 1461 = false ∨ p 13 = true ∨ p 7 = false ∨ p 1477 = true ∨ p 138 = true ∨ p 26 = false ∨ p 1466 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1461 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 13 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 7 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 1477 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 138 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 26 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))
  have u6 : p 1466 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl)))))))
  have t0 : p 134 = false := (step666 p h)
  have t1 : p 1468 = true := (Or.elim (step939 p h) (fun l0 => (False.elim (bool_contra l0 u1))) (fun r0 => r0))
  have t2 : p 1471 = true := (Or.elim (step945 p h) (fun l0 => (False.elim (bool_contra u6 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t1 l1))) (fun r1 => r1))))
  have t3 : p 1464 = false := (Or.elim (step961 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t2 l1))) (fun r1 => (False.elim (bool_contra r1 u3))))))
  have t4 : p 1463 = true := (Or.elim (step931 p h) (fun l0 => (False.elim (bool_contra u0 l0))) (fun r0 => r0))
  have t5 : p 2 = true := (Or.elim (step934 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u0 l1))) (fun r1 => (False.elim (bool_contra r1 t3))))))
  have t6 : p 1472 = false := (Or.elim (step957 p h) (fun l0 => (False.elim (bool_contra t4 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u3))))))
  have t7 : p 15 = false := (Or.elim (step34 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t5 l1))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra u5 r2))))))))
  have t8 : p 1469 = false := (Or.elim (step946 p h) (fun l0 => (False.elim (bool_contra u6 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t6))))))
  have t9 : p 16 = false := (Or.elim (step63 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u4))) (fun r1 => (False.elim (bool_contra r1 t7))))))
  have t10 : p 12 = true := (Or.elim (step941 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u1))) (fun r1 => (False.elim (bool_contra r1 t8))))))
  exact (Or.elim (step53 p h) (fun l0 => (bool_contra t10 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (bool_contra r1 t9)))))

theorem step1659 (p : Nat → Bool) (h : Constraints p) : p 13 = true ∨ p 7 = false ∨ p 1466 = false ∨ p 1477 = true ∨ p 138 = true ∨ p 26 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 13 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 7 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1466 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 1477 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 138 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 26 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl))))))
  have t0 : p 134 = false := (step666 p h)
  have t1 : p 1461 = false := (Or.elim (step1658 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u0))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u1 l2))) (fun r2 => (Or.elim r2 (fun l3 => (False.elim (bool_contra l3 u3))) (fun r3 => (Or.elim r3 (fun l4 => (False.elim (bool_contra l4 u4))) (fun r4 => (Or.elim r4 (fun l5 => (False.elim (bool_contra u5 l5))) (fun r5 => (False.elim (bool_contra u2 r5))))))))))))))
  have t2 : p 6 = true := (Or.elim (step928 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t1))))
  have t3 : p 15 = false := (Or.elim (step37 p h) (fun l0 => (False.elim (bool_contra u1 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t2 l1))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra u5 r2))))))))
  have t4 : p 2 = false := (Or.elim (step32 p h) (fun l0 => (False.elim (bool_contra u1 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t2 l2))) (fun r2 => (False.elim (bool_contra u5 r2))))))))
  have t5 : p 16 = false := (Or.elim (step63 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u4))) (fun r1 => (False.elim (bool_contra r1 t3))))))
  have t6 : p 1463 = true := (Or.elim (step933 p h) (fun l0 => (False.elim (bool_contra l0 t4))) (fun r0 => r0))
  have t7 : p 12 = false := (Or.elim (step53 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => (False.elim (bool_contra r1 t5))))))
  have t8 : p 1472 = false := (Or.elim (step957 p h) (fun l0 => (False.elim (bool_contra t6 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u3))))))
  have t9 : p 1469 = true := (Or.elim (step941 p h) (fun l0 => (False.elim (bool_contra l0 t7))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u0))) (fun r1 => r1))))
  exact (Or.elim (step946 p h) (fun l0 => (bool_contra u2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t9 l1)) (fun r1 => (bool_contra r1 t8)))))

theorem step1660 (p : Nat → Bool) (h : Constraints p) : p 3 = true ∨ p 8 = false ∨ p 1 = false ∨ p 6 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 3 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 8 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 6 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 130 = false := (step664 p h)
  have t1 : p 5 = true := (Or.elim (step44 p h) (fun l0 => (False.elim (bool_contra u1 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra l2 u0))) (fun r2 => r2))))))
  have t2 : p 9 = true := (Or.elim (step43 p h) (fun l0 => (False.elim (bool_contra u1 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra l2 u0))) (fun r2 => r2))))))
  exact (Or.elim (step26 p h) (fun l0 => (bool_contra u3 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u2 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t1 l2)) (fun r2 => (bool_contra t2 r2)))))))

theorem step1661 (p : Nat → Bool) (h : Constraints p) : p 1524 = true ∨ p 151 = true ∨ p 21 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1524 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 151 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 21 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 153 = false := (step676 p h)
  have t1 : p 1522 = false := (Or.elim (step1039 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t2 : p 1520 = false := (Or.elim (step1041 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t3 : p 94 = true := (Or.elim (step1638 p h) (fun l0 => (False.elim (bool_contra l0 u0))) (fun r0 => r0))
  have t4 : p 34 = true := (Or.elim (step1037 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t1))))
  have t5 : p 33 = true := (Or.elim (step1033 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t2))))
  have t6 : p 31 = true := (Or.elim (step1034 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t2))))
  have t7 : p 30 = false := (Or.elim (step109 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t6 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t5 l2))) (fun r2 => (False.elim (bool_contra t4 r2))))))))
  have t8 : p 29 = true := (Or.elim (step113 p h) (fun l0 => (False.elim (bool_contra t6 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra r2 t7))))))))
  have t9 : p 93 = false := (Or.elim (step1515 p h) (fun l0 => (False.elim (bool_contra t8 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t6 l1))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra t3 r2))))))))
  exact (Or.elim (step108 p h) (fun l0 => (bool_contra t8 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 u1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u2)) (fun r2 => (bool_contra r2 t9)))))))

theorem step1662 (p : Nat → Bool) (h : Constraints p) : p 1645 = false ∨ p 1659 = true ∨ p 1611 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1645 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 1659 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1611 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 74 = true := (step1548 p h)
  have t1 : p 76 = true := (step289 p h)
  have t2 : p 1623 = true := (Or.elim (step1218 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => r0))
  have t3 : p 1650 = false := (Or.elim (step1283 p h) (fun l0 => (False.elim (bool_contra t2 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u1))))))
  have t4 : p 1649 = true := (Or.elim (step1259 p h) (fun l0 => (False.elim (bool_contra u0 l0))) (fun r0 => r0))
  have t5 : p 1635 = false := (Or.elim (step1263 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u0 l1))) (fun r1 => (False.elim (bool_contra r1 t3))))))
  have t6 : p 1624 = false := (Or.elim (step1288 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t4 l1))) (fun r1 => (False.elim (bool_contra r1 u1))))))
  have t7 : p 1631 = false := (Or.elim (step1240 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t5))))
  have t8 : p 1619 = false := (Or.elim (step1219 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t6))))))
  have t9 : p 77 = true := (Or.elim (step1234 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t7))))
  have t10 : p 1617 = false := (Or.elim (step1207 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t8))))
  have t11 : p 72 = false := (Or.elim (step278 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t1 l2))) (fun r2 => (False.elim (bool_contra t9 r2))))))))
  exact (Or.elim (step1205 p h) (fun l0 => (bool_contra l0 t11)) (fun r0 => (bool_contra r0 t10)))

theorem step1663 (p : Nat → Bool) (h : Constraints p) : p 1645 = true ∨ p 91 = true ∨ p 85 = true ∨ p 86 = false ∨ p 88 = true ∨ p 57 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1645 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 91 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 85 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 86 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 88 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 57 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl))))))
  have t0 : p 212 = false := (step706 p h)
  have t1 : p 1639 = true := (Or.elim (step1243 p h) (fun l0 => (False.elim (bool_contra l0 u2))) (fun r0 => r0))
  have t2 : p 1641 = true := (Or.elim (step1247 p h) (fun l0 => (False.elim (bool_contra l0 u4))) (fun r0 => r0))
  have t3 : p 1642 = false := (Or.elim (step1253 p h) (fun l0 => (False.elim (bool_contra t1 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t4 : p 1640 = false := (Or.elim (step1255 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t2 l1))) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t5 : p 90 = true := (Or.elim (step1248 p h) (fun l0 => (False.elim (bool_contra l0 u4))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t3))))))
  have t6 : p 84 = true := (Or.elim (step1245 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u2))) (fun r1 => (False.elim (bool_contra r1 t4))))))
  have t7 : p 83 = true := (Or.elim (step445 p h) (fun l0 => (False.elim (bool_contra t5 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra r2 u1))))))))
  exact (Or.elim (step345 p h) (fun l0 => (bool_contra t6 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u5 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t7 l2)) (fun r2 => (bool_contra u3 r2)))))))

theorem step1664 (p : Nat → Bool) (h : Constraints p) : p 1677 = false ∨ p 1724 = true ∨ p 1679 = false ∨ p 98 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1677 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 1724 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1679 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 98 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 1711 = true := (step1586 p h)
  have t1 : p 231 = false := (step715 p h)
  have t2 : p 1691 = false := (Or.elim (step1434 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t0 l1))) (fun r1 => (False.elim (bool_contra r1 u1))))))
  have t3 : p 1683 = true := (Or.elim (step1335 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => r0))
  have t4 : p 1690 = true := (Or.elim (step1356 p h) (fun l0 => (False.elim (bool_contra u0 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t3 l1))) (fun r1 => r1))))
  have t5 : p 1684 = false := (Or.elim (step1357 p h) (fun l0 => (False.elim (bool_contra u0 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t2))))))
  have t6 : p 1712 = false := (Or.elim (step1429 p h) (fun l0 => (False.elim (bool_contra t4 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u1))))))
  have t7 : p 1681 = false := (Or.elim (step1336 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t5))))))
  have t8 : p 1699 = false := (Or.elim (step1643 p h) (fun l0 => (False.elim (bool_contra l0 t6))) (fun r0 => r0))
  have t9 : p 105 = true := (Or.elim (step1330 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t7))))
  have t10 : p 104 = true := (Or.elim (step1331 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t7))))
  have t11 : p 1697 = false := (Or.elim (step1370 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t8))))
  have t12 : p 1695 = false := (Or.elim (step1372 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t8))))
  have t13 : p 113 = true := (Or.elim (step1367 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t11))))
  have t14 : p 109 = true := (Or.elim (step1365 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t12))))
  have t15 : p 103 = false := (Or.elim (step545 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t10 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t9 l2))) (fun r2 => (False.elim (bool_contra t13 r2))))))))
  have t16 : p 118 = true := (Or.elim (step593 p h) (fun l0 => (False.elim (bool_contra t14 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra l2 t15))) (fun r2 => r2))))))
  exact (Or.elim (step642 p h) (fun l0 => (bool_contra t16 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u3 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t14 l2)) (fun r2 => (bool_contra t13 r2)))))))

theorem step1665 (p : Nat → Bool) (h : Constraints p) : p 1699 = true ∨ p 1682 = true ∨ p 98 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1699 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1682 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 98 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 231 = false := (step715 p h)
  have t1 : p 1697 = false := (Or.elim (step1370 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t2 : p 1695 = false := (Or.elim (step1372 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t3 : p 113 = true := (Or.elim (step1367 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t1))))
  have t4 : p 109 = true := (Or.elim (step1365 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t2))))
  have t5 : p 118 = false := (Or.elim (step642 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u2 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t4 l2))) (fun r2 => (False.elim (bool_contra t3 r2))))))))
  have t6 : p 103 = true := (Or.elim (step593 p h) (fun l0 => (False.elim (bool_contra t4 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra r2 t5))))))))
  have t7 : p 105 = false := (Or.elim (step547 p h) (fun l0 => (False.elim (bool_contra t6 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t4 l2))) (fun r2 => (False.elim (bool_contra t3 r2))))))))
  have t8 : p 104 = false := (Or.elim (step546 p h) (fun l0 => (False.elim (bool_contra t6 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t4 l2))) (fun r2 => (False.elim (bool_contra t3 r2))))))))
  exact (Or.elim (step1332 p h) (fun l0 => (bool_contra l0 t8)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t7)) (fun r1 => (bool_contra r1 u1)))))

theorem step1666 (p : Nat → Bool) (h : Constraints p) : p 1624 = true ∨ p 103 = true ∨ p 1636 = true ∨ p 1607 = false ∨ p 1611 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1624 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 103 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1636 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 1607 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 1611 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr hl)))))
  have t0 : p 74 = true := (step1548 p h)
  have t1 : p 76 = true := (step289 p h)
  have t2 : p 194 = false := (step698 p h)
  have t3 : p 1612 = false := (Or.elim (step1223 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t4 : p 1619 = false := (Or.elim (step1219 p h) (fun l0 => (False.elim (bool_contra u4 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t5 : p 1609 = false := (Or.elim (step1196 p h) (fun l0 => (False.elim (bool_contra u3 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t3))))))
  have t6 : p 1617 = false := (Or.elim (step1207 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t4))))
  have t7 : p 64 = true := (Or.elim (step1191 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t5))))
  have t8 : p 72 = true := (Or.elim (step1205 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t6))))
  have t9 : p 77 = false := (Or.elim (step278 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t8 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t1 l2))) (fun r2 => r2))))))
  have t10 : p 55 = true := (Or.elim (step271 p h) (fun l0 => (False.elim (bool_contra t8 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t2))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra r2 u1))))))))
  have t11 : p 1631 = true := (Or.elim (step1234 p h) (fun l0 => (False.elim (bool_contra l0 t9))) (fun r0 => r0))
  have t12 : p 80 = false := (Or.elim (step191 p h) (fun l0 => (False.elim (bool_contra t10 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t7 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t8 l2))) (fun r2 => r2))))))
  have t13 : p 1633 = false := (Or.elim (step1241 p h) (fun l0 => (False.elim (bool_contra t11 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u2))))))
  exact (Or.elim (step1235 p h) (fun l0 => (bool_contra l0 t12)) (fun r0 => (bool_contra r0 t13)))

theorem step1667 (p : Nat → Bool) (h : Constraints p) : p 119 = true ∨ p 109 = true ∨ p 88 = false ∨ p 92 = false ∨ p 1706 = true ∨ p 1703 = false ∨ p 1714 = true ∨ p 106 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 119 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 109 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 88 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 92 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 1706 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 1703 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))
  have u6 : p 1714 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))))
  have u7 : p 106 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl))))))))
  have t0 : p 232 = false := (step716 p h)
  have t1 : p 1705 = true := (Or.elim (step1382 p h) (fun l0 => (False.elim (bool_contra l0 u0))) (fun r0 => r0))
  have t2 : p 122 = true := (Or.elim (step1383 p h) (fun l0 => (False.elim (bool_contra l0 u0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u4))))))
  have t3 : p 1708 = true := (Or.elim (step1387 p h) (fun l0 => (False.elim (bool_contra u5 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t1 l1))) (fun r1 => r1))))
  have t4 : p 1700 = false := (Or.elim (step1403 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t3 l1))) (fun r1 => (False.elim (bool_contra r1 u6))))))
  have t5 : p 1696 = false := (Or.elim (step1375 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t4))))
  have t6 : p 110 = true := (Or.elim (step1366 p h) (fun l0 => (False.elim (bool_contra l0 u1))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t5))))))
  have t7 : p 89 = false := (Or.elim (step441 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u2 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u3 l2))) (fun r2 => (False.elim (bool_contra t6 r2))))))))
  have t8 : p 112 = true := (Or.elim (step598 p h) (fun l0 => (False.elim (bool_contra t6 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra l2 t7))) (fun r2 => (Or.elim r2 (fun l3 => (False.elim (bool_contra l3 u7))) (fun r3 => r3))))))))
  exact (Or.elim (step607 p h) (fun l0 => (bool_contra t8 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u3 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t6 l2)) (fun r2 => (bool_contra t2 r2)))))))

end Dfs112FirstBoolean
