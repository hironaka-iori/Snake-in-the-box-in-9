import Dfs112FirstBooleanPart0002
namespace Dfs112FirstBoolean
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem step1668 (p : Nat → Bool) (h : Constraints p) : p 110 = false ∨ p 111 = false ∨ p 106 = true ∨ p 89 = true ∨ p 92 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 110 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 111 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 106 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 89 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 92 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr hl)))))
  have t0 : p 232 = false := (step716 p h)
  have t1 : p 112 = true := (Or.elim (step598 p h) (fun l0 => (False.elim (bool_contra u0 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra l2 u3))) (fun r2 => (Or.elim r2 (fun l3 => (False.elim (bool_contra l3 u2))) (fun r3 => r3))))))))
  exact (Or.elim (step606 p h) (fun l0 => (bool_contra t1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u4 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra u0 l2)) (fun r2 => (bool_contra u1 r2)))))))

theorem step1669 (p : Nat → Bool) (h : Constraints p) : p 1696 = false ∨ p 1705 = false ∨ p 1714 = true ∨ p 106 = true ∨ p 104 = false ∨ p 105 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1696 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 1705 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1714 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 106 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 104 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 105 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl))))))
  have t0 : p 1707 = true := (Or.elim (step1384 p h) (fun l0 => (False.elim (bool_contra u1 l0))) (fun r0 => r0))
  have t1 : p 1701 = false := (Or.elim (step1407 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t0 l1))) (fun r1 => (False.elim (bool_contra r1 u2))))))
  have t2 : p 1700 = true := (Or.elim (step1375 p h) (fun l0 => (False.elim (bool_contra u0 l0))) (fun r0 => r0))
  have t3 : p 1697 = false := (Or.elim (step1376 p h) (fun l0 => (False.elim (bool_contra u0 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t1))))))
  have t4 : p 1708 = false := (Or.elim (step1403 p h) (fun l0 => (False.elim (bool_contra t2 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u2))))))
  have t5 : p 113 = true := (Or.elim (step1367 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t3))))
  have t6 : p 1703 = false := (Or.elim (step1387 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u1 l1))) (fun r1 => (False.elim (bool_contra r1 t4))))))
  exact (Or.elim (step1589 p h) (fun l0 => (bool_contra l0 t6)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 u3)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra u4 l2)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra u5 l3)) (fun r3 => (bool_contra t5 r3)))))))))

theorem step1670 (p : Nat → Bool) (h : Constraints p) : p 1705 = false ∨ p 1714 = true ∨ p 106 = true ∨ p 89 = true ∨ p 109 = true ∨ p 92 = false ∨ p 104 = false ∨ p 105 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1705 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 1714 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 106 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 89 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 109 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 92 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))
  have u6 : p 104 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))))
  have u7 : p 105 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl))))))))
  have t0 : p 1695 = true := (Or.elim (step1365 p h) (fun l0 => (False.elim (bool_contra l0 u4))) (fun r0 => r0))
  have t1 : p 1707 = true := (Or.elim (step1384 p h) (fun l0 => (False.elim (bool_contra u0 l0))) (fun r0 => r0))
  have t2 : p 1701 = false := (Or.elim (step1407 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t1 l1))) (fun r1 => (False.elim (bool_contra r1 u1))))))
  have t3 : p 1698 = false := (Or.elim (step1374 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t2))))))
  have t4 : p 1696 = false := (Or.elim (step1669 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u0 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra l2 u1))) (fun r2 => (Or.elim r2 (fun l3 => (False.elim (bool_contra l3 u2))) (fun r3 => (Or.elim r3 (fun l4 => (False.elim (bool_contra u6 l4))) (fun r4 => (False.elim (bool_contra u7 r4))))))))))))
  have t5 : p 110 = true := (Or.elim (step1366 p h) (fun l0 => (False.elim (bool_contra l0 u4))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t4))))))
  have t6 : p 111 = false := (Or.elim (step1668 p h) (fun l0 => (False.elim (bool_contra t5 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra l2 u2))) (fun r2 => (Or.elim r2 (fun l3 => (False.elim (bool_contra l3 u3))) (fun r3 => (False.elim (bool_contra u5 r3))))))))))
  have t7 : p 1697 = true := (Or.elim (step1368 p h) (fun l0 => (False.elim (bool_contra l0 t6))) (fun r0 => r0))
  have t8 : p 113 = true := (Or.elim (step1369 p h) (fun l0 => (False.elim (bool_contra l0 t6))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t3))))))
  have t9 : p 1700 = true := (Or.elim (step1373 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t7 l1))) (fun r1 => r1))))
  have t10 : p 1703 = true := (Or.elim (step1589 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u2))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u6 l2))) (fun r2 => (Or.elim r2 (fun l3 => (False.elim (bool_contra u7 l3))) (fun r3 => (False.elim (bool_contra t8 r3))))))))))
  have t11 : p 1708 = false := (Or.elim (step1403 p h) (fun l0 => (False.elim (bool_contra t9 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u1))))))
  exact (Or.elim (step1387 p h) (fun l0 => (bool_contra t10 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u0 l1)) (fun r1 => (bool_contra r1 t11)))))

theorem step1671 (p : Nat → Bool) (h : Constraints p) : p 1705 = true ∨ p 118 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1705 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 118 = false := bool_false_of_not_true (fun hl => hc (Or.inr hl))
  have t0 : p 122 = true := (Or.elim (step1381 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t1 : p 119 = true := (Or.elim (step1382 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  exact (Or.elim (step1615 p h) (fun l0 => (bool_contra l0 u1)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t1 l1)) (fun r1 => (bool_contra t0 r1)))))

theorem step1672 (p : Nat → Bool) (h : Constraints p) : p 110 = false ∨ p 89 = true ∨ p 92 = false ∨ p 106 = true ∨ p 122 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 110 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 89 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 92 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 106 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 122 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr hl)))))
  have t0 : p 232 = false := (step716 p h)
  have t1 : p 112 = true := (Or.elim (step598 p h) (fun l0 => (False.elim (bool_contra u0 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra l2 u1))) (fun r2 => (Or.elim r2 (fun l3 => (False.elim (bool_contra l3 u3))) (fun r3 => r3))))))))
  exact (Or.elim (step607 p h) (fun l0 => (bool_contra t1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u2 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra u0 l2)) (fun r2 => (bool_contra u4 r2)))))))

theorem step1673 (p : Nat → Bool) (h : Constraints p) : p 87 = true ∨ p 1679 = true ∨ p 118 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 87 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1679 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 118 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 220 = false := (step711 p h)
  have t1 : p 98 = true := (Or.elim (step1328 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u1))))
  have t2 : p 101 = true := (Or.elim (step1327 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u1))))
  have t3 : p 100 = true := (Or.elim (step502 p h) (fun l0 => (False.elim (bool_contra t1 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra l2 u0))) (fun r2 => (Or.elim r2 (fun l3 => l3) (fun r3 => (False.elim (bool_contra r3 u2))))))))))
  have t4 : p 99 = true := (Or.elim (step503 p h) (fun l0 => (False.elim (bool_contra t1 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra l2 u0))) (fun r2 => (Or.elim r2 (fun l3 => l3) (fun r3 => (False.elim (bool_contra r3 u2))))))))))
  exact (Or.elim (step1541 p h) (fun l0 => (bool_contra t1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t4 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t3 l2)) (fun r2 => (bool_contra t2 r2)))))))

theorem step1674 (p : Nat → Bool) (h : Constraints p) : p 1494 = true ∨ p 86 = true ∨ p 24 = true ∨ p 92 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1494 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 86 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 24 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 92 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 145 = false := (step672 p h)
  have t1 : p 1489 = true := (Or.elim (step981 p h) (fun l0 => (False.elim (bool_contra l0 u2))) (fun r0 => r0))
  have t2 : p 1490 = false := (Or.elim (step992 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t3 : p 1491 = false := (Or.elim (step990 p h) (fun l0 => (False.elim (bool_contra t1 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t4 : p 23 = true := (Or.elim (step983 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u2))) (fun r1 => (False.elim (bool_contra r1 t2))))))
  have t5 : p 27 = true := (Or.elim (step984 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t3))))
  have t6 : p 28 = true := (Or.elim (step82 p h) (fun l0 => (False.elim (bool_contra t4 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra r2 u1))))))))
  exact (Or.elim (step104 p h) (fun l0 => (bool_contra t6 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t4 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t5 l2)) (fun r2 => (bool_contra u3 r2)))))))

theorem step1675 (p : Nat → Bool) (h : Constraints p) : p 1715 = true ∨ p 1696 = false ∨ p 111 = true ∨ p 98 = false ∨ p 1703 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1715 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1696 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 111 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 98 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 1703 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr hl)))))
  have t0 : p 1697 = true := (Or.elim (step1368 p h) (fun l0 => (False.elim (bool_contra l0 u2))) (fun r0 => r0))
  have t1 : p 1701 = true := (Or.elim (step1376 p h) (fun l0 => (False.elim (bool_contra u1 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t0 l1))) (fun r1 => r1))))
  have t2 : p 1707 = true := (Or.elim (step1386 p h) (fun l0 => (False.elim (bool_contra u4 l0))) (fun r0 => r0))
  have t3 : p 1702 = false := (Or.elim (step1411 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t2 l1))) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t4 : p 1708 = false := (Or.elim (step1408 p h) (fun l0 => (False.elim (bool_contra t1 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t5 : p 1698 = false := (Or.elim (step1377 p h) (fun l0 => (False.elim (bool_contra u1 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t3))))))
  have t6 : p 1705 = false := (Or.elim (step1387 p h) (fun l0 => (False.elim (bool_contra u4 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t4))))))
  have t7 : p 113 = true := (Or.elim (step1369 p h) (fun l0 => (False.elim (bool_contra l0 u2))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t5))))))
  have t8 : p 119 = true := (Or.elim (step1382 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t6))))
  have t9 : p 118 = true := (Or.elim (step1671 p h) (fun l0 => (False.elim (bool_contra l0 t6))) (fun r0 => r0))
  exact (Or.elim (step644 p h) (fun l0 => (bool_contra t9 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u3 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t7 l2)) (fun r2 => (bool_contra t8 r2)))))))

theorem step1676 (p : Nat → Bool) (h : Constraints p) : p 50 = true ∨ p 1563 = true ∨ p 1544 = false ∨ p 122 = false ∨ p 1554 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 50 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1563 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1544 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 122 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 1554 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr hl)))))
  have t0 : p 171 = false := (step686 p h)
  have t1 : p 1556 = true := (Or.elim (step1090 p h) (fun l0 => (False.elim (bool_contra u4 l0))) (fun r0 => r0))
  have t2 : p 1550 = false := (Or.elim (step1113 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t1 l1))) (fun r1 => (False.elim (bool_contra r1 u1))))))
  have t3 : p 1547 = false := (Or.elim (step1080 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t2))))))
  have t4 : p 1546 = true := (Or.elim (step1073 p h) (fun l0 => (False.elim (bool_contra l0 u0))) (fun r0 => r0))
  have t5 : p 49 = true := (Or.elim (step1075 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u0))) (fun r1 => (False.elim (bool_contra r1 t3))))))
  have t6 : p 1549 = true := (Or.elim (step1079 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t4 l1))) (fun r1 => r1))))
  have t7 : p 54 = true := (Or.elim (step165 p h) (fun l0 => (False.elim (bool_contra t5 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => r1))))
  have t8 : p 53 = false := (Or.elim (step180 p h) (fun l0 => (False.elim (bool_contra t7 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t5 l1))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra u3 r2))))))))
  have t9 : p 1557 = false := (Or.elim (step1109 p h) (fun l0 => (False.elim (bool_contra t6 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u1))))))
  have t10 : p 1552 = true := (Or.elim (step1085 p h) (fun l0 => (False.elim (bool_contra l0 t8))) (fun r0 => r0))
  exact (Or.elim (step1093 p h) (fun l0 => (bool_contra t10 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u4 l1)) (fun r1 => (bool_contra r1 t9)))))

theorem step1677 (p : Nat → Bool) (h : Constraints p) : p 62 = false ∨ p 59 = false ∨ p 92 = false ∨ p 56 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 62 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 59 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 92 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 56 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 184 = false := (step693 p h)
  have t1 : p 63 = false := (Or.elim (step237 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u1 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u0 l2))) (fun r2 => (False.elim (bool_contra u2 r2))))))))
  have t2 : p 57 = true := (Or.elim (step234 p h) (fun l0 => (False.elim (bool_contra u0 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra r2 t1))))))))
  exact (Or.elim (step210 p h) (fun l0 => (bool_contra t2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u3 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra u1 l2)) (fun r2 => (bool_contra u0 r2)))))))

theorem step1678 (p : Nat → Bool) (h : Constraints p) : p 1571 = true ∨ p 1536 = false ∨ p 1557 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1571 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1536 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1557 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 1561 = true := (Or.elim (step1099 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => r0))
  have t1 : p 1562 = false := (Or.elim (step1122 p h) (fun l0 => (False.elim (bool_contra u1 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t2 : p 1537 = false := (Or.elim (step1127 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t0 l1))) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t3 : p 1548 = false := (Or.elim (step1104 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u2 l1))) (fun r1 => (False.elim (bool_contra r1 t1))))))
  have t4 : p 1533 = false := (Or.elim (step1059 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t2))))
  have t5 : p 1544 = false := (Or.elim (step1078 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t3))))
  have t6 : p 45 = true := (Or.elim (step1071 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t5))))
  have t7 : p 41 = false := (Or.elim (step1630 p h) (fun l0 => (False.elim (bool_contra l0 t5))) (fun r0 => r0))
  have t8 : p 42 = false := (Or.elim (step1612 p h) (fun l0 => (False.elim (bool_contra t6 l0))) (fun r0 => r0))
  have t9 : p 1528 = true := (Or.elim (step1044 p h) (fun l0 => (False.elim (bool_contra l0 t7))) (fun r0 => r0))
  have t10 : p 1530 = true := (Or.elim (step1048 p h) (fun l0 => (False.elim (bool_contra l0 t8))) (fun r0 => r0))
  exact (Or.elim (step1053 p h) (fun l0 => (bool_contra t9 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t10 l1)) (fun r1 => (bool_contra r1 t4)))))

theorem step1679 (p : Nat → Bool) (h : Constraints p) : p 1620 = true ∨ p 73 = true ∨ p 78 = false ∨ p 62 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1620 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 73 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 78 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 62 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 74 = true := (step1548 p h)
  have t1 : p 76 = true := (step289 p h)
  have t2 : p 191 = false := (step697 p h)
  have t3 : p 420 = false := (step1552 p h)
  have t4 : p 1617 = true := (Or.elim (step1204 p h) (fun l0 => (False.elim (bool_contra l0 u1))) (fun r0 => r0))
  have t5 : p 1618 = false := (Or.elim (step1208 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t6 : p 1615 = false := (Or.elim (step1210 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t4 l1))) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t7 : p 72 = true := (Or.elim (step1206 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u1))) (fun r1 => (False.elim (bool_contra r1 t5))))))
  have t8 : p 69 = true := (Or.elim (step1201 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t6))))
  have t9 : p 77 = false := (Or.elim (step278 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t7 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t1 l2))) (fun r2 => r2))))))
  have t10 : p 70 = true := (Or.elim (step263 p h) (fun l0 => (False.elim (bool_contra t8 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t2))) (fun r1 => r1))))
  have t11 : p 200 = true := (Or.elim (step295 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t9))))))
  have t12 : p 192 = true := (Or.elim (step266 p h) (fun l0 => (False.elim (bool_contra t10 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u3))))))
  have t13 : p 391 = true := (Or.elim (step846 p h) (fun l0 => (False.elim (bool_contra t11 l0))) (fun r0 => r0))
  have t14 : p 377 = true := (Or.elim (step831 p h) (fun l0 => (False.elim (bool_contra t12 l0))) (fun r0 => r0))
  have t15 : p 393 = true := (Or.elim (step847 p h) (fun l0 => (False.elim (bool_contra t13 l0))) (fun r0 => r0))
  have t16 : p 379 = true := (Or.elim (step833 p h) (fun l0 => (False.elim (bool_contra t14 l0))) (fun r0 => r0))
  have t17 : p 401 = true := (Or.elim (step854 p h) (fun l0 => (False.elim (bool_contra t15 l0))) (fun r0 => r0))
  have t18 : p 387 = true := (Or.elim (step839 p h) (fun l0 => (False.elim (bool_contra t16 l0))) (fun r0 => r0))
  have t19 : p 417 = true := (Or.elim (step865 p h) (fun l0 => (False.elim (bool_contra t17 l0))) (fun r0 => r0))
  have t20 : p 389 = true := (Or.elim (step842 p h) (fun l0 => (False.elim (bool_contra t18 l0))) (fun r0 => r0))
  exact (Or.elim (step871 p h) (fun l0 => (bool_contra t20 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t19 l1)) (fun r1 => (bool_contra r1 t3)))))

theorem step1680 (p : Nat → Bool) (h : Constraints p) : p 1673 = true ∨ p 1639 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1673 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1639 = false := bool_false_of_not_true (fun hl => hc (Or.inr hl))
  have t0 : p 217 = false := (step709 p h)
  have t1 : p 84 = true := (Or.elim (step1244 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u1))))
  have t2 : p 85 = true := (Or.elim (step1243 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u1))))
  have t3 : p 97 = true := (Or.elim (step1316 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t4 : p 95 = true := (Or.elim (step1317 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t5 : p 96 = false := (Or.elim (step492 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t1 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t4 l2))) (fun r2 => (False.elim (bool_contra t3 r2))))))))
  have t6 : p 83 = false := (Or.elim (step341 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t1 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t2 l2))) (fun r2 => (False.elim (bool_contra t4 r2))))))))
  exact (Or.elim (step487 p h) (fun l0 => (bool_contra t4 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 t6)) (fun r2 => (bool_contra r2 t5)))))))

theorem step1681 (p : Nat → Bool) (h : Constraints p) : p 95 = false ∨ p 1639 = true ∨ p 93 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 95 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 1639 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 93 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 217 = false := (step709 p h)
  have t1 : p 84 = true := (Or.elim (step1244 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u1))))
  have t2 : p 85 = true := (Or.elim (step1243 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u1))))
  have t3 : p 83 = false := (Or.elim (step341 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t1 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t2 l2))) (fun r2 => (False.elim (bool_contra u0 r2))))))))
  have t4 : p 96 = true := (Or.elim (step487 p h) (fun l0 => (False.elim (bool_contra u0 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra l2 t3))) (fun r2 => r2))))))
  exact (Or.elim (step490 p h) (fun l0 => (bool_contra t4 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t1 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra u2 l2)) (fun r2 => (bool_contra u0 r2)))))))

theorem step1682 (p : Nat → Bool) (h : Constraints p) : p 19 = false ∨ p 73 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 19 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 73 = true := bool_true_of_not_false (fun hl => hc (Or.inr hl))
  have t0 : p 141 = false := (step670 p h)
  have t1 : p 75 = true := (Or.elim (step71 p h) (fun l0 => (False.elim (bool_contra u0 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => r1))))
  have t2 : p 17 = true := (Or.elim (step72 p h) (fun l0 => (False.elim (bool_contra u0 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => r1))))
  exact (Or.elim (step1509 p h) (fun l0 => (bool_contra t2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u0 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra u1 l2)) (fun r2 => (bool_contra t1 r2)))))))

theorem step1683 (p : Nat → Bool) (h : Constraints p) : p 72 = false ∨ p 1636 = true ∨ p 55 = false ∨ p 64 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 72 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 1636 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 55 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 64 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 74 = true := (step1548 p h)
  have t1 : p 76 = true := (step289 p h)
  have t2 : p 77 = false := (Or.elim (step278 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u0 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t1 l2))) (fun r2 => r2))))))
  have t3 : p 80 = false := (Or.elim (step191 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u3 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u0 l2))) (fun r2 => r2))))))
  have t4 : p 1631 = true := (Or.elim (step1234 p h) (fun l0 => (False.elim (bool_contra l0 t2))) (fun r0 => r0))
  have t5 : p 1633 = true := (Or.elim (step1235 p h) (fun l0 => (False.elim (bool_contra l0 t3))) (fun r0 => r0))
  exact (Or.elim (step1241 p h) (fun l0 => (bool_contra t4 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t5 l1)) (fun r1 => (bool_contra r1 u1)))))

theorem step1684 (p : Nat → Bool) (h : Constraints p) : p 56 = false ∨ p 62 = false ∨ p 65 = true ∨ p 93 = false ∨ p 84 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 56 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 62 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 65 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 93 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 84 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr hl)))))
  have t0 : p 178 = false := (step689 p h)
  have t1 : p 81 = false := (Or.elim (step322 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u0 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u4 l2))) (fun r2 => (False.elim (bool_contra u3 r2))))))))
  have t2 : p 57 = true := (Or.elim (step200 p h) (fun l0 => (False.elim (bool_contra u0 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (Or.elim r2 (fun l3 => (False.elim (bool_contra l3 u2))) (fun r3 => (False.elim (bool_contra r3 t1))))))))))
  exact (Or.elim (step212 p h) (fun l0 => (bool_contra t2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u0 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra u1 l2)) (fun r2 => (bool_contra u4 r2)))))))

theorem step1685 (p : Nat → Bool) (h : Constraints p) : p 1493 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1493 = false := bool_false_of_not_true (fun hl => hc hl)
  have t0 : p 1491 = false := (Or.elim (step987 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t1 : p 1489 = false := (Or.elim (step989 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t2 : p 28 = true := (Or.elim (step1655 p h) (fun l0 => (False.elim (bool_contra l0 u0))) (fun r0 => r0))
  have t3 : p 27 = true := (Or.elim (step984 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t0))))
  have t4 : p 26 = true := (Or.elim (step985 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t0))))
  have t5 : p 23 = true := (Or.elim (step982 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t1))))
  exact (Or.elim (step102 p h) (fun l0 => (bool_contra t2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t5 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t4 l2)) (fun r2 => (bool_contra t3 r2)))))))

theorem step1686 (p : Nat → Bool) (h : Constraints p) : p 5 = true ∨ p 1481 = true ∨ p 1 = false ∨ p 6 = false ∨ p 7 = true ∨ p 1471 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 5 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1481 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 6 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 7 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 1471 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl))))))
  have t0 : p 137 = false := (step668 p h)
  have t1 : p 135 = false := (step667 p h)
  have t2 : p 15 = true := (Or.elim (step968 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u1))))
  have t3 : p 14 = true := (Or.elim (step62 p h) (fun l0 => (False.elim (bool_contra t2 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra l2 u4))) (fun r2 => r2))))))
  have t4 : p 18 = true := (Or.elim (step967 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u1))))
  have t5 : p 13 = false := (Or.elim (step56 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t1))) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t6 : p 8 = true := (Or.elim (step1608 p h) (fun l0 => (False.elim (bool_contra l0 u0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t3 l2))) (fun r2 => (Or.elim r2 (fun l3 => (False.elim (bool_contra l3 u4))) (fun r3 => (False.elim (bool_contra u3 r3))))))))))
  have t7 : p 1468 = true := (Or.elim (step939 p h) (fun l0 => (False.elim (bool_contra l0 t5))) (fun r0 => r0))
  have t8 : p 3 = true := (Or.elim (step1660 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t6 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u2 l2))) (fun r2 => (False.elim (bool_contra u3 r2))))))))
  have t9 : p 1466 = false := (Or.elim (step945 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t7 l1))) (fun r1 => (False.elim (bool_contra r1 u5))))))
  have t10 : p 10 = false := (Or.elim (step9 p h) (fun l0 => (False.elim (bool_contra t8 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t6 l1))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra t4 r2))))))))
  exact (Or.elim (step936 p h) (fun l0 => (bool_contra l0 t10)) (fun r0 => (bool_contra r0 t9)))

theorem step1687 (p : Nat → Bool) (h : Constraints p) : p 301 = true ∨ p 16 = false ∨ p 13 = true ∨ p 7 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 301 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 16 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 13 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 7 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 137 = false := (step668 p h)
  have t1 : p 299 = false := (Or.elim (step768 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t2 : p 271 = false := (Or.elim (step769 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t3 : p 283 = false := (Or.elim (step767 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t1))))
  have t4 : p 269 = false := (Or.elim (step743 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t2))))
  have t5 : p 275 = false := (Or.elim (step756 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t3))))
  have t6 : p 267 = false := (Or.elim (step740 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t4))))
  have t7 : p 138 = false := (Or.elim (step750 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t5))))
  have t8 : p 265 = false := (Or.elim (step739 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t6))))
  have t9 : p 15 = true := (Or.elim (step63 p h) (fun l0 => (False.elim (bool_contra u1 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t7))) (fun r1 => r1))))
  have t10 : p 136 = false := (Or.elim (step738 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t8))))
  have t11 : p 14 = true := (Or.elim (step62 p h) (fun l0 => (False.elim (bool_contra t9 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra l2 u3))) (fun r2 => r2))))))
  exact (Or.elim (step58 p h) (fun l0 => (bool_contra t11 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t10)) (fun r1 => (bool_contra r1 u2)))))

theorem step1688 (p : Nat → Bool) (h : Constraints p) : p 77 = true ∨ p 1637 = true ∨ p 80 = true ∨ p 200 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 77 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1637 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 80 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 200 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 201 = false := (step701 p h)
  have t1 : p 1631 = true := (Or.elim (step1234 p h) (fun l0 => (False.elim (bool_contra l0 u0))) (fun r0 => r0))
  have t2 : p 78 = false := (Or.elim (step295 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u3))) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t3 : p 1634 = false := (Or.elim (step1242 p h) (fun l0 => (False.elim (bool_contra t1 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u1))))))
  have t4 : p 79 = false := (Or.elim (step296 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => (False.elim (bool_contra r1 t2))))))
  exact (Or.elim (step1237 p h) (fun l0 => (bool_contra l0 t4)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 u2)) (fun r1 => (bool_contra r1 t3)))))

theorem step1689 (p : Nat → Bool) (h : Constraints p) : p 1624 = true ∨ p 1617 = false ∨ p 58 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1624 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1617 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 58 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 190 = false := (step696 p h)
  have t1 : p 1619 = true := (Or.elim (step1207 p h) (fun l0 => (False.elim (bool_contra u1 l0))) (fun r0 => r0))
  have t2 : p 1620 = false := (Or.elim (step1215 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t3 : p 1611 = false := (Or.elim (step1219 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t1 l1))) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t4 : p 1615 = false := (Or.elim (step1210 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u1 l1))) (fun r1 => (False.elim (bool_contra r1 t2))))))
  have t5 : p 1609 = false := (Or.elim (step1193 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t3))))
  have t6 : p 68 = true := (Or.elim (step1202 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t4))))
  have t7 : p 67 = true := (Or.elim (step1190 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t5))))
  have t8 : p 64 = true := (Or.elim (step1191 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t5))))
  have t9 : p 66 = true := (Or.elim (step261 p h) (fun l0 => (False.elim (bool_contra t6 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra l2 u2))) (fun r2 => r2))))))
  exact (Or.elim (step251 p h) (fun l0 => (bool_contra t9 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t8 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t7 l2)) (fun r2 => (bool_contra t6 r2)))))))

theorem step1690 (p : Nat → Bool) (h : Constraints p) : p 1623 = true ∨ p 58 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1623 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 58 = false := bool_false_of_not_true (fun hl => hc (Or.inr hl))
  have t0 : p 190 = false := (step696 p h)
  have t1 : p 1619 = false := (Or.elim (step1214 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t2 : p 1611 = false := (Or.elim (step1218 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t3 : p 1615 = false := (Or.elim (step1209 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t1))))
  have t4 : p 1609 = false := (Or.elim (step1193 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t2))))
  have t5 : p 68 = true := (Or.elim (step1202 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t3))))
  have t6 : p 67 = true := (Or.elim (step1190 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t4))))
  have t7 : p 64 = true := (Or.elim (step1191 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t4))))
  have t8 : p 66 = true := (Or.elim (step261 p h) (fun l0 => (False.elim (bool_contra t5 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra l2 u1))) (fun r2 => r2))))))
  exact (Or.elim (step251 p h) (fun l0 => (bool_contra t8 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t7 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t6 l2)) (fun r2 => (bool_contra t5 r2)))))))

theorem step1691 (p : Nat → Bool) (h : Constraints p) : p 1468 = true ∨ p 15 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1468 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 15 = false := bool_false_of_not_true (fun hl => hc (Or.inr hl))
  have t0 : p 135 = false := (step667 p h)
  have t1 : p 134 = false := (step666 p h)
  have t2 : p 302 = false := (step1554 p h)
  have t3 : p 13 = true := (Or.elim (step939 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t4 : p 12 = true := (Or.elim (step940 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t5 : p 14 = true := (Or.elim (step55 p h) (fun l0 => (False.elim (bool_contra t3 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => r1))))
  have t6 : p 16 = true := (Or.elim (step53 p h) (fun l0 => (False.elim (bool_contra t4 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t1))) (fun r1 => r1))))
  have t7 : p 136 = true := (Or.elim (step57 p h) (fun l0 => (False.elim (bool_contra t5 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u1))))))
  have t8 : p 138 = true := (Or.elim (step63 p h) (fun l0 => (False.elim (bool_contra t6 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u1))))))
  have t9 : p 265 = true := (Or.elim (step738 p h) (fun l0 => (False.elim (bool_contra t7 l0))) (fun r0 => r0))
  have t10 : p 275 = true := (Or.elim (step750 p h) (fun l0 => (False.elim (bool_contra t8 l0))) (fun r0 => r0))
  have t11 : p 267 = true := (Or.elim (step739 p h) (fun l0 => (False.elim (bool_contra t9 l0))) (fun r0 => r0))
  have t12 : p 283 = true := (Or.elim (step756 p h) (fun l0 => (False.elim (bool_contra t10 l0))) (fun r0 => r0))
  have t13 : p 269 = true := (Or.elim (step740 p h) (fun l0 => (False.elim (bool_contra t11 l0))) (fun r0 => r0))
  have t14 : p 299 = true := (Or.elim (step767 p h) (fun l0 => (False.elim (bool_contra t12 l0))) (fun r0 => r0))
  have t15 : p 271 = true := (Or.elim (step743 p h) (fun l0 => (False.elim (bool_contra t13 l0))) (fun r0 => r0))
  exact (Or.elim (step770 p h) (fun l0 => (bool_contra t15 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t14 l1)) (fun r1 => (bool_contra r1 t2)))))

theorem step1692 (p : Nat → Bool) (h : Constraints p) : p 3 = true ∨ p 6 = false ∨ p 8 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 3 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 6 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 8 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 130 = false := (step664 p h)
  have t1 : p 5 = true := (Or.elim (step44 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra l2 u0))) (fun r2 => r2))))))
  have t2 : p 9 = true := (Or.elim (step43 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra l2 u0))) (fun r2 => r2))))))
  exact (Or.elim (step1506 p h) (fun l0 => (bool_contra t1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u1 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra u2 l2)) (fun r2 => (bool_contra t2 r2)))))))

theorem step1693 (p : Nat → Bool) (h : Constraints p) : p 17 = true ∨ p 7 = true ∨ p 2 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 17 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 7 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 2 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 124 = false := (step661 p h)
  exact (Or.elim (step3 p h) (fun l0 => (bool_contra u2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u1)) (fun r2 => (bool_contra r2 u0)))))))

theorem step1694 (p : Nat → Bool) (h : Constraints p) : p 1 = true ∨ p 17 = true ∨ p 2 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 17 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 2 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 124 = false := (step661 p h)
  exact (Or.elim (step4 p h) (fun l0 => (bool_contra u2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u0)) (fun r2 => (bool_contra r2 u1)))))))

theorem step1695 (p : Nat → Bool) (h : Constraints p) : p 1 = true ∨ p 7 = true ∨ p 2 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 7 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 2 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 124 = false := (step661 p h)
  exact (Or.elim (step5 p h) (fun l0 => (bool_contra u2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u0)) (fun r2 => (bool_contra r2 u1)))))))

theorem step1696 (p : Nat → Bool) (h : Constraints p) : p 57 = true ∨ p 11 = true ∨ p 4 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 57 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 11 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 4 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 126 = false := (step662 p h)
  exact (Or.elim (step13 p h) (fun l0 => (bool_contra u2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u1)) (fun r2 => (bool_contra r2 u0)))))))

theorem step1697 (p : Nat → Bool) (h : Constraints p) : p 57 = true ∨ p 3 = true ∨ p 4 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 57 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 3 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 4 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 126 = false := (step662 p h)
  exact (Or.elim (step14 p h) (fun l0 => (bool_contra u2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u1)) (fun r2 => (bool_contra r2 u0)))))))

theorem step1698 (p : Nat → Bool) (h : Constraints p) : p 1 = true ∨ p 7 = true ∨ p 9 = true ∨ p 6 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 7 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 9 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 6 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 128 = false := (step663 p h)
  exact (Or.elim (step28 p h) (fun l0 => (bool_contra u3 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u0)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u1)) (fun r3 => (bool_contra r3 u2)))))))))

theorem step1699 (p : Nat → Bool) (h : Constraints p) : p 9 = true ∨ p 5 = true ∨ p 1 = true ∨ p 6 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 9 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 5 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 6 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 128 = false := (step663 p h)
  exact (Or.elim (step29 p h) (fun l0 => (bool_contra u3 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u2)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u1)) (fun r3 => (bool_contra r3 u0)))))))))

theorem step1700 (p : Nat → Bool) (h : Constraints p) : p 1 = true ∨ p 5 = true ∨ p 7 = true ∨ p 6 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 5 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 7 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 6 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 128 = false := (step663 p h)
  exact (Or.elim (step30 p h) (fun l0 => (bool_contra u3 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u0)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u1)) (fun r3 => (bool_contra r3 u2)))))))))

theorem step1701 (p : Nat → Bool) (h : Constraints p) : p 9 = true ∨ p 5 = true ∨ p 8 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 9 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 5 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 8 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 130 = false := (step664 p h)
  exact (Or.elim (step42 p h) (fun l0 => (bool_contra u2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u1)) (fun r2 => (bool_contra r2 u0)))))))

theorem step1702 (p : Nat → Bool) (h : Constraints p) : p 9 = true ∨ p 3 = true ∨ p 8 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 9 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 3 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 8 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 130 = false := (step664 p h)
  exact (Or.elim (step43 p h) (fun l0 => (bool_contra u2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u1)) (fun r2 => (bool_contra r2 u0)))))))

theorem step1703 (p : Nat → Bool) (h : Constraints p) : p 5 = true ∨ p 3 = true ∨ p 8 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 5 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 3 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 8 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 130 = false := (step664 p h)
  exact (Or.elim (step44 p h) (fun l0 => (bool_contra u2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u1)) (fun r2 => (bool_contra r2 u0)))))))

theorem step1704 (p : Nat → Bool) (h : Constraints p) : p 3 = true ∨ p 32 = true ∨ p 10 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 3 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 32 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 10 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 132 = false := (step665 p h)
  exact (Or.elim (step48 p h) (fun l0 => (bool_contra u2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u0)) (fun r2 => (bool_contra r2 u1)))))))

theorem step1705 (p : Nat → Bool) (h : Constraints p) : p 12 = false ∨ p 16 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 12 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 16 = false := bool_false_of_not_true (fun hl => hc (Or.inr hl))
  have t0 : p 134 = false := (step666 p h)
  exact (Or.elim (step53 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (bool_contra r1 u1)))))

theorem step1706 (p : Nat → Bool) (h : Constraints p) : p 12 = false ∨ p 11 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 12 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 11 = false := bool_false_of_not_true (fun hl => hc (Or.inr hl))
  have t0 : p 134 = false := (step666 p h)
  exact (Or.elim (step54 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (bool_contra r1 u1)))))

theorem step1707 (p : Nat → Bool) (h : Constraints p) : p 13 = false ∨ p 14 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 13 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 14 = false := bool_false_of_not_true (fun hl => hc (Or.inr hl))
  have t0 : p 135 = false := (step667 p h)
  exact (Or.elim (step55 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (bool_contra r1 u1)))))

end Dfs112FirstBoolean
