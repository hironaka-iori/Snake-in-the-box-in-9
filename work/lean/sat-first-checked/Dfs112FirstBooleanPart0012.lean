import Dfs112FirstBooleanPart0011
namespace Dfs112FirstBoolean
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem step2028 (p : Nat → Bool) (h : Constraints p) : p 1713 = true ∨ p 1707 = false ∨ p 94 = true ∨ p 93 = false ∨ p 1695 = false ∨ p 1699 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1713 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1707 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 94 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 93 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 1695 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 1699 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl))))))
  have t0 : p 1700 = false := (Or.elim (step1402 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u1 l1))) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t1 : p 1703 = false := (Or.elim (step2024 p h) (fun l0 => (False.elim (bool_contra l0 u0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra u5 r1))))))
  have t2 : p 1697 = false := (Or.elim (step1373 p h) (fun l0 => (False.elim (bool_contra u4 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t0))))))
  have t3 : p 117 = true := (Or.elim (step1378 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t1))))
  have t4 : p 116 = true := (Or.elim (step1379 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t1))))
  have t5 : p 113 = true := (Or.elim (step1367 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t2))))
  exact (Or.elim (step1625 p h) (fun l0 => (bool_contra t5 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u3 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t3 l2)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra t4 l3)) (fun r3 => (bool_contra r3 u2)))))))))

theorem step2029 (p : Nat → Bool) (h : Constraints p) : p 1703 = true ∨ p 113 = false ∨ p 94 = true ∨ p 93 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1703 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 113 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 94 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 93 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 117 = true := (Or.elim (step1378 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t1 : p 116 = true := (Or.elim (step1379 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  exact (Or.elim (step1625 p h) (fun l0 => (bool_contra u1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u3 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t0 l2)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra t1 l3)) (fun r3 => (bool_contra r3 u2)))))))))

theorem step2030 (p : Nat → Bool) (h : Constraints p) : p 1703 = false ∨ p 118 = false ∨ p 1709 = true ∨ p 1714 = true ∨ p 122 = true ∨ p 98 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1703 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 118 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1709 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 1714 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 122 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 98 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl))))))
  have t0 : p 1705 = true := (Or.elim (step1381 p h) (fun l0 => (False.elim (bool_contra l0 u4))) (fun r0 => r0))
  have t1 : p 1706 = false := (Or.elim (step1388 p h) (fun l0 => (False.elim (bool_contra u0 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u2))))))
  have t2 : p 1708 = true := (Or.elim (step1387 p h) (fun l0 => (False.elim (bool_contra u0 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t0 l1))) (fun r1 => r1))))
  have t3 : p 119 = true := (Or.elim (step1383 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u4))) (fun r1 => (False.elim (bool_contra r1 t1))))))
  have t4 : p 1700 = false := (Or.elim (step1403 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t2 l1))) (fun r1 => (False.elim (bool_contra r1 u3))))))
  exact (Or.elim (step1616 p h) (fun l0 => (bool_contra u5 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t4)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra u1 l2)) (fun r2 => (bool_contra t3 r2)))))))

theorem step2031 (p : Nat → Bool) (h : Constraints p) : p 1703 = true ∨ p 1681 = true ∨ p 94 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1703 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1681 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 94 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 104 = true := (Or.elim (step1331 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u1))))
  have t1 : p 105 = true := (Or.elim (step1330 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u1))))
  have t2 : p 116 = true := (Or.elim (step1379 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t3 : p 106 = true := (Or.elim (step1951 p h) (fun l0 => (False.elim (bool_contra l0 u0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t1 l2))) (fun r2 => (False.elim (bool_contra r2 u2))))))))
  exact (Or.elim (step580 p h) (fun l0 => (bool_contra t3 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t0 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t1 l2)) (fun r2 => (bool_contra t2 r2)))))))

theorem step2032 (p : Nat → Bool) (h : Constraints p) : p 1697 = true ∨ p 104 = false ∨ p 105 = false ∨ p 84 = false ∨ p 93 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1697 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 104 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 105 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 84 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 93 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr hl)))))
  have t0 : p 81 = false := (Or.elim (step328 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u3 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u4 l2))) (fun r2 => (False.elim (bool_contra u1 r2))))))))
  have t1 : p 113 = true := (Or.elim (step1367 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t2 : p 111 = true := (Or.elim (step1368 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t3 : p 103 = false := (Or.elim (step545 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u1 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u2 l2))) (fun r2 => (False.elim (bool_contra t1 r2))))))))
  have t4 : p 114 = false := (Or.elim (step616 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u4 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u1 l2))) (fun r2 => (False.elim (bool_contra t1 r2))))))))
  have t5 : p 107 = false := (Or.elim (step587 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u3 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u1 l2))) (fun r2 => (False.elim (bool_contra t2 r2))))))))
  exact (Or.elim (step1822 p h) (fun l0 => (bool_contra l0 t4)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t5)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 t0)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra u1 l3)) (fun r3 => (bool_contra r3 t3)))))))))

theorem step2033 (p : Nat → Bool) (h : Constraints p) : p 111 = false ∨ p 104 = false ∨ p 122 = false ∨ p 84 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 111 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 104 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 122 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 84 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 107 = false := (Or.elim (step587 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u3 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u1 l2))) (fun r2 => (False.elim (bool_contra u0 r2))))))))
  have t1 : p 112 = true := (Or.elim (step1968 p h) (fun l0 => (False.elim (bool_contra u0 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u3 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u1 l2))) (fun r2 => r2))))))
  have t2 : p 120 = true := (Or.elim (step1835 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u0 l1))) (fun r1 => (False.elim (bool_contra r1 t0))))))
  exact (Or.elim (step1545 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t1 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t2 l2)) (fun r2 => (bool_contra u2 r2)))))))

theorem step2034 (p : Nat → Bool) (h : Constraints p) : p 117 = false ∨ p 119 = false ∨ p 105 = false ∨ p 122 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 117 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 119 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 105 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 122 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 121 = true := (Or.elim (step2022 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u0 l1))) (fun r1 => (False.elim (bool_contra u2 r1))))))
  exact (Or.elim (step654 p h) (fun l0 => (bool_contra t0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u0 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra u1 l2)) (fun r2 => (bool_contra u3 r2)))))))

theorem step2035 (p : Nat → Bool) (h : Constraints p) : p 1697 = false ∨ p 118 = false ∨ p 1703 = false ∨ p 111 = false ∨ p 1714 = true ∨ p 122 = false ∨ p 98 = false ∨ p 1695 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1697 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 118 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1703 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 111 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 1714 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 122 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))
  have u6 : p 98 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))))
  have u7 : p 1695 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl))))))))
  have t0 : p 1707 = true := (Or.elim (step1386 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => r0))
  have t1 : p 1701 = false := (Or.elim (step1407 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t0 l1))) (fun r1 => (False.elim (bool_contra r1 u4))))))
  have t2 : p 1700 = true := (Or.elim (step1373 p h) (fun l0 => (False.elim (bool_contra u7 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u0 l1))) (fun r1 => r1))))
  have t3 : p 1696 = false := (Or.elim (step1376 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u0 l1))) (fun r1 => (False.elim (bool_contra r1 t1))))))
  have t4 : p 1708 = false := (Or.elim (step1403 p h) (fun l0 => (False.elim (bool_contra t2 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u4))))))
  have t5 : p 1705 = false := (Or.elim (step1387 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t4))))))
  have t6 : p 119 = true := (Or.elim (step1382 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t5))))
  have t7 : p 120 = false := (Or.elim (step651 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u3 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t6 l2))) (fun r2 => (False.elim (bool_contra u5 r2))))))))
  have t8 : p 109 = false := (Or.elim (step643 p h) (fun l0 => (False.elim (bool_contra u1 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u6 l1))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra t6 r2))))))))
  have t9 : p 112 = true := (Or.elim (step1834 p h) (fun l0 => (False.elim (bool_contra l0 t7))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra u3 r1))))))
  have t10 : p 110 = true := (Or.elim (step1366 p h) (fun l0 => (False.elim (bool_contra l0 t8))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t3))))))
  exact (Or.elim (step609 p h) (fun l0 => (bool_contra t9 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t10 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra u3 l2)) (fun r2 => (bool_contra u5 r2)))))))

theorem step2036 (p : Nat → Bool) (h : Constraints p) : p 116 = false ∨ p 110 = false ∨ p 113 = false ∨ p 105 = false ∨ p 93 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 116 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 110 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 113 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 105 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 93 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr hl)))))
  have t0 : p 115 = false := (Or.elim (step622 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u3 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u2 l2))) (fun r2 => (False.elim (bool_contra u0 r2))))))))
  have t1 : p 114 = false := (Or.elim (step618 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u4 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u2 l2))) (fun r2 => (False.elim (bool_contra u0 r2))))))))
  have t2 : p 106 = false := (Or.elim (step582 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u3 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u1 l2))) (fun r2 => (False.elim (bool_contra u0 r2))))))))
  exact (Or.elim (step1841 p h) (fun l0 => (bool_contra l0 t1)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 t2)) (fun r2 => (bool_contra u0 r2)))))))

theorem step2037 (p : Nat → Bool) (h : Constraints p) : p 113 = false ∨ p 1704 = true ∨ p 104 = false ∨ p 105 = false ∨ p 93 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 113 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 1704 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 104 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 105 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 93 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr hl)))))
  have t0 : p 103 = false := (Or.elim (step545 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u2 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u3 l2))) (fun r2 => (False.elim (bool_contra u0 r2))))))))
  have t1 : p 114 = false := (Or.elim (step616 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u4 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u2 l2))) (fun r2 => (False.elim (bool_contra u0 r2))))))))
  have t2 : p 115 = true := (Or.elim (step1840 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra l2 t0))) (fun r2 => (False.elim (bool_contra u0 r2))))))))
  have t3 : p 116 = false := (Or.elim (step622 p h) (fun l0 => (False.elim (bool_contra t2 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u3 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u0 l2))) (fun r2 => r2))))))
  have t4 : p 117 = false := (Or.elim (step623 p h) (fun l0 => (False.elim (bool_contra t2 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u3 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u0 l2))) (fun r2 => r2))))))
  exact (Or.elim (step1380 p h) (fun l0 => (bool_contra l0 t3)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t4)) (fun r1 => (bool_contra r1 u1)))))

theorem step2038 (p : Nat → Bool) (h : Constraints p) : p 116 = false ∨ p 104 = false ∨ p 94 = true ∨ p 105 = false ∨ p 93 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 116 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 104 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 94 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 105 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 93 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr hl)))))
  have t0 : p 106 = false := (Or.elim (step580 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u1 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u3 l2))) (fun r2 => (False.elim (bool_contra u0 r2))))))))
  have t1 : p 114 = false := (Or.elim (step617 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u4 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u1 l2))) (fun r2 => (False.elim (bool_contra u0 r2))))))))
  exact (Or.elim (step1844 p h) (fun l0 => (bool_contra l0 t1)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 u2)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra u0 l2)) (fun r2 => (bool_contra r2 t0)))))))

theorem step2039 (p : Nat → Bool) (h : Constraints p) : p 1714 = true ∨ p 116 = true ∨ p 1703 = false ∨ p 104 = false ∨ p 1695 = false ∨ p 105 = false ∨ p 93 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1714 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 116 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1703 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 104 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 1695 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 105 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))
  have u6 : p 93 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl)))))))
  have t0 : p 1699 = true := (Or.elim (step1372 p h) (fun l0 => (False.elim (bool_contra u4 l0))) (fun r0 => r0))
  have t1 : p 1709 = false := (Or.elim (step1399 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t2 : p 1704 = false := (Or.elim (step2021 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t1))) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t3 : p 113 = false := (Or.elim (step2037 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t2))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u3 l2))) (fun r2 => (Or.elim r2 (fun l3 => (False.elim (bool_contra u5 l3))) (fun r3 => (False.elim (bool_contra u6 r3))))))))))
  have t4 : p 1697 = true := (Or.elim (step1367 p h) (fun l0 => (False.elim (bool_contra l0 t3))) (fun r0 => r0))
  have t5 : p 1700 = true := (Or.elim (step1373 p h) (fun l0 => (False.elim (bool_contra u4 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t4 l1))) (fun r1 => r1))))
  have t6 : p 1708 = false := (Or.elim (step1403 p h) (fun l0 => (False.elim (bool_contra t5 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t7 : p 1705 = false := (Or.elim (step1387 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t6))))))
  have t8 : p 119 = true := (Or.elim (step1382 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t7))))
  have t9 : p 122 = true := (Or.elim (step1381 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t7))))
  have t10 : p 117 = false := (Or.elim (step2034 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t8 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u5 l2))) (fun r2 => (False.elim (bool_contra t9 r2))))))))
  exact (Or.elim (step1380 p h) (fun l0 => (bool_contra l0 u1)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t10)) (fun r1 => (bool_contra r1 t2)))))

theorem step2040 (p : Nat → Bool) (h : Constraints p) : p 1639 = true ∨ p 1674 = true ∨ p 94 = true ∨ p 93 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1639 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1674 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 94 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 93 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 85 = true := (Or.elim (step1243 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t1 : p 84 = true := (Or.elim (step1244 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t2 : p 95 = false := (Or.elim (step1681 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u0))) (fun r1 => (False.elim (bool_contra u3 r1))))))
  have t3 : p 97 = true := (Or.elim (step1318 p h) (fun l0 => (False.elim (bool_contra l0 t2))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u1))))))
  have t4 : p 96 = false := (Or.elim (step491 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t1 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u3 l2))) (fun r2 => (False.elim (bool_contra t3 r2))))))))
  have t5 : p 86 = true := (Or.elim (step1810 p h) (fun l0 => (False.elim (bool_contra l0 u2))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t4))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra t3 r2))))))))
  exact (Or.elim (step379 p h) (fun l0 => (bool_contra t5 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t1 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t0 l2)) (fun r2 => (bool_contra t3 r2)))))))

theorem step2041 (p : Nat → Bool) (h : Constraints p) : p 1676 = false ∨ p 1725 = true ∨ p 1690 = true ∨ p 94 = true ∨ p 1695 = false ∨ p 1679 = false ∨ p 105 = false ∨ p 93 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1676 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 1725 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1690 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 94 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 1695 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 1679 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))
  have u6 : p 105 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))))
  have u7 : p 93 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl))))))))
  have t0 : p 1683 = true := (Or.elim (step1335 p h) (fun l0 => (False.elim (bool_contra u5 l0))) (fun r0 => r0))
  have t1 : p 1684 = false := (Or.elim (step1352 p h) (fun l0 => (False.elim (bool_contra u0 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u2))))))
  have t2 : p 1689 = true := (Or.elim (step1351 p h) (fun l0 => (False.elim (bool_contra u0 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t0 l1))) (fun r1 => r1))))
  have t3 : p 1681 = false := (Or.elim (step1336 p h) (fun l0 => (False.elim (bool_contra u5 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t1))))))
  have t4 : p 1714 = false := (Or.elim (step1426 p h) (fun l0 => (False.elim (bool_contra t2 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u1))))))
  have t5 : p 104 = true := (Or.elim (step1331 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t3))))
  have t6 : p 1703 = true := (Or.elim (step2031 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t3))) (fun r1 => (False.elim (bool_contra r1 u3))))))
  have t7 : p 116 = true := (Or.elim (step2039 p h) (fun l0 => (False.elim (bool_contra l0 t4))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t6 l2))) (fun r2 => (Or.elim r2 (fun l3 => (False.elim (bool_contra t5 l3))) (fun r3 => (Or.elim r3 (fun l4 => (False.elim (bool_contra u4 l4))) (fun r4 => (Or.elim r4 (fun l5 => (False.elim (bool_contra u6 l5))) (fun r5 => (False.elim (bool_contra u7 r5))))))))))))))
  exact (Or.elim (step2038 p h) (fun l0 => (bool_contra t7 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t5 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u3)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra u6 l3)) (fun r3 => (bool_contra u7 r3)))))))))

theorem step2042 (p : Nat → Bool) (h : Constraints p) : p 1659 = true ∨ p 1644 = false ∨ p 1633 = false ∨ p 1611 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1659 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1644 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1633 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 1611 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 1635 = true := (Or.elim (step1238 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => r0))
  have t1 : p 1649 = true := (Or.elim (step1262 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u1 l1))) (fun r1 => r1))))
  have t2 : p 1623 = true := (Or.elim (step1218 p h) (fun l0 => (False.elim (bool_contra u3 l0))) (fun r0 => r0))
  have t3 : p 1650 = false := (Or.elim (step1283 p h) (fun l0 => (False.elim (bool_contra t2 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t4 : p 1624 = false := (Or.elim (step1288 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t1 l1))) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t5 : p 1636 = false := (Or.elim (step1267 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u1 l1))) (fun r1 => (False.elim (bool_contra r1 t3))))))
  have t6 : p 1619 = false := (Or.elim (step1219 p h) (fun l0 => (False.elim (bool_contra u3 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t4))))))
  have t7 : p 1631 = false := (Or.elim (step1241 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u2 l1))) (fun r1 => (False.elim (bool_contra r1 t5))))))
  have t8 : p 1617 = false := (Or.elim (step1207 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t6))))
  have t9 : p 77 = true := (Or.elim (step1234 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t7))))
  have t10 : p 72 = true := (Or.elim (step1205 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t8))))
  exact (Or.elim (step1783 p h) (fun l0 => (bool_contra t10 l0)) (fun r0 => (bool_contra t9 r0)))

theorem step2043 (p : Nat → Bool) (h : Constraints p) : p 104 = false ∨ p 1714 = true ∨ p 94 = true ∨ p 1695 = false ∨ p 105 = false ∨ p 93 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 104 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 1714 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 94 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 1695 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 105 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 93 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl))))))
  have t0 : p 116 = false := (Or.elim (step2038 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u0 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra l2 u2))) (fun r2 => (Or.elim r2 (fun l3 => (False.elim (bool_contra u4 l3))) (fun r3 => (False.elim (bool_contra u5 r3))))))))))
  have t1 : p 1703 = true := (Or.elim (step1379 p h) (fun l0 => (False.elim (bool_contra l0 t0))) (fun r0 => r0))
  exact (Or.elim (step2039 p h) (fun l0 => (bool_contra l0 u1)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t1 l2)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra u0 l3)) (fun r3 => (Or.elim r3 (fun l4 => (bool_contra u3 l4)) (fun r4 => (Or.elim r4 (fun l5 => (bool_contra u4 l5)) (fun r5 => (bool_contra u5 r5)))))))))))))

theorem step2044 (p : Nat → Bool) (h : Constraints p) : p 1713 = true ∨ p 94 = true ∨ p 1695 = false ∨ p 105 = false ∨ p 93 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1713 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 94 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1695 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 105 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 93 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr hl)))))
  have t0 : p 1699 = true := (Or.elim (step1372 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => r0))
  have t1 : p 1703 = false := (Or.elim (step2024 p h) (fun l0 => (False.elim (bool_contra l0 u0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra t0 r1))))))
  have t2 : p 1707 = false := (Or.elim (step2028 p h) (fun l0 => (False.elim (bool_contra l0 u0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra l2 u1))) (fun r2 => (Or.elim r2 (fun l3 => (False.elim (bool_contra u4 l3))) (fun r3 => (Or.elim r3 (fun l4 => (False.elim (bool_contra u2 l4))) (fun r4 => (False.elim (bool_contra t0 r4))))))))))))
  have t3 : p 117 = true := (Or.elim (step1378 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t1))))
  have t4 : p 1705 = false := (Or.elim (step1384 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t2))))
  have t5 : p 121 = true := (Or.elim (step2022 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t3 l1))) (fun r1 => (False.elim (bool_contra u3 r1))))))
  have t6 : p 122 = true := (Or.elim (step1381 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t4))))
  have t7 : p 119 = true := (Or.elim (step1382 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t4))))
  exact (Or.elim (step654 p h) (fun l0 => (bool_contra t5 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t3 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t7 l2)) (fun r2 => (bool_contra t6 r2)))))))

theorem step2045 (p : Nat → Bool) (h : Constraints p) : p 1724 = true ∨ p 1675 = false ∨ p 94 = true ∨ p 1695 = false ∨ p 1679 = false ∨ p 105 = false ∨ p 93 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1724 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1675 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 94 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 1695 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 1679 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 105 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))
  have u6 : p 93 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl)))))))
  have t0 : p 1683 = true := (Or.elim (step1335 p h) (fun l0 => (False.elim (bool_contra u4 l0))) (fun r0 => r0))
  have t1 : p 1688 = true := (Or.elim (step1346 p h) (fun l0 => (False.elim (bool_contra u1 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t0 l1))) (fun r1 => r1))))
  have t2 : p 1713 = true := (Or.elim (step2044 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u2))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u3 l2))) (fun r2 => (Or.elim r2 (fun l3 => (False.elim (bool_contra u5 l3))) (fun r3 => (False.elim (bool_contra u6 r3))))))))))
  have t3 : p 1714 = false := (Or.elim (step1420 p h) (fun l0 => (False.elim (bool_contra t1 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t4 : p 1689 = false := (Or.elim (step1425 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t2 l1))) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t5 : p 104 = false := (Or.elim (step2043 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t3))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra l2 u2))) (fun r2 => (Or.elim r2 (fun l3 => (False.elim (bool_contra u3 l3))) (fun r3 => (Or.elim r3 (fun l4 => (False.elim (bool_contra u5 l4))) (fun r4 => (False.elim (bool_contra u6 r4))))))))))))
  have t6 : p 1684 = false := (Or.elim (step1347 p h) (fun l0 => (False.elim (bool_contra u1 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t4))))))
  have t7 : p 1681 = true := (Or.elim (step1331 p h) (fun l0 => (False.elim (bool_contra l0 t5))) (fun r0 => r0))
  exact (Or.elim (step1336 p h) (fun l0 => (bool_contra u4 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t7 l1)) (fun r1 => (bool_contra r1 t6)))))

theorem step2046 (p : Nat → Bool) (h : Constraints p) : p 1706 = false ∨ p 1703 = false ∨ p 104 = false ∨ p 1715 = true ∨ p 1695 = false ∨ p 105 = false ∨ p 93 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1706 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 1703 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 104 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 1715 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 1695 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 105 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))
  have u6 : p 93 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl)))))))
  have t0 : p 1699 = true := (Or.elim (step1372 p h) (fun l0 => (False.elim (bool_contra u4 l0))) (fun r0 => r0))
  have t1 : p 1710 = false := (Or.elim (step1400 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u3))))))
  have t2 : p 1709 = true := (Or.elim (step1388 p h) (fun l0 => (False.elim (bool_contra u1 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u0 l1))) (fun r1 => r1))))
  have t3 : p 1704 = false := (Or.elim (step1391 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u0 l1))) (fun r1 => (False.elim (bool_contra r1 t1))))))
  have t4 : p 1700 = false := (Or.elim (step1404 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t2 l1))) (fun r1 => (False.elim (bool_contra r1 u3))))))
  have t5 : p 113 = false := (Or.elim (step2037 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t3))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u2 l2))) (fun r2 => (Or.elim r2 (fun l3 => (False.elim (bool_contra u5 l3))) (fun r3 => (False.elim (bool_contra u6 r3))))))))))
  have t6 : p 1697 = false := (Or.elim (step1373 p h) (fun l0 => (False.elim (bool_contra u4 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t4))))))
  exact (Or.elim (step1367 p h) (fun l0 => (bool_contra l0 t5)) (fun r0 => (bool_contra r0 t6)))

theorem step2047 (p : Nat → Bool) (h : Constraints p) : p 84 = true ∨ p 83 = false ∨ p 95 = false ∨ p 1659 = true ∨ p 1611 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 84 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 83 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 95 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 1659 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 1611 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr hl)))))
  have t0 : p 1645 = false := (Or.elim (step1662 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u3))) (fun r1 => (False.elim (bool_contra u4 r1))))))
  have t1 : p 1644 = true := (Or.elim (step1911 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u0))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u1 l2))) (fun r2 => (False.elim (bool_contra u2 r2))))))))
  have t2 : p 1633 = false := (Or.elim (step2042 p h) (fun l0 => (False.elim (bool_contra l0 u3))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t1 l1))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra u4 r2))))))))
  have t3 : p 80 = true := (Or.elim (step1235 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t2))))
  have t4 : p 85 = false := (Or.elim (step338 p h) (fun l0 => (False.elim (bool_contra u1 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t3 l1))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra u2 r2))))))))
  have t5 : p 90 = false := (Or.elim (step339 p h) (fun l0 => (False.elim (bool_contra u1 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t3 l1))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra u2 r2))))))))
  have t6 : p 1640 = true := (Or.elim (step1245 p h) (fun l0 => (False.elim (bool_contra l0 u0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t4))) (fun r1 => r1))))
  have t7 : p 1641 = true := (Or.elim (step1246 p h) (fun l0 => (False.elim (bool_contra l0 t5))) (fun r0 => r0))
  exact (Or.elim (step1255 p h) (fun l0 => (bool_contra t6 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t7 l1)) (fun r1 => (bool_contra r1 t0)))))

theorem step2048 (p : Nat → Bool) (h : Constraints p) : p 1633 = false ∨ p 1658 = true ∨ p 1611 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1633 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 1658 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1611 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 1623 = true := (Or.elim (step1218 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => r0))
  have t1 : p 1649 = false := (Or.elim (step1282 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u1))))))
  have t2 : p 1636 = false := (Or.elim (step1879 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t1))))
  have t3 : p 1635 = true := (Or.elim (step1238 p h) (fun l0 => (False.elim (bool_contra u0 l0))) (fun r0 => r0))
  have t4 : p 1631 = false := (Or.elim (step1241 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u0 l1))) (fun r1 => (False.elim (bool_contra r1 t2))))))
  have t5 : p 1648 = true := (Or.elim (step1878 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra t3 r0))))
  have t6 : p 77 = true := (Or.elim (step1234 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t4))))
  have t7 : p 1624 = false := (Or.elim (step1287 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t5 l1))) (fun r1 => (False.elim (bool_contra r1 u1))))))
  have t8 : p 72 = false := (Or.elim (step1783 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra t6 r0))))
  have t9 : p 1619 = false := (Or.elim (step1219 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t7))))))
  have t10 : p 1617 = true := (Or.elim (step1205 p h) (fun l0 => (False.elim (bool_contra l0 t8))) (fun r0 => r0))
  exact (Or.elim (step1207 p h) (fun l0 => (bool_contra t10 l0)) (fun r0 => (bool_contra r0 t9)))

theorem step2049 (p : Nat → Bool) (h : Constraints p) : p 1657 = true ∨ p 1611 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1657 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1611 = true := bool_true_of_not_false (fun hl => hc (Or.inr hl))
  have t0 : p 1623 = true := (Or.elim (step1218 p h) (fun l0 => (False.elim (bool_contra u1 l0))) (fun r0 => r0))
  have t1 : p 1624 = false := (Or.elim (step1881 p h) (fun l0 => (False.elim (bool_contra l0 u0))) (fun r0 => r0))
  have t2 : p 1648 = false := (Or.elim (step1281 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t3 : p 1619 = false := (Or.elim (step1219 p h) (fun l0 => (False.elim (bool_contra u1 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t1))))))
  have t4 : p 1635 = false := (Or.elim (step1878 p h) (fun l0 => (False.elim (bool_contra l0 t2))) (fun r0 => r0))
  have t5 : p 1617 = false := (Or.elim (step1207 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t3))))
  have t6 : p 1631 = false := (Or.elim (step1240 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t4))))
  have t7 : p 72 = true := (Or.elim (step1205 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t5))))
  have t8 : p 77 = true := (Or.elim (step1234 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t6))))
  exact (Or.elim (step1783 p h) (fun l0 => (bool_contra t7 l0)) (fun r0 => (bool_contra t8 r0)))

theorem step2050 (p : Nat → Bool) (h : Constraints p) : p 1658 = true ∨ p 88 = true ∨ p 1635 = false ∨ p 92 = false ∨ p 1611 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1658 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 88 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1635 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 92 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 1611 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr hl)))))
  have t0 : p 1623 = true := (Or.elim (step1218 p h) (fun l0 => (False.elim (bool_contra u4 l0))) (fun r0 => r0))
  have t1 : p 1649 = false := (Or.elim (step1282 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t2 : p 1639 = false := (Or.elim (step2026 p h) (fun l0 => (False.elim (bool_contra l0 u0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra u4 r1))))))
  have t3 : p 1644 = false := (Or.elim (step1262 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t1))))))
  have t4 : p 85 = true := (Or.elim (step1243 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t2))))
  exact (Or.elim (step1973 p h) (fun l0 => (bool_contra l0 t3)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 u1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t4 l2)) (fun r2 => (bool_contra u3 r2)))))))

theorem step2051 (p : Nat → Bool) (h : Constraints p) : p 1673 = true ∨ p 92 = false ∨ p 94 = true ∨ p 93 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1673 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 92 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 94 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 93 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 97 = true := (Or.elim (step1316 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t1 : p 95 = true := (Or.elim (step1317 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t2 : p 96 = false := (Or.elim (step493 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u3 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t1 l2))) (fun r2 => (False.elim (bool_contra t0 r2))))))))
  have t3 : p 102 = true := (Or.elim (step1624 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t1 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u3 l2))) (fun r2 => (Or.elim r2 (fun l3 => l3) (fun r3 => (False.elim (bool_contra r3 u2))))))))))
  have t4 : p 86 = true := (Or.elim (step1810 p h) (fun l0 => (False.elim (bool_contra l0 u2))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t2))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra t0 r2))))))))
  exact (Or.elim (step1533 p h) (fun l0 => (bool_contra t4 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u1 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t0 l2)) (fun r2 => (bool_contra t3 r2)))))))

theorem step2052 (p : Nat → Bool) (h : Constraints p) : p 83 = false ∨ p 1639 = false ∨ p 95 = false ∨ p 1659 = true ∨ p 1611 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 83 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 1639 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 95 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 1659 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 1611 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr hl)))))
  have t0 : p 84 = true := (Or.elim (step2047 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u0 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u2 l2))) (fun r2 => (Or.elim r2 (fun l3 => (False.elim (bool_contra l3 u3))) (fun r3 => (False.elim (bool_contra u4 r3))))))))))
  have t1 : p 80 = false := (Or.elim (step336 p h) (fun l0 => (False.elim (bool_contra u0 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t0 l2))) (fun r2 => (False.elim (bool_contra u2 r2))))))))
  have t2 : p 90 = false := (Or.elim (step342 p h) (fun l0 => (False.elim (bool_contra u0 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t0 l1))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra u2 r2))))))))
  have t3 : p 1633 = true := (Or.elim (step1235 p h) (fun l0 => (False.elim (bool_contra l0 t1))) (fun r0 => r0))
  have t4 : p 1641 = true := (Or.elim (step1246 p h) (fun l0 => (False.elim (bool_contra l0 t2))) (fun r0 => r0))
  have t5 : p 1644 = false := (Or.elim (step2042 p h) (fun l0 => (False.elim (bool_contra l0 u3))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t3 l2))) (fun r2 => (False.elim (bool_contra u4 r2))))))))
  exact (Or.elim (step1252 p h) (fun l0 => (bool_contra u1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t4 l1)) (fun r1 => (bool_contra r1 t5)))))

theorem step2053 (p : Nat → Bool) (h : Constraints p) : p 85 = false ∨ p 80 = false ∨ p 90 = false ∨ p 92 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 85 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 80 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 90 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 92 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 91 = false := (Or.elim (step449 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u0 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u2 l2))) (fun r2 => (False.elim (bool_contra u3 r2))))))))
  have t1 : p 83 = false := (Or.elim (step337 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u1 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u0 l2))) (fun r2 => (False.elim (bool_contra u2 r2))))))))
  exact (Or.elim (step1802 p h) (fun l0 => (bool_contra l0 t1)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u2 l1)) (fun r1 => (bool_contra r1 t0)))))

theorem step2054 (p : Nat → Bool) (h : Constraints p) : p 84 = false ∨ p 97 = false ∨ p 92 = false ∨ p 94 = true ∨ p 93 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 84 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 97 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 92 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 94 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 93 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr hl)))))
  have t0 : p 96 = false := (Or.elim (step491 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u0 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u4 l2))) (fun r2 => (False.elim (bool_contra u1 r2))))))))
  have t1 : p 86 = false := (Or.elim (step380 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u0 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u2 l2))) (fun r2 => (False.elim (bool_contra u1 r2))))))))
  exact (Or.elim (step1810 p h) (fun l0 => (bool_contra l0 u3)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 t1)) (fun r2 => (bool_contra u1 r2)))))))

theorem step2055 (p : Nat → Bool) (h : Constraints p) : p 1640 = false ∨ p 1659 = true ∨ p 92 = false ∨ p 1611 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1640 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 1659 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 92 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 1611 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 1645 = false := (Or.elim (step1662 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u1))) (fun r1 => (False.elim (bool_contra u3 r1))))))
  have t1 : p 1644 = true := (Or.elim (step1254 p h) (fun l0 => (False.elim (bool_contra u0 l0))) (fun r0 => r0))
  have t2 : p 1641 = false := (Or.elim (step1255 p h) (fun l0 => (False.elim (bool_contra u0 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t0))))))
  have t3 : p 1633 = false := (Or.elim (step2042 p h) (fun l0 => (False.elim (bool_contra l0 u1))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t1 l1))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra u3 r2))))))))
  have t4 : p 80 = false := (Or.elim (step1650 p h) (fun l0 => (False.elim (bool_contra l0 t2))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra u2 r1))))))
  exact (Or.elim (step1235 p h) (fun l0 => (bool_contra l0 t4)) (fun r0 => (bool_contra r0 t3)))

theorem step2056 (p : Nat → Bool) (h : Constraints p) : p 1725 = true ∨ p 1676 = false ∨ p 94 = true ∨ p 1695 = false ∨ p 1679 = false ∨ p 105 = false ∨ p 93 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1725 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1676 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 94 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 1695 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 1679 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 105 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))
  have u6 : p 93 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl)))))))
  have t0 : p 1713 = true := (Or.elim (step2044 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u2))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u3 l2))) (fun r2 => (Or.elim r2 (fun l3 => (False.elim (bool_contra u5 l3))) (fun r3 => (False.elim (bool_contra u6 r3))))))))))
  have t1 : p 1690 = false := (Or.elim (step1430 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t0 l1))) (fun r1 => (False.elim (bool_contra r1 u0))))))
  exact (Or.elim (step2041 p h) (fun l0 => (bool_contra u1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 u0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 t1)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u2)) (fun r3 => (Or.elim r3 (fun l4 => (bool_contra u3 l4)) (fun r4 => (Or.elim r4 (fun l5 => (bool_contra u4 l5)) (fun r5 => (Or.elim r5 (fun l6 => (bool_contra u5 l6)) (fun r6 => (bool_contra u6 r6)))))))))))))))

theorem step2057 (p : Nat → Bool) (h : Constraints p) : p 1607 = true ∨ p 88 = false ∨ p 92 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1607 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 88 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 92 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 62 = true := (Or.elim (step1187 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t1 : p 61 = true := (Or.elim (step1188 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t2 : p 89 = true := (Or.elim (step1631 p h) (fun l0 => (False.elim (bool_contra t1 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t0 l1))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra u2 r2))))))))
  exact (Or.elim (step434 p h) (fun l0 => (bool_contra t2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t1 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra u1 l2)) (fun r2 => (bool_contra u2 r2)))))))

theorem step2058 (p : Nat → Bool) (h : Constraints p) : p 1612 = false ∨ p 1658 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1612 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 1658 = false := bool_false_of_not_true (fun hl => hc (Or.inr hl))
  have t0 : p 1625 = false := (Or.elim (step1882 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u1))))
  have t1 : p 1624 = true := (Or.elim (step1223 p h) (fun l0 => (False.elim (bool_contra u0 l0))) (fun r0 => r0))
  have t2 : p 1619 = false := (Or.elim (step1224 p h) (fun l0 => (False.elim (bool_contra u0 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t0))))))
  have t3 : p 1648 = false := (Or.elim (step1287 p h) (fun l0 => (False.elim (bool_contra t1 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u1))))))
  have t4 : p 1617 = false := (Or.elim (step1207 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t2))))
  have t5 : p 1635 = false := (Or.elim (step1878 p h) (fun l0 => (False.elim (bool_contra l0 t3))) (fun r0 => r0))
  have t6 : p 72 = true := (Or.elim (step1205 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t4))))
  have t7 : p 1631 = false := (Or.elim (step1240 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t5))))
  have t8 : p 77 = false := (Or.elim (step1783 p h) (fun l0 => (False.elim (bool_contra t6 l0))) (fun r0 => r0))
  exact (Or.elim (step1234 p h) (fun l0 => (bool_contra l0 t8)) (fun r0 => (bool_contra r0 t7)))

theorem step2059 (p : Nat → Bool) (h : Constraints p) : p 92 = false ∨ p 1607 = true ∨ p 1658 = true ∨ p 1611 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 92 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 1607 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1658 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 1611 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 1639 = false := (Or.elim (step2026 p h) (fun l0 => (False.elim (bool_contra l0 u2))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra u3 r1))))))
  have t1 : p 85 = true := (Or.elim (step1243 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t0))))
  have t2 : p 88 = false := (Or.elim (step2057 p h) (fun l0 => (False.elim (bool_contra l0 u1))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra u0 r1))))))
  have t3 : p 1635 = false := (Or.elim (step2050 p h) (fun l0 => (False.elim (bool_contra l0 u2))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t2))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (Or.elim r2 (fun l3 => (False.elim (bool_contra u0 l3))) (fun r3 => (False.elim (bool_contra u3 r3))))))))))
  have t4 : p 1644 = true := (Or.elim (step1973 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t2))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t1 l2))) (fun r2 => (False.elim (bool_contra u0 r2))))))))
  have t5 : p 1631 = false := (Or.elim (step1240 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t3))))
  have t6 : p 1648 = true := (Or.elim (step1258 p h) (fun l0 => (False.elim (bool_contra t4 l0))) (fun r0 => r0))
  have t7 : p 77 = true := (Or.elim (step1234 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t5))))
  have t8 : p 1624 = false := (Or.elim (step1287 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t6 l1))) (fun r1 => (False.elim (bool_contra r1 u2))))))
  have t9 : p 72 = false := (Or.elim (step1783 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra t7 r0))))
  have t10 : p 1619 = false := (Or.elim (step1219 p h) (fun l0 => (False.elim (bool_contra u3 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t8))))))
  have t11 : p 1617 = true := (Or.elim (step1205 p h) (fun l0 => (False.elim (bool_contra l0 t9))) (fun r0 => r0))
  exact (Or.elim (step1207 p h) (fun l0 => (bool_contra t11 l0)) (fun r0 => (bool_contra r0 t10)))

theorem step2060 (p : Nat → Bool) (h : Constraints p) : p 1573 = true ∨ p 1555 = false ∨ p 56 = true ∨ p 1524 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1573 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1555 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 56 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 1524 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 1552 = true := (Or.elim (step1084 p h) (fun l0 => (False.elim (bool_contra l0 u2))) (fun r0 => r0))
  have t1 : p 1558 = true := (Or.elim (step1094 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u1 l1))) (fun r1 => r1))))
  have t2 : p 1562 = true := (Or.elim (step1100 p h) (fun l0 => (False.elim (bool_contra t1 l0))) (fun r0 => r0))
  have t3 : p 1536 = true := (Or.elim (step1061 p h) (fun l0 => (False.elim (bool_contra u3 l0))) (fun r0 => r0))
  have t4 : p 1564 = false := (Or.elim (step1124 p h) (fun l0 => (False.elim (bool_contra t3 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t5 : p 1538 = false := (Or.elim (step1135 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t2 l1))) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t6 : p 1530 = false := (Or.elim (step1606 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u3 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t1 l2))) (fun r2 => (False.elim (bool_contra r2 u0))))))))
  have t7 : p 1549 = false := (Or.elim (step1110 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t1 l1))) (fun r1 => (False.elim (bool_contra r1 t4))))))
  have t8 : p 1533 = false := (Or.elim (step1063 p h) (fun l0 => (False.elim (bool_contra u3 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t5))))))
  have t9 : p 43 = true := (Or.elim (step1047 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t6))))
  have t10 : p 42 = true := (Or.elim (step1048 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t6))))
  have t11 : p 1544 = true := (Or.elim (step1953 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t8))))
  have t12 : p 1548 = true := (Or.elim (step1078 p h) (fun l0 => (False.elim (bool_contra t11 l0))) (fun r0 => r0))
  have t13 : p 1546 = false := (Or.elim (step1079 p h) (fun l0 => (False.elim (bool_contra t11 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t7))))))
  have t14 : p 1559 = false := (Or.elim (step1106 p h) (fun l0 => (False.elim (bool_contra t12 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t4))))))
  have t15 : p 53 = false := (Or.elim (step1955 p h) (fun l0 => (False.elim (bool_contra t9 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t10 l1))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra r2 t13))))))))
  have t16 : p 1553 = false := (Or.elim (step1097 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u1 l1))) (fun r1 => (False.elim (bool_contra r1 t14))))))
  exact (Or.elim (step1086 p h) (fun l0 => (bool_contra l0 t15)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 u2)) (fun r1 => (bool_contra r1 t16)))))

theorem step2061 (p : Nat → Bool) (h : Constraints p) : p 1500 = true ∨ p 19 = true ∨ p 1481 = false ∨ p 81 = true ∨ p 80 = false ∨ p 85 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1500 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 19 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1481 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 81 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 80 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 85 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl))))))
  have t0 : p 1483 = true := (Or.elim (step971 p h) (fun l0 => (False.elim (bool_contra l0 u1))) (fun r0 => r0))
  have t1 : p 1486 = true := (Or.elim (step976 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t0 l1))) (fun r1 => r1))))
  have t2 : p 1487 = false := (Or.elim (step1870 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t3 : p 1494 = false := (Or.elim (step1002 p h) (fun l0 => (False.elim (bool_contra t1 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t4 : p 1484 = false := (Or.elim (step977 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t2))))))
  have t5 : p 1492 = false := (Or.elim (step988 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t3))))
  have t6 : p 24 = true := (Or.elim (step1918 p h) (fun l0 => (False.elim (bool_contra l0 t3))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u5 l1))) (fun r1 => r1))))
  have t7 : p 21 = true := (Or.elim (step972 p h) (fun l0 => (False.elim (bool_contra l0 u1))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t4))))))
  have t8 : p 20 = false := (Or.elim (step73 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t7 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t6 l2))) (fun r2 => (False.elim (bool_contra u4 r2))))))))
  have t9 : p 25 = true := (Or.elim (step1717 p h) (fun l0 => (False.elim (bool_contra l0 t8))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u3))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t7 l2))) (fun r2 => r2))))))
  have t10 : p 27 = false := (Or.elim (step92 p h) (fun l0 => (False.elim (bool_contra t9 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t7 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t6 l2))) (fun r2 => r2))))))
  have t11 : p 26 = false := (Or.elim (step91 p h) (fun l0 => (False.elim (bool_contra t9 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t7 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t6 l2))) (fun r2 => r2))))))
  exact (Or.elim (step986 p h) (fun l0 => (bool_contra l0 t11)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t10)) (fun r1 => (bool_contra r1 t5)))))

theorem step2062 (p : Nat → Bool) (h : Constraints p) : p 24 = false ∨ p 5 = false ∨ p 60 = false ∨ p 1477 = true ∨ p 62 = false ∨ p 84 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 24 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 5 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 60 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 1477 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 62 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 84 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl))))))
  have t0 : p 1471 = true := (Or.elim (step1582 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u1 l2))) (fun r2 => (False.elim (bool_contra u0 r2))))))))
  have t1 : p 13 = false := (Or.elim (step24 p h) (fun l0 => (False.elim (bool_contra u1 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u0 l2))) (fun r2 => (False.elim (bool_contra u2 r2))))))))
  have t2 : p 6 = false := (Or.elim (step20 p h) (fun l0 => (False.elim (bool_contra u1 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u0 l2))) (fun r2 => (False.elim (bool_contra u2 r2))))))))
  have t3 : p 8 = false := (Or.elim (step23 p h) (fun l0 => (False.elim (bool_contra u1 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u0 l2))) (fun r2 => (False.elim (bool_contra u2 r2))))))))
  have t4 : p 1464 = false := (Or.elim (step961 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t0 l1))) (fun r1 => (False.elim (bool_contra r1 u3))))))
  have t5 : p 1468 = true := (Or.elim (step939 p h) (fun l0 => (False.elim (bool_contra l0 t1))) (fun r0 => r0))
  have t6 : p 1461 = true := (Or.elim (step928 p h) (fun l0 => (False.elim (bool_contra l0 t2))) (fun r0 => r0))
  have t7 : p 1462 = false := (Or.elim (step932 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t4))))
  have t8 : p 1463 = true := (Or.elim (step931 p h) (fun l0 => (False.elim (bool_contra t6 l0))) (fun r0 => r0))
  have t9 : p 4 = true := (Or.elim (step930 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t2))) (fun r1 => (False.elim (bool_contra r1 t7))))))
  have t10 : p 1472 = false := (Or.elim (step957 p h) (fun l0 => (False.elim (bool_contra t8 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u3))))))
  have t11 : p 57 = false := (Or.elim (step209 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t9 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u4 l2))) (fun r2 => (False.elim (bool_contra u5 r2))))))))
  have t12 : p 11 = true := (Or.elim (step1696 p h) (fun l0 => (False.elim (bool_contra l0 t11))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra t9 r1))))))
  have t13 : p 3 = true := (Or.elim (step1697 p h) (fun l0 => (False.elim (bool_contra l0 t11))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra t9 r1))))))
  have t14 : p 1467 = false := (Or.elim (step948 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t5 l1))) (fun r1 => (False.elim (bool_contra r1 t10))))))
  have t15 : p 10 = false := (Or.elim (step1505 p h) (fun l0 => (False.elim (bool_contra t13 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t9 l1))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra t12 r2))))))))
  exact (Or.elim (step938 p h) (fun l0 => (bool_contra l0 t3)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t15)) (fun r1 => (bool_contra r1 t14)))))

theorem step2063 (p : Nat → Bool) (h : Constraints p) : p 6 = true ∨ p 8 = true ∨ p 1468 = false ∨ p 1477 = true ∨ p 62 = false ∨ p 84 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 6 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 8 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1468 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 1477 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 62 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 84 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl))))))
  have t0 : p 1466 = true := (Or.elim (step937 p h) (fun l0 => (False.elim (bool_contra l0 u1))) (fun r0 => r0))
  have t1 : p 1471 = true := (Or.elim (step945 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u2 l1))) (fun r1 => r1))))
  have t2 : p 1464 = false := (Or.elim (step961 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t1 l1))) (fun r1 => (False.elim (bool_contra r1 u3))))))
  have t3 : p 1462 = false := (Or.elim (step932 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t2))))
  have t4 : p 1461 = true := (Or.elim (step928 p h) (fun l0 => (False.elim (bool_contra l0 u0))) (fun r0 => r0))
  have t5 : p 4 = true := (Or.elim (step930 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u0))) (fun r1 => (False.elim (bool_contra r1 t3))))))
  have t6 : p 1463 = true := (Or.elim (step931 p h) (fun l0 => (False.elim (bool_contra t4 l0))) (fun r0 => r0))
  have t7 : p 57 = false := (Or.elim (step209 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t5 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u4 l2))) (fun r2 => (False.elim (bool_contra u5 r2))))))))
  have t8 : p 11 = true := (Or.elim (step1696 p h) (fun l0 => (False.elim (bool_contra l0 t7))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra t5 r1))))))
  have t9 : p 3 = true := (Or.elim (step1697 p h) (fun l0 => (False.elim (bool_contra l0 t7))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra t5 r1))))))
  have t10 : p 1472 = false := (Or.elim (step957 p h) (fun l0 => (False.elim (bool_contra t6 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u3))))))
  have t11 : p 10 = false := (Or.elim (step1505 p h) (fun l0 => (False.elim (bool_contra t9 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t5 l1))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra t8 r2))))))))
  have t12 : p 1467 = false := (Or.elim (step948 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u2 l1))) (fun r1 => (False.elim (bool_contra r1 t10))))))
  exact (Or.elim (step938 p h) (fun l0 => (bool_contra l0 u1)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t11)) (fun r1 => (bool_contra r1 t12)))))

theorem step2064 (p : Nat → Bool) (h : Constraints p) : p 4 = false ∨ p 8 = true ∨ p 13 = true ∨ p 1494 = false ∨ p 1477 = true ∨ p 1512 = true ∨ p 1483 = false ∨ p 18 = true ∨ p 61 = false ∨ p 62 = false ∨ p 84 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 4 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 8 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 13 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 1494 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 1477 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 1512 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))
  have u6 : p 1483 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))))
  have u7 : p 18 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))))
  have u8 : p 61 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))))))
  have u9 : p 62 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))))))
  have u10 : p 84 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl)))))))))))
  have t0 : p 1468 = true := (Or.elim (step939 p h) (fun l0 => (False.elim (bool_contra l0 u2))) (fun r0 => r0))
  have t1 : p 57 = false := (Or.elim (step209 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u0 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u9 l2))) (fun r2 => (False.elim (bool_contra u10 r2))))))))
  have t2 : p 11 = true := (Or.elim (step1696 p h) (fun l0 => (False.elim (bool_contra l0 t1))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra u0 r1))))))
  have t3 : p 3 = true := (Or.elim (step1697 p h) (fun l0 => (False.elim (bool_contra l0 t1))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra u0 r1))))))
  have t4 : p 10 = false := (Or.elim (step1505 p h) (fun l0 => (False.elim (bool_contra t3 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u0 l1))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra t2 r2))))))))
  have t5 : p 125 = true := (Or.elim (step10 p h) (fun l0 => (False.elim (bool_contra t3 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra l2 u1))) (fun r2 => (Or.elim r2 (fun l3 => (False.elim (bool_contra l3 t4))) (fun r3 => (False.elim (bool_contra r3 u7))))))))))
  have t6 : p 1467 = true := (Or.elim (step938 p h) (fun l0 => (False.elim (bool_contra l0 u1))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t4))) (fun r1 => r1))))
  have t7 : p 245 = true := (Or.elim (step723 p h) (fun l0 => (False.elim (bool_contra t5 l0))) (fun r0 => r0))
  have t8 : p 1472 = true := (Or.elim (step948 p h) (fun l0 => (False.elim (bool_contra t6 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t0 l1))) (fun r1 => r1))))
  have t9 : p 247 = true := (Or.elim (step724 p h) (fun l0 => (False.elim (bool_contra t7 l0))) (fun r0 => r0))
  have t10 : p 1476 = true := (Or.elim (step952 p h) (fun l0 => (False.elim (bool_contra t8 l0))) (fun r0 => r0))
  have t11 : p 1463 = false := (Or.elim (step957 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t8 l1))) (fun r1 => (False.elim (bool_contra r1 u4))))))
  have t12 : p 255 = true := (Or.elim (step732 p h) (fun l0 => (False.elim (bool_contra t9 l0))) (fun r0 => r0))
  have t13 : p 1501 = false := (Or.elim (step1020 p h) (fun l0 => (False.elim (bool_contra t10 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u5))))))
  have t14 : p 7 = false := (Or.elim (step1964 p h) (fun l0 => (False.elim (bool_contra l0 t11))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra u8 r1))))))
  have t15 : p 269 = false := (Or.elim (step1852 p h) (fun l0 => (False.elim (bool_contra t12 l0))) (fun r0 => r0))
  have t16 : p 1487 = false := (Or.elim (step1006 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u3 l1))) (fun r1 => (False.elim (bool_contra r1 t13))))))
  have t17 : p 267 = false := (Or.elim (step740 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t15))))
  have t18 : p 1482 = false := (Or.elim (step979 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u6 l1))) (fun r1 => (False.elim (bool_contra r1 t16))))))
  have t19 : p 265 = false := (Or.elim (step739 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t17))))
  have t20 : p 15 = true := (Or.elim (step969 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u7))) (fun r1 => (False.elim (bool_contra r1 t18))))))
  have t21 : p 136 = false := (Or.elim (step738 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t19))))
  have t22 : p 14 = true := (Or.elim (step1711 p h) (fun l0 => (False.elim (bool_contra t20 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t14))) (fun r1 => r1))))
  exact (Or.elim (step58 p h) (fun l0 => (bool_contra t22 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t21)) (fun r1 => (bool_contra r1 u2)))))

theorem step2065 (p : Nat → Bool) (h : Constraints p) : p 8 = true ∨ p 13 = true ∨ p 1494 = false ∨ p 1557 = false ∨ p 1500 = false ∨ p 73 = false ∨ p 18 = true ∨ p 61 = false ∨ p 62 = false ∨ p 84 = false ∨ p 1595 = true ∨ p 1524 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 8 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 13 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1494 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 1557 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 1500 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 73 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))
  have u6 : p 18 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))))
  have u7 : p 61 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))))
  have u8 : p 62 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))))))
  have u9 : p 84 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))))))
  have u10 : p 1595 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))))))))
  have u11 : p 1524 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl))))))))))))
  have t0 : p 1468 = true := (Or.elim (step939 p h) (fun l0 => (False.elim (bool_contra l0 u1))) (fun r0 => r0))
  have t1 : p 1536 = true := (Or.elim (step1061 p h) (fun l0 => (False.elim (bool_contra u11 l0))) (fun r0 => r0))
  have t2 : p 1571 = true := (Or.elim (step1678 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t1 l1))) (fun r1 => (False.elim (bool_contra u3 r1))))))
  have t3 : p 1512 = false := (Or.elim (step1182 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t2 l1))) (fun r1 => (False.elim (bool_contra r1 u10))))))
  have t4 : p 1477 = false := (Or.elim (step1026 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u4 l1))) (fun r1 => (False.elim (bool_contra r1 t3))))))
  have t5 : p 1561 = true := (Or.elim (step1099 p h) (fun l0 => (False.elim (bool_contra u3 l0))) (fun r0 => r0))
  have t6 : p 19 = false := (Or.elim (step1682 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra u5 r0))))
  have t7 : p 1483 = true := (Or.elim (step971 p h) (fun l0 => (False.elim (bool_contra l0 t6))) (fun r0 => r0))
  have t8 : p 1466 = true := (Or.elim (step937 p h) (fun l0 => (False.elim (bool_contra l0 u0))) (fun r0 => r0))
  have t9 : p 1471 = true := (Or.elim (step945 p h) (fun l0 => (False.elim (bool_contra t8 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t0 l1))) (fun r1 => r1))))
  have t10 : p 1464 = false := (Or.elim (step961 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t9 l1))) (fun r1 => (False.elim (bool_contra r1 t4))))))
  have t11 : p 4 = false := (Or.elim (step2064 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u0))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra l2 u1))) (fun r2 => (Or.elim r2 (fun l3 => (False.elim (bool_contra u2 l3))) (fun r3 => (Or.elim r3 (fun l4 => (False.elim (bool_contra l4 t4))) (fun r4 => (Or.elim r4 (fun l5 => (False.elim (bool_contra l5 t3))) (fun r5 => (Or.elim r5 (fun l6 => (False.elim (bool_contra t7 l6))) (fun r6 => (Or.elim r6 (fun l7 => (False.elim (bool_contra l7 u6))) (fun r7 => (Or.elim r7 (fun l8 => (False.elim (bool_contra u7 l8))) (fun r8 => (Or.elim r8 (fun l9 => (False.elim (bool_contra u8 l9))) (fun r9 => (False.elim (bool_contra u9 r9))))))))))))))))))))))
  have t12 : p 1461 = true := (Or.elim (step929 p h) (fun l0 => (False.elim (bool_contra l0 t11))) (fun r0 => r0))
  have t13 : p 7 = false := (Or.elim (step1646 p h) (fun l0 => (False.elim (bool_contra l0 t10))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t11))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra u7 r2))))))))
  have t14 : p 1463 = true := (Or.elim (step931 p h) (fun l0 => (False.elim (bool_contra t12 l0))) (fun r0 => r0))
  have t15 : p 2 = true := (Or.elim (step934 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t12 l1))) (fun r1 => (False.elim (bool_contra r1 t10))))))
  have t16 : p 17 = true := (Or.elim (step1693 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t13))) (fun r1 => (False.elim (bool_contra t15 r1))))))
  have t17 : p 1476 = true := (Or.elim (step956 p h) (fun l0 => (False.elim (bool_contra t14 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t9 l1))) (fun r1 => r1))))
  have t18 : p 39 = false := (Or.elim (step66 p h) (fun l0 => (False.elim (bool_contra t16 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t15 l1))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra u5 r2))))))))
  have t19 : p 1511 = true := (Or.elim (step1019 p h) (fun l0 => (False.elim (bool_contra t17 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u4 l1))) (fun r1 => r1))))
  have t20 : p 1528 = true := (Or.elim (step1045 p h) (fun l0 => (False.elim (bool_contra l0 t18))) (fun r0 => r0))
  have t21 : p 1572 = false := (Or.elim (step1178 p h) (fun l0 => (False.elim (bool_contra t19 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u10))))))
  have t22 : p 1532 = true := (Or.elim (step1052 p h) (fun l0 => (False.elim (bool_contra t20 l0))) (fun r0 => r0))
  have t23 : p 1538 = false := (Or.elim (step1134 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t5 l1))) (fun r1 => (False.elim (bool_contra r1 t21))))))
  have t24 : p 1537 = true := (Or.elim (step1062 p h) (fun l0 => (False.elim (bool_contra u11 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t22 l1))) (fun r1 => r1))))
  have t25 : p 1533 = false := (Or.elim (step1063 p h) (fun l0 => (False.elim (bool_contra u11 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t23))))))
  have t26 : p 1562 = false := (Or.elim (step1128 p h) (fun l0 => (False.elim (bool_contra t24 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t21))))))
  have t27 : p 1544 = true := (Or.elim (step1953 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t25))))
  have t28 : p 1548 = false := (Or.elim (step1104 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u3 l1))) (fun r1 => (False.elim (bool_contra r1 t26))))))
  exact (Or.elim (step1078 p h) (fun l0 => (bool_contra t27 l0)) (fun r0 => (bool_contra r0 t28)))

theorem step2066 (p : Nat → Bool) (h : Constraints p) : p 1462 = false ∨ p 1470 = false ∨ p 1494 = false ∨ p 1557 = false ∨ p 1500 = false ∨ p 73 = false ∨ p 18 = true ∨ p 61 = false ∨ p 1595 = true ∨ p 1524 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1462 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 1470 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1494 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 1557 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 1500 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 73 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))
  have u6 : p 18 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))))
  have u7 : p 61 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))))
  have u8 : p 1595 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))))))
  have u9 : p 1524 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl))))))))))
  have t0 : p 1536 = true := (Or.elim (step1061 p h) (fun l0 => (False.elim (bool_contra u9 l0))) (fun r0 => r0))
  have t1 : p 1571 = true := (Or.elim (step1678 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t0 l1))) (fun r1 => (False.elim (bool_contra u3 r1))))))
  have t2 : p 1512 = false := (Or.elim (step1182 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t1 l1))) (fun r1 => (False.elim (bool_contra r1 u8))))))
  have t3 : p 1477 = false := (Or.elim (step1026 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u4 l1))) (fun r1 => (False.elim (bool_contra r1 t2))))))
  have t4 : p 1465 = false := (Or.elim (step965 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u1 l1))) (fun r1 => (False.elim (bool_contra r1 t3))))))
  have t5 : p 1561 = true := (Or.elim (step1099 p h) (fun l0 => (False.elim (bool_contra u3 l0))) (fun r0 => r0))
  have t6 : p 19 = false := (Or.elim (step1682 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra u5 r0))))
  have t7 : p 1483 = true := (Or.elim (step971 p h) (fun l0 => (False.elim (bool_contra l0 t6))) (fun r0 => r0))
  have t8 : p 1464 = true := (Or.elim (step932 p h) (fun l0 => (False.elim (bool_contra u0 l0))) (fun r0 => r0))
  have t9 : p 2 = true := (Or.elim (step935 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u0 l1))) (fun r1 => (False.elim (bool_contra r1 t4))))))
  have t10 : p 1476 = true := (Or.elim (step960 p h) (fun l0 => (False.elim (bool_contra t8 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u1 l1))) (fun r1 => r1))))
  have t11 : p 1501 = false := (Or.elim (step1020 p h) (fun l0 => (False.elim (bool_contra t10 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t2))))))
  have t12 : p 1511 = true := (Or.elim (step1019 p h) (fun l0 => (False.elim (bool_contra t10 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u4 l1))) (fun r1 => r1))))
  have t13 : p 1487 = false := (Or.elim (step1006 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u2 l1))) (fun r1 => (False.elim (bool_contra r1 t11))))))
  have t14 : p 1572 = false := (Or.elim (step1178 p h) (fun l0 => (False.elim (bool_contra t12 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u8))))))
  have t15 : p 1482 = false := (Or.elim (step979 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t7 l1))) (fun r1 => (False.elim (bool_contra r1 t13))))))
  have t16 : p 1538 = false := (Or.elim (step1134 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t5 l1))) (fun r1 => (False.elim (bool_contra r1 t14))))))
  have t17 : p 15 = true := (Or.elim (step969 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u6))) (fun r1 => (False.elim (bool_contra r1 t15))))))
  have t18 : p 1533 = false := (Or.elim (step1063 p h) (fun l0 => (False.elim (bool_contra u9 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t16))))))
  have t19 : p 7 = false := (Or.elim (step35 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t9 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t17 l2))) (fun r2 => (False.elim (bool_contra u7 r2))))))))
  have t20 : p 1544 = true := (Or.elim (step1953 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t18))))
  have t21 : p 17 = true := (Or.elim (step1693 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t19))) (fun r1 => (False.elim (bool_contra t9 r1))))))
  have t22 : p 1548 = true := (Or.elim (step1078 p h) (fun l0 => (False.elim (bool_contra t20 l0))) (fun r0 => r0))
  have t23 : p 39 = false := (Or.elim (step66 p h) (fun l0 => (False.elim (bool_contra t21 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t9 l1))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra u5 r2))))))))
  have t24 : p 1562 = true := (Or.elim (step1104 p h) (fun l0 => (False.elim (bool_contra t22 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u3 l1))) (fun r1 => r1))))
  have t25 : p 1528 = true := (Or.elim (step1045 p h) (fun l0 => (False.elim (bool_contra l0 t23))) (fun r0 => r0))
  have t26 : p 1537 = false := (Or.elim (step1128 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t24 l1))) (fun r1 => (False.elim (bool_contra r1 t14))))))
  have t27 : p 1532 = true := (Or.elim (step1052 p h) (fun l0 => (False.elim (bool_contra t25 l0))) (fun r0 => r0))
  exact (Or.elim (step1062 p h) (fun l0 => (bool_contra u9 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t27 l1)) (fun r1 => (bool_contra r1 t26)))))

theorem step2067 (p : Nat → Bool) (h : Constraints p) : p 13 = true ∨ p 88 = false ∨ p 5 = false ∨ p 60 = false ∨ p 1555 = true ∨ p 1557 = false ∨ p 1500 = false ∨ p 73 = false ∨ p 18 = true ∨ p 61 = false ∨ p 62 = false ∨ p 75 = false ∨ p 1639 = true ∨ p 1595 = true ∨ p 1524 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 13 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 88 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 5 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 60 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 1555 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 1557 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))
  have u6 : p 1500 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))))
  have u7 : p 73 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))))
  have u8 : p 18 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))))))
  have u9 : p 61 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))))))
  have u10 : p 62 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))))))))
  have u11 : p 75 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))))))))
  have u12 : p 1639 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))))))))))
  have u13 : p 1595 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))))))))))
  have u14 : p 1524 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl)))))))))))))))
  have t0 : p 85 = true := (Or.elim (step1243 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u12))))
  have t1 : p 84 = true := (Or.elim (step1244 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u12))))
  have t2 : p 1536 = true := (Or.elim (step1061 p h) (fun l0 => (False.elim (bool_contra u14 l0))) (fun r0 => r0))
  have t3 : p 1571 = true := (Or.elim (step1678 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t2 l1))) (fun r1 => (False.elim (bool_contra u5 r1))))))
  have t4 : p 1512 = false := (Or.elim (step1182 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t3 l1))) (fun r1 => (False.elim (bool_contra r1 u13))))))
  have t5 : p 1477 = false := (Or.elim (step1026 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u6 l1))) (fun r1 => (False.elim (bool_contra r1 t4))))))
  have t6 : p 24 = false := (Or.elim (step2062 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u2 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u3 l2))) (fun r2 => (Or.elim r2 (fun l3 => (False.elim (bool_contra l3 t5))) (fun r3 => (Or.elim r3 (fun l4 => (False.elim (bool_contra u10 l4))) (fun r4 => (False.elim (bool_contra t1 r4))))))))))))
  have t7 : p 1494 = true := (Or.elim (step1918 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t0 l1))) (fun r1 => (False.elim (bool_contra r1 t6))))))
  have t8 : p 1561 = true := (Or.elim (step1099 p h) (fun l0 => (False.elim (bool_contra u5 l0))) (fun r0 => r0))
  have t9 : p 1481 = true := (Or.elim (step967 p h) (fun l0 => (False.elim (bool_contra l0 u8))) (fun r0 => r0))
  have t10 : p 19 = false := (Or.elim (step1682 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra u7 r0))))
  have t11 : p 1483 = true := (Or.elim (step971 p h) (fun l0 => (False.elim (bool_contra l0 t10))) (fun r0 => r0))
  have t12 : p 1486 = true := (Or.elim (step976 p h) (fun l0 => (False.elim (bool_contra t9 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t11 l1))) (fun r1 => r1))))
  have t13 : p 1468 = true := (Or.elim (step939 p h) (fun l0 => (False.elim (bool_contra l0 u0))) (fun r0 => r0))
  have t14 : p 1470 = true := (Or.elim (step942 p h) (fun l0 => (False.elim (bool_contra t13 l0))) (fun r0 => r0))
  have t15 : p 8 = true := (Or.elim (step2065 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u0))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t7 l2))) (fun r2 => (Or.elim r2 (fun l3 => (False.elim (bool_contra u5 l3))) (fun r3 => (Or.elim r3 (fun l4 => (False.elim (bool_contra u6 l4))) (fun r4 => (Or.elim r4 (fun l5 => (False.elim (bool_contra u7 l5))) (fun r5 => (Or.elim r5 (fun l6 => (False.elim (bool_contra l6 u8))) (fun r6 => (Or.elim r6 (fun l7 => (False.elim (bool_contra u9 l7))) (fun r7 => (Or.elim r7 (fun l8 => (False.elim (bool_contra u10 l8))) (fun r8 => (Or.elim r8 (fun l9 => (False.elim (bool_contra t1 l9))) (fun r9 => (Or.elim r9 (fun l10 => (False.elim (bool_contra l10 u13))) (fun r10 => (False.elim (bool_contra u14 r10))))))))))))))))))))))))
  have t16 : p 6 = false := (Or.elim (step17 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t15 l2))) (fun r2 => (False.elim (bool_contra u3 r2))))))))
  have t17 : p 1461 = true := (Or.elim (step928 p h) (fun l0 => (False.elim (bool_contra l0 t16))) (fun r0 => r0))
  have t18 : p 1463 = true := (Or.elim (step931 p h) (fun l0 => (False.elim (bool_contra t17 l0))) (fun r0 => r0))
  have t19 : p 1462 = false := (Or.elim (step2066 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t14 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t7 l2))) (fun r2 => (Or.elim r2 (fun l3 => (False.elim (bool_contra u5 l3))) (fun r3 => (Or.elim r3 (fun l4 => (False.elim (bool_contra u6 l4))) (fun r4 => (Or.elim r4 (fun l5 => (False.elim (bool_contra u7 l5))) (fun r5 => (Or.elim r5 (fun l6 => (False.elim (bool_contra l6 u8))) (fun r6 => (Or.elim r6 (fun l7 => (False.elim (bool_contra u9 l7))) (fun r7 => (Or.elim r7 (fun l8 => (False.elim (bool_contra l8 u13))) (fun r8 => (False.elim (bool_contra u14 r8))))))))))))))))))))
  have t20 : p 4 = true := (Or.elim (step930 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t16))) (fun r1 => (False.elim (bool_contra r1 t19))))))
  have t21 : p 57 = false := (Or.elim (step209 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t20 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u10 l2))) (fun r2 => (False.elim (bool_contra t1 r2))))))))
  have t22 : p 63 = true := (Or.elim (step1764 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t21))) (fun r1 => (False.elim (bool_contra u10 r1))))))
  have t23 : p 1471 = true := (Or.elim (step1963 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t20 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra l2 u4))) (fun r2 => (Or.elim r2 (fun l3 => (False.elim (bool_contra u11 l3))) (fun r3 => (Or.elim r3 (fun l4 => (False.elim (bool_contra t13 l4))) (fun r4 => (False.elim (bool_contra t22 r4))))))))))))
  have t24 : p 1464 = false := (Or.elim (step961 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t23 l1))) (fun r1 => (False.elim (bool_contra r1 t5))))))
  have t25 : p 1476 = true := (Or.elim (step956 p h) (fun l0 => (False.elim (bool_contra t18 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t23 l1))) (fun r1 => r1))))
  have t26 : p 26 = false := (Or.elim (step1928 p h) (fun l0 => (False.elim (bool_contra u9 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u1 l1))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra r2 t24))))))))
  have t27 : p 2 = true := (Or.elim (step934 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t17 l1))) (fun r1 => (False.elim (bool_contra r1 t24))))))
  have t28 : p 1501 = false := (Or.elim (step1020 p h) (fun l0 => (False.elim (bool_contra t25 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t4))))))
  have t29 : p 1511 = true := (Or.elim (step1019 p h) (fun l0 => (False.elim (bool_contra t25 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u6 l1))) (fun r1 => r1))))
  have t30 : p 1491 = true := (Or.elim (step985 p h) (fun l0 => (False.elim (bool_contra l0 t26))) (fun r0 => r0))
  have t31 : p 1495 = false := (Or.elim (step1003 p h) (fun l0 => (False.elim (bool_contra t12 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t28))))))
  have t32 : p 1487 = false := (Or.elim (step1006 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t7 l1))) (fun r1 => (False.elim (bool_contra r1 t28))))))
  have t33 : p 1572 = false := (Or.elim (step1178 p h) (fun l0 => (False.elim (bool_contra t29 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u13))))))
  have t34 : p 1490 = false := (Or.elim (step993 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t30 l1))) (fun r1 => (False.elim (bool_contra r1 t31))))))
  have t35 : p 1482 = false := (Or.elim (step979 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t11 l1))) (fun r1 => (False.elim (bool_contra r1 t32))))))
  have t36 : p 1538 = false := (Or.elim (step1134 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t8 l1))) (fun r1 => (False.elim (bool_contra r1 t33))))))
  have t37 : p 23 = true := (Or.elim (step983 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t6))) (fun r1 => (False.elim (bool_contra r1 t34))))))
  have t38 : p 15 = true := (Or.elim (step969 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u8))) (fun r1 => (False.elim (bool_contra r1 t35))))))
  have t39 : p 1533 = false := (Or.elim (step1063 p h) (fun l0 => (False.elim (bool_contra u14 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t36))))))
  have t40 : p 22 = true := (Or.elim (step1597 p h) (fun l0 => (False.elim (bool_contra t37 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u12))))))
  have t41 : p 7 = false := (Or.elim (step35 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t27 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t38 l2))) (fun r2 => (False.elim (bool_contra u9 r2))))))))
  have t42 : p 42 = false := (Or.elim (step80 p h) (fun l0 => (False.elim (bool_contra t40 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t37 l1))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra t0 r2))))))))
  have t43 : p 17 = true := (Or.elim (step1693 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t41))) (fun r1 => (False.elim (bool_contra t27 r1))))))
  have t44 : p 1530 = true := (Or.elim (step1048 p h) (fun l0 => (False.elim (bool_contra l0 t42))) (fun r0 => r0))
  have t45 : p 39 = false := (Or.elim (step66 p h) (fun l0 => (False.elim (bool_contra t43 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t27 l1))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra u7 r2))))))))
  have t46 : p 1528 = false := (Or.elim (step1053 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t44 l1))) (fun r1 => (False.elim (bool_contra r1 t39))))))
  exact (Or.elim (step1045 p h) (fun l0 => (bool_contra l0 t45)) (fun r0 => (bool_contra r0 t46)))

end Dfs112FirstBoolean
