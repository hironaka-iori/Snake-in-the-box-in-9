import Dfs112FirstBooleanPart0000
namespace Dfs112FirstBoolean
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem step1588 (p : Nat → Bool) (h : Constraints p) : p 93 = false ∨ p 106 = true ∨ p 103 = true ∨ p 104 = false ∨ p 113 = false ∨ p 21 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 93 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 106 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 103 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 104 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 113 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 21 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl))))))
  have t0 : p 226 = false := (step713 p h)
  have t1 : p 114 = false := (Or.elim (step616 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u0 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u3 l2))) (fun r2 => (False.elim (bool_contra u4 r2))))))))
  have t2 : p 81 = false := (Or.elim (step318 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u5 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u0 l2))) (fun r2 => (False.elim (bool_contra u3 r2))))))))
  exact (Or.elim (step556 p h) (fun l0 => (bool_contra u3 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 t2)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u2)) (fun r3 => (Or.elim r3 (fun l4 => (bool_contra l4 u1)) (fun r4 => (bool_contra r4 t1)))))))))))

theorem step1589 (p : Nat → Bool) (h : Constraints p) : p 1703 = true ∨ p 106 = true ∨ p 104 = false ∨ p 105 = false ∨ p 113 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1703 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 106 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 104 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 105 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 113 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr hl)))))
  have t0 : p 238 = false := (step719 p h)
  have t1 : p 117 = true := (Or.elim (step1378 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t2 : p 116 = true := (Or.elim (step1379 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t3 : p 115 = false := (Or.elim (step623 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u3 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u4 l2))) (fun r2 => (False.elim (bool_contra t1 r2))))))))
  have t4 : p 114 = false := (Or.elim (step619 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u2 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u4 l2))) (fun r2 => (False.elim (bool_contra t2 r2))))))))
  exact (Or.elim (step628 p h) (fun l0 => (bool_contra t2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u1)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 t4)) (fun r3 => (bool_contra r3 t3)))))))))

theorem step1590 (p : Nat → Bool) (h : Constraints p) : p 1656 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1656 = false := bool_false_of_not_true (fun hl => hc hl)
  have t0 : p 1647 = true := (step1585 p h)
  have t1 : p 1643 = true := (step1579 p h)
  have t2 : p 74 = true := (step1548 p h)
  have t3 : p 76 = true := (step289 p h)
  have t4 : p 1648 = false := (Or.elim (step1275 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t5 : p 1623 = false := (Or.elim (step1280 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t0 l1))) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t6 : p 1635 = false := (Or.elim (step1261 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t1 l1))) (fun r1 => (False.elim (bool_contra r1 t4))))))
  have t7 : p 1619 = false := (Or.elim (step1214 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t5))))
  have t8 : p 1631 = false := (Or.elim (step1240 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t6))))
  have t9 : p 1617 = false := (Or.elim (step1207 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t7))))
  have t10 : p 77 = true := (Or.elim (step1234 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t8))))
  have t11 : p 72 = true := (Or.elim (step1205 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t9))))
  exact (Or.elim (step278 p h) (fun l0 => (bool_contra t2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t11 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t3 l2)) (fun r2 => (bool_contra t10 r2)))))))

theorem step1591 (p : Nat → Bool) (h : Constraints p) : p 1691 = true ∨ p 1673 = false ∨ p 1676 = false ∨ p 111 = false ∨ p 93 = true ∨ p 98 = true ∨ p 1681 = false ∨ p 106 = true ∨ p 110 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1691 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1673 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1676 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 111 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 93 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 98 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))
  have u6 : p 1681 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))))
  have u7 : p 106 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))))
  have u8 : p 110 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl)))))))))
  have t0 : p 232 = false := (step716 p h)
  have t1 : p 1679 = true := (Or.elim (step1328 p h) (fun l0 => (False.elim (bool_contra l0 u5))) (fun r0 => r0))
  have t2 : p 1684 = true := (Or.elim (step1336 p h) (fun l0 => (False.elim (bool_contra t1 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u6 l1))) (fun r1 => r1))))
  have t3 : p 1685 = false := (Or.elim (step1353 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t4 : p 1677 = false := (Or.elim (step1357 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t2 l1))) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t5 : p 1680 = false := (Or.elim (step1339 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u6 l1))) (fun r1 => (False.elim (bool_contra r1 t3))))))
  have t6 : p 1672 = false := (Or.elim (step1325 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u1 l1))) (fun r1 => (False.elim (bool_contra r1 t4))))))
  have t7 : p 101 = true := (Or.elim (step1329 p h) (fun l0 => (False.elim (bool_contra l0 u5))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t5))))))
  have t8 : p 92 = true := (Or.elim (step1315 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u4))) (fun r1 => (False.elim (bool_contra r1 t6))))))
  have t9 : p 112 = false := (Or.elim (step606 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t8 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u8 l2))) (fun r2 => (False.elim (bool_contra u3 r2))))))))
  have t10 : p 89 = false := (Or.elim (step443 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t8 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t7 l2))) (fun r2 => (False.elim (bool_contra u8 r2))))))))
  exact (Or.elim (step598 p h) (fun l0 => (bool_contra u8 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 t10)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u7)) (fun r3 => (bool_contra r3 t9)))))))))

theorem step1592 (p : Nat → Bool) (h : Constraints p) : p 19 = false ∨ p 1618 = true ∨ p 1558 = true ∨ p 60 = true ∨ p 79 = false ∨ p 80 = false ∨ p 103 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 19 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 1618 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1558 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 60 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 79 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 80 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))
  have u6 : p 103 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl)))))))
  have t0 : p 201 = false := (step701 p h)
  have t1 : p 194 = false := (step698 p h)
  have t2 : p 75 = true := (Or.elim (step297 p h) (fun l0 => (False.elim (bool_contra u4 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => r1))))
  have t3 : p 59 = false := (Or.elim (step281 p h) (fun l0 => (False.elim (bool_contra t2 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u0 l1))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra u4 r2))))))))
  have t4 : p 73 = false := (Or.elim (step282 p h) (fun l0 => (False.elim (bool_contra t2 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u0 l1))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra u4 r2))))))))
  have t5 : p 1555 = true := (Or.elim (step1089 p h) (fun l0 => (False.elim (bool_contra l0 t3))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u3))) (fun r1 => r1))))
  have t6 : p 72 = true := (Or.elim (step1206 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t4))) (fun r1 => (False.elim (bool_contra r1 u1))))))
  have t7 : p 1552 = false := (Or.elim (step1094 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t5 l1))) (fun r1 => (False.elim (bool_contra r1 u2))))))
  have t8 : p 55 = true := (Or.elim (step271 p h) (fun l0 => (False.elim (bool_contra t6 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t1))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra r2 u6))))))))
  have t9 : p 56 = true := (Or.elim (step1084 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t7))))
  exact (Or.elim (step187 p h) (fun l0 => (bool_contra t8 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t9 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t6 l2)) (fun r2 => (bool_contra u5 r2)))))))

theorem step1593 (p : Nat → Bool) (h : Constraints p) : p 1494 = true ∨ p 1639 = true ∨ p 24 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1494 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1639 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 24 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 145 = false := (step672 p h)
  have t1 : p 84 = true := (Or.elim (step1244 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u1))))
  have t2 : p 85 = true := (Or.elim (step1243 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u1))))
  have t3 : p 1489 = true := (Or.elim (step981 p h) (fun l0 => (False.elim (bool_contra l0 u2))) (fun r0 => r0))
  have t4 : p 1490 = false := (Or.elim (step992 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t5 : p 1491 = false := (Or.elim (step990 p h) (fun l0 => (False.elim (bool_contra t3 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t6 : p 23 = true := (Or.elim (step983 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u2))) (fun r1 => (False.elim (bool_contra r1 t4))))))
  have t7 : p 27 = true := (Or.elim (step984 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t5))))
  have t8 : p 26 = true := (Or.elim (step985 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t5))))
  have t9 : p 28 = false := (Or.elim (step102 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t6 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t8 l2))) (fun r2 => (False.elim (bool_contra t7 r2))))))))
  have t10 : p 86 = false := (Or.elim (step369 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t6 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t1 l2))) (fun r2 => (False.elim (bool_contra t2 r2))))))))
  exact (Or.elim (step82 p h) (fun l0 => (bool_contra t6 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 t9)) (fun r2 => (bool_contra r2 t10)))))))

theorem step1594 (p : Nat → Bool) (h : Constraints p) : p 1524 = true ∨ p 42 = false ∨ p 85 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1524 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 42 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 85 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 155 = false := (step677 p h)
  have t1 : p 1522 = false := (Or.elim (step1039 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t2 : p 1520 = false := (Or.elim (step1041 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t3 : p 35 = true := (Or.elim (step1036 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t1))))
  have t4 : p 34 = true := (Or.elim (step1037 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t1))))
  have t5 : p 33 = true := (Or.elim (step1033 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t2))))
  have t6 : p 31 = true := (Or.elim (step1034 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t2))))
  have t7 : p 22 = false := (Or.elim (step81 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t5 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u1 l2))) (fun r2 => (False.elim (bool_contra u2 r2))))))))
  have t8 : p 37 = false := (Or.elim (step131 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t5 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t4 l2))) (fun r2 => (False.elim (bool_contra t3 r2))))))))
  have t9 : p 30 = false := (Or.elim (step109 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t6 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t5 l2))) (fun r2 => (False.elim (bool_contra t4 r2))))))))
  exact (Or.elim (step124 p h) (fun l0 => (bool_contra t5 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 t7)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 t9)) (fun r3 => (bool_contra r3 t8)))))))))

theorem step1595 (p : Nat → Bool) (h : Constraints p) : p 34 = false ∨ p 22 = true ∨ p 33 = false ∨ p 35 = false ∨ p 31 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 34 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 22 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 33 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 35 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 31 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr hl)))))
  have t0 : p 155 = false := (step677 p h)
  have t1 : p 37 = false := (Or.elim (step131 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u2 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u0 l2))) (fun r2 => (False.elim (bool_contra u3 r2))))))))
  have t2 : p 30 = false := (Or.elim (step109 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u4 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u2 l2))) (fun r2 => (False.elim (bool_contra u0 r2))))))))
  exact (Or.elim (step124 p h) (fun l0 => (bool_contra u2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u1)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 t2)) (fun r3 => (bool_contra r3 t1)))))))))

theorem step1596 (p : Nat → Bool) (h : Constraints p) : p 53 = false ∨ p 50 = false ∨ p 38 = true ∨ p 39 = false ∨ p 43 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 53 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 50 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 38 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 39 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 43 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr hl)))))
  have t0 : p 165 = false := (step683 p h)
  have t1 : p 44 = false := (Or.elim (step152 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u3 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u4 l2))) (fun r2 => (False.elim (bool_contra u0 r2))))))))
  have t2 : p 52 = false := (Or.elim (step175 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u4 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u1 l2))) (fun r2 => (False.elim (bool_contra u0 r2))))))))
  exact (Or.elim (step150 p h) (fun l0 => (bool_contra u4 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u2)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 t1)) (fun r3 => (bool_contra r3 t2)))))))))

theorem step1597 (p : Nat → Bool) (h : Constraints p) : p 23 = false ∨ p 22 = true ∨ p 1639 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 23 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 22 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1639 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 145 = false := (step672 p h)
  have t1 : p 84 = true := (Or.elim (step1244 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u2))))
  have t2 : p 85 = true := (Or.elim (step1243 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u2))))
  have t3 : p 86 = false := (Or.elim (step369 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u0 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t1 l2))) (fun r2 => (False.elim (bool_contra t2 r2))))))))
  exact (Or.elim (step83 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u1)) (fun r2 => (bool_contra r2 t3)))))))

theorem step1598 (p : Nat → Bool) (h : Constraints p) : p 1657 = true ∨ p 73 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1657 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 73 = false := bool_false_of_not_true (fun hl => hc (Or.inr hl))
  have t0 : p 1647 = true := (step1585 p h)
  have t1 : p 1643 = true := (step1579 p h)
  have t2 : p 74 = true := (step1548 p h)
  have t3 : p 76 = true := (step289 p h)
  have t4 : p 1617 = true := (Or.elim (step1204 p h) (fun l0 => (False.elim (bool_contra l0 u1))) (fun r0 => r0))
  have t5 : p 1619 = true := (Or.elim (step1207 p h) (fun l0 => (False.elim (bool_contra t4 l0))) (fun r0 => r0))
  have t6 : p 1623 = true := (Or.elim (step1214 p h) (fun l0 => (False.elim (bool_contra t5 l0))) (fun r0 => r0))
  have t7 : p 1624 = false := (Or.elim (step1286 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t0 l1))) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t8 : p 1648 = false := (Or.elim (step1281 p h) (fun l0 => (False.elim (bool_contra t6 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t9 : p 1620 = false := (Or.elim (step1215 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t7))))
  have t10 : p 1635 = false := (Or.elim (step1261 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t1 l1))) (fun r1 => (False.elim (bool_contra r1 t8))))))
  have t11 : p 1618 = false := (Or.elim (step1208 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t9))))
  have t12 : p 1631 = false := (Or.elim (step1240 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t10))))
  have t13 : p 72 = true := (Or.elim (step1206 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u1))) (fun r1 => (False.elim (bool_contra r1 t11))))))
  have t14 : p 77 = true := (Or.elim (step1234 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t12))))
  exact (Or.elim (step278 p h) (fun l0 => (bool_contra t2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t13 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t3 l2)) (fun r2 => (bool_contra t14 r2)))))))

theorem step1599 (p : Nat → Bool) (h : Constraints p) : p 101 = false ∨ p 1677 = true ∨ p 93 = true ∨ p 94 = false ∨ p 61 = false ∨ p 62 = false ∨ p 67 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 101 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 1677 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 93 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 94 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 61 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 62 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))
  have u6 : p 67 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl)))))))
  have t0 : p 183 = false := (step692 p h)
  have t1 : p 97 = false := (Or.elim (step480 p h) (fun l0 => (False.elim (bool_contra u3 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u6 l1))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra u0 r2))))))))
  have t2 : p 1673 = true := (Or.elim (step1316 p h) (fun l0 => (False.elim (bool_contra l0 t1))) (fun r0 => r0))
  have t3 : p 1672 = false := (Or.elim (step1325 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t2 l1))) (fun r1 => (False.elim (bool_contra r1 u1))))))
  have t4 : p 92 = true := (Or.elim (step1315 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u2))) (fun r1 => (False.elim (bool_contra r1 t3))))))
  have t5 : p 63 = false := (Or.elim (step238 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u4 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u5 l2))) (fun r2 => (False.elim (bool_contra t4 r2))))))))
  have t6 : p 89 = false := (Or.elim (step437 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u4 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t4 l2))) (fun r2 => (False.elim (bool_contra u0 r2))))))))
  exact (Or.elim (step228 p h) (fun l0 => (bool_contra u4 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 t5)) (fun r2 => (bool_contra r2 t6)))))))

theorem step1600 (p : Nat → Bool) (h : Constraints p) : p 1639 = true ∨ p 1673 = true ∨ p 80 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1639 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1673 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 80 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 217 = false := (step709 p h)
  have t1 : p 95 = true := (Or.elim (step1317 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u1))))
  have t2 : p 97 = true := (Or.elim (step1316 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u1))))
  have t3 : p 85 = true := (Or.elim (step1243 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t4 : p 84 = true := (Or.elim (step1244 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t5 : p 83 = false := (Or.elim (step338 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u2 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t3 l2))) (fun r2 => (False.elim (bool_contra t1 r2))))))))
  have t6 : p 96 = false := (Or.elim (step492 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t4 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t1 l2))) (fun r2 => (False.elim (bool_contra t2 r2))))))))
  exact (Or.elim (step487 p h) (fun l0 => (bool_contra t1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 t5)) (fun r2 => (bool_contra r2 t6)))))))

theorem step1601 (p : Nat → Bool) (h : Constraints p) : p 1673 = true ∨ p 1644 = true ∨ p 80 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1673 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1644 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 80 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 212 = false := (step706 p h)
  have t1 : p 95 = true := (Or.elim (step1317 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t2 : p 1639 = true := (Or.elim (step1600 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u0))) (fun r1 => (False.elim (bool_contra u2 r1))))))
  have t3 : p 1641 = false := (Or.elim (step1252 p h) (fun l0 => (False.elim (bool_contra t2 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u1))))))
  have t4 : p 90 = true := (Or.elim (step1246 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t3))))
  have t5 : p 88 = true := (Or.elim (step1247 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t3))))
  have t6 : p 83 = false := (Or.elim (step339 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u2 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t4 l2))) (fun r2 => (False.elim (bool_contra t1 r2))))))))
  have t7 : p 87 = true := (Or.elim (step446 p h) (fun l0 => (False.elim (bool_contra t4 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra l2 t6))) (fun r2 => r2))))))
  have t8 : p 91 = true := (Or.elim (step445 p h) (fun l0 => (False.elim (bool_contra t4 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra l2 t6))) (fun r2 => r2))))))
  exact (Or.elim (step1534 p h) (fun l0 => (bool_contra t7 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t5 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t4 l2)) (fun r2 => (bool_contra t8 r2)))))))

theorem step1602 (p : Nat → Bool) (h : Constraints p) : p 1641 = true ∨ p 1640 = true ∨ p 80 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1641 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1640 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 80 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 212 = false := (step706 p h)
  have t1 : p 90 = true := (Or.elim (step1246 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t2 : p 88 = true := (Or.elim (step1247 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t3 : p 87 = false := (Or.elim (step408 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u2 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t2 l2))) (fun r2 => (False.elim (bool_contra t1 r2))))))))
  have t4 : p 83 = true := (Or.elim (step446 p h) (fun l0 => (False.elim (bool_contra t1 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra r2 t3))))))))
  have t5 : p 84 = false := (Or.elim (step335 p h) (fun l0 => (False.elim (bool_contra t4 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u2 l1))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra t1 r2))))))))
  have t6 : p 85 = false := (Or.elim (step337 p h) (fun l0 => (False.elim (bool_contra t4 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u2 l1))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra t1 r2))))))))
  exact (Or.elim (step1245 p h) (fun l0 => (bool_contra l0 t5)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t6)) (fun r1 => (bool_contra r1 u1)))))

theorem step1603 (p : Nat → Bool) (h : Constraints p) : p 90 = false ∨ p 88 = false ∨ p 83 = true ∨ p 80 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 90 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 88 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 83 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 80 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 212 = false := (step706 p h)
  have t1 : p 87 = true := (Or.elim (step446 p h) (fun l0 => (False.elim (bool_contra u0 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra l2 u2))) (fun r2 => r2))))))
  exact (Or.elim (step408 p h) (fun l0 => (bool_contra t1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u3 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra u1 l2)) (fun r2 => (bool_contra u0 r2)))))))

theorem step1604 (p : Nat → Bool) (h : Constraints p) : p 1536 = true ∨ p 85 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1536 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 85 = true := bool_true_of_not_false (fun hl => hc (Or.inr hl))
  have t0 : p 1532 = false := (Or.elim (step1058 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t1 : p 1524 = false := (Or.elim (step1061 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t2 : p 1530 = false := (Or.elim (step1050 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t0))))
  have t3 : p 42 = false := (Or.elim (step1594 p h) (fun l0 => (False.elim (bool_contra l0 t1))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra u1 r1))))))
  exact (Or.elim (step1048 p h) (fun l0 => (bool_contra l0 t3)) (fun r0 => (bool_contra r0 t2)))

theorem step1605 (p : Nat → Bool) (h : Constraints p) : p 1524 = true ∨ p 1693 = true ∨ p 98 = true ∨ p 1671 = false ∨ p 94 = false ∨ p 67 = false ∨ p 1682 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1524 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1693 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 98 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 1671 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 94 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 67 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))
  have u6 : p 1682 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl)))))))
  have t0 : p 157 = false := (step679 p h)
  have t1 : p 1522 = false := (Or.elim (step1039 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t2 : p 1520 = false := (Or.elim (step1041 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t3 : p 35 = true := (Or.elim (step1036 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t1))))
  have t4 : p 34 = true := (Or.elim (step1037 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t1))))
  have t5 : p 33 = true := (Or.elim (step1033 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t2))))
  have t6 : p 31 = true := (Or.elim (step1034 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t2))))
  have t7 : p 37 = false := (Or.elim (step131 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t5 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t4 l2))) (fun r2 => (False.elim (bool_contra t3 r2))))))))
  have t8 : p 97 = false := (Or.elim (step468 p h) (fun l0 => (False.elim (bool_contra u4 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t6 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u5 l2))) (fun r2 => r2))))))
  have t9 : p 101 = false := (Or.elim (step469 p h) (fun l0 => (False.elim (bool_contra u4 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t6 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u5 l2))) (fun r2 => r2))))))
  have t10 : p 32 = true := (Or.elim (step128 p h) (fun l0 => (False.elim (bool_contra t3 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra r2 t7))))))))
  have t11 : p 1680 = true := (Or.elim (step1329 p h) (fun l0 => (False.elim (bool_contra l0 u2))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t9))) (fun r1 => r1))))
  have t12 : p 95 = false := (Or.elim (step119 p h) (fun l0 => (False.elim (bool_contra t10 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t5 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t3 l2))) (fun r2 => r2))))))
  have t13 : p 1686 = true := (Or.elim (step1340 p h) (fun l0 => (False.elim (bool_contra t11 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u6 l1))) (fun r1 => r1))))
  have t14 : p 1674 = true := (Or.elim (step1318 p h) (fun l0 => (False.elim (bool_contra l0 t12))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t8))) (fun r1 => r1))))
  have t15 : p 1677 = false := (Or.elim (step1359 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t13 l1))) (fun r1 => (False.elim (bool_contra r1 u1))))))
  exact (Or.elim (step1323 p h) (fun l0 => (bool_contra u3 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t14 l1)) (fun r1 => (bool_contra r1 t15)))))

theorem step1606 (p : Nat → Bool) (h : Constraints p) : p 1530 = false ∨ p 1524 = false ∨ p 1558 = false ∨ p 1573 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1530 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 1524 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1558 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 1573 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 171 = false := (step686 p h)
  have t1 : p 1562 = true := (Or.elim (step1100 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => r0))
  have t2 : p 1538 = false := (Or.elim (step1135 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t1 l1))) (fun r1 => (False.elim (bool_contra r1 u3))))))
  have t3 : p 1533 = false := (Or.elim (step1063 p h) (fun l0 => (False.elim (bool_contra u1 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t2))))))
  have t4 : p 1532 = true := (Or.elim (step1050 p h) (fun l0 => (False.elim (bool_contra u0 l0))) (fun r0 => r0))
  have t5 : p 1537 = true := (Or.elim (step1062 p h) (fun l0 => (False.elim (bool_contra u1 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t4 l1))) (fun r1 => r1))))
  have t6 : p 1528 = false := (Or.elim (step1053 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u0 l1))) (fun r1 => (False.elim (bool_contra r1 t3))))))
  have t7 : p 1563 = false := (Or.elim (step1129 p h) (fun l0 => (False.elim (bool_contra t5 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u3))))))
  have t8 : p 41 = true := (Or.elim (step1044 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t6))))
  have t9 : p 1548 = false := (Or.elim (step1105 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u2 l1))) (fun r1 => (False.elim (bool_contra r1 t7))))))
  have t10 : p 1546 = false := (Or.elim (step1076 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t9))))
  have t11 : p 1544 = false := (Or.elim (step1078 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t9))))
  have t12 : p 49 = true := (Or.elim (step1074 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t10))))
  have t13 : p 47 = true := (Or.elim (step1070 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t11))))
  have t14 : p 48 = true := (Or.elim (step166 p h) (fun l0 => (False.elim (bool_contra t12 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => r1))))
  exact (Or.elim (step163 p h) (fun l0 => (bool_contra t14 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t8 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t13 l2)) (fun r2 => (bool_contra t12 r2)))))))

theorem step1607 (p : Nat → Bool) (h : Constraints p) : p 1623 = true ∨ p 1636 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1623 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1636 = false := bool_false_of_not_true (fun hl => hc (Or.inr hl))
  have t0 : p 74 = true := (step1548 p h)
  have t1 : p 76 = true := (step289 p h)
  have t2 : p 186 = false := (step694 p h)
  have t3 : p 1619 = false := (Or.elim (step1214 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t4 : p 1611 = false := (Or.elim (step1218 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t5 : p 1617 = false := (Or.elim (step1207 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t3))))
  have t6 : p 1615 = false := (Or.elim (step1209 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t3))))
  have t7 : p 1609 = false := (Or.elim (step1193 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t4))))
  have t8 : p 72 = true := (Or.elim (step1205 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t5))))
  have t9 : p 68 = true := (Or.elim (step1202 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t6))))
  have t10 : p 67 = true := (Or.elim (step1190 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t7))))
  have t11 : p 64 = true := (Or.elim (step1191 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t7))))
  have t12 : p 77 = false := (Or.elim (step278 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t8 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t1 l2))) (fun r2 => r2))))))
  have t13 : p 66 = false := (Or.elim (step251 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t11 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t10 l2))) (fun r2 => (False.elim (bool_contra t9 r2))))))))
  have t14 : p 1631 = true := (Or.elim (step1234 p h) (fun l0 => (False.elim (bool_contra l0 t12))) (fun r0 => r0))
  have t15 : p 55 = true := (Or.elim (step243 p h) (fun l0 => (False.elim (bool_contra t11 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t2))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra r2 t13))))))))
  have t16 : p 1633 = false := (Or.elim (step1241 p h) (fun l0 => (False.elim (bool_contra t14 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u1))))))
  have t17 : p 80 = false := (Or.elim (step191 p h) (fun l0 => (False.elim (bool_contra t15 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t11 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t8 l2))) (fun r2 => r2))))))
  exact (Or.elim (step1235 p h) (fun l0 => (bool_contra l0 t17)) (fun r0 => (bool_contra r0 t16)))

theorem step1608 (p : Nat → Bool) (h : Constraints p) : p 5 = true ∨ p 8 = true ∨ p 14 = false ∨ p 7 = true ∨ p 6 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 5 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 8 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 14 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 7 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 6 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr hl)))))
  have t0 : p 135 = false := (step667 p h)
  have t1 : p 128 = false := (step663 p h)
  have t2 : p 270 = false := (step1565 p h)
  have t3 : p 13 = false := (Or.elim (step56 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t4 : p 9 = true := (Or.elim (step27 p h) (fun l0 => (False.elim (bool_contra u4 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra l2 u0))) (fun r2 => (Or.elim r2 (fun l3 => (False.elim (bool_contra l3 u3))) (fun r3 => r3))))))))
  have t5 : p 136 = true := (Or.elim (step58 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t3))))))
  have t6 : p 131 = true := (Or.elim (step45 p h) (fun l0 => (False.elim (bool_contra t4 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u1))))))
  have t7 : p 265 = true := (Or.elim (step738 p h) (fun l0 => (False.elim (bool_contra t5 l0))) (fun r0 => r0))
  have t8 : p 257 = true := (Or.elim (step734 p h) (fun l0 => (False.elim (bool_contra t6 l0))) (fun r0 => r0))
  have t9 : p 267 = true := (Or.elim (step739 p h) (fun l0 => (False.elim (bool_contra t7 l0))) (fun r0 => r0))
  have t10 : p 261 = true := (Or.elim (step737 p h) (fun l0 => (False.elim (bool_contra t8 l0))) (fun r0 => r0))
  exact (Or.elim (step742 p h) (fun l0 => (bool_contra t10 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t9 l1)) (fun r1 => (bool_contra r1 t2)))))

theorem step1609 (p : Nat → Bool) (h : Constraints p) : p 12 = false ∨ p 4 = false ∨ p 10 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 12 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 4 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 10 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 134 = false := (step666 p h)
  have t1 : p 11 = true := (Or.elim (step54 p h) (fun l0 => (False.elim (bool_contra u0 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => r1))))
  exact (Or.elim (step49 p h) (fun l0 => (bool_contra t1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u1 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra u2 l2)) (fun r2 => (bool_contra u0 r2)))))))

theorem step1610 (p : Nat → Bool) (h : Constraints p) : p 95 = true ∨ p 1689 = true ∨ p 85 = false ∨ p 84 = false ∨ p 92 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 95 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1689 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 85 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 84 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 92 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr hl)))))
  have t0 : p 219 = false := (step710 p h)
  have t1 : p 1671 = true := (Or.elim (step1314 p h) (fun l0 => (False.elim (bool_contra l0 u4))) (fun r0 => r0))
  have t2 : p 1677 = false := (Or.elim (step1355 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u1))))
  have t3 : p 1674 = false := (Or.elim (step1323 p h) (fun l0 => (False.elim (bool_contra t1 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t2))))))
  have t4 : p 1673 = true := (Or.elim (step1317 p h) (fun l0 => (False.elim (bool_contra l0 u0))) (fun r0 => r0))
  have t5 : p 97 = true := (Or.elim (step1318 p h) (fun l0 => (False.elim (bool_contra l0 u0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t3))))))
  have t6 : p 1676 = true := (Or.elim (step1322 p h) (fun l0 => (False.elim (bool_contra t1 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t4 l1))) (fun r1 => r1))))
  have t7 : p 1672 = false := (Or.elim (step1325 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t4 l1))) (fun r1 => (False.elim (bool_contra r1 t2))))))
  have t8 : p 86 = false := (Or.elim (step379 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u3 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u2 l2))) (fun r2 => (False.elim (bool_contra t5 r2))))))))
  have t9 : p 1683 = false := (Or.elim (step1351 p h) (fun l0 => (False.elim (bool_contra t6 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u1))))))
  have t10 : p 93 = true := (Or.elim (step1315 p h) (fun l0 => (False.elim (bool_contra l0 u4))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t7))))))
  have t11 : p 1679 = false := (Or.elim (step1335 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t9))))
  have t12 : p 96 = false := (Or.elim (step491 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u3 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t10 l2))) (fun r2 => (False.elim (bool_contra t5 r2))))))))
  have t13 : p 101 = true := (Or.elim (step1327 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t11))))
  have t14 : p 94 = true := (Or.elim (step498 p h) (fun l0 => (False.elim (bool_contra t5 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra l2 t8))) (fun r2 => (Or.elim r2 (fun l3 => l3) (fun r3 => (False.elim (bool_contra r3 t12))))))))))
  exact (Or.elim (step483 p h) (fun l0 => (bool_contra t14 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t10 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t5 l2)) (fun r2 => (bool_contra t13 r2)))))))

theorem step1611 (p : Nat → Bool) (h : Constraints p) : p 1689 = true ∨ p 85 = false ∨ p 84 = false ∨ p 92 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1689 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 85 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 84 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 92 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 217 = false := (step709 p h)
  have t1 : p 1677 = false := (Or.elim (step1355 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t2 : p 95 = true := (Or.elim (step1610 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u0))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u1 l2))) (fun r2 => (Or.elim r2 (fun l3 => (False.elim (bool_contra u2 l3))) (fun r3 => (False.elim (bool_contra r3 u3))))))))))
  have t3 : p 83 = false := (Or.elim (step341 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u2 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u1 l2))) (fun r2 => (False.elim (bool_contra t2 r2))))))))
  have t4 : p 96 = true := (Or.elim (step487 p h) (fun l0 => (False.elim (bool_contra t2 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra l2 t3))) (fun r2 => r2))))))
  have t5 : p 93 = false := (Or.elim (step490 p h) (fun l0 => (False.elim (bool_contra t4 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u2 l1))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra t2 r2))))))))
  have t6 : p 97 = false := (Or.elim (step492 p h) (fun l0 => (False.elim (bool_contra t4 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u2 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t2 l2))) (fun r2 => r2))))))
  have t7 : p 1672 = true := (Or.elim (step1315 p h) (fun l0 => (False.elim (bool_contra l0 u3))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t5))) (fun r1 => r1))))
  have t8 : p 1673 = true := (Or.elim (step1316 p h) (fun l0 => (False.elim (bool_contra l0 t6))) (fun r0 => r0))
  exact (Or.elim (step1325 p h) (fun l0 => (bool_contra t7 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t8 l1)) (fun r1 => (bool_contra r1 t1)))))

theorem step1612 (p : Nat → Bool) (h : Constraints p) : p 45 = false ∨ p 42 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 45 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 42 = true := bool_true_of_not_false (fun hl => hc (Or.inr hl))
  have t0 : p 167 = false := (step684 p h)
  have t1 : p 46 = true := (Or.elim (step156 p h) (fun l0 => (False.elim (bool_contra u0 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => r1))))
  have t2 : p 40 = true := (Or.elim (step157 p h) (fun l0 => (False.elim (bool_contra u0 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => r1))))
  exact (Or.elim (step1519 p h) (fun l0 => (bool_contra t2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u1 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra u0 l2)) (fun r2 => (bool_contra t1 r2)))))))

theorem step1613 (p : Nat → Bool) (h : Constraints p) : p 1708 = true ∨ p 116 = true ∨ p 98 = false ∨ p 50 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1708 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 116 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 98 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 50 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 241 = false := (step721 p h)
  have t1 : p 1703 = true := (Or.elim (step1379 p h) (fun l0 => (False.elim (bool_contra l0 u1))) (fun r0 => r0))
  have t2 : p 1704 = false := (Or.elim (step1389 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t3 : p 1705 = false := (Or.elim (step1387 p h) (fun l0 => (False.elim (bool_contra t1 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t4 : p 117 = true := (Or.elim (step1380 p h) (fun l0 => (False.elim (bool_contra l0 u1))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t2))))))
  have t5 : p 122 = true := (Or.elim (step1381 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t3))))
  have t6 : p 119 = true := (Or.elim (step1382 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t3))))
  have t7 : p 121 = false := (Or.elim (step654 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t4 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t6 l2))) (fun r2 => (False.elim (bool_contra t5 r2))))))))
  have t8 : p 118 = false := (Or.elim (step638 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u3 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u2 l2))) (fun r2 => (False.elim (bool_contra t6 r2))))))))
  exact (Or.elim (step649 p h) (fun l0 => (bool_contra t6 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 t8)) (fun r2 => (bool_contra r2 t7)))))))

theorem step1614 (p : Nat → Bool) (h : Constraints p) : p 1683 = true ∨ p 1713 = true ∨ p 67 = false ∨ p 50 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1683 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1713 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 67 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 50 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 238 = false := (step719 p h)
  have t1 : p 241 = false := (step721 p h)
  have t2 : p 1681 = false := (Or.elim (step1333 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t3 : p 1679 = false := (Or.elim (step1335 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t4 : p 1699 = true := (Or.elim (step1587 p h) (fun l0 => (False.elim (bool_contra l0 u0))) (fun r0 => r0))
  have t5 : p 105 = true := (Or.elim (step1330 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t2))))
  have t6 : p 104 = true := (Or.elim (step1331 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t2))))
  have t7 : p 101 = true := (Or.elim (step1327 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t3))))
  have t8 : p 98 = true := (Or.elim (step1328 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t3))))
  have t9 : p 1708 = false := (Or.elim (step1398 p h) (fun l0 => (False.elim (bool_contra t4 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u1))))))
  have t10 : p 116 = true := (Or.elim (step1613 p h) (fun l0 => (False.elim (bool_contra l0 t9))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t8 l2))) (fun r2 => (False.elim (bool_contra u3 r2))))))))
  have t11 : p 94 = false := (Or.elim (step482 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u2 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t7 l2))) (fun r2 => (False.elim (bool_contra t10 r2))))))))
  have t12 : p 106 = false := (Or.elim (step580 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t6 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t5 l2))) (fun r2 => (False.elim (bool_contra t10 r2))))))))
  have t13 : p 115 = true := (Or.elim (step630 p h) (fun l0 => (False.elim (bool_contra t10 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra l2 t11))) (fun r2 => (Or.elim r2 (fun l3 => (False.elim (bool_contra l3 t12))) (fun r3 => r3))))))))
  have t14 : p 113 = false := (Or.elim (step622 p h) (fun l0 => (False.elim (bool_contra t13 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t5 l1))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra t10 r2))))))))
  have t15 : p 117 = false := (Or.elim (step624 p h) (fun l0 => (False.elim (bool_contra t13 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t5 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t10 l2))) (fun r2 => r2))))))
  have t16 : p 1703 = true := (Or.elim (step1378 p h) (fun l0 => (False.elim (bool_contra l0 t15))) (fun r0 => r0))
  have t17 : p 1707 = true := (Or.elim (step1386 p h) (fun l0 => (False.elim (bool_contra t16 l0))) (fun r0 => r0))
  have t18 : p 1705 = false := (Or.elim (step1387 p h) (fun l0 => (False.elim (bool_contra t16 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t9))))))
  have t19 : p 1700 = false := (Or.elim (step1402 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t17 l1))) (fun r1 => (False.elim (bool_contra r1 u1))))))
  have t20 : p 122 = true := (Or.elim (step1381 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t18))))
  have t21 : p 119 = true := (Or.elim (step1382 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t18))))
  have t22 : p 1698 = false := (Or.elim (step1371 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t19))))
  have t23 : p 118 = false := (Or.elim (step638 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u3 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t8 l2))) (fun r2 => (False.elim (bool_contra t21 r2))))))))
  have t24 : p 111 = true := (Or.elim (step1369 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t14))) (fun r1 => (False.elim (bool_contra r1 t22))))))
  have t25 : p 120 = true := (Or.elim (step650 p h) (fun l0 => (False.elim (bool_contra t21 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra l2 t23))) (fun r2 => r2))))))
  exact (Or.elim (step651 p h) (fun l0 => (bool_contra t25 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t24 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t21 l2)) (fun r2 => (bool_contra t20 r2)))))))

theorem step1615 (p : Nat → Bool) (h : Constraints p) : p 118 = true ∨ p 119 = false ∨ p 122 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 118 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 119 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 122 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 241 = false := (step721 p h)
  have t1 : p 121 = true := (Or.elim (step649 p h) (fun l0 => (False.elim (bool_contra u1 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra l2 u0))) (fun r2 => r2))))))
  have t2 : p 120 = true := (Or.elim (step650 p h) (fun l0 => (False.elim (bool_contra u1 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra l2 u0))) (fun r2 => r2))))))
  exact (Or.elim (step1547 p h) (fun l0 => (bool_contra u1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t2 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t1 l2)) (fun r2 => (bool_contra u2 r2)))))))

theorem step1616 (p : Nat → Bool) (h : Constraints p) : p 98 = false ∨ p 1700 = true ∨ p 118 = false ∨ p 119 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 98 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 1700 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 118 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 119 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 109 = false := (Or.elim (step643 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u0 l1))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra u3 r2))))))))
  have t1 : p 113 = false := (Or.elim (step644 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u0 l1))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra u3 r2))))))))
  have t2 : p 1695 = true := (Or.elim (step1365 p h) (fun l0 => (False.elim (bool_contra l0 t0))) (fun r0 => r0))
  have t3 : p 1697 = true := (Or.elim (step1367 p h) (fun l0 => (False.elim (bool_contra l0 t1))) (fun r0 => r0))
  exact (Or.elim (step1373 p h) (fun l0 => (bool_contra t2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t3 l1)) (fun r1 => (bool_contra r1 u1)))))

theorem step1617 (p : Nat → Bool) (h : Constraints p) : p 113 = true ∨ p 1700 = true ∨ p 119 = false ∨ p 122 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 113 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1700 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 119 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 122 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 233 = false := (step717 p h)
  have t1 : p 1698 = false := (Or.elim (step1371 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u1))))
  have t2 : p 1697 = true := (Or.elim (step1367 p h) (fun l0 => (False.elim (bool_contra l0 u0))) (fun r0 => r0))
  have t3 : p 111 = true := (Or.elim (step1369 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u0))) (fun r1 => (False.elim (bool_contra r1 t1))))))
  have t4 : p 1695 = false := (Or.elim (step1373 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t2 l1))) (fun r1 => (False.elim (bool_contra r1 u1))))))
  have t5 : p 120 = false := (Or.elim (step651 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t3 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u2 l2))) (fun r2 => (False.elim (bool_contra u3 r2))))))))
  have t6 : p 110 = true := (Or.elim (step1364 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t4))))
  have t7 : p 112 = true := (Or.elim (step603 p h) (fun l0 => (False.elim (bool_contra t3 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra r2 t5))))))))
  exact (Or.elim (step609 p h) (fun l0 => (bool_contra t7 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t6 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t3 l2)) (fun r2 => (bool_contra u3 r2)))))))

theorem step1618 (p : Nat → Bool) (h : Constraints p) : p 1700 = true ∨ p 119 = false ∨ p 122 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1700 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 119 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 122 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 233 = false := (step717 p h)
  have t1 : p 118 = true := (Or.elim (step1615 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u1 l1))) (fun r1 => (False.elim (bool_contra u2 r1))))))
  have t2 : p 1696 = false := (Or.elim (step1375 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t3 : p 113 = true := (Or.elim (step1617 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u0))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u1 l2))) (fun r2 => (False.elim (bool_contra u2 r2))))))))
  have t4 : p 109 = false := (Or.elim (step645 p h) (fun l0 => (False.elim (bool_contra t1 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t3 l2))) (fun r2 => (False.elim (bool_contra u1 r2))))))))
  have t5 : p 1695 = true := (Or.elim (step1365 p h) (fun l0 => (False.elim (bool_contra l0 t4))) (fun r0 => r0))
  have t6 : p 110 = true := (Or.elim (step1366 p h) (fun l0 => (False.elim (bool_contra l0 t4))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t2))))))
  have t7 : p 1697 = false := (Or.elim (step1373 p h) (fun l0 => (False.elim (bool_contra t5 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t8 : p 111 = true := (Or.elim (step1368 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t7))))
  have t9 : p 120 = false := (Or.elim (step651 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t8 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u1 l2))) (fun r2 => (False.elim (bool_contra u2 r2))))))))
  have t10 : p 112 = false := (Or.elim (step609 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t6 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t8 l2))) (fun r2 => (False.elim (bool_contra u2 r2))))))))
  exact (Or.elim (step603 p h) (fun l0 => (bool_contra t8 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 t10)) (fun r2 => (bool_contra r2 t9)))))))

theorem step1619 (p : Nat → Bool) (h : Constraints p) : p 1675 = true ∨ p 101 = false ∨ p 94 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1675 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 101 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 94 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 219 = false := (step710 p h)
  have t1 : p 1673 = false := (Or.elim (step1319 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t2 : p 1671 = false := (Or.elim (step1321 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t3 : p 97 = true := (Or.elim (step1316 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t1))))
  have t4 : p 95 = true := (Or.elim (step1317 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t1))))
  have t5 : p 93 = true := (Or.elim (step1313 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t2))))
  have t6 : p 92 = true := (Or.elim (step1314 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t2))))
  have t7 : p 102 = false := (Or.elim (step523 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t6 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t3 l2))) (fun r2 => (False.elim (bool_contra u1 r2))))))))
  have t8 : p 96 = false := (Or.elim (step493 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t5 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t4 l2))) (fun r2 => (False.elim (bool_contra t3 r2))))))))
  exact (Or.elim (step495 p h) (fun l0 => (bool_contra t3 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u2)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 t8)) (fun r3 => (bool_contra r3 t7)))))))))

theorem step1620 (p : Nat → Bool) (h : Constraints p) : p 106 = false ∨ p 110 = false ∨ p 1682 = true ∨ p 116 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 106 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 110 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1682 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 116 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 104 = false := (Or.elim (step581 p h) (fun l0 => (False.elim (bool_contra u0 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u1 l2))) (fun r2 => (False.elim (bool_contra u3 r2))))))))
  have t1 : p 105 = false := (Or.elim (step582 p h) (fun l0 => (False.elim (bool_contra u0 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u1 l2))) (fun r2 => (False.elim (bool_contra u3 r2))))))))
  exact (Or.elim (step1332 p h) (fun l0 => (bool_contra l0 t0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t1)) (fun r1 => (bool_contra r1 u2)))))

theorem step1621 (p : Nat → Bool) (h : Constraints p) : p 1695 = true ∨ p 1684 = true ∨ p 1698 = true ∨ p 117 = false ∨ p 122 = false ∨ p 116 = false ∨ p 94 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1695 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1684 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1698 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 117 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 122 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 116 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))
  have u6 : p 94 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl)))))))
  have t0 : p 238 = false := (step719 p h)
  have t1 : p 233 = false := (step717 p h)
  have t2 : p 231 = false := (step715 p h)
  have t3 : p 1682 = false := (Or.elim (step1334 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u1))))
  have t4 : p 110 = true := (Or.elim (step1364 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t5 : p 109 = true := (Or.elim (step1365 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t6 : p 106 = false := (Or.elim (step1620 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t4 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra l2 t3))) (fun r2 => (False.elim (bool_contra u5 r2))))))))
  have t7 : p 115 = true := (Or.elim (step630 p h) (fun l0 => (False.elim (bool_contra u5 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra l2 u6))) (fun r2 => (Or.elim r2 (fun l3 => (False.elim (bool_contra l3 t6))) (fun r3 => r3))))))))
  have t8 : p 114 = true := (Or.elim (step631 p h) (fun l0 => (False.elim (bool_contra u5 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra l2 u6))) (fun r2 => (Or.elim r2 (fun l3 => (False.elim (bool_contra l3 t6))) (fun r3 => r3))))))))
  have t9 : p 105 = false := (Or.elim (step624 p h) (fun l0 => (False.elim (bool_contra t7 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u5 l2))) (fun r2 => (False.elim (bool_contra u3 r2))))))))
  have t10 : p 113 = false := (Or.elim (step625 p h) (fun l0 => (False.elim (bool_contra t7 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u5 l2))) (fun r2 => (False.elim (bool_contra u3 r2))))))))
  have t11 : p 1681 = true := (Or.elim (step1330 p h) (fun l0 => (False.elim (bool_contra l0 t9))) (fun r0 => r0))
  have t12 : p 104 = true := (Or.elim (step1332 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t9))) (fun r1 => (False.elim (bool_contra r1 t3))))))
  have t13 : p 111 = true := (Or.elim (step1369 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t10))) (fun r1 => (False.elim (bool_contra r1 u2))))))
  have t14 : p 1679 = false := (Or.elim (step1336 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t11 l1))) (fun r1 => (False.elim (bool_contra r1 u1))))))
  have t15 : p 112 = false := (Or.elim (step609 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t4 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t13 l2))) (fun r2 => (False.elim (bool_contra u4 r2))))))))
  have t16 : p 98 = true := (Or.elim (step1328 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t14))))
  have t17 : p 107 = true := (Or.elim (step605 p h) (fun l0 => (False.elim (bool_contra t13 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t1))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra r2 t15))))))))
  have t18 : p 103 = false := (Or.elim (step551 p h) (fun l0 => (False.elim (bool_contra t12 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t17 l2))) (fun r2 => (False.elim (bool_contra t8 r2))))))))
  have t19 : p 87 = true := (Or.elim (step595 p h) (fun l0 => (False.elim (bool_contra t5 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t2))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra r2 t18))))))))
  have t20 : p 118 = true := (Or.elim (step593 p h) (fun l0 => (False.elim (bool_contra t5 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t2))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra l2 t18))) (fun r2 => r2))))))
  exact (Or.elim (step1536 p h) (fun l0 => (bool_contra t19 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t16 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t5 l2)) (fun r2 => (bool_contra t20 r2)))))))

theorem step1622 (p : Nat → Bool) (h : Constraints p) : p 1684 = true ∨ p 117 = false ∨ p 1700 = true ∨ p 122 = false ∨ p 116 = false ∨ p 94 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1684 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 117 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1700 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 122 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 116 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 94 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl))))))
  have t0 : p 238 = false := (step719 p h)
  have t1 : p 231 = false := (step715 p h)
  have t2 : p 1696 = false := (Or.elim (step1375 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u2))))
  have t3 : p 1698 = false := (Or.elim (step1371 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u2))))
  have t4 : p 1682 = false := (Or.elim (step1334 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t5 : p 1695 = true := (Or.elim (step1621 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u0))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra l2 t3))) (fun r2 => (Or.elim r2 (fun l3 => (False.elim (bool_contra u1 l3))) (fun r3 => (Or.elim r3 (fun l4 => (False.elim (bool_contra u3 l4))) (fun r4 => (Or.elim r4 (fun l5 => (False.elim (bool_contra u4 l5))) (fun r5 => (False.elim (bool_contra r5 u5))))))))))))))
  have t6 : p 1697 = false := (Or.elim (step1373 p h) (fun l0 => (False.elim (bool_contra t5 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u2))))))
  have t7 : p 113 = true := (Or.elim (step1367 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t6))))
  have t8 : p 115 = false := (Or.elim (step625 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t7 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u4 l2))) (fun r2 => (False.elim (bool_contra u1 r2))))))))
  have t9 : p 106 = true := (Or.elim (step630 p h) (fun l0 => (False.elim (bool_contra u4 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra l2 u5))) (fun r2 => (Or.elim r2 (fun l3 => l3) (fun r3 => (False.elim (bool_contra r3 t8))))))))))
  have t10 : p 114 = true := (Or.elim (step629 p h) (fun l0 => (False.elim (bool_contra u4 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra l2 u5))) (fun r2 => (Or.elim r2 (fun l3 => l3) (fun r3 => (False.elim (bool_contra r3 t8))))))))))
  have t11 : p 110 = false := (Or.elim (step1620 p h) (fun l0 => (False.elim (bool_contra t9 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra l2 t4))) (fun r2 => (False.elim (bool_contra u4 r2))))))))
  have t12 : p 104 = false := (Or.elim (step619 p h) (fun l0 => (False.elim (bool_contra t10 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t7 l2))) (fun r2 => (False.elim (bool_contra u4 r2))))))))
  have t13 : p 109 = true := (Or.elim (step1366 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t11))) (fun r1 => (False.elim (bool_contra r1 t2))))))
  have t14 : p 1681 = true := (Or.elim (step1331 p h) (fun l0 => (False.elim (bool_contra l0 t12))) (fun r0 => r0))
  have t15 : p 105 = true := (Or.elim (step1332 p h) (fun l0 => (False.elim (bool_contra l0 t12))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t4))))))
  have t16 : p 1679 = false := (Or.elim (step1336 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t14 l1))) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t17 : p 103 = false := (Or.elim (step547 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t15 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t13 l2))) (fun r2 => (False.elim (bool_contra t7 r2))))))))
  have t18 : p 98 = true := (Or.elim (step1328 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t16))))
  have t19 : p 118 = true := (Or.elim (step593 p h) (fun l0 => (False.elim (bool_contra t13 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra l2 t17))) (fun r2 => r2))))))
  exact (Or.elim (step642 p h) (fun l0 => (bool_contra t19 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t18 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t13 l2)) (fun r2 => (bool_contra t7 r2)))))))

theorem step1623 (p : Nat → Bool) (h : Constraints p) : p 92 = true ∨ p 1676 = true ∨ p 122 = false ∨ p 101 = false ∨ p 94 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 92 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1676 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 122 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 101 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 94 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr hl)))))
  have t0 : p 219 = false := (step710 p h)
  have t1 : p 1672 = false := (Or.elim (step1324 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u1))))
  have t2 : p 1671 = true := (Or.elim (step1314 p h) (fun l0 => (False.elim (bool_contra l0 u0))) (fun r0 => r0))
  have t3 : p 1673 = false := (Or.elim (step1322 p h) (fun l0 => (False.elim (bool_contra t2 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u1))))))
  have t4 : p 93 = true := (Or.elim (step1315 p h) (fun l0 => (False.elim (bool_contra l0 u0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t1))))))
  have t5 : p 97 = true := (Or.elim (step1316 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t3))))
  have t6 : p 95 = true := (Or.elim (step1317 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t3))))
  have t7 : p 96 = false := (Or.elim (step493 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t4 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t6 l2))) (fun r2 => (False.elim (bool_contra t5 r2))))))))
  have t8 : p 102 = false := (Or.elim (step526 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t5 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u3 l2))) (fun r2 => (False.elim (bool_contra u2 r2))))))))
  exact (Or.elim (step495 p h) (fun l0 => (bool_contra t5 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u4)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 t7)) (fun r3 => (bool_contra r3 t8)))))))))

theorem step1624 (p : Nat → Bool) (h : Constraints p) : p 97 = false ∨ p 95 = false ∨ p 93 = false ∨ p 102 = true ∨ p 94 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 97 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 95 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 93 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 102 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 94 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr hl)))))
  have t0 : p 219 = false := (step710 p h)
  have t1 : p 96 = true := (Or.elim (step495 p h) (fun l0 => (False.elim (bool_contra u0 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra l2 u4))) (fun r2 => (Or.elim r2 (fun l3 => l3) (fun r3 => (False.elim (bool_contra r3 u3))))))))))
  exact (Or.elim (step493 p h) (fun l0 => (bool_contra t1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u2 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra u1 l2)) (fun r2 => (bool_contra u0 r2)))))))

theorem step1625 (p : Nat → Bool) (h : Constraints p) : p 113 = false ∨ p 93 = false ∨ p 117 = false ∨ p 116 = false ∨ p 94 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 113 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 93 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 117 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 116 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 94 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr hl)))))
  have t0 : p 238 = false := (step719 p h)
  have t1 : p 115 = false := (Or.elim (step625 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u0 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u3 l2))) (fun r2 => (False.elim (bool_contra u2 r2))))))))
  have t2 : p 114 = false := (Or.elim (step618 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u1 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u0 l2))) (fun r2 => (False.elim (bool_contra u3 r2))))))))
  exact (Or.elim (step629 p h) (fun l0 => (bool_contra u3 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u4)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 t2)) (fun r3 => (bool_contra r3 t1)))))))))

theorem step1626 (p : Nat → Bool) (h : Constraints p) : p 110 = false ∨ p 106 = false ∨ p 102 = true ∨ p 92 = false ∨ p 1685 = true ∨ p 116 = false ∨ p 101 = false ∨ p 94 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 110 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 106 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 102 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 92 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 1685 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 116 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))
  have u6 : p 101 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))))
  have u7 : p 94 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl))))))))
  have t0 : p 223 = false := (step712 p h)
  have t1 : p 89 = false := (Or.elim (step443 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u3 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u6 l2))) (fun r2 => (False.elim (bool_contra u0 r2))))))))
  have t2 : p 1682 = true := (Or.elim (step1620 p h) (fun l0 => (False.elim (bool_contra u1 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u0 l1))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra u5 r2))))))))
  have t3 : p 100 = true := (Or.elim (step520 p h) (fun l0 => (False.elim (bool_contra u6 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra l2 t1))) (fun r2 => (Or.elim r2 (fun l3 => (False.elim (bool_contra l3 u7))) (fun r3 => (Or.elim r3 (fun l4 => l4) (fun r4 => (False.elim (bool_contra r4 u2))))))))))))
  have t4 : p 99 = true := (Or.elim (step521 p h) (fun l0 => (False.elim (bool_contra u6 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra l2 t1))) (fun r2 => (Or.elim r2 (fun l3 => (False.elim (bool_contra l3 u7))) (fun r3 => (Or.elim r3 (fun l4 => l4) (fun r4 => (False.elim (bool_contra r4 u2))))))))))))
  have t5 : p 1679 = false := (Or.elim (step1337 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t2 l1))) (fun r1 => (False.elim (bool_contra r1 u4))))))
  have t6 : p 98 = false := (Or.elim (step1541 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t4 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t3 l2))) (fun r2 => (False.elim (bool_contra u6 r2))))))))
  exact (Or.elim (step1328 p h) (fun l0 => (bool_contra l0 t6)) (fun r0 => (bool_contra r0 t5)))

theorem step1627 (p : Nat → Bool) (h : Constraints p) : p 1524 = true ∨ p 22 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1524 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 22 = false := bool_false_of_not_true (fun hl => hc (Or.inr hl))
  have t0 : p 1522 = false := (Or.elim (step1039 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t1 : p 1520 = false := (Or.elim (step1041 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t2 : p 35 = true := (Or.elim (step1036 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t0))))
  have t3 : p 34 = true := (Or.elim (step1037 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t0))))
  have t4 : p 33 = true := (Or.elim (step1033 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t1))))
  have t5 : p 31 = true := (Or.elim (step1034 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t1))))
  exact (Or.elim (step1595 p h) (fun l0 => (bool_contra t3 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 u1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t4 l2)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra t2 l3)) (fun r3 => (bool_contra t5 r3)))))))))

end Dfs112FirstBoolean
