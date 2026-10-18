import Dfs112FirstBooleanPart0146
namespace Dfs112FirstBoolean
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem step7428 (p : Nat → Bool) (h : Constraints p) : p 1609 = true ∨ p 19 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1609 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 19 = false := bool_false_of_not_true (fun hl => hc (Or.inr hl))
  have t0 : p 87 = false := (step7415 p h)
  have t1 : p 80 = true := (step7392 p h)
  have t2 : p 59 = true := (step7354 p h)
  have t3 : p 85 = true := (step7423 p h)
  have t4 : p 18 = true := (step7284 p h)
  have t5 : p 1617 = true := (step7289 p h)
  have t6 : p 1611 = true := (step7427 p h)
  have t7 : p 1648 = true := (step7294 p h)
  have t8 : p 1725 = true := (step7402 p h)
  have t9 : p 1592 = true := (Or.elim (step7408 p h) (fun l0 => (False.elim (bool_contra l0 u1))) (fun r0 => r0))
  have t10 : p 1748 = false := (Or.elim (step1896 p h) (fun l0 => (False.elim (bool_contra t9 l0))) (fun r0 => r0))
  have t11 : p 1661 = false := (Or.elim (step1479 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t8 l1))) (fun r1 => (False.elim (bool_contra r1 t10))))))
  have t12 : p 56 = false := (Or.elim (step5046 p h) (fun l0 => (False.elim (bool_contra t8 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t11))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t2 l2))) (fun r2 => (Or.elim r2 (fun l3 => (False.elim (bool_contra t1 l3))) (fun r3 => (Or.elim r3 (fun l4 => (False.elim (bool_contra l4 t0))) (fun r4 => r4))))))))))
  have t13 : p 1499 = true := (Or.elim (step4386 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra l2 t0))) (fun r2 => (False.elim (bool_contra t1 r2))))))))
  have t14 : p 1509 = true := (Or.elim (step2193 p h) (fun l0 => (False.elim (bool_contra t13 l0))) (fun r0 => r0))
  have t15 : p 60 = false := (Or.elim (step2223 p h) (fun l0 => (False.elim (bool_contra l0 u0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t1 l1))) (fun r1 => r1))))
  have t16 : p 68 = false := (Or.elim (step7278 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t3 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra l2 u0))) (fun r2 => (False.elim (bool_contra t2 r2))))))))
  have t17 : p 1554 = true := (Or.elim (step1087 p h) (fun l0 => (False.elim (bool_contra l0 t15))) (fun r0 => r0))
  have t18 : p 1615 = true := (Or.elim (step1202 p h) (fun l0 => (False.elim (bool_contra l0 t16))) (fun r0 => r0))
  have t19 : p 1573 = true := (Or.elim (step4287 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t3 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra l2 t12))) (fun r2 => (Or.elim r2 (fun l3 => (False.elim (bool_contra t4 l3))) (fun r3 => (False.elim (bool_contra t17 r3))))))))))
  have t20 : p 1620 = true := (Or.elim (step1210 p h) (fun l0 => (False.elim (bool_contra t18 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t5 l1))) (fun r1 => r1))))
  have t21 : p 1594 = true := (Or.elim (step1167 p h) (fun l0 => (False.elim (bool_contra t14 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t19 l1))) (fun r1 => r1))))
  have t22 : p 1625 = true := (Or.elim (step1220 p h) (fun l0 => (False.elim (bool_contra t6 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t20 l1))) (fun r1 => r1))))
  have t23 : p 1746 = false := (Or.elim (step1898 p h) (fun l0 => (False.elim (bool_contra t21 l0))) (fun r0 => r0))
  have t24 : p 1659 = true := (Or.elim (step1294 p h) (fun l0 => (False.elim (bool_contra t22 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t7 l1))) (fun r1 => r1))))
  exact (Or.elim (step1464 p h) (fun l0 => (bool_contra t24 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t8 l1)) (fun r1 => (bool_contra r1 t23)))))

theorem step7429 (p : Nat → Bool) (h : Constraints p) : p 19 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 19 = false := bool_false_of_not_true (fun hl => hc hl)
  have t0 : p 1607 = true := (step7425 p h)
  have t1 : p 59 = true := (step7354 p h)
  have t2 : p 72 = false := (step7286 p h)
  have t3 : p 1725 = true := (step7402 p h)
  have t4 : p 1639 = false := (step7421 p h)
  have t5 : p 87 = false := (step7415 p h)
  have t6 : p 80 = true := (step7392 p h)
  have t7 : p 1499 = true := (Or.elim (step4386 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u0))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra l2 t5))) (fun r2 => (False.elim (bool_contra t6 r2))))))))
  have t8 : p 1609 = true := (Or.elim (step7428 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t9 : p 1612 = true := (Or.elim (step1196 p h) (fun l0 => (False.elim (bool_contra t0 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t8 l1))) (fun r1 => r1))))
  have t10 : p 1572 = false := (Or.elim (step5019 p h) (fun l0 => (False.elim (bool_contra l0 u0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t2))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t9 l2))) (fun r2 => (Or.elim r2 (fun l3 => (False.elim (bool_contra t6 l3))) (fun r3 => (Or.elim r3 (fun l4 => (False.elim (bool_contra t1 l4))) (fun r4 => (Or.elim r4 (fun l5 => (False.elim (bool_contra t3 l5))) (fun r5 => (Or.elim r5 (fun l6 => l6) (fun r6 => (False.elim (bool_contra r6 t5))))))))))))))))
  have t11 : p 1476 = false := (Or.elim (step6491 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t9 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t7 l2))) (fun r2 => (Or.elim r2 (fun l3 => (False.elim (bool_contra t3 l3))) (fun r3 => (Or.elim r3 (fun l4 => (False.elim (bool_contra t6 l4))) (fun r4 => (False.elim (bool_contra r4 t4))))))))))))
  have t12 : p 1554 = false := (Or.elim (step5011 p h) (fun l0 => (False.elim (bool_contra l0 t10))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t5))) (fun r1 => r1))))
  have t13 : p 60 = false := (Or.elim (step6576 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t11))) (fun r1 => (False.elim (bool_contra t6 r1))))))
  exact (Or.elim (step1087 p h) (fun l0 => (bool_contra l0 t13)) (fun r0 => (bool_contra r0 t12)))

theorem step7430 (p : Nat → Bool) (h : Constraints p) : p 75 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 75 = false := bool_false_of_not_true (fun hl => hc hl)
  have t0 : p 19 = true := (step7429 p h)
  exact (Or.elim (step1714 p h) (fun l0 => (bool_contra t0 l0)) (fun r0 => (bool_contra r0 u0)))

theorem step7431 (p : Nat → Bool) (h : Constraints p) : p 73 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 73 = true := bool_true_of_not_false (fun hl => hc hl)
  have t0 : p 19 = true := (step7429 p h)
  exact (Or.elim (step1682 p h) (fun l0 => (bool_contra t0 l0)) (fun r0 => (bool_contra u0 r0)))

theorem step7432 (p : Nat → Bool) (h : Constraints p) : p 79 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 79 = true := bool_true_of_not_false (fun hl => hc hl)
  have t0 : p 19 = true := (step7429 p h)
  have t1 : p 59 = true := (step7354 p h)
  have t2 : p 75 = true := (step7430 p h)
  exact (Or.elim (step281 p h) (fun l0 => (bool_contra t2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t0 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t1 l2)) (fun r2 => (bool_contra u0 r2)))))))

theorem step7433 (p : Nat → Bool) (h : Constraints p) : p 1618 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1618 = false := bool_false_of_not_true (fun hl => hc hl)
  have t0 : p 73 = false := (step7431 p h)
  have t1 : p 72 = false := (step7286 p h)
  exact (Or.elim (step1206 p h) (fun l0 => (bool_contra l0 t1)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (bool_contra r1 u0)))))

theorem step7434 (p : Nat → Bool) (h : Constraints p) : p 1633 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1633 = false := bool_false_of_not_true (fun hl => hc hl)
  have t0 : p 79 = false := (step7432 p h)
  exact (Or.elim (step1236 p h) (fun l0 => (bool_contra l0 t0)) (fun r0 => (bool_contra r0 u0)))

theorem step7435 (p : Nat → Bool) (h : Constraints p) : p 1626 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1626 = false := bool_false_of_not_true (fun hl => hc hl)
  have t0 : p 1618 = true := (step7433 p h)
  have t1 : p 1611 = true := (step7427 p h)
  have t2 : p 1639 = false := (step7421 p h)
  have t3 : p 59 = true := (step7354 p h)
  exact (Or.elim (step7158 p h) (fun l0 => (bool_contra l0 u0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t0 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 t2)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra t1 l3)) (fun r3 => (bool_contra t3 r3)))))))))

theorem step7436 (p : Nat → Bool) (h : Constraints p) : p 1636 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1636 = false := bool_false_of_not_true (fun hl => hc hl)
  have t0 : p 1633 = true := (step7434 p h)
  have t1 : p 1631 = true := (step7290 p h)
  exact (Or.elim (step1241 p h) (fun l0 => (bool_contra t1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t0 l1)) (fun r1 => (bool_contra r1 u0)))))

theorem step7437 (p : Nat → Bool) (h : Constraints p) : p 1660 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1660 = false := bool_false_of_not_true (fun hl => hc hl)
  have t0 : p 1626 = true := (step7435 p h)
  have t1 : p 1648 = true := (step7294 p h)
  exact (Or.elim (step1301 p h) (fun l0 => (bool_contra t0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t1 l1)) (fun r1 => (bool_contra r1 u0)))))

theorem step7438 (p : Nat → Bool) (h : Constraints p) : p 1649 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1649 = false := bool_false_of_not_true (fun hl => hc hl)
  have t0 : p 1636 = true := (step7436 p h)
  exact (Or.elim (step1879 p h) (fun l0 => (bool_contra t0 l0)) (fun r0 => (bool_contra r0 u0)))

theorem step7439 (p : Nat → Bool) (h : Constraints p) : p 1747 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1747 = false := bool_false_of_not_true (fun hl => hc hl)
  have t0 : p 1660 = true := (step7437 p h)
  have t1 : p 1725 = true := (step7402 p h)
  exact (Or.elim (step1471 p h) (fun l0 => (bool_contra t0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t1 l1)) (fun r1 => (bool_contra r1 u0)))))

theorem step7440 (p : Nat → Bool) (h : Constraints p) : p 1661 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1661 = false := bool_false_of_not_true (fun hl => hc hl)
  have t0 : p 1649 = true := (step7438 p h)
  have t1 : p 1626 = true := (step7435 p h)
  exact (Or.elim (step1302 p h) (fun l0 => (bool_contra t1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t0 l1)) (fun r1 => (bool_contra r1 u0)))))

theorem step7441 (p : Nat → Bool) (h : Constraints p) : p 1593 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1593 = true := bool_true_of_not_false (fun hl => hc hl)
  have t0 : p 1747 = true := (step7439 p h)
  exact (Or.elim (step1897 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (bool_contra t0 r0)))

theorem step7442 (p : Nat → Bool) (h : Constraints p) : p 56 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 56 = true := bool_true_of_not_false (fun hl => hc hl)
  have t0 : p 1661 = true := (step7440 p h)
  have t1 : p 87 = false := (step7415 p h)
  have t2 : p 59 = true := (step7354 p h)
  have t3 : p 1724 = true := (step6481 p h)
  have t4 : p 80 = true := (step7392 p h)
  exact (Or.elim (step5045 p h) (fun l0 => (bool_contra t0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t2 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t4 l2)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 t1)) (fun r3 => (Or.elim r3 (fun l4 => (bool_contra u0 l4)) (fun r4 => (bool_contra t3 r4)))))))))))

theorem step7443 (p : Nat → Bool) (h : Constraints p) : p 1748 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1748 = false := bool_false_of_not_true (fun hl => hc hl)
  have t0 : p 1661 = true := (step7440 p h)
  have t1 : p 1725 = true := (step7402 p h)
  exact (Or.elim (step1479 p h) (fun l0 => (bool_contra t0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t1 l1)) (fun r1 => (bool_contra r1 u0)))))

theorem step7444 (p : Nat → Bool) (h : Constraints p) : p 1573 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1573 = true := bool_true_of_not_false (fun hl => hc hl)
  have t0 : p 1593 = false := (step7441 p h)
  have t1 : p 1508 = true := (step7426 p h)
  exact (Or.elim (step1159 p h) (fun l0 => (bool_contra t1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u0 l1)) (fun r1 => (bool_contra r1 t0)))))

theorem step7445 (p : Nat → Bool) (h : Constraints p) : p 1592 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1592 = true := bool_true_of_not_false (fun hl => hc hl)
  have t0 : p 1748 = true := (step7443 p h)
  exact (Or.elim (step1896 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (bool_contra t0 r0)))

theorem step7446 (p : Nat → Bool) (h : Constraints p) : p 1554 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1554 = true := bool_true_of_not_false (fun hl => hc hl)
  have t0 : p 1573 = false := (step7444 p h)
  have t1 : p 18 = true := (step7284 p h)
  have t2 : p 85 = true := (step7423 p h)
  have t3 : p 56 = false := (step7442 p h)
  exact (Or.elim (step4287 p h) (fun l0 => (bool_contra l0 t0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t2 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 t3)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra t1 l3)) (fun r3 => (bool_contra u0 r3)))))))))

theorem step7447 (p : Nat → Bool) (h : Constraints p) : p 1509 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1509 = true := bool_true_of_not_false (fun hl => hc hl)
  have t0 : p 1592 = false := (step7445 p h)
  exact (Or.elim (step5210 p h) (fun l0 => (bool_contra l0 t0)) (fun r0 => (bool_contra u0 r0)))

theorem step7448 (p : Nat → Bool) (h : Constraints p) : p 60 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 60 = false := bool_false_of_not_true (fun hl => hc hl)
  have t0 : p 1554 = false := (step7446 p h)
  exact (Or.elim (step1087 p h) (fun l0 => (bool_contra l0 u0)) (fun r0 => (bool_contra r0 t0)))

theorem step7449 (p : Nat → Bool) (h : Constraints p) : False := by
  have t0 : p 1509 = false := (step7447 p h)
  have t1 : p 60 = true := (step7448 p h)
  have t2 : p 87 = false := (step7415 p h)
  exact (Or.elim (step6004 p h) (fun l0 => (bool_contra t1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (bool_contra r1 t2)))))

end Dfs112FirstBoolean
