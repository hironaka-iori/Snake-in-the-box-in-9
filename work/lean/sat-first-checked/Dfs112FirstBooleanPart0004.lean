import Dfs112FirstBooleanPart0003
namespace Dfs112FirstBoolean
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem step1708 (p : Nat → Bool) (h : Constraints p) : p 13 = false ∨ p 5 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 13 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 5 = false := bool_false_of_not_true (fun hl => hc (Or.inr hl))
  have t0 : p 135 = false := (step667 p h)
  exact (Or.elim (step56 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (bool_contra r1 u1)))))

theorem step1709 (p : Nat → Bool) (h : Constraints p) : p 14 = true ∨ p 15 = false ∨ p 16 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 14 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 15 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 16 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 137 = false := (step668 p h)
  exact (Or.elim (step60 p h) (fun l0 => (bool_contra u1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u0)) (fun r2 => (bool_contra r2 u2)))))))

theorem step1710 (p : Nat → Bool) (h : Constraints p) : p 15 = false ∨ p 7 = true ∨ p 16 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 15 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 7 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 16 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 137 = false := (step668 p h)
  exact (Or.elim (step61 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u1)) (fun r2 => (bool_contra r2 u2)))))))

theorem step1711 (p : Nat → Bool) (h : Constraints p) : p 15 = false ∨ p 7 = true ∨ p 14 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 15 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 7 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 14 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 137 = false := (step668 p h)
  exact (Or.elim (step62 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u1)) (fun r2 => (bool_contra r2 u2)))))))

theorem step1712 (p : Nat → Bool) (h : Constraints p) : p 40 = false ∨ p 18 = false ∨ p 3 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 40 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 18 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 3 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 74 = true := (step1548 p h)
  exact (Or.elim (step69 p h) (fun l0 => (bool_contra u1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u2 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra u0 l2)) (fun r2 => (bool_contra t0 r2)))))))

theorem step1713 (p : Nat → Bool) (h : Constraints p) : p 40 = true ∨ p 18 = false ∨ p 3 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 40 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 18 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 3 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 140 = false := (step669 p h)
  exact (Or.elim (step70 p h) (fun l0 => (bool_contra u1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u2)) (fun r2 => (bool_contra r2 u0)))))))

theorem step1714 (p : Nat → Bool) (h : Constraints p) : p 19 = false ∨ p 75 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 19 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 75 = false := bool_false_of_not_true (fun hl => hc (Or.inr hl))
  have t0 : p 141 = false := (step670 p h)
  exact (Or.elim (step71 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (bool_contra r1 u1)))))

theorem step1715 (p : Nat → Bool) (h : Constraints p) : p 19 = false ∨ p 17 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 19 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 17 = false := bool_false_of_not_true (fun hl => hc (Or.inr hl))
  have t0 : p 141 = false := (step670 p h)
  exact (Or.elim (step72 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (bool_contra r1 u1)))))

theorem step1716 (p : Nat → Bool) (h : Constraints p) : p 29 = true ∨ p 20 = true ∨ p 21 = false ∨ p 81 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 29 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 20 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 21 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 81 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 143 = false := (step671 p h)
  exact (Or.elim (step76 p h) (fun l0 => (bool_contra u2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u1)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u0)) (fun r3 => (bool_contra r3 u3)))))))))

theorem step1717 (p : Nat → Bool) (h : Constraints p) : p 20 = true ∨ p 81 = true ∨ p 21 = false ∨ p 25 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 20 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 81 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 21 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 25 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 143 = false := (step671 p h)
  exact (Or.elim (step77 p h) (fun l0 => (bool_contra u2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u0)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u3)) (fun r3 => (bool_contra r3 u1)))))))))

theorem step1718 (p : Nat → Bool) (h : Constraints p) : p 86 = true ∨ p 23 = false ∨ p 28 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 86 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 23 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 28 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 145 = false := (step672 p h)
  exact (Or.elim (step82 p h) (fun l0 => (bool_contra u1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u2)) (fun r2 => (bool_contra r2 u0)))))))

theorem step1719 (p : Nat → Bool) (h : Constraints p) : p 22 = true ∨ p 86 = true ∨ p 23 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 22 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 86 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 23 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 145 = false := (step672 p h)
  exact (Or.elim (step83 p h) (fun l0 => (bool_contra u2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u0)) (fun r2 => (bool_contra r2 u1)))))))

theorem step1720 (p : Nat → Bool) (h : Constraints p) : p 22 = true ∨ p 23 = false ∨ p 28 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 22 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 23 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 28 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 145 = false := (step672 p h)
  exact (Or.elim (step84 p h) (fun l0 => (bool_contra u1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u0)) (fun r2 => (bool_contra r2 u2)))))))

theorem step1721 (p : Nat → Bool) (h : Constraints p) : p 20 = true ∨ p 87 = true ∨ p 25 = true ∨ p 24 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 20 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 87 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 25 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 24 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 146 = false := (step673 p h)
  exact (Or.elim (step87 p h) (fun l0 => (bool_contra u3 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u0)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u2)) (fun r3 => (bool_contra r3 u1)))))))))

theorem step1722 (p : Nat → Bool) (h : Constraints p) : p 87 = true ∨ p 25 = true ∨ p 24 = false ∨ p 5 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 87 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 25 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 24 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 5 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 146 = false := (step673 p h)
  exact (Or.elim (step88 p h) (fun l0 => (bool_contra u2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u3)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u1)) (fun r3 => (bool_contra r3 u0)))))))))

theorem step1723 (p : Nat → Bool) (h : Constraints p) : p 20 = true ∨ p 24 = false ∨ p 87 = true ∨ p 5 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 20 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 24 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 87 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 5 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 146 = false := (step673 p h)
  exact (Or.elim (step89 p h) (fun l0 => (bool_contra u1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u3)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u0)) (fun r3 => (bool_contra r3 u2)))))))))

theorem step1724 (p : Nat → Bool) (h : Constraints p) : p 20 = true ∨ p 25 = true ∨ p 5 = true ∨ p 24 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 20 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 25 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 5 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 24 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 146 = false := (step673 p h)
  exact (Or.elim (step90 p h) (fun l0 => (bool_contra u3 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u2)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u0)) (fun r3 => (bool_contra r3 u1)))))))))

theorem step1725 (p : Nat → Bool) (h : Constraints p) : p 25 = true ∨ p 89 = true ∨ p 7 = true ∨ p 26 = false ∨ p 44 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 25 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 89 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 7 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 26 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 44 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr hl)))))
  have t0 : p 148 = false := (step674 p h)
  exact (Or.elim (step98 p h) (fun l0 => (bool_contra u3 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u2)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u0)) (fun r3 => (Or.elim r3 (fun l4 => (bool_contra l4 u4)) (fun r4 => (bool_contra r4 u1)))))))))))

theorem step1726 (p : Nat → Bool) (h : Constraints p) : p 25 = true ∨ p 36 = true ∨ p 27 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 25 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 36 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 27 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 149 = false := (step675 p h)
  exact (Or.elim (step100 p h) (fun l0 => (bool_contra u2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u0)) (fun r2 => (bool_contra r2 u1)))))))

theorem step1727 (p : Nat → Bool) (h : Constraints p) : p 25 = true ∨ p 27 = false ∨ p 28 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 25 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 27 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 28 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 149 = false := (step675 p h)
  exact (Or.elim (step101 p h) (fun l0 => (bool_contra u1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u0)) (fun r2 => (bool_contra r2 u2)))))))

theorem step1728 (p : Nat → Bool) (h : Constraints p) : p 94 = true ∨ p 31 = false ∨ p 30 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 94 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 31 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 30 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 153 = false := (step676 p h)
  exact (Or.elim (step111 p h) (fun l0 => (bool_contra u1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u2)) (fun r2 => (bool_contra r2 u0)))))))

theorem step1729 (p : Nat → Bool) (h : Constraints p) : p 29 = true ∨ p 94 = true ∨ p 31 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 29 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 94 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 31 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 153 = false := (step676 p h)
  exact (Or.elim (step112 p h) (fun l0 => (bool_contra u2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u0)) (fun r2 => (bool_contra r2 u1)))))))

theorem step1730 (p : Nat → Bool) (h : Constraints p) : p 29 = true ∨ p 31 = false ∨ p 30 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 29 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 31 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 30 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 153 = false := (step676 p h)
  exact (Or.elim (step113 p h) (fun l0 => (bool_contra u1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u0)) (fun r2 => (bool_contra r2 u2)))))))

theorem step1731 (p : Nat → Bool) (h : Constraints p) : p 52 = true ∨ p 100 = true ∨ p 37 = true ∨ p 34 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 52 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 100 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 37 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 34 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 156 = false := (step678 p h)
  exact (Or.elim (step125 p h) (fun l0 => (bool_contra u3 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u2)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u0)) (fun r3 => (bool_contra r3 u1)))))))))

theorem step1732 (p : Nat → Bool) (h : Constraints p) : p 30 = true ∨ p 100 = true ∨ p 34 = false ∨ p 37 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 30 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 100 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 34 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 37 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 156 = false := (step678 p h)
  exact (Or.elim (step126 p h) (fun l0 => (bool_contra u2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u0)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u3)) (fun r3 => (bool_contra r3 u1)))))))))

theorem step1733 (p : Nat → Bool) (h : Constraints p) : p 52 = true ∨ p 30 = true ∨ p 37 = true ∨ p 34 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 52 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 30 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 37 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 34 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 156 = false := (step678 p h)
  exact (Or.elim (step127 p h) (fun l0 => (bool_contra u3 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u1)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u2)) (fun r3 => (bool_contra r3 u0)))))))))

theorem step1734 (p : Nat → Bool) (h : Constraints p) : p 37 = true ∨ p 35 = false ∨ p 32 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 37 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 35 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 32 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 157 = false := (step679 p h)
  exact (Or.elim (step128 p h) (fun l0 => (bool_contra u1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u2)) (fun r2 => (bool_contra r2 u0)))))))

theorem step1735 (p : Nat → Bool) (h : Constraints p) : p 36 = true ∨ p 35 = false ∨ p 32 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 36 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 35 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 32 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 157 = false := (step679 p h)
  exact (Or.elim (step129 p h) (fun l0 => (bool_contra u1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u2)) (fun r2 => (bool_contra r2 u0)))))))

theorem step1736 (p : Nat → Bool) (h : Constraints p) : p 38 = true ∨ p 106 = true ∨ p 39 = false ∨ p 44 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 38 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 106 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 39 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 44 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 161 = false := (step680 p h)
  exact (Or.elim (step137 p h) (fun l0 => (bool_contra u2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u0)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u3)) (fun r3 => (bool_contra r3 u1)))))))))

theorem step1737 (p : Nat → Bool) (h : Constraints p) : p 17 = true ∨ p 106 = true ∨ p 39 = false ∨ p 44 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 17 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 106 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 39 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 44 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 161 = false := (step680 p h)
  exact (Or.elim (step138 p h) (fun l0 => (bool_contra u2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u0)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u3)) (fun r3 => (bool_contra r3 u1)))))))))

theorem step1738 (p : Nat → Bool) (h : Constraints p) : p 17 = true ∨ p 38 = true ∨ p 39 = false ∨ p 106 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 17 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 38 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 39 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 106 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 161 = false := (step680 p h)
  exact (Or.elim (step139 p h) (fun l0 => (bool_contra u2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u0)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u1)) (fun r3 => (bool_contra r3 u3)))))))))

theorem step1739 (p : Nat → Bool) (h : Constraints p) : p 41 = false ∨ p 40 = true ∨ p 107 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 41 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 40 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 107 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 163 = false := (step681 p h)
  exact (Or.elim (step147 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u1)) (fun r2 => (bool_contra r2 u2)))))))

theorem step1740 (p : Nat → Bool) (h : Constraints p) : p 48 = true ∨ p 41 = false ∨ p 40 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 48 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 41 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 40 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 163 = false := (step681 p h)
  exact (Or.elim (step148 p h) (fun l0 => (bool_contra u1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u2)) (fun r2 => (bool_contra r2 u0)))))))

theorem step1741 (p : Nat → Bool) (h : Constraints p) : p 46 = true ∨ p 52 = true ∨ p 44 = true ∨ p 43 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 46 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 52 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 44 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 43 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 165 = false := (step683 p h)
  exact (Or.elim (step149 p h) (fun l0 => (bool_contra u3 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u2)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u0)) (fun r3 => (bool_contra r3 u1)))))))))

theorem step1742 (p : Nat → Bool) (h : Constraints p) : p 52 = true ∨ p 38 = true ∨ p 43 = false ∨ p 44 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 52 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 38 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 43 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 44 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 165 = false := (step683 p h)
  exact (Or.elim (step150 p h) (fun l0 => (bool_contra u2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u1)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u3)) (fun r3 => (bool_contra r3 u0)))))))))

theorem step1743 (p : Nat → Bool) (h : Constraints p) : p 45 = false ∨ p 46 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 45 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 46 = false := bool_false_of_not_true (fun hl => hc (Or.inr hl))
  have t0 : p 167 = false := (step684 p h)
  exact (Or.elim (step156 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (bool_contra r1 u1)))))

theorem step1744 (p : Nat → Bool) (h : Constraints p) : p 45 = false ∨ p 40 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 45 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 40 = false := bool_false_of_not_true (fun hl => hc (Or.inr hl))
  have t0 : p 167 = false := (step684 p h)
  exact (Or.elim (step157 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (bool_contra r1 u1)))))

theorem step1745 (p : Nat → Bool) (h : Constraints p) : p 48 = true ∨ p 47 = false ∨ p 40 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 48 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 47 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 40 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 169 = false := (step685 p h)
  exact (Or.elim (step161 p h) (fun l0 => (bool_contra u1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u2)) (fun r2 => (bool_contra r2 u0)))))))

theorem step1746 (p : Nat → Bool) (h : Constraints p) : p 40 = true ∨ p 47 = false ∨ p 32 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 40 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 47 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 32 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 169 = false := (step685 p h)
  exact (Or.elim (step162 p h) (fun l0 => (bool_contra u1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u2)) (fun r2 => (bool_contra r2 u0)))))))

theorem step1747 (p : Nat → Bool) (h : Constraints p) : p 49 = false ∨ p 54 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 49 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 54 = false := bool_false_of_not_true (fun hl => hc (Or.inr hl))
  have t0 : p 171 = false := (step686 p h)
  exact (Or.elim (step165 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (bool_contra r1 u1)))))

end Dfs112FirstBoolean
