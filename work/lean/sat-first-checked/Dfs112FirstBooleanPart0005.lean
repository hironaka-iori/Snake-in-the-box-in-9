import Dfs112FirstBooleanPart0004
namespace Dfs112FirstBoolean
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem step1748 (p : Nat → Bool) (h : Constraints p) : p 49 = false ∨ p 48 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 49 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 48 = false := bool_false_of_not_true (fun hl => hc (Or.inr hl))
  have t0 : p 171 = false := (step686 p h)
  exact (Or.elim (step166 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (bool_contra r1 u1)))))

theorem step1749 (p : Nat → Bool) (h : Constraints p) : p 52 = true ∨ p 118 = true ∨ p 50 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 52 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 118 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 50 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 172 = false := (step687 p h)
  exact (Or.elim (step167 p h) (fun l0 => (bool_contra u2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u0)) (fun r2 => (bool_contra r2 u1)))))))

theorem step1750 (p : Nat → Bool) (h : Constraints p) : p 51 = true ∨ p 118 = true ∨ p 50 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 51 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 118 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 50 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 172 = false := (step687 p h)
  exact (Or.elim (step168 p h) (fun l0 => (bool_contra u2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u0)) (fun r2 => (bool_contra r2 u1)))))))

theorem step1751 (p : Nat → Bool) (h : Constraints p) : p 51 = true ∨ p 52 = true ∨ p 50 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 51 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 52 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 50 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 172 = false := (step687 p h)
  exact (Or.elim (step169 p h) (fun l0 => (bool_contra u2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u0)) (fun r2 => (bool_contra r2 u1)))))))

theorem step1752 (p : Nat → Bool) (h : Constraints p) : p 56 = false ∨ p 65 = true ∨ p 57 = true ∨ p 81 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 56 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 65 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 57 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 81 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 178 = false := (step689 p h)
  exact (Or.elim (step200 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u2)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u1)) (fun r3 => (bool_contra r3 u3)))))))))

theorem step1753 (p : Nat → Bool) (h : Constraints p) : p 55 = true ∨ p 81 = true ∨ p 56 = false ∨ p 65 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 55 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 81 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 56 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 65 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 178 = false := (step689 p h)
  exact (Or.elim (step201 p h) (fun l0 => (bool_contra u2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u0)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u3)) (fun r3 => (bool_contra r3 u1)))))))))

theorem step1754 (p : Nat → Bool) (h : Constraints p) : p 55 = true ∨ p 81 = true ∨ p 56 = false ∨ p 57 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 55 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 81 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 56 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 57 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 178 = false := (step689 p h)
  exact (Or.elim (step202 p h) (fun l0 => (bool_contra u2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u0)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u3)) (fun r3 => (bool_contra r3 u1)))))))))

theorem step1755 (p : Nat → Bool) (h : Constraints p) : p 63 = true ∨ p 86 = true ∨ p 59 = false ∨ p 57 = true ∨ p 58 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 63 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 86 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 59 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 57 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 58 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr hl)))))
  have t0 : p 181 = false := (step690 p h)
  exact (Or.elim (step222 p h) (fun l0 => (bool_contra u2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u3)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u4)) (fun r3 => (Or.elim r3 (fun l4 => (bool_contra l4 u0)) (fun r4 => (bool_contra r4 u1)))))))))))

theorem step1756 (p : Nat → Bool) (h : Constraints p) : p 60 = false ∨ p 55 = true ∨ p 87 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 60 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 55 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 87 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 182 = false := (step691 p h)
  exact (Or.elim (step224 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u1)) (fun r2 => (bool_contra r2 u2)))))))

theorem step1757 (p : Nat → Bool) (h : Constraints p) : p 87 = true ∨ p 60 = false ∨ p 5 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 87 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 60 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 5 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 182 = false := (step691 p h)
  exact (Or.elim (step225 p h) (fun l0 => (bool_contra u1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u2)) (fun r2 => (bool_contra r2 u0)))))))

theorem step1758 (p : Nat → Bool) (h : Constraints p) : p 55 = true ∨ p 60 = false ∨ p 5 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 55 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 60 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 5 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 182 = false := (step691 p h)
  exact (Or.elim (step226 p h) (fun l0 => (bool_contra u1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u2)) (fun r2 => (bool_contra r2 u0)))))))

theorem step1759 (p : Nat → Bool) (h : Constraints p) : p 63 = true ∨ p 89 = true ∨ p 61 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 63 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 89 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 61 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 183 = false := (step692 p h)
  exact (Or.elim (step228 p h) (fun l0 => (bool_contra u2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u0)) (fun r2 => (bool_contra r2 u1)))))))

theorem step1760 (p : Nat → Bool) (h : Constraints p) : p 7 = true ∨ p 89 = true ∨ p 61 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 7 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 89 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 61 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 183 = false := (step692 p h)
  exact (Or.elim (step229 p h) (fun l0 => (bool_contra u2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u0)) (fun r2 => (bool_contra r2 u1)))))))

theorem step1761 (p : Nat → Bool) (h : Constraints p) : p 63 = true ∨ p 7 = true ∨ p 61 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 63 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 7 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 61 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 183 = false := (step692 p h)
  exact (Or.elim (step230 p h) (fun l0 => (bool_contra u2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u1)) (fun r2 => (bool_contra r2 u0)))))))

theorem step1762 (p : Nat → Bool) (h : Constraints p) : p 70 = true ∨ p 63 = true ∨ p 62 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 70 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 63 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 62 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 184 = false := (step693 p h)
  exact (Or.elim (step232 p h) (fun l0 => (bool_contra u2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u1)) (fun r2 => (bool_contra r2 u0)))))))

theorem step1763 (p : Nat → Bool) (h : Constraints p) : p 70 = true ∨ p 62 = false ∨ p 57 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 70 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 62 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 57 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 184 = false := (step693 p h)
  exact (Or.elim (step233 p h) (fun l0 => (bool_contra u1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u2)) (fun r2 => (bool_contra r2 u0)))))))

theorem step1764 (p : Nat → Bool) (h : Constraints p) : p 63 = true ∨ p 57 = true ∨ p 62 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 63 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 57 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 62 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 184 = false := (step693 p h)
  exact (Or.elim (step234 p h) (fun l0 => (bool_contra u2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u1)) (fun r2 => (bool_contra r2 u0)))))))

theorem step1765 (p : Nat → Bool) (h : Constraints p) : p 66 = true ∨ p 65 = true ∨ p 64 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 66 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 65 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 64 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 186 = false := (step694 p h)
  exact (Or.elim (step242 p h) (fun l0 => (bool_contra u2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u1)) (fun r2 => (bool_contra r2 u0)))))))

theorem step1766 (p : Nat → Bool) (h : Constraints p) : p 66 = true ∨ p 55 = true ∨ p 64 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 66 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 55 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 64 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 186 = false := (step694 p h)
  exact (Or.elim (step243 p h) (fun l0 => (bool_contra u2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u1)) (fun r2 => (bool_contra r2 u0)))))))

theorem step1767 (p : Nat → Bool) (h : Constraints p) : p 55 = true ∨ p 65 = true ∨ p 64 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 55 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 65 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 64 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 186 = false := (step694 p h)
  exact (Or.elim (step244 p h) (fun l0 => (bool_contra u2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u0)) (fun r2 => (bool_contra r2 u1)))))))

theorem step1768 (p : Nat → Bool) (h : Constraints p) : p 94 = true ∨ p 66 = true ∨ p 67 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 94 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 66 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 67 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 189 = false := (step695 p h)
  exact (Or.elim (step255 p h) (fun l0 => (bool_contra u2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u1)) (fun r2 => (bool_contra r2 u0)))))))

theorem step1769 (p : Nat → Bool) (h : Constraints p) : p 94 = true ∨ p 65 = true ∨ p 67 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 94 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 65 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 67 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 189 = false := (step695 p h)
  exact (Or.elim (step256 p h) (fun l0 => (bool_contra u2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u1)) (fun r2 => (bool_contra r2 u0)))))))

theorem step1770 (p : Nat → Bool) (h : Constraints p) : p 66 = true ∨ p 65 = true ∨ p 67 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 66 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 65 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 67 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 189 = false := (step695 p h)
  exact (Or.elim (step257 p h) (fun l0 => (bool_contra u2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u1)) (fun r2 => (bool_contra r2 u0)))))))

theorem step1771 (p : Nat → Bool) (h : Constraints p) : p 66 = true ∨ p 68 = false ∨ p 71 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 66 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 68 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 71 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 190 = false := (step696 p h)
  exact (Or.elim (step259 p h) (fun l0 => (bool_contra u1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u0)) (fun r2 => (bool_contra r2 u2)))))))

theorem step1772 (p : Nat → Bool) (h : Constraints p) : p 68 = false ∨ p 71 = true ∨ p 58 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 68 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 71 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 58 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 190 = false := (step696 p h)
  exact (Or.elim (step260 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u2)) (fun r2 => (bool_contra r2 u1)))))))

theorem step1773 (p : Nat → Bool) (h : Constraints p) : p 66 = true ∨ p 68 = false ∨ p 58 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 66 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 68 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 58 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 190 = false := (step696 p h)
  exact (Or.elim (step261 p h) (fun l0 => (bool_contra u1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u2)) (fun r2 => (bool_contra r2 u0)))))))

theorem step1774 (p : Nat → Bool) (h : Constraints p) : p 69 = false ∨ p 71 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 69 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 71 = false := bool_false_of_not_true (fun hl => hc (Or.inr hl))
  have t0 : p 191 = false := (step697 p h)
  exact (Or.elim (step262 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (bool_contra r1 u1)))))

theorem step1775 (p : Nat → Bool) (h : Constraints p) : p 69 = false ∨ p 70 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 69 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 70 = false := bool_false_of_not_true (fun hl => hc (Or.inr hl))
  have t0 : p 191 = false := (step697 p h)
  exact (Or.elim (step263 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (bool_contra r1 u1)))))

theorem step1776 (p : Nat → Bool) (h : Constraints p) : p 103 = false ∨ p 55 = false ∨ p 72 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 103 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 55 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 72 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 74 = true := (step1548 p h)
  exact (Or.elim (step270 p h) (fun l0 => (bool_contra u2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u1 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t0 l2)) (fun r2 => (bool_contra u0 r2)))))))

theorem step1777 (p : Nat → Bool) (h : Constraints p) : p 55 = true ∨ p 103 = true ∨ p 72 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 55 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 103 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 72 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 194 = false := (step698 p h)
  exact (Or.elim (step271 p h) (fun l0 => (bool_contra u2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u0)) (fun r2 => (bool_contra r2 u1)))))))

theorem step1778 (p : Nat → Bool) (h : Constraints p) : p 75 = true ∨ p 106 = true ∨ p 73 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 75 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 106 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 73 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 195 = false := (step699 p h)
  exact (Or.elim (step273 p h) (fun l0 => (bool_contra u2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u0)) (fun r2 => (bool_contra r2 u1)))))))

theorem step1779 (p : Nat → Bool) (h : Constraints p) : p 17 = true ∨ p 106 = true ∨ p 73 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 17 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 106 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 73 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 195 = false := (step699 p h)
  exact (Or.elim (step274 p h) (fun l0 => (bool_contra u2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u0)) (fun r2 => (bool_contra r2 u1)))))))

theorem step1780 (p : Nat → Bool) (h : Constraints p) : p 17 = true ∨ p 75 = true ∨ p 73 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 17 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 75 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 73 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 195 = false := (step699 p h)
  exact (Or.elim (step275 p h) (fun l0 => (bool_contra u2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u0)) (fun r2 => (bool_contra r2 u1)))))))

theorem step1781 (p : Nat → Bool) (h : Constraints p) : p 18 = false ∨ p 72 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 18 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 72 = true := bool_true_of_not_false (fun hl => hc (Or.inr hl))
  have t0 : p 74 = true := (step1548 p h)
  have t1 : p 76 = true := (step289 p h)
  exact (Or.elim (step276 p h) (fun l0 => (bool_contra t0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u0 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra u1 l2)) (fun r2 => (bool_contra t1 r2)))))))

theorem step1782 (p : Nat → Bool) (h : Constraints p) : p 18 = false ∨ p 77 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 18 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 77 = true := bool_true_of_not_false (fun hl => hc (Or.inr hl))
  have t0 : p 76 = true := (step289 p h)
  have t1 : p 74 = true := (step1548 p h)
  exact (Or.elim (step277 p h) (fun l0 => (bool_contra t1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u0 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t0 l2)) (fun r2 => (bool_contra u1 r2)))))))

theorem step1783 (p : Nat → Bool) (h : Constraints p) : p 72 = false ∨ p 77 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 72 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 77 = true := bool_true_of_not_false (fun hl => hc (Or.inr hl))
  have t0 : p 76 = true := (step289 p h)
  have t1 : p 74 = true := (step1548 p h)
  exact (Or.elim (step278 p h) (fun l0 => (bool_contra t1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u0 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t0 l2)) (fun r2 => (bool_contra u1 r2)))))))

theorem step1784 (p : Nat → Bool) (h : Constraints p) : p 196 = false ∨ p 77 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 196 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 77 = true := bool_true_of_not_false (fun hl => hc (Or.inr hl))
  have t0 : p 76 = true := (step289 p h)
  exact (Or.elim (step279 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t0 l1)) (fun r1 => (bool_contra u1 r1)))))

theorem step1785 (p : Nat → Bool) (h : Constraints p) : p 77 = true ∨ p 72 = true ∨ p 196 = true ∨ p 18 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 77 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 72 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 196 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 18 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 74 = true := (step1548 p h)
  exact (Or.elim (step280 p h) (fun l0 => (bool_contra t0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 u2)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u3)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u1)) (fun r3 => (bool_contra r3 u0)))))))))

theorem step1786 (p : Nat → Bool) (h : Constraints p) : p 77 = false ∨ p 78 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 77 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 78 = false := bool_false_of_not_true (fun hl => hc (Or.inr hl))
  have t0 : p 199 = false := (step700 p h)
  exact (Or.elim (step290 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (bool_contra r1 u1)))))

theorem step1787 (p : Nat → Bool) (h : Constraints p) : p 79 = false ∨ p 78 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 79 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 78 = false := bool_false_of_not_true (fun hl => hc (Or.inr hl))
  have t0 : p 201 = false := (step701 p h)
  exact (Or.elim (step296 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (bool_contra r1 u1)))))

end Dfs112FirstBoolean
