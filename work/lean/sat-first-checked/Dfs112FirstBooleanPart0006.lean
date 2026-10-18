import Dfs112FirstBooleanPart0005
namespace Dfs112FirstBoolean
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem step1788 (p : Nat → Bool) (h : Constraints p) : p 79 = false ∨ p 75 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 79 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 75 = false := bool_false_of_not_true (fun hl => hc (Or.inr hl))
  have t0 : p 201 = false := (step701 p h)
  exact (Or.elim (step297 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (bool_contra r1 u1)))))

theorem step1789 (p : Nat → Bool) (h : Constraints p) : p 87 = true ∨ p 103 = true ∨ p 80 = false ∨ p 83 = true ∨ p 55 = true ∨ p 81 = true ∨ p 82 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 87 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 103 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 80 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 83 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 55 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 81 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))
  have u6 : p 82 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl)))))))
  have t0 : p 202 = false := (step702 p h)
  exact (Or.elim (step308 p h) (fun l0 => (bool_contra u2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u4)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u5)) (fun r3 => (Or.elim r3 (fun l4 => (bool_contra l4 u6)) (fun r4 => (Or.elim r4 (fun l5 => (bool_contra l5 u3)) (fun r5 => (Or.elim r5 (fun l6 => (bool_contra l6 u0)) (fun r6 => (bool_contra r6 u1)))))))))))))))

theorem step1790 (p : Nat → Bool) (h : Constraints p) : p 107 = true ∨ p 83 = true ∨ p 81 = true ∨ p 86 = true ∨ p 84 = false ∨ p 96 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 107 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 83 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 81 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 86 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 84 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 96 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl))))))
  have t0 : p 206 = false := (step703 p h)
  exact (Or.elim (step349 p h) (fun l0 => (bool_contra u4 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u2)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u1)) (fun r3 => (Or.elim r3 (fun l4 => (bool_contra l4 u3)) (fun r4 => (Or.elim r4 (fun l5 => (bool_contra l5 u5)) (fun r5 => (bool_contra r5 u0)))))))))))))

theorem step1791 (p : Nat → Bool) (h : Constraints p) : p 107 = true ∨ p 81 = true ∨ p 96 = true ∨ p 57 = true ∨ p 84 = false ∨ p 86 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 107 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 81 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 96 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 57 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 84 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 86 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl))))))
  have t0 : p 206 = false := (step703 p h)
  exact (Or.elim (step350 p h) (fun l0 => (bool_contra u4 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u3)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u1)) (fun r3 => (Or.elim r3 (fun l4 => (bool_contra l4 u5)) (fun r4 => (Or.elim r4 (fun l5 => (bool_contra l5 u2)) (fun r5 => (bool_contra r5 u0)))))))))))))

theorem step1792 (p : Nat → Bool) (h : Constraints p) : p 107 = true ∨ p 81 = true ∨ p 57 = true ∨ p 84 = false ∨ p 86 = true ∨ p 83 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 107 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 81 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 57 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 84 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 86 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 83 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl))))))
  have t0 : p 206 = false := (step703 p h)
  exact (Or.elim (step351 p h) (fun l0 => (bool_contra u3 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u2)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u1)) (fun r3 => (Or.elim r3 (fun l4 => (bool_contra l4 u5)) (fun r4 => (Or.elim r4 (fun l5 => (bool_contra l5 u4)) (fun r5 => (bool_contra r5 u0)))))))))))))

theorem step1793 (p : Nat → Bool) (h : Constraints p) : p 83 = true ∨ p 81 = true ∨ p 96 = true ∨ p 57 = true ∨ p 86 = true ∨ p 84 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 83 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 81 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 96 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 57 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 86 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 84 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl))))))
  have t0 : p 206 = false := (step703 p h)
  exact (Or.elim (step352 p h) (fun l0 => (bool_contra u5 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u3)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u1)) (fun r3 => (Or.elim r3 (fun l4 => (bool_contra l4 u0)) (fun r4 => (Or.elim r4 (fun l5 => (bool_contra l5 u4)) (fun r5 => (bool_contra r5 u2)))))))))))))

theorem step1794 (p : Nat → Bool) (h : Constraints p) : p 108 = true ∨ p 82 = true ∨ p 58 = true ∨ p 85 = false ∨ p 86 = true ∨ p 83 = true ∨ p 91 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 108 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 82 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 58 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 85 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 86 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 83 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))
  have u6 : p 91 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl)))))))
  have t0 : p 207 = false := (step704 p h)
  exact (Or.elim (step365 p h) (fun l0 => (bool_contra u3 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u2)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u1)) (fun r3 => (Or.elim r3 (fun l4 => (bool_contra l4 u5)) (fun r4 => (Or.elim r4 (fun l5 => (bool_contra l5 u4)) (fun r5 => (Or.elim r5 (fun l6 => (bool_contra l6 u6)) (fun r6 => (bool_contra r6 u0)))))))))))))))

theorem step1795 (p : Nat → Bool) (h : Constraints p) : p 22 = true ∨ p 82 = true ∨ p 58 = true ∨ p 85 = false ∨ p 83 = true ∨ p 86 = true ∨ p 91 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 22 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 82 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 58 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 85 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 83 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 86 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))
  have u6 : p 91 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl)))))))
  have t0 : p 207 = false := (step704 p h)
  exact (Or.elim (step366 p h) (fun l0 => (bool_contra u3 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u0)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u2)) (fun r3 => (Or.elim r3 (fun l4 => (bool_contra l4 u1)) (fun r4 => (Or.elim r4 (fun l5 => (bool_contra l5 u4)) (fun r5 => (Or.elim r5 (fun l6 => (bool_contra l6 u5)) (fun r6 => (bool_contra r6 u6)))))))))))))))

theorem step1796 (p : Nat → Bool) (h : Constraints p) : p 100 = true ∨ p 87 = true ∨ p 89 = true ∨ p 91 = true ∨ p 88 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 100 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 87 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 89 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 91 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 88 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr hl)))))
  have t0 : p 210 = false := (step705 p h)
  exact (Or.elim (step420 p h) (fun l0 => (bool_contra u4 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u1)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u2)) (fun r3 => (Or.elim r3 (fun l4 => (bool_contra l4 u3)) (fun r4 => (bool_contra r4 u0)))))))))))

theorem step1797 (p : Nat → Bool) (h : Constraints p) : p 91 = true ∨ p 88 = false ∨ p 89 = true ∨ p 100 = true ∨ p 82 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 91 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 88 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 89 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 100 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 82 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr hl)))))
  have t0 : p 210 = false := (step705 p h)
  exact (Or.elim (step421 p h) (fun l0 => (bool_contra u1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u4)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u2)) (fun r3 => (Or.elim r3 (fun l4 => (bool_contra l4 u0)) (fun r4 => (bool_contra r4 u3)))))))))))

theorem step1798 (p : Nat → Bool) (h : Constraints p) : p 100 = true ∨ p 87 = true ∨ p 91 = true ∨ p 82 = true ∨ p 88 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 100 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 87 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 91 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 82 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 88 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr hl)))))
  have t0 : p 210 = false := (step705 p h)
  exact (Or.elim (step422 p h) (fun l0 => (bool_contra u4 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u3)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u1)) (fun r3 => (Or.elim r3 (fun l4 => (bool_contra l4 u2)) (fun r4 => (bool_contra r4 u0)))))))))))

theorem step1799 (p : Nat → Bool) (h : Constraints p) : p 100 = true ∨ p 88 = false ∨ p 82 = true ∨ p 87 = true ∨ p 89 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 100 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 88 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 82 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 87 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 89 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr hl)))))
  have t0 : p 210 = false := (step705 p h)
  exact (Or.elim (step423 p h) (fun l0 => (bool_contra u1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u2)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u3)) (fun r3 => (Or.elim r3 (fun l4 => (bool_contra l4 u4)) (fun r4 => (bool_contra r4 u0)))))))))))

theorem step1800 (p : Nat → Bool) (h : Constraints p) : p 91 = true ∨ p 88 = false ∨ p 89 = true ∨ p 82 = true ∨ p 87 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 91 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 88 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 89 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 82 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 87 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr hl)))))
  have t0 : p 210 = false := (step705 p h)
  exact (Or.elim (step424 p h) (fun l0 => (bool_contra u1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u3)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u4)) (fun r3 => (Or.elim r3 (fun l4 => (bool_contra l4 u2)) (fun r4 => (bool_contra r4 u0)))))))))))

theorem step1801 (p : Nat → Bool) (h : Constraints p) : p 87 = true ∨ p 90 = false ∨ p 91 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 87 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 90 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 91 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 212 = false := (step706 p h)
  exact (Or.elim (step444 p h) (fun l0 => (bool_contra u1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u0)) (fun r2 => (bool_contra r2 u2)))))))

theorem step1802 (p : Nat → Bool) (h : Constraints p) : p 83 = true ∨ p 90 = false ∨ p 91 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 83 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 90 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 91 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 212 = false := (step706 p h)
  exact (Or.elim (step445 p h) (fun l0 => (bool_contra u1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u0)) (fun r2 => (bool_contra r2 u2)))))))

theorem step1803 (p : Nat → Bool) (h : Constraints p) : p 87 = true ∨ p 83 = true ∨ p 90 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 87 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 83 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 90 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 212 = false := (step706 p h)
  exact (Or.elim (step446 p h) (fun l0 => (bool_contra u2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u1)) (fun r2 => (bool_contra r2 u0)))))))

theorem step1804 (p : Nat → Bool) (h : Constraints p) : p 83 = true ∨ p 95 = false ∨ p 96 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 83 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 95 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 96 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 217 = false := (step709 p h)
  exact (Or.elim (step487 p h) (fun l0 => (bool_contra u1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u0)) (fun r2 => (bool_contra r2 u2)))))))

theorem step1805 (p : Nat → Bool) (h : Constraints p) : p 96 = true ∨ p 95 = false ∨ p 32 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 96 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 95 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 32 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 217 = false := (step709 p h)
  exact (Or.elim (step488 p h) (fun l0 => (bool_contra u1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u2)) (fun r2 => (bool_contra r2 u0)))))))

theorem step1806 (p : Nat → Bool) (h : Constraints p) : p 83 = true ∨ p 95 = false ∨ p 32 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 83 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 95 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 32 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 217 = false := (step709 p h)
  exact (Or.elim (step489 p h) (fun l0 => (bool_contra u1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u2)) (fun r2 => (bool_contra r2 u0)))))))

theorem step1807 (p : Nat → Bool) (h : Constraints p) : p 94 = true ∨ p 96 = true ∨ p 97 = false ∨ p 102 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 94 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 96 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 97 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 102 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 219 = false := (step710 p h)
  exact (Or.elim (step495 p h) (fun l0 => (bool_contra u2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u0)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u1)) (fun r3 => (bool_contra r3 u3)))))))))

theorem step1808 (p : Nat → Bool) (h : Constraints p) : p 96 = true ∨ p 102 = true ∨ p 86 = true ∨ p 97 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 96 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 102 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 86 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 97 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 219 = false := (step710 p h)
  exact (Or.elim (step496 p h) (fun l0 => (bool_contra u3 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u2)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u0)) (fun r3 => (bool_contra r3 u1)))))))))

theorem step1809 (p : Nat → Bool) (h : Constraints p) : p 94 = true ∨ p 102 = true ∨ p 97 = false ∨ p 86 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 94 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 102 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 97 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 86 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 219 = false := (step710 p h)
  exact (Or.elim (step497 p h) (fun l0 => (bool_contra u2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u3)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u0)) (fun r3 => (bool_contra r3 u1)))))))))

theorem step1810 (p : Nat → Bool) (h : Constraints p) : p 94 = true ∨ p 96 = true ∨ p 86 = true ∨ p 97 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 94 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 96 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 86 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 97 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 219 = false := (step710 p h)
  exact (Or.elim (step498 p h) (fun l0 => (bool_contra u3 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u2)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u0)) (fun r3 => (bool_contra r3 u1)))))))))

theorem step1811 (p : Nat → Bool) (h : Constraints p) : p 100 = true ∨ p 118 = true ∨ p 98 = false ∨ p 99 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 100 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 118 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 98 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 99 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 220 = false := (step711 p h)
  exact (Or.elim (step501 p h) (fun l0 => (bool_contra u2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u3)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u0)) (fun r3 => (bool_contra r3 u1)))))))))

theorem step1812 (p : Nat → Bool) (h : Constraints p) : p 100 = true ∨ p 87 = true ∨ p 118 = true ∨ p 98 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 100 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 87 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 118 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 98 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 220 = false := (step711 p h)
  exact (Or.elim (step502 p h) (fun l0 => (bool_contra u3 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u1)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u0)) (fun r3 => (bool_contra r3 u2)))))))))

theorem step1813 (p : Nat → Bool) (h : Constraints p) : p 87 = true ∨ p 118 = true ∨ p 98 = false ∨ p 99 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 87 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 118 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 98 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 99 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 220 = false := (step711 p h)
  exact (Or.elim (step503 p h) (fun l0 => (bool_contra u2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u0)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u3)) (fun r3 => (bool_contra r3 u1)))))))))

theorem step1814 (p : Nat → Bool) (h : Constraints p) : p 100 = true ∨ p 87 = true ∨ p 98 = false ∨ p 99 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 100 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 87 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 98 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 99 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 220 = false := (step711 p h)
  exact (Or.elim (step504 p h) (fun l0 => (bool_contra u2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u1)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u3)) (fun r3 => (bool_contra r3 u0)))))))))

theorem step1815 (p : Nat → Bool) (h : Constraints p) : p 100 = true ∨ p 94 = true ∨ p 99 = true ∨ p 101 = false ∨ p 102 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 100 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 94 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 99 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 101 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 102 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr hl)))))
  have t0 : p 223 = false := (step712 p h)
  exact (Or.elim (step518 p h) (fun l0 => (bool_contra u3 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u1)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u2)) (fun r3 => (Or.elim r3 (fun l4 => (bool_contra l4 u0)) (fun r4 => (bool_contra r4 u4)))))))))))

theorem step1816 (p : Nat → Bool) (h : Constraints p) : p 100 = true ∨ p 89 = true ∨ p 102 = true ∨ p 101 = false ∨ p 99 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 100 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 89 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 102 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 101 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 99 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr hl)))))
  have t0 : p 223 = false := (step712 p h)
  exact (Or.elim (step519 p h) (fun l0 => (bool_contra u3 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u1)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u4)) (fun r3 => (Or.elim r3 (fun l4 => (bool_contra l4 u0)) (fun r4 => (bool_contra r4 u2)))))))))))

theorem step1817 (p : Nat → Bool) (h : Constraints p) : p 100 = true ∨ p 94 = true ∨ p 102 = true ∨ p 101 = false ∨ p 89 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 100 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 94 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 102 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 101 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 89 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr hl)))))
  have t0 : p 223 = false := (step712 p h)
  exact (Or.elim (step520 p h) (fun l0 => (bool_contra u3 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u4)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u1)) (fun r3 => (Or.elim r3 (fun l4 => (bool_contra l4 u0)) (fun r4 => (bool_contra r4 u2)))))))))))

theorem step1818 (p : Nat → Bool) (h : Constraints p) : p 99 = true ∨ p 94 = true ∨ p 102 = true ∨ p 101 = false ∨ p 89 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 99 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 94 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 102 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 101 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 89 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr hl)))))
  have t0 : p 223 = false := (step712 p h)
  exact (Or.elim (step521 p h) (fun l0 => (bool_contra u3 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u4)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u1)) (fun r3 => (Or.elim r3 (fun l4 => (bool_contra l4 u0)) (fun r4 => (bool_contra r4 u2)))))))))))

theorem step1819 (p : Nat → Bool) (h : Constraints p) : p 100 = true ∨ p 94 = true ∨ p 89 = true ∨ p 101 = false ∨ p 99 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 100 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 94 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 89 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 101 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 99 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr hl)))))
  have t0 : p 223 = false := (step712 p h)
  exact (Or.elim (step522 p h) (fun l0 => (bool_contra u3 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u2)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u1)) (fun r3 => (Or.elim r3 (fun l4 => (bool_contra l4 u4)) (fun r4 => (bool_contra r4 u0)))))))))))

theorem step1820 (p : Nat → Bool) (h : Constraints p) : p 114 = true ∨ p 106 = true ∨ p 103 = true ∨ p 104 = false ∨ p 107 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 114 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 106 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 103 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 104 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 107 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr hl)))))
  have t0 : p 226 = false := (step713 p h)
  exact (Or.elim (step553 p h) (fun l0 => (bool_contra u3 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u2)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u1)) (fun r3 => (Or.elim r3 (fun l4 => (bool_contra l4 u4)) (fun r4 => (bool_contra r4 u0)))))))))))

theorem step1821 (p : Nat → Bool) (h : Constraints p) : p 114 = true ∨ p 107 = true ∨ p 81 = true ∨ p 104 = false ∨ p 106 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 114 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 107 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 81 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 104 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 106 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr hl)))))
  have t0 : p 226 = false := (step713 p h)
  exact (Or.elim (step554 p h) (fun l0 => (bool_contra u3 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u2)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u4)) (fun r3 => (Or.elim r3 (fun l4 => (bool_contra l4 u1)) (fun r4 => (bool_contra r4 u0)))))))))))

theorem step1822 (p : Nat → Bool) (h : Constraints p) : p 114 = true ∨ p 107 = true ∨ p 81 = true ∨ p 104 = false ∨ p 103 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 114 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 107 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 81 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 104 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 103 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr hl)))))
  have t0 : p 226 = false := (step713 p h)
  exact (Or.elim (step555 p h) (fun l0 => (bool_contra u3 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u2)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u4)) (fun r3 => (Or.elim r3 (fun l4 => (bool_contra l4 u1)) (fun r4 => (bool_contra r4 u0)))))))))))

theorem step1823 (p : Nat → Bool) (h : Constraints p) : p 114 = true ∨ p 103 = true ∨ p 106 = true ∨ p 81 = true ∨ p 104 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 114 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 103 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 106 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 81 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 104 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr hl)))))
  have t0 : p 226 = false := (step713 p h)
  exact (Or.elim (step556 p h) (fun l0 => (bool_contra u4 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u3)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u1)) (fun r3 => (Or.elim r3 (fun l4 => (bool_contra l4 u2)) (fun r4 => (bool_contra r4 u0)))))))))))

theorem step1824 (p : Nat → Bool) (h : Constraints p) : p 106 = true ∨ p 103 = true ∨ p 81 = true ∨ p 107 = true ∨ p 104 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 106 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 103 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 81 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 107 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 104 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr hl)))))
  have t0 : p 226 = false := (step713 p h)
  exact (Or.elim (step557 p h) (fun l0 => (bool_contra u4 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u2)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u1)) (fun r3 => (Or.elim r3 (fun l4 => (bool_contra l4 u0)) (fun r4 => (bool_contra r4 u3)))))))))))

theorem step1825 (p : Nat → Bool) (h : Constraints p) : p 115 = true ∨ p 106 = true ∨ p 105 = false ∨ p 82 = true ∨ p 103 = true ∨ p 108 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 115 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 106 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 105 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 82 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 103 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 108 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl))))))
  have t0 : p 227 = false := (step714 p h)
  exact (Or.elim (step561 p h) (fun l0 => (bool_contra u2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u3)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u4)) (fun r3 => (Or.elim r3 (fun l4 => (bool_contra l4 u1)) (fun r4 => (Or.elim r4 (fun l5 => (bool_contra l5 u5)) (fun r5 => (bool_contra r5 u0)))))))))))))

theorem step1826 (p : Nat → Bool) (h : Constraints p) : p 38 = true ∨ p 106 = true ∨ p 105 = false ∨ p 103 = true ∨ p 108 = true ∨ p 82 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 38 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 106 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 105 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 103 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 108 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 82 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl))))))
  have t0 : p 227 = false := (step714 p h)
  exact (Or.elim (step562 p h) (fun l0 => (bool_contra u2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u0)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u5)) (fun r3 => (Or.elim r3 (fun l4 => (bool_contra l4 u3)) (fun r4 => (Or.elim r4 (fun l5 => (bool_contra l5 u1)) (fun r5 => (bool_contra r5 u4)))))))))))))

theorem step1827 (p : Nat → Bool) (h : Constraints p) : p 109 = false ∨ p 118 = true ∨ p 103 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 109 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 118 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 103 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 231 = false := (step715 p h)
  exact (Or.elim (step593 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u2)) (fun r2 => (bool_contra r2 u1)))))))

end Dfs112FirstBoolean
