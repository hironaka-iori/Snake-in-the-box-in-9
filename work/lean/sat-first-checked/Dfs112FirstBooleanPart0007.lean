import Dfs112FirstBooleanPart0006
namespace Dfs112FirstBoolean
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem step1828 (p : Nat → Bool) (h : Constraints p) : p 109 = false ∨ p 87 = true ∨ p 118 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 109 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 87 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 118 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 231 = false := (step715 p h)
  exact (Or.elim (step594 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u1)) (fun r2 => (bool_contra r2 u2)))))))

theorem step1829 (p : Nat → Bool) (h : Constraints p) : p 87 = true ∨ p 109 = false ∨ p 103 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 87 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 109 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 103 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 231 = false := (step715 p h)
  exact (Or.elim (step595 p h) (fun l0 => (bool_contra u1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u0)) (fun r2 => (bool_contra r2 u2)))))))

theorem step1830 (p : Nat → Bool) (h : Constraints p) : p 112 = true ∨ p 110 = false ∨ p 89 = true ∨ p 106 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 112 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 110 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 89 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 106 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 232 = false := (step716 p h)
  exact (Or.elim (step598 p h) (fun l0 => (bool_contra u1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u2)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u3)) (fun r3 => (bool_contra r3 u0)))))))))

theorem step1831 (p : Nat → Bool) (h : Constraints p) : p 44 = true ∨ p 112 = true ∨ p 110 = false ∨ p 106 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 44 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 112 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 110 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 106 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 232 = false := (step716 p h)
  exact (Or.elim (step599 p h) (fun l0 => (bool_contra u2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u0)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u3)) (fun r3 => (bool_contra r3 u1)))))))))

theorem step1832 (p : Nat → Bool) (h : Constraints p) : p 44 = true ∨ p 112 = true ∨ p 89 = true ∨ p 110 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 44 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 112 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 89 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 110 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 232 = false := (step716 p h)
  exact (Or.elim (step600 p h) (fun l0 => (bool_contra u3 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u0)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u2)) (fun r3 => (bool_contra r3 u1)))))))))

theorem step1833 (p : Nat → Bool) (h : Constraints p) : p 44 = true ∨ p 110 = false ∨ p 89 = true ∨ p 106 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 44 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 110 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 89 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 106 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 232 = false := (step716 p h)
  exact (Or.elim (step601 p h) (fun l0 => (bool_contra u1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u0)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u2)) (fun r3 => (bool_contra r3 u3)))))))))

theorem step1834 (p : Nat → Bool) (h : Constraints p) : p 120 = true ∨ p 112 = true ∨ p 111 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 120 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 112 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 111 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 233 = false := (step717 p h)
  exact (Or.elim (step603 p h) (fun l0 => (bool_contra u2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u1)) (fun r2 => (bool_contra r2 u0)))))))

theorem step1835 (p : Nat → Bool) (h : Constraints p) : p 120 = true ∨ p 111 = false ∨ p 107 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 120 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 111 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 107 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 233 = false := (step717 p h)
  exact (Or.elim (step604 p h) (fun l0 => (bool_contra u1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u2)) (fun r2 => (bool_contra r2 u0)))))))

theorem step1836 (p : Nat → Bool) (h : Constraints p) : p 112 = true ∨ p 111 = false ∨ p 107 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 112 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 111 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 107 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 233 = false := (step717 p h)
  exact (Or.elim (step605 p h) (fun l0 => (bool_contra u1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u2)) (fun r2 => (bool_contra r2 u0)))))))

theorem step1837 (p : Nat → Bool) (h : Constraints p) : p 114 = true ∨ p 115 = true ∨ p 118 = true ∨ p 113 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 114 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 115 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 118 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 113 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 235 = false := (step718 p h)
  exact (Or.elim (step612 p h) (fun l0 => (bool_contra u3 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u0)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u1)) (fun r3 => (bool_contra r3 u2)))))))))

theorem step1838 (p : Nat → Bool) (h : Constraints p) : p 115 = true ∨ p 113 = false ∨ p 118 = true ∨ p 103 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 115 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 113 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 118 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 103 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 235 = false := (step718 p h)
  exact (Or.elim (step613 p h) (fun l0 => (bool_contra u1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u3)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u0)) (fun r3 => (bool_contra r3 u2)))))))))

theorem step1839 (p : Nat → Bool) (h : Constraints p) : p 114 = true ∨ p 113 = false ∨ p 118 = true ∨ p 103 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 114 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 113 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 118 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 103 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 235 = false := (step718 p h)
  exact (Or.elim (step614 p h) (fun l0 => (bool_contra u1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u3)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u0)) (fun r3 => (bool_contra r3 u2)))))))))

theorem step1840 (p : Nat → Bool) (h : Constraints p) : p 115 = true ∨ p 114 = true ∨ p 103 = true ∨ p 113 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 115 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 114 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 103 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 113 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 235 = false := (step718 p h)
  exact (Or.elim (step615 p h) (fun l0 => (bool_contra u3 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u2)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u1)) (fun r3 => (bool_contra r3 u0)))))))))

theorem step1841 (p : Nat → Bool) (h : Constraints p) : p 114 = true ∨ p 115 = true ∨ p 106 = true ∨ p 116 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 114 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 115 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 106 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 116 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 238 = false := (step719 p h)
  exact (Or.elim (step628 p h) (fun l0 => (bool_contra u3 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u2)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u0)) (fun r3 => (bool_contra r3 u1)))))))))

theorem step1842 (p : Nat → Bool) (h : Constraints p) : p 114 = true ∨ p 115 = true ∨ p 116 = false ∨ p 94 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 114 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 115 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 116 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 94 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 238 = false := (step719 p h)
  exact (Or.elim (step629 p h) (fun l0 => (bool_contra u2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u3)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u0)) (fun r3 => (bool_contra r3 u1)))))))))

theorem step1843 (p : Nat → Bool) (h : Constraints p) : p 115 = true ∨ p 94 = true ∨ p 116 = false ∨ p 106 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 115 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 94 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 116 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 106 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 238 = false := (step719 p h)
  exact (Or.elim (step630 p h) (fun l0 => (bool_contra u2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u1)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u3)) (fun r3 => (bool_contra r3 u0)))))))))

theorem step1844 (p : Nat → Bool) (h : Constraints p) : p 114 = true ∨ p 94 = true ∨ p 116 = false ∨ p 106 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 114 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 94 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 116 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 106 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 238 = false := (step719 p h)
  exact (Or.elim (step631 p h) (fun l0 => (bool_contra u2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u1)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 u3)) (fun r3 => (bool_contra r3 u0)))))))))

theorem step1845 (p : Nat → Bool) (h : Constraints p) : p 115 = true ∨ p 117 = false ∨ p 121 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 115 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 117 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 121 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 239 = false := (step720 p h)
  exact (Or.elim (step633 p h) (fun l0 => (bool_contra u1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u0)) (fun r2 => (bool_contra r2 u2)))))))

theorem step1846 (p : Nat → Bool) (h : Constraints p) : p 117 = false ∨ p 121 = true ∨ p 108 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 117 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 121 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 108 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 239 = false := (step720 p h)
  exact (Or.elim (step634 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u2)) (fun r2 => (bool_contra r2 u1)))))))

theorem step1847 (p : Nat → Bool) (h : Constraints p) : p 115 = true ∨ p 117 = false ∨ p 108 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 115 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 117 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 108 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 239 = false := (step720 p h)
  exact (Or.elim (step635 p h) (fun l0 => (bool_contra u1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u2)) (fun r2 => (bool_contra r2 u0)))))))

theorem step1848 (p : Nat → Bool) (h : Constraints p) : p 121 = true ∨ p 120 = true ∨ p 119 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 121 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 120 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 119 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 241 = false := (step721 p h)
  exact (Or.elim (step648 p h) (fun l0 => (bool_contra u2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u1)) (fun r2 => (bool_contra r2 u0)))))))

theorem step1849 (p : Nat → Bool) (h : Constraints p) : p 120 = true ∨ p 119 = false ∨ p 118 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 120 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 119 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 118 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 241 = false := (step721 p h)
  exact (Or.elim (step650 p h) (fun l0 => (bool_contra u1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u2)) (fun r2 => (bool_contra r2 u0)))))))

theorem step1850 (p : Nat → Bool) (h : Constraints p) : p 123 = false ∨ p 245 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 123 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 245 = true := bool_true_of_not_false (fun hl => hc (Or.inr hl))
  have t0 : p 248 = false := (step1570 p h)
  exact (Or.elim (step726 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u1 l1)) (fun r1 => (bool_contra r1 t0)))))

theorem step1851 (p : Nat → Bool) (h : Constraints p) : p 261 = false ∨ p 267 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 261 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 267 = true := bool_true_of_not_false (fun hl => hc (Or.inr hl))
  have t0 : p 270 = false := (step1565 p h)
  exact (Or.elim (step742 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u1 l1)) (fun r1 => (bool_contra r1 t0)))))

theorem step1852 (p : Nat → Bool) (h : Constraints p) : p 255 = false ∨ p 269 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 255 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 269 = true := bool_true_of_not_false (fun hl => hc (Or.inr hl))
  have t0 : p 272 = false := (step1559 p h)
  exact (Or.elim (step746 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u1 l1)) (fun r1 => (bool_contra r1 t0)))))

theorem step1853 (p : Nat → Bool) (h : Constraints p) : p 271 = false ∨ p 299 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 271 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 299 = true := bool_true_of_not_false (fun hl => hc (Or.inr hl))
  have t0 : p 302 = false := (step1554 p h)
  exact (Or.elim (step770 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u1 l1)) (fun r1 => (bool_contra r1 t0)))))

theorem step1854 (p : Nat → Bool) (h : Constraints p) : p 173 = false ∨ p 174 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 173 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 174 = true := bool_true_of_not_false (fun hl => hc (Or.inr hl))
  have t0 : p 338 = false := (step1572 p h)
  exact (Or.elim (step794 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u1 l1)) (fun r1 => (bool_contra r1 t0)))))

theorem step1855 (p : Nat → Bool) (h : Constraints p) : p 347 = false ∨ p 353 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 347 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 353 = true := bool_true_of_not_false (fun hl => hc (Or.inr hl))
  have t0 : p 356 = false := (step1563 p h)
  exact (Or.elim (step808 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u1 l1)) (fun r1 => (bool_contra r1 t0)))))

theorem step1856 (p : Nat → Bool) (h : Constraints p) : p 341 = false ∨ p 355 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 341 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 355 = true := bool_true_of_not_false (fun hl => hc (Or.inr hl))
  have t0 : p 358 = false := (step1558 p h)
  exact (Or.elim (step812 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u1 l1)) (fun r1 => (bool_contra r1 t0)))))

theorem step1857 (p : Nat → Bool) (h : Constraints p) : p 301 = false ∨ p 359 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 301 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 359 = true := bool_true_of_not_false (fun hl => hc (Or.inr hl))
  have t0 : p 362 = false := (step1550 p h)
  exact (Or.elim (step820 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u1 l1)) (fun r1 => (bool_contra r1 t0)))))

theorem step1858 (p : Nat → Bool) (h : Constraints p) : p 192 = false ∨ p 193 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 192 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 193 = true := bool_true_of_not_false (fun hl => hc (Or.inr hl))
  have t0 : p 378 = false := (step1571 p h)
  exact (Or.elim (step832 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u1 l1)) (fun r1 => (bool_contra r1 t0)))))

theorem step1859 (p : Nat → Bool) (h : Constraints p) : p 379 = false ∨ p 385 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 379 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 385 = true := bool_true_of_not_false (fun hl => hc (Or.inr hl))
  have t0 : p 388 = false := (step1562 p h)
  exact (Or.elim (step840 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u1 l1)) (fun r1 => (bool_contra r1 t0)))))

theorem step1860 (p : Nat → Bool) (h : Constraints p) : p 373 = false ∨ p 387 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 373 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 387 = true := bool_true_of_not_false (fun hl => hc (Or.inr hl))
  have t0 : p 390 = false := (step1557 p h)
  exact (Or.elim (step845 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u1 l1)) (fun r1 => (bool_contra r1 t0)))))

theorem step1861 (p : Nat → Bool) (h : Constraints p) : p 393 = false ∨ p 399 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 393 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 399 = true := bool_true_of_not_false (fun hl => hc (Or.inr hl))
  have t0 : p 402 = false := (step1561 p h)
  exact (Or.elim (step855 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u1 l1)) (fun r1 => (bool_contra r1 t0)))))

theorem step1862 (p : Nat → Bool) (h : Constraints p) : p 401 = false ∨ p 415 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 401 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 415 = true := bool_true_of_not_false (fun hl => hc (Or.inr hl))
  have t0 : p 418 = false := (step1556 p h)
  exact (Or.elim (step866 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u1 l1)) (fun r1 => (bool_contra r1 t0)))))

theorem step1863 (p : Nat → Bool) (h : Constraints p) : p 389 = false ∨ p 417 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 389 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 417 = true := bool_true_of_not_false (fun hl => hc (Or.inr hl))
  have t0 : p 420 = false := (step1552 p h)
  exact (Or.elim (step871 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u1 l1)) (fun r1 => (bool_contra r1 t0)))))

theorem step1864 (p : Nat → Bool) (h : Constraints p) : p 469 = false ∨ p 471 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 469 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 471 = true := bool_true_of_not_false (fun hl => hc (Or.inr hl))
  have t0 : p 474 = false := (step1567 p h)
  exact (Or.elim (step907 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u1 l1)) (fun r1 => (bool_contra r1 t0)))))

theorem step1865 (p : Nat → Bool) (h : Constraints p) : p 447 = false ∨ p 477 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 447 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 477 = true := bool_true_of_not_false (fun hl => hc (Or.inr hl))
  have t0 : p 480 = false := (step1551 p h)
  exact (Or.elim (step917 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u1 l1)) (fun r1 => (bool_contra r1 t0)))))

theorem step1866 (p : Nat → Bool) (h : Constraints p) : p 419 = false ∨ p 479 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 419 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 479 = true := bool_true_of_not_false (fun hl => hc (Or.inr hl))
  have t0 : p 482 = false := (step1549 p h)
  exact (Or.elim (step921 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u1 l1)) (fun r1 => (bool_contra r1 t0)))))

theorem step1867 (p : Nat → Bool) (h : Constraints p) : p 361 = false ∨ p 481 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 361 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 481 = true := bool_true_of_not_false (fun hl => hc (Or.inr hl))
  have t0 : p 484 = false := (step926 p h)
  exact (Or.elim (step924 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u1 l1)) (fun r1 => (bool_contra r1 t0)))))

end Dfs112FirstBoolean
