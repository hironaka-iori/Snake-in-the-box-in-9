import Dfs112FirstBooleanInputs
namespace Dfs112FirstBoolean
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem step1548 (p : Nat → Bool) (h : Constraints p) : p 74 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 74 = false := bool_false_of_not_true (fun hl => hc hl)
  have t0 : p 76 = true := (step289 p h)
  exact (Or.elim (step288 p h) (fun l0 => (bool_contra t0 l0)) (fun r0 => (bool_contra r0 u0)))

theorem step1549 (p : Nat → Bool) (h : Constraints p) : p 482 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 482 = true := bool_true_of_not_false (fun hl => hc hl)
  have t0 : p 484 = false := (step926 p h)
  exact (Or.elim (step923 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (bool_contra r0 t0)))

theorem step1550 (p : Nat → Bool) (h : Constraints p) : p 362 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 362 = true := bool_true_of_not_false (fun hl => hc hl)
  have t0 : p 484 = false := (step926 p h)
  exact (Or.elim (step925 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (bool_contra r0 t0)))

theorem step1551 (p : Nat → Bool) (h : Constraints p) : p 480 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 480 = true := bool_true_of_not_false (fun hl => hc hl)
  have t0 : p 482 = false := (step1549 p h)
  exact (Or.elim (step919 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (bool_contra r0 t0)))

theorem step1552 (p : Nat → Bool) (h : Constraints p) : p 420 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 420 = true := bool_true_of_not_false (fun hl => hc hl)
  have t0 : p 482 = false := (step1549 p h)
  exact (Or.elim (step922 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (bool_contra r0 t0)))

theorem step1553 (p : Nat → Bool) (h : Constraints p) : p 360 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 360 = true := bool_true_of_not_false (fun hl => hc hl)
  have t0 : p 362 = false := (step1550 p h)
  exact (Or.elim (step818 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (bool_contra r0 t0)))

theorem step1554 (p : Nat → Bool) (h : Constraints p) : p 302 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 302 = true := bool_true_of_not_false (fun hl => hc hl)
  have t0 : p 362 = false := (step1550 p h)
  exact (Or.elim (step821 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (bool_contra r0 t0)))

theorem step1555 (p : Nat → Bool) (h : Constraints p) : p 478 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 478 = true := bool_true_of_not_false (fun hl => hc hl)
  have t0 : p 480 = false := (step1551 p h)
  exact (Or.elim (step915 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (bool_contra r0 t0)))

theorem step1556 (p : Nat → Bool) (h : Constraints p) : p 418 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 418 = true := bool_true_of_not_false (fun hl => hc hl)
  have t0 : p 420 = false := (step1552 p h)
  exact (Or.elim (step869 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (bool_contra r0 t0)))

theorem step1557 (p : Nat → Bool) (h : Constraints p) : p 390 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 390 = true := bool_true_of_not_false (fun hl => hc hl)
  have t0 : p 420 = false := (step1552 p h)
  exact (Or.elim (step872 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (bool_contra r0 t0)))

theorem step1558 (p : Nat → Bool) (h : Constraints p) : p 358 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 358 = true := bool_true_of_not_false (fun hl => hc hl)
  have t0 : p 360 = false := (step1553 p h)
  exact (Or.elim (step815 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (bool_contra r0 t0)))

theorem step1559 (p : Nat → Bool) (h : Constraints p) : p 272 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 272 = true := bool_true_of_not_false (fun hl => hc hl)
  have t0 : p 302 = false := (step1554 p h)
  exact (Or.elim (step771 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (bool_contra r0 t0)))

theorem step1560 (p : Nat → Bool) (h : Constraints p) : p 476 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 476 = true := bool_true_of_not_false (fun hl => hc hl)
  have t0 : p 478 = false := (step1555 p h)
  exact (Or.elim (step912 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (bool_contra r0 t0)))

theorem step1561 (p : Nat → Bool) (h : Constraints p) : p 402 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 402 = true := bool_true_of_not_false (fun hl => hc hl)
  have t0 : p 418 = false := (step1556 p h)
  exact (Or.elim (step867 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (bool_contra r0 t0)))

theorem step1562 (p : Nat → Bool) (h : Constraints p) : p 388 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 388 = true := bool_true_of_not_false (fun hl => hc hl)
  have t0 : p 390 = false := (step1557 p h)
  exact (Or.elim (step843 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (bool_contra r0 t0)))

theorem step1563 (p : Nat → Bool) (h : Constraints p) : p 356 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 356 = true := bool_true_of_not_false (fun hl => hc hl)
  have t0 : p 358 = false := (step1558 p h)
  exact (Or.elim (step810 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (bool_contra r0 t0)))

theorem step1564 (p : Nat → Bool) (h : Constraints p) : p 342 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 342 = true := bool_true_of_not_false (fun hl => hc hl)
  have t0 : p 358 = false := (step1558 p h)
  exact (Or.elim (step813 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (bool_contra r0 t0)))

theorem step1565 (p : Nat → Bool) (h : Constraints p) : p 270 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 270 = true := bool_true_of_not_false (fun hl => hc hl)
  have t0 : p 272 = false := (step1559 p h)
  exact (Or.elim (step744 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (bool_contra r0 t0)))

theorem step1566 (p : Nat → Bool) (h : Constraints p) : p 256 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 256 = true := bool_true_of_not_false (fun hl => hc hl)
  have t0 : p 272 = false := (step1559 p h)
  exact (Or.elim (step747 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (bool_contra r0 t0)))

theorem step1567 (p : Nat → Bool) (h : Constraints p) : p 474 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 474 = true := bool_true_of_not_false (fun hl => hc hl)
  have t0 : p 476 = false := (step1560 p h)
  exact (Or.elim (step909 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (bool_contra r0 t0)))

theorem step1568 (p : Nat → Bool) (h : Constraints p) : p 380 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 380 = true := bool_true_of_not_false (fun hl => hc hl)
  have t0 : p 388 = false := (step1562 p h)
  exact (Or.elim (step841 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (bool_contra r0 t0)))

theorem step1569 (p : Nat → Bool) (h : Constraints p) : p 340 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 340 = true := bool_true_of_not_false (fun hl => hc hl)
  have t0 : p 342 = false := (step1564 p h)
  exact (Or.elim (step798 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (bool_contra r0 t0)))

theorem step1570 (p : Nat → Bool) (h : Constraints p) : p 248 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 248 = true := bool_true_of_not_false (fun hl => hc hl)
  have t0 : p 256 = false := (step1566 p h)
  exact (Or.elim (step733 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (bool_contra r0 t0)))

theorem step1571 (p : Nat → Bool) (h : Constraints p) : p 378 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 378 = true := bool_true_of_not_false (fun hl => hc hl)
  have t0 : p 380 = false := (step1568 p h)
  exact (Or.elim (step834 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (bool_contra r0 t0)))

theorem step1572 (p : Nat → Bool) (h : Constraints p) : p 338 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 338 = true := bool_true_of_not_false (fun hl => hc hl)
  have t0 : p 340 = false := (step1569 p h)
  exact (Or.elim (step796 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (bool_contra r0 t0)))

theorem step1573 (p : Nat → Bool) (h : Constraints p) : p 123 = true ∨ p 125 = true ∨ p 127 = true ∨ p 129 = true ∨ p 131 = true ∨ p 133 = true ∨ p 136 = true ∨ p 138 = true ∨ p 139 = true ∨ p 142 = true ∨ p 144 = true ∨ p 147 = true ∨ p 150 = true ∨ p 151 = true ∨ p 152 = true ∨ p 154 = true ∨ p 158 = true ∨ p 159 = true ∨ p 160 = true ∨ p 162 = true ∨ p 166 = true ∨ p 168 = true ∨ p 170 = true ∨ p 173 = true ∨ p 174 = true ∨ p 176 = true ∨ p 177 = true ∨ p 179 = true ∨ p 180 = true ∨ p 185 = true ∨ p 187 = true ∨ p 188 = true ∨ p 192 = true ∨ p 193 = true ∨ p 196 = true ∨ p 197 = true ∨ p 200 = true ∨ p 203 = true ∨ p 204 = true ∨ p 205 = true ∨ p 208 = true ∨ p 209 = true ∨ p 211 = true ∨ p 213 = true ∨ p 216 = true ∨ p 218 = true ∨ p 221 = true ∨ p 222 = true ∨ p 224 = true ∨ p 225 = true ∨ p 228 = true ∨ p 229 = true ∨ p 230 = true ∨ p 234 = true ∨ p 236 = true ∨ p 237 = true ∨ p 240 = true ∨ p 242 = true ∨ p 243 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 123 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 125 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 127 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 129 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 131 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 133 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))
  have u6 : p 136 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))))
  have u7 : p 138 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))))
  have u8 : p 139 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))))))
  have u9 : p 142 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))))))
  have u10 : p 144 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))))))))
  have u11 : p 147 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))))))))
  have u12 : p 150 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))))))))))
  have u13 : p 151 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))))))))))
  have u14 : p 152 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))))))))))))
  have u15 : p 154 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))))))))))))
  have u16 : p 158 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))))))))))))))
  have u17 : p 159 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))))))))))))))
  have u18 : p 160 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))))))))))))))))
  have u19 : p 162 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))))))))))))))))
  have u20 : p 166 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))))))))))))))))))
  have u21 : p 168 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))))))))))))))))))
  have u22 : p 170 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))))))))))))))))))))
  have u23 : p 173 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))))))))))))))))))))
  have u24 : p 174 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))))))))))))))))))))))
  have u25 : p 176 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))))))))))))))))))))))
  have u26 : p 177 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))))))))))))))))))))))))
  have u27 : p 179 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))))))))))))))))))))))))
  have u28 : p 180 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))))))))))))))))))))))))))
  have u29 : p 185 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))))))))))))))))))))))))))
  have u30 : p 187 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))))))))))))))))))))))))))))
  have u31 : p 188 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))))))))))))))))))))))))))))
  have u32 : p 192 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))))))))))))))))))))))))))))))
  have u33 : p 193 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))))))))))))))))))))))))))))))
  have u34 : p 196 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))))))))))))))))))))))))))))))))
  have u35 : p 197 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))))))))))))))))))))))))))))))))
  have u36 : p 200 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))))))))))))))))))))))))))))))))))
  have u37 : p 203 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))))))))))))))))))))))))))))))))))
  have u38 : p 204 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))))))))))))))))))))))))))))))))))))
  have u39 : p 205 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))))))))))))))))))))))))))))))))))))
  have u40 : p 208 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))))))))))))))))))))))))))))))))))))))
  have u41 : p 209 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))))))))))))))))))))))))))))))))))))))
  have u42 : p 211 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))))))))))))))))))))))))))))))))))))))))
  have u43 : p 213 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))))))))))))))))))))))))))))))))))))))))
  have u44 : p 216 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))))))))))))))))))))))))))))))))))))))))))
  have u45 : p 218 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))))))))))))))))))))))))))))))))))))))))))
  have u46 : p 221 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))))))))))))))))))))))))))))))))))))))))))))
  have u47 : p 222 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))))))))))))))))))))))))))))))))))))))))))))
  have u48 : p 224 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))))))))))))))))))))))))))))))))))))))))))))))
  have u49 : p 225 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))))))))))))))))))))))))))))))))))))))))))))))
  have u50 : p 228 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))))))))))))))))))))))))))))))))))))))))))))))))
  have u51 : p 229 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))))))))))))))))))))))))))))))))))))))))))))))))
  have u52 : p 230 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))))))))))))))))))))))))))))))))))))))))))))))))))
  have u53 : p 234 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))))))))))))))))))))))))))))))))))))))))))))))))))
  have u54 : p 236 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  have u55 : p 237 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  have u56 : p 240 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  have u57 : p 242 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  have u58 : p 243 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  have t0 : p 124 = false := (step661 p h)
  have t1 : p 126 = false := (step662 p h)
  have t2 : p 128 = false := (step663 p h)
  have t3 : p 130 = false := (step664 p h)
  have t4 : p 132 = false := (step665 p h)
  have t5 : p 134 = false := (step666 p h)
  have t6 : p 135 = false := (step667 p h)
  have t7 : p 137 = false := (step668 p h)
  have t8 : p 140 = false := (step669 p h)
  have t9 : p 141 = false := (step670 p h)
  have t10 : p 143 = false := (step671 p h)
  have t11 : p 145 = false := (step672 p h)
  have t12 : p 146 = false := (step673 p h)
  have t13 : p 148 = false := (step674 p h)
  have t14 : p 149 = false := (step675 p h)
  have t15 : p 153 = false := (step676 p h)
  have t16 : p 155 = false := (step677 p h)
  have t17 : p 156 = false := (step678 p h)
  have t18 : p 157 = false := (step679 p h)
  have t19 : p 161 = false := (step680 p h)
  have t20 : p 163 = false := (step681 p h)
  have t21 : p 164 = false := (step682 p h)
  have t22 : p 165 = false := (step683 p h)
  have t23 : p 167 = false := (step684 p h)
  have t24 : p 169 = false := (step685 p h)
  have t25 : p 171 = false := (step686 p h)
  have t26 : p 172 = false := (step687 p h)
  have t27 : p 175 = false := (step688 p h)
  have t28 : p 178 = false := (step689 p h)
  have t29 : p 181 = false := (step690 p h)
  have t30 : p 182 = false := (step691 p h)
  have t31 : p 183 = false := (step692 p h)
  have t32 : p 184 = false := (step693 p h)
  have t33 : p 186 = false := (step694 p h)
  have t34 : p 189 = false := (step695 p h)
  have t35 : p 190 = false := (step696 p h)
  have t36 : p 191 = false := (step697 p h)
  have t37 : p 194 = false := (step698 p h)
  have t38 : p 195 = false := (step699 p h)
  have t39 : p 199 = false := (step700 p h)
  have t40 : p 201 = false := (step701 p h)
  have t41 : p 202 = false := (step702 p h)
  have t42 : p 206 = false := (step703 p h)
  have t43 : p 207 = false := (step704 p h)
  have t44 : p 210 = false := (step705 p h)
  have t45 : p 212 = false := (step706 p h)
  have t46 : p 214 = false := (step707 p h)
  have t47 : p 215 = false := (step708 p h)
  have t48 : p 217 = false := (step709 p h)
  have t49 : p 219 = false := (step710 p h)
  have t50 : p 220 = false := (step711 p h)
  have t51 : p 223 = false := (step712 p h)
  have t52 : p 226 = false := (step713 p h)
  have t53 : p 227 = false := (step714 p h)
  have t54 : p 231 = false := (step715 p h)
  have t55 : p 232 = false := (step716 p h)
  have t56 : p 233 = false := (step717 p h)
  have t57 : p 235 = false := (step718 p h)
  have t58 : p 238 = false := (step719 p h)
  have t59 : p 239 = false := (step720 p h)
  have t60 : p 241 = false := (step721 p h)
  have t61 : p 244 = false := (step722 p h)
  exact (Or.elim (step927 p h) (fun l0 => (bool_contra l0 u0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 u1)) (fun r2 => (Or.elim r2 (fun l3 => (bool_contra l3 t1)) (fun r3 => (Or.elim r3 (fun l4 => (bool_contra l4 u2)) (fun r4 => (Or.elim r4 (fun l5 => (bool_contra l5 t2)) (fun r5 => (Or.elim r5 (fun l6 => (bool_contra l6 u3)) (fun r6 => (Or.elim r6 (fun l7 => (bool_contra l7 t3)) (fun r7 => (Or.elim r7 (fun l8 => (bool_contra l8 u4)) (fun r8 => (Or.elim r8 (fun l9 => (bool_contra l9 t4)) (fun r9 => (Or.elim r9 (fun l10 => (bool_contra l10 u5)) (fun r10 => (Or.elim r10 (fun l11 => (bool_contra l11 t5)) (fun r11 => (Or.elim r11 (fun l12 => (bool_contra l12 t6)) (fun r12 => (Or.elim r12 (fun l13 => (bool_contra l13 u6)) (fun r13 => (Or.elim r13 (fun l14 => (bool_contra l14 t7)) (fun r14 => (Or.elim r14 (fun l15 => (bool_contra l15 u7)) (fun r15 => (Or.elim r15 (fun l16 => (bool_contra l16 u8)) (fun r16 => (Or.elim r16 (fun l17 => (bool_contra l17 t8)) (fun r17 => (Or.elim r17 (fun l18 => (bool_contra l18 t9)) (fun r18 => (Or.elim r18 (fun l19 => (bool_contra l19 u9)) (fun r19 => (Or.elim r19 (fun l20 => (bool_contra l20 t10)) (fun r20 => (Or.elim r20 (fun l21 => (bool_contra l21 u10)) (fun r21 => (Or.elim r21 (fun l22 => (bool_contra l22 t11)) (fun r22 => (Or.elim r22 (fun l23 => (bool_contra l23 t12)) (fun r23 => (Or.elim r23 (fun l24 => (bool_contra l24 u11)) (fun r24 => (Or.elim r24 (fun l25 => (bool_contra l25 t13)) (fun r25 => (Or.elim r25 (fun l26 => (bool_contra l26 t14)) (fun r26 => (Or.elim r26 (fun l27 => (bool_contra l27 u12)) (fun r27 => (Or.elim r27 (fun l28 => (bool_contra l28 u13)) (fun r28 => (Or.elim r28 (fun l29 => (bool_contra l29 u14)) (fun r29 => (Or.elim r29 (fun l30 => (bool_contra l30 t15)) (fun r30 => (Or.elim r30 (fun l31 => (bool_contra l31 u15)) (fun r31 => (Or.elim r31 (fun l32 => (bool_contra l32 t16)) (fun r32 => (Or.elim r32 (fun l33 => (bool_contra l33 t17)) (fun r33 => (Or.elim r33 (fun l34 => (bool_contra l34 t18)) (fun r34 => (Or.elim r34 (fun l35 => (bool_contra l35 u16)) (fun r35 => (Or.elim r35 (fun l36 => (bool_contra l36 u17)) (fun r36 => (Or.elim r36 (fun l37 => (bool_contra l37 u18)) (fun r37 => (Or.elim r37 (fun l38 => (bool_contra l38 t19)) (fun r38 => (Or.elim r38 (fun l39 => (bool_contra l39 u19)) (fun r39 => (Or.elim r39 (fun l40 => (bool_contra l40 t20)) (fun r40 => (Or.elim r40 (fun l41 => (bool_contra l41 t21)) (fun r41 => (Or.elim r41 (fun l42 => (bool_contra l42 t22)) (fun r42 => (Or.elim r42 (fun l43 => (bool_contra l43 u20)) (fun r43 => (Or.elim r43 (fun l44 => (bool_contra l44 t23)) (fun r44 => (Or.elim r44 (fun l45 => (bool_contra l45 u21)) (fun r45 => (Or.elim r45 (fun l46 => (bool_contra l46 t24)) (fun r46 => (Or.elim r46 (fun l47 => (bool_contra l47 u22)) (fun r47 => (Or.elim r47 (fun l48 => (bool_contra l48 t25)) (fun r48 => (Or.elim r48 (fun l49 => (bool_contra l49 t26)) (fun r49 => (Or.elim r49 (fun l50 => (bool_contra l50 u23)) (fun r50 => (Or.elim r50 (fun l51 => (bool_contra l51 u24)) (fun r51 => (Or.elim r51 (fun l52 => (bool_contra l52 t27)) (fun r52 => (Or.elim r52 (fun l53 => (bool_contra l53 u25)) (fun r53 => (Or.elim r53 (fun l54 => (bool_contra l54 u26)) (fun r54 => (Or.elim r54 (fun l55 => (bool_contra l55 t28)) (fun r55 => (Or.elim r55 (fun l56 => (bool_contra l56 u27)) (fun r56 => (Or.elim r56 (fun l57 => (bool_contra l57 u28)) (fun r57 => (Or.elim r57 (fun l58 => (bool_contra l58 t29)) (fun r58 => (Or.elim r58 (fun l59 => (bool_contra l59 t30)) (fun r59 => (Or.elim r59 (fun l60 => (bool_contra l60 t31)) (fun r60 => (Or.elim r60 (fun l61 => (bool_contra l61 t32)) (fun r61 => (Or.elim r61 (fun l62 => (bool_contra l62 u29)) (fun r62 => (Or.elim r62 (fun l63 => (bool_contra l63 t33)) (fun r63 => (Or.elim r63 (fun l64 => (bool_contra l64 u30)) (fun r64 => (Or.elim r64 (fun l65 => (bool_contra l65 u31)) (fun r65 => (Or.elim r65 (fun l66 => (bool_contra l66 t34)) (fun r66 => (Or.elim r66 (fun l67 => (bool_contra l67 t35)) (fun r67 => (Or.elim r67 (fun l68 => (bool_contra l68 t36)) (fun r68 => (Or.elim r68 (fun l69 => (bool_contra l69 u32)) (fun r69 => (Or.elim r69 (fun l70 => (bool_contra l70 u33)) (fun r70 => (Or.elim r70 (fun l71 => (bool_contra l71 t37)) (fun r71 => (Or.elim r71 (fun l72 => (bool_contra l72 t38)) (fun r72 => (Or.elim r72 (fun l73 => (bool_contra l73 u34)) (fun r73 => (Or.elim r73 (fun l74 => (bool_contra l74 u35)) (fun r74 => (Or.elim r74 (fun l75 => (bool_contra l75 t39)) (fun r75 => (Or.elim r75 (fun l76 => (bool_contra l76 u36)) (fun r76 => (Or.elim r76 (fun l77 => (bool_contra l77 t40)) (fun r77 => (Or.elim r77 (fun l78 => (bool_contra l78 t41)) (fun r78 => (Or.elim r78 (fun l79 => (bool_contra l79 u37)) (fun r79 => (Or.elim r79 (fun l80 => (bool_contra l80 u38)) (fun r80 => (Or.elim r80 (fun l81 => (bool_contra l81 u39)) (fun r81 => (Or.elim r81 (fun l82 => (bool_contra l82 t42)) (fun r82 => (Or.elim r82 (fun l83 => (bool_contra l83 t43)) (fun r83 => (Or.elim r83 (fun l84 => (bool_contra l84 u40)) (fun r84 => (Or.elim r84 (fun l85 => (bool_contra l85 u41)) (fun r85 => (Or.elim r85 (fun l86 => (bool_contra l86 t44)) (fun r86 => (Or.elim r86 (fun l87 => (bool_contra l87 u42)) (fun r87 => (Or.elim r87 (fun l88 => (bool_contra l88 t45)) (fun r88 => (Or.elim r88 (fun l89 => (bool_contra l89 u43)) (fun r89 => (Or.elim r89 (fun l90 => (bool_contra l90 t46)) (fun r90 => (Or.elim r90 (fun l91 => (bool_contra l91 t47)) (fun r91 => (Or.elim r91 (fun l92 => (bool_contra l92 u44)) (fun r92 => (Or.elim r92 (fun l93 => (bool_contra l93 t48)) (fun r93 => (Or.elim r93 (fun l94 => (bool_contra l94 u45)) (fun r94 => (Or.elim r94 (fun l95 => (bool_contra l95 t49)) (fun r95 => (Or.elim r95 (fun l96 => (bool_contra l96 t50)) (fun r96 => (Or.elim r96 (fun l97 => (bool_contra l97 u46)) (fun r97 => (Or.elim r97 (fun l98 => (bool_contra l98 u47)) (fun r98 => (Or.elim r98 (fun l99 => (bool_contra l99 t51)) (fun r99 => (Or.elim r99 (fun l100 => (bool_contra l100 u48)) (fun r100 => (Or.elim r100 (fun l101 => (bool_contra l101 u49)) (fun r101 => (Or.elim r101 (fun l102 => (bool_contra l102 t52)) (fun r102 => (Or.elim r102 (fun l103 => (bool_contra l103 t53)) (fun r103 => (Or.elim r103 (fun l104 => (bool_contra l104 u50)) (fun r104 => (Or.elim r104 (fun l105 => (bool_contra l105 u51)) (fun r105 => (Or.elim r105 (fun l106 => (bool_contra l106 u52)) (fun r106 => (Or.elim r106 (fun l107 => (bool_contra l107 t54)) (fun r107 => (Or.elim r107 (fun l108 => (bool_contra l108 t55)) (fun r108 => (Or.elim r108 (fun l109 => (bool_contra l109 t56)) (fun r109 => (Or.elim r109 (fun l110 => (bool_contra l110 u53)) (fun r110 => (Or.elim r110 (fun l111 => (bool_contra l111 t57)) (fun r111 => (Or.elim r111 (fun l112 => (bool_contra l112 u54)) (fun r112 => (Or.elim r112 (fun l113 => (bool_contra l113 u55)) (fun r113 => (Or.elim r113 (fun l114 => (bool_contra l114 t58)) (fun r114 => (Or.elim r114 (fun l115 => (bool_contra l115 t59)) (fun r115 => (Or.elim r115 (fun l116 => (bool_contra l116 u56)) (fun r116 => (Or.elim r116 (fun l117 => (bool_contra l117 t60)) (fun r117 => (Or.elim r117 (fun l118 => (bool_contra l118 u57)) (fun r118 => (Or.elim r118 (fun l119 => (bool_contra l119 u58)) (fun r119 => (bool_contra r119 t61)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem step1574 (p : Nat → Bool) (h : Constraints p) : p 1617 = true ∨ p 1486 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1617 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1486 = false := bool_false_of_not_true (fun hl => hc (Or.inr hl))
  have t0 : p 76 = true := (step289 p h)
  have t1 : p 74 = true := (step1548 p h)
  have t2 : p 141 = false := (step670 p h)
  have t3 : p 73 = true := (Or.elim (step1204 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t4 : p 72 = true := (Or.elim (step1205 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t5 : p 18 = false := (Or.elim (step276 p h) (fun l0 => (False.elim (bool_contra t1 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t4 l2))) (fun r2 => (False.elim (bool_contra t0 r2))))))))
  have t6 : p 1481 = true := (Or.elim (step967 p h) (fun l0 => (False.elim (bool_contra l0 t5))) (fun r0 => r0))
  have t7 : p 1483 = false := (Or.elim (step976 p h) (fun l0 => (False.elim (bool_contra t6 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u1))))))
  have t8 : p 19 = true := (Or.elim (step971 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t7))))
  have t9 : p 75 = true := (Or.elim (step71 p h) (fun l0 => (False.elim (bool_contra t8 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t2))) (fun r1 => r1))))
  have t10 : p 17 = true := (Or.elim (step72 p h) (fun l0 => (False.elim (bool_contra t8 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t2))) (fun r1 => r1))))
  exact (Or.elim (step1509 p h) (fun l0 => (bool_contra t10 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t8 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t3 l2)) (fun r2 => (bool_contra t9 r2)))))))

theorem step1575 (p : Nat → Bool) (h : Constraints p) : p 1493 = true ∨ p 21 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1493 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 21 = true := bool_true_of_not_false (fun hl => hc (Or.inr hl))
  have t0 : p 149 = false := (step675 p h)
  have t1 : p 1491 = false := (Or.elim (step987 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t2 : p 1489 = false := (Or.elim (step989 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t3 : p 27 = true := (Or.elim (step984 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t1))))
  have t4 : p 26 = true := (Or.elim (step985 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t1))))
  have t5 : p 23 = true := (Or.elim (step982 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t2))))
  have t6 : p 25 = false := (Or.elim (step93 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u1 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t4 l2))) (fun r2 => (False.elim (bool_contra t3 r2))))))))
  have t7 : p 28 = false := (Or.elim (step102 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t5 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t4 l2))) (fun r2 => (False.elim (bool_contra t3 r2))))))))
  exact (Or.elim (step101 p h) (fun l0 => (bool_contra t3 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 t6)) (fun r2 => (bool_contra r2 t7)))))))

theorem step1576 (p : Nat → Bool) (h : Constraints p) : p 1474 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1474 = false := bool_false_of_not_true (fun hl => hc hl)
  have t0 : p 135 = false := (step667 p h)
  have t1 : p 1470 = false := (Or.elim (step950 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t2 : p 1463 = false := (Or.elim (step954 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t3 : p 1468 = false := (Or.elim (step942 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t1))))
  have t4 : p 1466 = false := (Or.elim (step944 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t1))))
  have t5 : p 1461 = false := (Or.elim (step931 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t2))))
  have t6 : p 13 = true := (Or.elim (step939 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t3))))
  have t7 : p 8 = true := (Or.elim (step937 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t4))))
  have t8 : p 6 = true := (Or.elim (step928 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t5))))
  have t9 : p 5 = true := (Or.elim (step56 p h) (fun l0 => (False.elim (bool_contra t6 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => r1))))
  exact (Or.elim (step15 p h) (fun l0 => (bool_contra t9 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t8 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t7 l2)) (fun r2 => (bool_contra t6 r2)))))))

theorem step1577 (p : Nat → Bool) (h : Constraints p) : p 1497 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1497 = false := bool_false_of_not_true (fun hl => hc hl)
  have t0 : p 1493 = false := (Or.elim (step994 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t1 : p 1485 = false := (Or.elim (step997 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t2 : p 21 = false := (Or.elim (step1575 p h) (fun l0 => (False.elim (bool_contra l0 t0))) (fun r0 => r0))
  have t3 : p 1483 = false := (Or.elim (step973 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t1))))
  exact (Or.elim (step970 p h) (fun l0 => (bool_contra l0 t2)) (fun r0 => (bool_contra r0 t3)))

theorem step1578 (p : Nat → Bool) (h : Constraints p) : p 1648 = true ∨ p 24 = false ∨ p 1631 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1648 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 24 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1631 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 212 = false := (step706 p h)
  have t1 : p 1635 = true := (Or.elim (step1240 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => r0))
  have t2 : p 1636 = false := (Or.elim (step1265 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t3 : p 1643 = false := (Or.elim (step1261 p h) (fun l0 => (False.elim (bool_contra t1 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t4 : p 1633 = false := (Or.elim (step1241 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t2))))))
  have t5 : p 1641 = false := (Or.elim (step1249 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t3))))
  have t6 : p 1639 = false := (Or.elim (step1251 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t3))))
  have t7 : p 80 = true := (Or.elim (step1235 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t4))))
  have t8 : p 90 = true := (Or.elim (step1246 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t5))))
  have t9 : p 88 = true := (Or.elim (step1247 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t5))))
  have t10 : p 85 = true := (Or.elim (step1243 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t6))))
  have t11 : p 87 = false := (Or.elim (step388 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u1 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t7 l2))) (fun r2 => (False.elim (bool_contra t9 r2))))))))
  have t12 : p 91 = true := (Or.elim (step444 p h) (fun l0 => (False.elim (bool_contra t8 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra l2 t11))) (fun r2 => r2))))))
  exact (Or.elim (step447 p h) (fun l0 => (bool_contra t12 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t10 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t9 l2)) (fun r2 => (bool_contra t8 r2)))))))

theorem step1579 (p : Nat → Bool) (h : Constraints p) : p 1643 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1643 = false := bool_false_of_not_true (fun hl => hc hl)
  have t0 : p 212 = false := (step706 p h)
  have t1 : p 1641 = false := (Or.elim (step1249 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t2 : p 1639 = false := (Or.elim (step1251 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t3 : p 90 = true := (Or.elim (step1246 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t1))))
  have t4 : p 88 = true := (Or.elim (step1247 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t1))))
  have t5 : p 85 = true := (Or.elim (step1243 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t2))))
  have t6 : p 84 = true := (Or.elim (step1244 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t2))))
  have t7 : p 91 = false := (Or.elim (step447 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t5 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t4 l2))) (fun r2 => (False.elim (bool_contra t3 r2))))))))
  have t8 : p 83 = false := (Or.elim (step340 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t6 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t5 l2))) (fun r2 => (False.elim (bool_contra t3 r2))))))))
  exact (Or.elim (step445 p h) (fun l0 => (bool_contra t3 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 t8)) (fun r2 => (bool_contra r2 t7)))))))

theorem step1580 (p : Nat → Bool) (h : Constraints p) : p 61 = false ∨ p 88 = false ∨ p 26 = false ∨ p 15 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 61 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 88 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 26 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 15 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 183 = false := (step692 p h)
  have t1 : p 89 = false := (Or.elim (step425 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u2 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u0 l2))) (fun r2 => (False.elim (bool_contra u1 r2))))))))
  have t2 : p 7 = false := (Or.elim (step40 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u3 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u2 l2))) (fun r2 => (False.elim (bool_contra u0 r2))))))))
  exact (Or.elim (step229 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 t2)) (fun r2 => (bool_contra r2 t1)))))))

theorem step1581 (p : Nat → Bool) (h : Constraints p) : p 1661 = true ∨ p 1557 = true ∨ p 1607 = false ∨ p 80 = true ∨ p 1631 = false ∨ p 1618 = false ∨ p 19 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1661 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1557 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 1607 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 80 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 1631 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 1618 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))
  have u6 : p 19 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl)))))))
  have t0 : p 141 = false := (step670 p h)
  have t1 : p 1643 = true := (step1579 p h)
  have t2 : p 189 = false := (step695 p h)
  have t3 : p 1620 = true := (Or.elim (step1208 p h) (fun l0 => (False.elim (bool_contra u5 l0))) (fun r0 => r0))
  have t4 : p 1611 = true := (Or.elim (step1195 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => r0))
  have t5 : p 1625 = true := (Or.elim (step1220 p h) (fun l0 => (False.elim (bool_contra t4 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t3 l1))) (fun r1 => r1))))
  have t6 : p 1633 = true := (Or.elim (step1235 p h) (fun l0 => (False.elim (bool_contra l0 u3))) (fun r0 => r0))
  have t7 : p 1636 = true := (Or.elim (step1241 p h) (fun l0 => (False.elim (bool_contra u4 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t6 l1))) (fun r1 => r1))))
  have t8 : p 1649 = true := (Or.elim (step1266 p h) (fun l0 => (False.elim (bool_contra t7 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t1 l1))) (fun r1 => r1))))
  have t9 : p 75 = true := (Or.elim (step71 p h) (fun l0 => (False.elim (bool_contra u6 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => r1))))
  have t10 : p 1626 = false := (Or.elim (step1302 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t8 l1))) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t11 : p 1650 = false := (Or.elim (step1296 p h) (fun l0 => (False.elim (bool_contra t5 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t12 : p 1612 = false := (Or.elim (step1225 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t3 l1))) (fun r1 => (False.elim (bool_contra r1 t10))))))
  have t13 : p 1621 = false := (Or.elim (step1221 p h) (fun l0 => (False.elim (bool_contra t4 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t10))))))
  have t14 : p 1637 = false := (Or.elim (step1271 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t1 l1))) (fun r1 => (False.elim (bool_contra r1 t11))))))
  have t15 : p 1609 = false := (Or.elim (step1196 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t12))))))
  have t16 : p 1615 = false := (Or.elim (step1211 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u5 l1))) (fun r1 => (False.elim (bool_contra r1 t13))))))
  have t17 : p 1634 = false := (Or.elim (step1242 p h) (fun l0 => (False.elim (bool_contra u4 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t14))))))
  have t18 : p 67 = true := (Or.elim (step1190 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t15))))
  have t19 : p 64 = true := (Or.elim (step1191 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t15))))
  have t20 : p 68 = true := (Or.elim (step1202 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t16))))
  have t21 : p 79 = true := (Or.elim (step1237 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u3))) (fun r1 => (False.elim (bool_contra r1 t17))))))
  have t22 : p 66 = false := (Or.elim (step251 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t19 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t18 l2))) (fun r2 => (False.elim (bool_contra t20 r2))))))))
  have t23 : p 59 = false := (Or.elim (step281 p h) (fun l0 => (False.elim (bool_contra t9 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u6 l1))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra t21 r2))))))))
  have t24 : p 65 = true := (Or.elim (step257 p h) (fun l0 => (False.elim (bool_contra t18 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t2))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra r2 t22))))))))
  have t25 : p 1554 = true := (Or.elim (step1088 p h) (fun l0 => (False.elim (bool_contra l0 t23))) (fun r0 => r0))
  have t26 : p 56 = false := (Or.elim (step245 p h) (fun l0 => (False.elim (bool_contra t24 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t19 l2))) (fun r2 => (False.elim (bool_contra t18 r2))))))))
  have t27 : p 1552 = false := (Or.elim (step1093 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t25 l1))) (fun r1 => (False.elim (bool_contra r1 u1))))))
  exact (Or.elim (step1084 p h) (fun l0 => (bool_contra l0 t26)) (fun r0 => (bool_contra r0 t27)))

theorem step1582 (p : Nat → Bool) (h : Constraints p) : p 60 = false ∨ p 1471 = true ∨ p 5 = false ∨ p 24 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 60 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 1471 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 5 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 24 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 8 = false := (Or.elim (step23 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u3 l2))) (fun r2 => (False.elim (bool_contra u0 r2))))))))
  have t1 : p 13 = false := (Or.elim (step24 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u3 l2))) (fun r2 => (False.elim (bool_contra u0 r2))))))))
  have t2 : p 1466 = true := (Or.elim (step937 p h) (fun l0 => (False.elim (bool_contra l0 t0))) (fun r0 => r0))
  have t3 : p 1468 = true := (Or.elim (step939 p h) (fun l0 => (False.elim (bool_contra l0 t1))) (fun r0 => r0))
  exact (Or.elim (step945 p h) (fun l0 => (bool_contra t2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t3 l1)) (fun r1 => (bool_contra r1 u1)))))

theorem step1583 (p : Nat → Bool) (h : Constraints p) : p 1544 = true ∨ p 18 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1544 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 18 = true := bool_true_of_not_false (fun hl => hc (Or.inr hl))
  have t0 : p 167 = false := (step684 p h)
  have t1 : p 47 = true := (Or.elim (step1070 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t2 : p 45 = true := (Or.elim (step1071 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t3 : p 40 = true := (Or.elim (step157 p h) (fun l0 => (False.elim (bool_contra t2 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => r1))))
  exact (Or.elim (step143 p h) (fun l0 => (bool_contra t3 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u1 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t2 l2)) (fun r2 => (bool_contra t1 r2)))))))

theorem step1584 (p : Nat → Bool) (h : Constraints p) : p 1626 = true ∨ p 84 = false ∨ p 59 = false ∨ p 61 = true ∨ p 1618 = false ∨ p 75 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1626 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 84 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 59 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 61 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 1618 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 75 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl))))))
  have t0 : p 184 = false := (step693 p h)
  have t1 : p 190 = false := (step696 p h)
  have t2 : p 1607 = true := (Or.elim (step1188 p h) (fun l0 => (False.elim (bool_contra l0 u3))) (fun r0 => r0))
  have t3 : p 1611 = true := (Or.elim (step1195 p h) (fun l0 => (False.elim (bool_contra t2 l0))) (fun r0 => r0))
  have t4 : p 1620 = true := (Or.elim (step1208 p h) (fun l0 => (False.elim (bool_contra u4 l0))) (fun r0 => r0))
  have t5 : p 1612 = false := (Or.elim (step1225 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t4 l1))) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t6 : p 1621 = false := (Or.elim (step1221 p h) (fun l0 => (False.elim (bool_contra t3 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t7 : p 1608 = false := (Or.elim (step1198 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t5))))
  have t8 : p 1609 = false := (Or.elim (step1196 p h) (fun l0 => (False.elim (bool_contra t2 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t5))))))
  have t9 : p 1615 = false := (Or.elim (step1211 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u4 l1))) (fun r1 => (False.elim (bool_contra r1 t6))))))
  have t10 : p 62 = true := (Or.elim (step1189 p h) (fun l0 => (False.elim (bool_contra l0 u3))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t7))))))
  have t11 : p 67 = true := (Or.elim (step1190 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t8))))
  have t12 : p 64 = true := (Or.elim (step1191 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t8))))
  have t13 : p 68 = true := (Or.elim (step1202 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t9))))
  have t14 : p 57 = false := (Or.elim (step213 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u2 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t10 l2))) (fun r2 => (False.elim (bool_contra u1 r2))))))))
  have t15 : p 66 = false := (Or.elim (step251 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t12 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t11 l2))) (fun r2 => (False.elim (bool_contra t13 r2))))))))
  have t16 : p 63 = true := (Or.elim (step234 p h) (fun l0 => (False.elim (bool_contra t10 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t0))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra l2 t14))) (fun r2 => r2))))))
  have t17 : p 58 = true := (Or.elim (step261 p h) (fun l0 => (False.elim (bool_contra t13 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t1))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra r2 t15))))))))
  exact (Or.elim (step220 p h) (fun l0 => (bool_contra u2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t17 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t16 l2)) (fun r2 => (bool_contra u5 r2)))))))

theorem step1585 (p : Nat → Bool) (h : Constraints p) : p 1647 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1647 = false := bool_false_of_not_true (fun hl => hc hl)
  have t0 : p 1643 = true := (step1579 p h)
  exact (Or.elim (step1257 p h) (fun l0 => (bool_contra t0 l0)) (fun r0 => (bool_contra r0 u0)))

theorem step1586 (p : Nat → Bool) (h : Constraints p) : p 1711 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1711 = false := bool_false_of_not_true (fun hl => hc hl)
  have t0 : p 241 = false := (step721 p h)
  have t1 : p 1707 = false := (Or.elim (step1392 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t2 : p 1699 = false := (Or.elim (step1396 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t3 : p 1705 = false := (Or.elim (step1384 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t1))))
  have t4 : p 1703 = false := (Or.elim (step1386 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t1))))
  have t5 : p 1697 = false := (Or.elim (step1370 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t2))))
  have t6 : p 122 = true := (Or.elim (step1381 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t3))))
  have t7 : p 119 = true := (Or.elim (step1382 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t3))))
  have t8 : p 117 = true := (Or.elim (step1378 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t4))))
  have t9 : p 111 = true := (Or.elim (step1368 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t5))))
  have t10 : p 121 = false := (Or.elim (step654 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t8 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t7 l2))) (fun r2 => (False.elim (bool_contra t6 r2))))))))
  have t11 : p 120 = false := (Or.elim (step651 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t9 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t7 l2))) (fun r2 => (False.elim (bool_contra t6 r2))))))))
  exact (Or.elim (step648 p h) (fun l0 => (bool_contra t7 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 t11)) (fun r2 => (bool_contra r2 t10)))))))

theorem step1587 (p : Nat → Bool) (h : Constraints p) : p 1683 = true ∨ p 1699 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1683 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1699 = false := bool_false_of_not_true (fun hl => hc (Or.inr hl))
  have t0 : p 231 = false := (step715 p h)
  have t1 : p 1695 = false := (Or.elim (step1372 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u1))))
  have t2 : p 109 = true := (Or.elim (step1365 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t1))))
  have t3 : p 1697 = false := (Or.elim (step1370 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u1))))
  have t4 : p 113 = true := (Or.elim (step1367 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t3))))
  have t5 : p 1681 = false := (Or.elim (step1333 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t6 : p 1679 = false := (Or.elim (step1335 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t7 : p 105 = true := (Or.elim (step1330 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t5))))
  have t8 : p 98 = true := (Or.elim (step1328 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t6))))
  have t9 : p 103 = false := (Or.elim (step547 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t7 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t2 l2))) (fun r2 => (False.elim (bool_contra t4 r2))))))))
  have t10 : p 118 = false := (Or.elim (step642 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t8 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t2 l2))) (fun r2 => (False.elim (bool_contra t4 r2))))))))
  exact (Or.elim (step593 p h) (fun l0 => (bool_contra t2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t0)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra l2 t9)) (fun r2 => (bool_contra r2 t10)))))))

end Dfs112FirstBoolean
