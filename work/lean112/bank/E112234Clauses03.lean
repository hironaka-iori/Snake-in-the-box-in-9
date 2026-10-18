import E112234Semantics
import B112E234Inputs
namespace Snake9.Regrowth.E112234
noncomputable section
local instance blockDec3 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause97 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 90 = false ∨ valuation q 96 = false ∨ valuation q 98 = false := by
  rw [value90, value96, value97, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (469 : Vertex) (453 : Vertex) (468 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause98 (q : Snake 81) (h : Conditions q) : valuation q 104 = false := by
  rw [value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (13 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause99 (q : Snake 81) (h : Conditions q) : valuation q 111 = false := by
  rw [value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (161 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause100 (q : Snake 81) (h : Conditions q) : valuation q 112 = false := by
  rw [value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (162 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause101 (q : Snake 81) (h : Conditions q) : valuation q 115 = false := by
  rw [value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (171 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause102 (q : Snake 81) (h : Conditions q) : valuation q 116 = false := by
  rw [value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (173 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause103 (q : Snake 81) (h : Conditions q) : valuation q 121 = false := by
  rw [value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (179 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause104 (q : Snake 81) (h : Conditions q) : valuation q 122 = false := by
  rw [value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (182 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause105 (q : Snake 81) (h : Conditions q) : valuation q 124 = false := by
  rw [value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (188 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause106 (q : Snake 81) (h : Conditions q) : valuation q 129 = false := by
  rw [value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (227 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause107 (q : Snake 81) (h : Conditions q) : valuation q 131 = false := by
  rw [value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (229 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause108 (q : Snake 81) (h : Conditions q) : valuation q 132 = false := by
  rw [value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (234 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause109 (q : Snake 81) (h : Conditions q) : valuation q 134 = false := by
  rw [value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (236 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause110 (q : Snake 81) (h : Conditions q) : valuation q 138 = false := by
  rw [value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (247 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause111 (q : Snake 81) (h : Conditions q) : valuation q 139 = false := by
  rw [value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (248 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause112 (q : Snake 81) (h : Conditions q) : valuation q 144 = false := by
  rw [value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (259 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause113 (q : Snake 81) (h : Conditions q) : valuation q 149 = false := by
  rw [value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (268 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause114 (q : Snake 81) (h : Conditions q) : valuation q 165 = false := by
  rw [value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (364 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause115 (q : Snake 81) (h : Conditions q) : valuation q 170 = false := by
  rw [value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (376 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause116 (q : Snake 81) (h : Conditions q) : valuation q 178 = false := by
  rw [value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (403 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause117 (q : Snake 81) (h : Conditions q) : valuation q 179 = false := by
  rw [value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (419 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause118 (q : Snake 81) (h : Conditions q) : valuation q 180 = false := by
  rw [value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (421 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause119 (q : Snake 81) (h : Conditions q) : valuation q 183 = false := by
  rw [value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (436 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause120 (q : Snake 81) (h : Conditions q) : valuation q 185 = false := by
  rw [value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (439 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause121 (q : Snake 81) (h : Conditions q) : valuation q 192 = false := by
  rw [value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (453 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem counterClause122 (q : Nat → Bool) : valuationOf q 120 = false ∨ valuationOf q 231 = true := by
  have hs : count231 q = (countLit q [120]) + (countLit q [121]) := List.countP_append (p := literal q) (l₁ := [120]) (l₂ := [121])
  have hm := merge_left (literal (valuationOf q) (120)) (literal (valuationOf q) (231)) (countLit q [120]) (countLit q [121]) (count231 q) 1 (meaning120 q) (meaning231 q) hs
  change valuationOf q 120 = false ∨ valuationOf q 231 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause122 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 231 = true := counterClause122 (baseVal q)

theorem counterClause123 (q : Nat → Bool) : valuationOf q 119 = false ∨ valuationOf q 233 = true := by
  have hs : count233 q = (countLit q [119]) + (countLit q [120, 121]) := List.countP_append (p := literal q) (l₁ := [119]) (l₂ := [120, 121])
  have hm := merge_left (literal (valuationOf q) (119)) (literal (valuationOf q) (233)) (countLit q [119]) (countLit q [120, 121]) (count233 q) 1 (meaning119 q) (meaning233 q) hs
  change valuationOf q 119 = false ∨ valuationOf q 233 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause123 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 233 = true := counterClause123 (baseVal q)

theorem counterClause124 (q : Nat → Bool) : valuationOf q 119 = false ∨ valuationOf q 231 = false ∨ valuationOf q 234 = true := by
  have hs : count233 q = (countLit q [119]) + (countLit q [120, 121]) := List.countP_append (p := literal q) (l₁ := [119]) (l₂ := [120, 121])
  have hm := merge_two (literal (valuationOf q) (119)) (literal (valuationOf q) (231)) (literal (valuationOf q) (234)) (countLit q [119]) (countLit q [120, 121]) (count233 q) 1 1 (meaning119 q) (meaning231 q) (meaning234 q) hs
  change valuationOf q 119 = false ∨ valuationOf q 231 = false ∨ valuationOf q 234 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause124 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 231 = false ∨ valuation q 234 = true := counterClause124 (baseVal q)

theorem counterClause125 (q : Nat → Bool) : valuationOf q 233 = false ∨ valuationOf q 235 = true := by
  have hs : count235 q = (countLit q [116, 117, 118]) + (countLit q [119, 120, 121]) := List.countP_append (p := literal q) (l₁ := [116, 117, 118]) (l₂ := [119, 120, 121])
  have hm := merge_right (literal (valuationOf q) (233)) (literal (valuationOf q) (235)) (countLit q [116, 117, 118]) (countLit q [119, 120, 121]) (count235 q) 1 (meaning233 q) (meaning235 q) hs
  change valuationOf q 233 = false ∨ valuationOf q 235 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause125 (q : Snake 81) (h : Conditions q) : valuation q 233 = false ∨ valuation q 235 = true := counterClause125 (baseVal q)

theorem counterClause126 (q : Nat → Bool) : valuationOf q 234 = false ∨ valuationOf q 236 = true := by
  have hs : count235 q = (countLit q [116, 117, 118]) + (countLit q [119, 120, 121]) := List.countP_append (p := literal q) (l₁ := [116, 117, 118]) (l₂ := [119, 120, 121])
  have hm := merge_right (literal (valuationOf q) (234)) (literal (valuationOf q) (236)) (countLit q [116, 117, 118]) (countLit q [119, 120, 121]) (count235 q) 2 (meaning234 q) (meaning236 q) hs
  change valuationOf q 234 = false ∨ valuationOf q 236 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause126 (q : Snake 81) (h : Conditions q) : valuation q 234 = false ∨ valuation q 236 = true := counterClause126 (baseVal q)

theorem counterClause127 (q : Nat → Bool) : valuationOf q 123 = false ∨ valuationOf q 237 = true := by
  have hs : count237 q = (countLit q [123]) + (countLit q [124]) := List.countP_append (p := literal q) (l₁ := [123]) (l₂ := [124])
  have hm := merge_left (literal (valuationOf q) (123)) (literal (valuationOf q) (237)) (countLit q [123]) (countLit q [124]) (count237 q) 1 (meaning123 q) (meaning237 q) hs
  change valuationOf q 123 = false ∨ valuationOf q 237 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause127 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 237 = true := counterClause127 (baseVal q)

theorem counterClause128 (q : Nat → Bool) : valuationOf q 237 = false ∨ valuationOf q 239 = true := by
  have hs : count239 q = (countLit q [122]) + (countLit q [123, 124]) := List.countP_append (p := literal q) (l₁ := [122]) (l₂ := [123, 124])
  have hm := merge_right (literal (valuationOf q) (237)) (literal (valuationOf q) (239)) (countLit q [122]) (countLit q [123, 124]) (count239 q) 1 (meaning237 q) (meaning239 q) hs
  change valuationOf q 237 = false ∨ valuationOf q 239 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause128 (q : Snake 81) (h : Conditions q) : valuation q 237 = false ∨ valuation q 239 = true := counterClause128 (baseVal q)

theorem block3 (q : Snake 81) (h : Conditions q) : B112E234.Block3 (valuation q) :=
  ⟨clause97 q h, clause98 q h, clause99 q h, clause100 q h, clause101 q h, clause102 q h, clause103 q h, clause104 q h, clause105 q h, clause106 q h, clause107 q h, clause108 q h, clause109 q h, clause110 q h, clause111 q h, clause112 q h, clause113 q h, clause114 q h, clause115 q h, clause116 q h, clause117 q h, clause118 q h, clause119 q h, clause120 q h, clause121 q h, clause122 q h, clause123 q h, clause124 q h, clause125 q h, clause126 q h, clause127 q h, clause128 q h⟩

end
end Snake9.Regrowth.E112234
