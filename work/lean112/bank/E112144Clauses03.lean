import E112144Semantics
import B112E144Inputs
namespace Snake9.Regrowth.E112144
noncomputable section
local instance blockDec3 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause97 (q : Snake 81) (h : Conditions q) : valuation q 134 = false := by
  rw [value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (171 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause98 (q : Snake 81) (h : Conditions q) : valuation q 140 = false := by
  rw [value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (179 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause99 (q : Snake 81) (h : Conditions q) : valuation q 151 = false := by
  rw [value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (211 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause100 (q : Snake 81) (h : Conditions q) : valuation q 152 = false := by
  rw [value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (227 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause101 (q : Snake 81) (h : Conditions q) : valuation q 153 = false := by
  rw [value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (229 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause102 (q : Snake 81) (h : Conditions q) : valuation q 156 = false := by
  rw [value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (244 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause103 (q : Snake 81) (h : Conditions q) : valuation q 158 = false := by
  rw [value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (247 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause104 (q : Snake 81) (h : Conditions q) : valuation q 162 = false := by
  rw [value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (261 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause105 (q : Snake 81) (h : Conditions q) : valuation q 164 = false := by
  rw [value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (276 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause106 (q : Snake 81) (h : Conditions q) : valuation q 166 = false := by
  rw [value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (279 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause107 (q : Snake 81) (h : Conditions q) : valuation q 172 = false := by
  rw [value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (321 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause108 (q : Snake 81) (h : Conditions q) : valuation q 173 = false := by
  rw [value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (327 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause109 (q : Snake 81) (h : Conditions q) : valuation q 176 = false := by
  rw [value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (333 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause110 (q : Snake 81) (h : Conditions q) : valuation q 180 = false := by
  rw [value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (339 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause111 (q : Snake 81) (h : Conditions q) : valuation q 195 = false := by
  rw [value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (443 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause112 (q : Snake 81) (h : Conditions q) : valuation q 200 = false := by
  rw [value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (453 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem counterClause113 (q : Nat → Bool) : valuationOf q 109 = false ∨ valuationOf q 213 = true := by
  have hs : count213 q = (countLit q [108]) + (countLit q [109]) := List.countP_append (p := literal q) (l₁ := [108]) (l₂ := [109])
  have hm := merge_right (literal (valuationOf q) (109)) (literal (valuationOf q) (213)) (countLit q [108]) (countLit q [109]) (count213 q) 1 (meaning109 q) (meaning213 q) hs
  change valuationOf q 109 = false ∨ valuationOf q 213 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause113 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 213 = true := counterClause113 (baseVal q)

theorem counterClause114 (q : Nat → Bool) : valuationOf q 213 = false ∨ valuationOf q 215 = true := by
  have hs : count215 q = (countLit q [107]) + (countLit q [108, 109]) := List.countP_append (p := literal q) (l₁ := [107]) (l₂ := [108, 109])
  have hm := merge_right (literal (valuationOf q) (213)) (literal (valuationOf q) (215)) (countLit q [107]) (countLit q [108, 109]) (count215 q) 1 (meaning213 q) (meaning215 q) hs
  change valuationOf q 213 = false ∨ valuationOf q 215 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause114 (q : Snake 81) (h : Conditions q) : valuation q 213 = false ∨ valuation q 215 = true := counterClause114 (baseVal q)

theorem counterClause115 (q : Nat → Bool) : valuationOf q 112 = false ∨ valuationOf q 217 = true := by
  have hs : count217 q = (countLit q [111]) + (countLit q [112]) := List.countP_append (p := literal q) (l₁ := [111]) (l₂ := [112])
  have hm := merge_right (literal (valuationOf q) (112)) (literal (valuationOf q) (217)) (countLit q [111]) (countLit q [112]) (count217 q) 1 (meaning112 q) (meaning217 q) hs
  change valuationOf q 112 = false ∨ valuationOf q 217 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause115 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 217 = true := counterClause115 (baseVal q)

theorem counterClause116 (q : Nat → Bool) : valuationOf q 217 = false ∨ valuationOf q 219 = true := by
  have hs : count219 q = (countLit q [110]) + (countLit q [111, 112]) := List.countP_append (p := literal q) (l₁ := [110]) (l₂ := [111, 112])
  have hm := merge_right (literal (valuationOf q) (217)) (literal (valuationOf q) (219)) (countLit q [110]) (countLit q [111, 112]) (count219 q) 1 (meaning217 q) (meaning219 q) hs
  change valuationOf q 217 = false ∨ valuationOf q 219 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause116 (q : Snake 81) (h : Conditions q) : valuation q 217 = false ∨ valuation q 219 = true := counterClause116 (baseVal q)

theorem counterClause117 (q : Nat → Bool) : valuationOf q 110 = false ∨ valuationOf q 219 = true := by
  have hs : count219 q = (countLit q [110]) + (countLit q [111, 112]) := List.countP_append (p := literal q) (l₁ := [110]) (l₂ := [111, 112])
  have hm := merge_left (literal (valuationOf q) (110)) (literal (valuationOf q) (219)) (countLit q [110]) (countLit q [111, 112]) (count219 q) 1 (meaning110 q) (meaning219 q) hs
  change valuationOf q 110 = false ∨ valuationOf q 219 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause117 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 219 = true := counterClause117 (baseVal q)

theorem counterClause118 (q : Nat → Bool) : valuationOf q 219 = false ∨ valuationOf q 221 = true := by
  have hs : count221 q = (countLit q [107, 108, 109]) + (countLit q [110, 111, 112]) := List.countP_append (p := literal q) (l₁ := [107, 108, 109]) (l₂ := [110, 111, 112])
  have hm := merge_right (literal (valuationOf q) (219)) (literal (valuationOf q) (221)) (countLit q [107, 108, 109]) (countLit q [110, 111, 112]) (count221 q) 1 (meaning219 q) (meaning221 q) hs
  change valuationOf q 219 = false ∨ valuationOf q 221 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause118 (q : Snake 81) (h : Conditions q) : valuation q 219 = false ∨ valuation q 221 = true := counterClause118 (baseVal q)

theorem counterClause119 (q : Nat → Bool) : valuationOf q 215 = false ∨ valuationOf q 221 = true := by
  have hs : count221 q = (countLit q [107, 108, 109]) + (countLit q [110, 111, 112]) := List.countP_append (p := literal q) (l₁ := [107, 108, 109]) (l₂ := [110, 111, 112])
  have hm := merge_left (literal (valuationOf q) (215)) (literal (valuationOf q) (221)) (countLit q [107, 108, 109]) (countLit q [110, 111, 112]) (count221 q) 1 (meaning215 q) (meaning221 q) hs
  change valuationOf q 215 = false ∨ valuationOf q 221 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause119 (q : Snake 81) (h : Conditions q) : valuation q 215 = false ∨ valuation q 221 = true := counterClause119 (baseVal q)

theorem counterClause120 (q : Nat → Bool) : valuationOf q 116 = false ∨ valuationOf q 227 = true := by
  have hs : count227 q = (countLit q [116]) + (countLit q [117]) := List.countP_append (p := literal q) (l₁ := [116]) (l₂ := [117])
  have hm := merge_left (literal (valuationOf q) (116)) (literal (valuationOf q) (227)) (countLit q [116]) (countLit q [117]) (count227 q) 1 (meaning116 q) (meaning227 q) hs
  change valuationOf q 116 = false ∨ valuationOf q 227 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause120 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 227 = true := counterClause120 (baseVal q)

theorem counterClause121 (q : Nat → Bool) : valuationOf q 227 = false ∨ valuationOf q 231 = true := by
  have hs : count231 q = (countLit q [116, 117]) + (countLit q [118, 119]) := List.countP_append (p := literal q) (l₁ := [116, 117]) (l₂ := [118, 119])
  have hm := merge_left (literal (valuationOf q) (227)) (literal (valuationOf q) (231)) (countLit q [116, 117]) (countLit q [118, 119]) (count231 q) 1 (meaning227 q) (meaning231 q) hs
  change valuationOf q 227 = false ∨ valuationOf q 231 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause121 (q : Snake 81) (h : Conditions q) : valuation q 227 = false ∨ valuation q 231 = true := counterClause121 (baseVal q)

theorem counterClause122 (q : Nat → Bool) : valuationOf q 231 = false ∨ valuationOf q 233 = true := by
  have hs : count233 q = (countLit q [113, 114, 115]) + (countLit q [116, 117, 118, 119]) := List.countP_append (p := literal q) (l₁ := [113, 114, 115]) (l₂ := [116, 117, 118, 119])
  have hm := merge_right (literal (valuationOf q) (231)) (literal (valuationOf q) (233)) (countLit q [113, 114, 115]) (countLit q [116, 117, 118, 119]) (count233 q) 1 (meaning231 q) (meaning233 q) hs
  change valuationOf q 231 = false ∨ valuationOf q 233 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause122 (q : Snake 81) (h : Conditions q) : valuation q 231 = false ∨ valuation q 233 = true := counterClause122 (baseVal q)

theorem counterClause123 (q : Nat → Bool) : valuationOf q 233 = false ∨ valuationOf q 235 = true := by
  have hs : count235 q = (countLit q [107, 108, 109, 110, 111, 112]) + (countLit q [113, 114, 115, 116, 117, 118, 119]) := List.countP_append (p := literal q) (l₁ := [107, 108, 109, 110, 111, 112]) (l₂ := [113, 114, 115, 116, 117, 118, 119])
  have hm := merge_right (literal (valuationOf q) (233)) (literal (valuationOf q) (235)) (countLit q [107, 108, 109, 110, 111, 112]) (countLit q [113, 114, 115, 116, 117, 118, 119]) (count235 q) 1 (meaning233 q) (meaning235 q) hs
  change valuationOf q 233 = false ∨ valuationOf q 235 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause123 (q : Snake 81) (h : Conditions q) : valuation q 233 = false ∨ valuation q 235 = true := counterClause123 (baseVal q)

theorem counterClause124 (q : Nat → Bool) : valuationOf q 221 = false ∨ valuationOf q 235 = true := by
  have hs : count235 q = (countLit q [107, 108, 109, 110, 111, 112]) + (countLit q [113, 114, 115, 116, 117, 118, 119]) := List.countP_append (p := literal q) (l₁ := [107, 108, 109, 110, 111, 112]) (l₂ := [113, 114, 115, 116, 117, 118, 119])
  have hm := merge_left (literal (valuationOf q) (221)) (literal (valuationOf q) (235)) (countLit q [107, 108, 109, 110, 111, 112]) (countLit q [113, 114, 115, 116, 117, 118, 119]) (count235 q) 1 (meaning221 q) (meaning235 q) hs
  change valuationOf q 221 = false ∨ valuationOf q 235 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause124 (q : Snake 81) (h : Conditions q) : valuation q 221 = false ∨ valuation q 235 = true := counterClause124 (baseVal q)

theorem counterClause125 (q : Nat → Bool) : valuationOf q 121 = false ∨ valuationOf q 237 = true := by
  have hs : count237 q = (countLit q [121]) + (countLit q [122]) := List.countP_append (p := literal q) (l₁ := [121]) (l₂ := [122])
  have hm := merge_left (literal (valuationOf q) (121)) (literal (valuationOf q) (237)) (countLit q [121]) (countLit q [122]) (count237 q) 1 (meaning121 q) (meaning237 q) hs
  change valuationOf q 121 = false ∨ valuationOf q 237 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause125 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 237 = true := counterClause125 (baseVal q)

theorem counterClause126 (q : Nat → Bool) : valuationOf q 237 = false ∨ valuationOf q 239 = true := by
  have hs : count239 q = (countLit q [120]) + (countLit q [121, 122]) := List.countP_append (p := literal q) (l₁ := [120]) (l₂ := [121, 122])
  have hm := merge_right (literal (valuationOf q) (237)) (literal (valuationOf q) (239)) (countLit q [120]) (countLit q [121, 122]) (count239 q) 1 (meaning237 q) (meaning239 q) hs
  change valuationOf q 237 = false ∨ valuationOf q 239 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause126 (q : Snake 81) (h : Conditions q) : valuation q 237 = false ∨ valuation q 239 = true := counterClause126 (baseVal q)

theorem counterClause127 (q : Nat → Bool) : valuationOf q 124 = false ∨ valuationOf q 241 = true := by
  have hs : count241 q = (countLit q [124]) + (countLit q [125]) := List.countP_append (p := literal q) (l₁ := [124]) (l₂ := [125])
  have hm := merge_left (literal (valuationOf q) (124)) (literal (valuationOf q) (241)) (countLit q [124]) (countLit q [125]) (count241 q) 1 (meaning124 q) (meaning241 q) hs
  change valuationOf q 124 = false ∨ valuationOf q 241 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause127 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 241 = true := counterClause127 (baseVal q)

theorem counterClause128 (q : Nat → Bool) : valuationOf q 241 = false ∨ valuationOf q 243 = true := by
  have hs : count243 q = (countLit q [123]) + (countLit q [124, 125]) := List.countP_append (p := literal q) (l₁ := [123]) (l₂ := [124, 125])
  have hm := merge_right (literal (valuationOf q) (241)) (literal (valuationOf q) (243)) (countLit q [123]) (countLit q [124, 125]) (count243 q) 1 (meaning241 q) (meaning243 q) hs
  change valuationOf q 241 = false ∨ valuationOf q 243 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause128 (q : Snake 81) (h : Conditions q) : valuation q 241 = false ∨ valuation q 243 = true := counterClause128 (baseVal q)

theorem block3 (q : Snake 81) (h : Conditions q) : B112E144.Block3 (valuation q) :=
  ⟨clause97 q h, clause98 q h, clause99 q h, clause100 q h, clause101 q h, clause102 q h, clause103 q h, clause104 q h, clause105 q h, clause106 q h, clause107 q h, clause108 q h, clause109 q h, clause110 q h, clause111 q h, clause112 q h, clause113 q h, clause114 q h, clause115 q h, clause116 q h, clause117 q h, clause118 q h, clause119 q h, clause120 q h, clause121 q h, clause122 q h, clause123 q h, clause124 q h, clause125 q h, clause126 q h, clause127 q h, clause128 q h⟩

end
end Snake9.Regrowth.E112144
