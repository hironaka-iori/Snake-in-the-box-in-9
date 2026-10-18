import E112246Semantics
import B112E246Inputs
namespace Snake9.Regrowth.E112246
noncomputable section
local instance blockDec4 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause129 (q : Snake 81) (h : Conditions q) : valuation q 176 = false := by
  rw [value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (307 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause130 (q : Snake 81) (h : Conditions q) : valuation q 177 = false := by
  rw [value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (310 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause131 (q : Snake 81) (h : Conditions q) : valuation q 179 = false := by
  rw [value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (316 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause132 (q : Snake 81) (h : Conditions q) : valuation q 187 = false := by
  rw [value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (339 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause133 (q : Snake 81) (h : Conditions q) : valuation q 188 = false := by
  rw [value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (355 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause134 (q : Snake 81) (h : Conditions q) : valuation q 189 = false := by
  rw [value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (357 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause135 (q : Snake 81) (h : Conditions q) : valuation q 192 = false := by
  rw [value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (372 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause136 (q : Snake 81) (h : Conditions q) : valuation q 194 = false := by
  rw [value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (375 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause137 (q : Snake 81) (h : Conditions q) : valuation q 199 = false := by
  rw [value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (451 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause138 (q : Snake 81) (h : Conditions q) : valuation q 201 = false := by
  rw [value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (453 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause139 (q : Snake 81) (h : Conditions q) : valuation q 202 = false := by
  rw [value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (458 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause140 (q : Snake 81) (h : Conditions q) : valuation q 203 = false := by
  rw [value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (460 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause141 (q : Snake 81) (h : Conditions q) : valuation q 208 = false := by
  rw [value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (471 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause142 (q : Snake 81) (h : Conditions q) : valuation q 209 = false := by
  rw [value209]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (472 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause143 (q : Snake 81) (h : Conditions q) : valuation q 211 = false := by
  rw [value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (475 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem counterClause144 (q : Nat → Bool) : valuationOf q 186 = false ∨ valuationOf q 367 = true := by
  have hs : count367 q = (countLit q [186]) + (countLit q [187, 188]) := List.countP_append (p := literal q) (l₁ := [186]) (l₂ := [187, 188])
  have hm := merge_left (literal (valuationOf q) (186)) (literal (valuationOf q) (367)) (countLit q [186]) (countLit q [187, 188]) (count367 q) 1 (meaning186 q) (meaning367 q) hs
  change valuationOf q 186 = false ∨ valuationOf q 367 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause144 (q : Snake 81) (h : Conditions q) : valuation q 186 = false ∨ valuation q 367 = true := counterClause144 (baseVal q)

theorem counterClause145 (q : Nat → Bool) : valuationOf q 191 = false ∨ valuationOf q 369 = true := by
  have hs : count369 q = (countLit q [190]) + (countLit q [191]) := List.countP_append (p := literal q) (l₁ := [190]) (l₂ := [191])
  have hm := merge_right (literal (valuationOf q) (191)) (literal (valuationOf q) (369)) (countLit q [190]) (countLit q [191]) (count369 q) 1 (meaning191 q) (meaning369 q) hs
  change valuationOf q 191 = false ∨ valuationOf q 369 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause145 (q : Snake 81) (h : Conditions q) : valuation q 191 = false ∨ valuation q 369 = true := counterClause145 (baseVal q)

theorem counterClause146 (q : Nat → Bool) : valuationOf q 369 = false ∨ valuationOf q 371 = true := by
  have hs : count371 q = (countLit q [189]) + (countLit q [190, 191]) := List.countP_append (p := literal q) (l₁ := [189]) (l₂ := [190, 191])
  have hm := merge_right (literal (valuationOf q) (369)) (literal (valuationOf q) (371)) (countLit q [189]) (countLit q [190, 191]) (count371 q) 1 (meaning369 q) (meaning371 q) hs
  change valuationOf q 369 = false ∨ valuationOf q 371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause146 (q : Snake 81) (h : Conditions q) : valuation q 369 = false ∨ valuation q 371 = true := counterClause146 (baseVal q)

theorem counterClause147 (q : Nat → Bool) : valuationOf q 371 = false ∨ valuationOf q 373 = true := by
  have hs : count373 q = (countLit q [186, 187, 188]) + (countLit q [189, 190, 191]) := List.countP_append (p := literal q) (l₁ := [186, 187, 188]) (l₂ := [189, 190, 191])
  have hm := merge_right (literal (valuationOf q) (371)) (literal (valuationOf q) (373)) (countLit q [186, 187, 188]) (countLit q [189, 190, 191]) (count373 q) 1 (meaning371 q) (meaning373 q) hs
  change valuationOf q 371 = false ∨ valuationOf q 373 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause147 (q : Snake 81) (h : Conditions q) : valuation q 371 = false ∨ valuation q 373 = true := counterClause147 (baseVal q)

theorem counterClause148 (q : Nat → Bool) : valuationOf q 367 = false ∨ valuationOf q 373 = true := by
  have hs : count373 q = (countLit q [186, 187, 188]) + (countLit q [189, 190, 191]) := List.countP_append (p := literal q) (l₁ := [186, 187, 188]) (l₂ := [189, 190, 191])
  have hm := merge_left (literal (valuationOf q) (367)) (literal (valuationOf q) (373)) (countLit q [186, 187, 188]) (countLit q [189, 190, 191]) (count373 q) 1 (meaning367 q) (meaning373 q) hs
  change valuationOf q 367 = false ∨ valuationOf q 373 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause148 (q : Snake 81) (h : Conditions q) : valuation q 367 = false ∨ valuation q 373 = true := counterClause148 (baseVal q)

theorem counterClause149 (q : Nat → Bool) : valuationOf q 198 = false ∨ valuationOf q 381 = true := by
  have hs : count381 q = (countLit q [197]) + (countLit q [198]) := List.countP_append (p := literal q) (l₁ := [197]) (l₂ := [198])
  have hm := merge_right (literal (valuationOf q) (198)) (literal (valuationOf q) (381)) (countLit q [197]) (countLit q [198]) (count381 q) 1 (meaning198 q) (meaning381 q) hs
  change valuationOf q 198 = false ∨ valuationOf q 381 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause149 (q : Snake 81) (h : Conditions q) : valuation q 198 = false ∨ valuation q 381 = true := counterClause149 (baseVal q)

theorem counterClause150 (q : Nat → Bool) : valuationOf q 381 = false ∨ valuationOf q 383 = true := by
  have hs : count383 q = (countLit q [195, 196]) + (countLit q [197, 198]) := List.countP_append (p := literal q) (l₁ := [195, 196]) (l₂ := [197, 198])
  have hm := merge_right (literal (valuationOf q) (381)) (literal (valuationOf q) (383)) (countLit q [195, 196]) (countLit q [197, 198]) (count383 q) 1 (meaning381 q) (meaning383 q) hs
  change valuationOf q 381 = false ∨ valuationOf q 383 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause150 (q : Snake 81) (h : Conditions q) : valuation q 381 = false ∨ valuation q 383 = true := counterClause150 (baseVal q)

theorem counterClause151 (q : Nat → Bool) : valuationOf q 383 = false ∨ valuationOf q 385 = true := by
  have hs : count385 q = (countLit q [192, 193, 194]) + (countLit q [195, 196, 197, 198]) := List.countP_append (p := literal q) (l₁ := [192, 193, 194]) (l₂ := [195, 196, 197, 198])
  have hm := merge_right (literal (valuationOf q) (383)) (literal (valuationOf q) (385)) (countLit q [192, 193, 194]) (countLit q [195, 196, 197, 198]) (count385 q) 1 (meaning383 q) (meaning385 q) hs
  change valuationOf q 383 = false ∨ valuationOf q 385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause151 (q : Snake 81) (h : Conditions q) : valuation q 383 = false ∨ valuation q 385 = true := counterClause151 (baseVal q)

theorem counterClause152 (q : Nat → Bool) : valuationOf q 385 = false ∨ valuationOf q 387 = true := by
  have hs : count387 q = (countLit q [186, 187, 188, 189, 190, 191]) + (countLit q [192, 193, 194, 195, 196, 197, 198]) := List.countP_append (p := literal q) (l₁ := [186, 187, 188, 189, 190, 191]) (l₂ := [192, 193, 194, 195, 196, 197, 198])
  have hm := merge_right (literal (valuationOf q) (385)) (literal (valuationOf q) (387)) (countLit q [186, 187, 188, 189, 190, 191]) (countLit q [192, 193, 194, 195, 196, 197, 198]) (count387 q) 1 (meaning385 q) (meaning387 q) hs
  change valuationOf q 385 = false ∨ valuationOf q 387 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause152 (q : Snake 81) (h : Conditions q) : valuation q 385 = false ∨ valuation q 387 = true := counterClause152 (baseVal q)

theorem counterClause153 (q : Nat → Bool) : valuationOf q 373 = false ∨ valuationOf q 387 = true := by
  have hs : count387 q = (countLit q [186, 187, 188, 189, 190, 191]) + (countLit q [192, 193, 194, 195, 196, 197, 198]) := List.countP_append (p := literal q) (l₁ := [186, 187, 188, 189, 190, 191]) (l₂ := [192, 193, 194, 195, 196, 197, 198])
  have hm := merge_left (literal (valuationOf q) (373)) (literal (valuationOf q) (387)) (countLit q [186, 187, 188, 189, 190, 191]) (countLit q [192, 193, 194, 195, 196, 197, 198]) (count387 q) 1 (meaning373 q) (meaning387 q) hs
  change valuationOf q 373 = false ∨ valuationOf q 387 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause153 (q : Snake 81) (h : Conditions q) : valuation q 373 = false ∨ valuation q 387 = true := counterClause153 (baseVal q)

theorem counterClause154 (q : Nat → Bool) : valuationOf q 373 = false ∨ valuationOf q 385 = false ∨ valuationOf q 388 = true := by
  have hs : count387 q = (countLit q [186, 187, 188, 189, 190, 191]) + (countLit q [192, 193, 194, 195, 196, 197, 198]) := List.countP_append (p := literal q) (l₁ := [186, 187, 188, 189, 190, 191]) (l₂ := [192, 193, 194, 195, 196, 197, 198])
  have hm := merge_two (literal (valuationOf q) (373)) (literal (valuationOf q) (385)) (literal (valuationOf q) (388)) (countLit q [186, 187, 188, 189, 190, 191]) (countLit q [192, 193, 194, 195, 196, 197, 198]) (count387 q) 1 1 (meaning373 q) (meaning385 q) (meaning388 q) hs
  change valuationOf q 373 = false ∨ valuationOf q 385 = false ∨ valuationOf q 388 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause154 (q : Snake 81) (h : Conditions q) : valuation q 373 = false ∨ valuation q 385 = false ∨ valuation q 388 = true := counterClause154 (baseVal q)

theorem counterClause155 (q : Nat → Bool) : valuationOf q 200 = false ∨ valuationOf q 389 = true := by
  have hs : count389 q = (countLit q [200]) + (countLit q [201]) := List.countP_append (p := literal q) (l₁ := [200]) (l₂ := [201])
  have hm := merge_left (literal (valuationOf q) (200)) (literal (valuationOf q) (389)) (countLit q [200]) (countLit q [201]) (count389 q) 1 (meaning200 q) (meaning389 q) hs
  change valuationOf q 200 = false ∨ valuationOf q 389 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause155 (q : Snake 81) (h : Conditions q) : valuation q 200 = false ∨ valuation q 389 = true := counterClause155 (baseVal q)

theorem counterClause156 (q : Nat → Bool) : valuationOf q 389 = false ∨ valuationOf q 391 = true := by
  have hs : count391 q = (countLit q [199]) + (countLit q [200, 201]) := List.countP_append (p := literal q) (l₁ := [199]) (l₂ := [200, 201])
  have hm := merge_right (literal (valuationOf q) (389)) (literal (valuationOf q) (391)) (countLit q [199]) (countLit q [200, 201]) (count391 q) 1 (meaning389 q) (meaning391 q) hs
  change valuationOf q 389 = false ∨ valuationOf q 391 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause156 (q : Snake 81) (h : Conditions q) : valuation q 389 = false ∨ valuation q 391 = true := counterClause156 (baseVal q)

theorem counterClause157 (q : Nat → Bool) : valuationOf q 205 = false ∨ valuationOf q 395 = true := by
  have hs : count395 q = (countLit q [204]) + (countLit q [205]) := List.countP_append (p := literal q) (l₁ := [204]) (l₂ := [205])
  have hm := merge_right (literal (valuationOf q) (205)) (literal (valuationOf q) (395)) (countLit q [204]) (countLit q [205]) (count395 q) 1 (meaning205 q) (meaning395 q) hs
  change valuationOf q 205 = false ∨ valuationOf q 395 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause157 (q : Snake 81) (h : Conditions q) : valuation q 205 = false ∨ valuation q 395 = true := counterClause157 (baseVal q)

theorem counterClause158 (q : Nat → Bool) : valuationOf q 204 = false ∨ valuationOf q 395 = true := by
  have hs : count395 q = (countLit q [204]) + (countLit q [205]) := List.countP_append (p := literal q) (l₁ := [204]) (l₂ := [205])
  have hm := merge_left (literal (valuationOf q) (204)) (literal (valuationOf q) (395)) (countLit q [204]) (countLit q [205]) (count395 q) 1 (meaning204 q) (meaning395 q) hs
  change valuationOf q 204 = false ∨ valuationOf q 395 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause158 (q : Snake 81) (h : Conditions q) : valuation q 204 = false ∨ valuation q 395 = true := counterClause158 (baseVal q)

theorem counterClause159 (q : Nat → Bool) : valuationOf q 395 = false ∨ valuationOf q 397 = true := by
  have hs : count397 q = (countLit q [202, 203]) + (countLit q [204, 205]) := List.countP_append (p := literal q) (l₁ := [202, 203]) (l₂ := [204, 205])
  have hm := merge_right (literal (valuationOf q) (395)) (literal (valuationOf q) (397)) (countLit q [202, 203]) (countLit q [204, 205]) (count397 q) 1 (meaning395 q) (meaning397 q) hs
  change valuationOf q 395 = false ∨ valuationOf q 397 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause159 (q : Snake 81) (h : Conditions q) : valuation q 395 = false ∨ valuation q 397 = true := counterClause159 (baseVal q)

theorem counterClause160 (q : Nat → Bool) : valuationOf q 397 = false ∨ valuationOf q 399 = true := by
  have hs : count399 q = (countLit q [199, 200, 201]) + (countLit q [202, 203, 204, 205]) := List.countP_append (p := literal q) (l₁ := [199, 200, 201]) (l₂ := [202, 203, 204, 205])
  have hm := merge_right (literal (valuationOf q) (397)) (literal (valuationOf q) (399)) (countLit q [199, 200, 201]) (countLit q [202, 203, 204, 205]) (count399 q) 1 (meaning397 q) (meaning399 q) hs
  change valuationOf q 397 = false ∨ valuationOf q 399 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause160 (q : Snake 81) (h : Conditions q) : valuation q 397 = false ∨ valuation q 399 = true := counterClause160 (baseVal q)

theorem block4 (q : Snake 81) (h : Conditions q) : B112E246.Block4 (valuation q) :=
  ⟨clause129 q h, clause130 q h, clause131 q h, clause132 q h, clause133 q h, clause134 q h, clause135 q h, clause136 q h, clause137 q h, clause138 q h, clause139 q h, clause140 q h, clause141 q h, clause142 q h, clause143 q h, clause144 q h, clause145 q h, clause146 q h, clause147 q h, clause148 q h, clause149 q h, clause150 q h, clause151 q h, clause152 q h, clause153 q h, clause154 q h, clause155 q h, clause156 q h, clause157 q h, clause158 q h, clause159 q h, clause160 q h⟩

end
end Snake9.Regrowth.E112246
