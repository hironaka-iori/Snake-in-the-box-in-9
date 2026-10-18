import E112120Semantics
import B112E120Inputs
namespace Snake9.Regrowth.E112120
noncomputable section
local instance blockDec11 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause353 (q : Snake 81) (h : Conditions q) : valuation q 186 = false := by
  rw [value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (339 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause354 (q : Snake 81) (h : Conditions q) : valuation q 188 = false := by
  rw [value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (346 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause355 (q : Snake 81) (h : Conditions q) : valuation q 189 = false := by
  rw [value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (348 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause356 (q : Snake 81) (h : Conditions q) : valuation q 193 = false := by
  rw [value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (385 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause357 (q : Snake 81) (h : Conditions q) : valuation q 197 = false := by
  rw [value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (391 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause358 (q : Snake 81) (h : Conditions q) : valuation q 201 = false := by
  rw [value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (397 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause359 (q : Snake 81) (h : Conditions q) : valuation q 207 = false := by
  rw [value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (403 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause360 (q : Snake 81) (h : Conditions q) : valuation q 208 = false := by
  rw [value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (406 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause361 (q : Snake 81) (h : Conditions q) : valuation q 211 = false := by
  rw [value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (410 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause362 (q : Snake 81) (h : Conditions q) : valuation q 212 = false := by
  rw [value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (412 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause363 (q : Snake 81) (h : Conditions q) : valuation q 216 = false := by
  rw [value216]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (451 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause364 (q : Snake 81) (h : Conditions q) : valuation q 218 = false := by
  rw [value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (453 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause365 (q : Snake 81) (h : Conditions q) : valuation q 220 = false := by
  rw [value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (458 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause366 (q : Snake 81) (h : Conditions q) : valuation q 222 = false := by
  rw [value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (460 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause367 (q : Snake 81) (h : Conditions q) : valuation q 225 = false := by
  rw [value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (468 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause368 (q : Snake 81) (h : Conditions q) : valuation q 228 = false := by
  rw [value228]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (471 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause369 (q : Snake 81) (h : Conditions q) : valuation q 229 = false := by
  rw [value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (472 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause370 (q : Snake 81) (h : Conditions q) : valuation q 231 = false := by
  rw [value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (475 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem counterClause371 (q : Nat → Bool) : valuationOf q 120 = false ∨ valuationOf q 233 = true := by
  have hs : count233 q = (countLit q [119]) + (countLit q [120]) := List.countP_append (p := literal q) (l₁ := [119]) (l₂ := [120])
  have hm := merge_right (literal (valuationOf q) (120)) (literal (valuationOf q) (233)) (countLit q [119]) (countLit q [120]) (count233 q) 1 (meaning120 q) (meaning233 q) hs
  change valuationOf q 120 = false ∨ valuationOf q 233 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause371 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 233 = true := counterClause371 (baseVal q)

theorem counterClause372 (q : Nat → Bool) : valuationOf q 119 = false ∨ valuationOf q 233 = true := by
  have hs : count233 q = (countLit q [119]) + (countLit q [120]) := List.countP_append (p := literal q) (l₁ := [119]) (l₂ := [120])
  have hm := merge_left (literal (valuationOf q) (119)) (literal (valuationOf q) (233)) (countLit q [119]) (countLit q [120]) (count233 q) 1 (meaning119 q) (meaning233 q) hs
  change valuationOf q 119 = false ∨ valuationOf q 233 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause372 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 233 = true := counterClause372 (baseVal q)

theorem counterClause373 (q : Nat → Bool) : valuationOf q 233 = false ∨ valuationOf q 235 = true := by
  have hs : count235 q = (countLit q [118]) + (countLit q [119, 120]) := List.countP_append (p := literal q) (l₁ := [118]) (l₂ := [119, 120])
  have hm := merge_right (literal (valuationOf q) (233)) (literal (valuationOf q) (235)) (countLit q [118]) (countLit q [119, 120]) (count235 q) 1 (meaning233 q) (meaning235 q) hs
  change valuationOf q 233 = false ∨ valuationOf q 235 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause373 (q : Snake 81) (h : Conditions q) : valuation q 233 = false ∨ valuation q 235 = true := counterClause373 (baseVal q)

theorem counterClause374 (q : Nat → Bool) : valuationOf q 235 = false ∨ valuationOf q 243 = true := by
  have hs : count243 q = (countLit q [118, 119, 120]) + (countLit q [121, 122, 123, 124]) := List.countP_append (p := literal q) (l₁ := [118, 119, 120]) (l₂ := [121, 122, 123, 124])
  have hm := merge_left (literal (valuationOf q) (235)) (literal (valuationOf q) (243)) (countLit q [118, 119, 120]) (countLit q [121, 122, 123, 124]) (count243 q) 1 (meaning235 q) (meaning243 q) hs
  change valuationOf q 235 = false ∨ valuationOf q 243 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause374 (q : Snake 81) (h : Conditions q) : valuation q 235 = false ∨ valuation q 243 = true := counterClause374 (baseVal q)

theorem counterClause375 (q : Nat → Bool) : valuationOf q 243 = false ∨ valuationOf q 257 = true := by
  have hs : count257 q = (countLit q [118, 119, 120, 121, 122, 123, 124]) + (countLit q [125, 126, 127, 128, 129, 130, 131]) := List.countP_append (p := literal q) (l₁ := [118, 119, 120, 121, 122, 123, 124]) (l₂ := [125, 126, 127, 128, 129, 130, 131])
  have hm := merge_left (literal (valuationOf q) (243)) (literal (valuationOf q) (257)) (countLit q [118, 119, 120, 121, 122, 123, 124]) (countLit q [125, 126, 127, 128, 129, 130, 131]) (count257 q) 1 (meaning243 q) (meaning257 q) hs
  change valuationOf q 243 = false ∨ valuationOf q 257 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause375 (q : Snake 81) (h : Conditions q) : valuation q 243 = false ∨ valuation q 257 = true := counterClause375 (baseVal q)

theorem counterClause376 (q : Nat → Bool) : valuationOf q 142 = false ∨ valuationOf q 275 = true := by
  have hs : count275 q = (countLit q [142]) + (countLit q [143]) := List.countP_append (p := literal q) (l₁ := [142]) (l₂ := [143])
  have hm := merge_left (literal (valuationOf q) (142)) (literal (valuationOf q) (275)) (countLit q [142]) (countLit q [143]) (count275 q) 1 (meaning142 q) (meaning275 q) hs
  change valuationOf q 142 = false ∨ valuationOf q 275 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause376 (q : Snake 81) (h : Conditions q) : valuation q 142 = false ∨ valuation q 275 = true := counterClause376 (baseVal q)

theorem counterClause377 (q : Nat → Bool) : valuationOf q 275 = false ∨ valuationOf q 279 = true := by
  have hs : count279 q = (countLit q [142, 143]) + (countLit q [144, 145]) := List.countP_append (p := literal q) (l₁ := [142, 143]) (l₂ := [144, 145])
  have hm := merge_left (literal (valuationOf q) (275)) (literal (valuationOf q) (279)) (countLit q [142, 143]) (countLit q [144, 145]) (count279 q) 1 (meaning275 q) (meaning279 q) hs
  change valuationOf q 275 = false ∨ valuationOf q 279 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause377 (q : Snake 81) (h : Conditions q) : valuation q 275 = false ∨ valuation q 279 = true := counterClause377 (baseVal q)

theorem counterClause378 (q : Nat → Bool) : valuationOf q 279 = false ∨ valuationOf q 281 = true := by
  have hs : count281 q = (countLit q [139, 140, 141]) + (countLit q [142, 143, 144, 145]) := List.countP_append (p := literal q) (l₁ := [139, 140, 141]) (l₂ := [142, 143, 144, 145])
  have hm := merge_right (literal (valuationOf q) (279)) (literal (valuationOf q) (281)) (countLit q [139, 140, 141]) (countLit q [142, 143, 144, 145]) (count281 q) 1 (meaning279 q) (meaning281 q) hs
  change valuationOf q 279 = false ∨ valuationOf q 281 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause378 (q : Snake 81) (h : Conditions q) : valuation q 279 = false ∨ valuation q 281 = true := counterClause378 (baseVal q)

theorem counterClause379 (q : Nat → Bool) : valuationOf q 281 = false ∨ valuationOf q 283 = true := by
  have hs : count283 q = (countLit q [132, 133, 134, 135, 136, 137, 138]) + (countLit q [139, 140, 141, 142, 143, 144, 145]) := List.countP_append (p := literal q) (l₁ := [132, 133, 134, 135, 136, 137, 138]) (l₂ := [139, 140, 141, 142, 143, 144, 145])
  have hm := merge_right (literal (valuationOf q) (281)) (literal (valuationOf q) (283)) (countLit q [132, 133, 134, 135, 136, 137, 138]) (countLit q [139, 140, 141, 142, 143, 144, 145]) (count283 q) 1 (meaning281 q) (meaning283 q) hs
  change valuationOf q 281 = false ∨ valuationOf q 283 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause379 (q : Snake 81) (h : Conditions q) : valuation q 281 = false ∨ valuation q 283 = true := counterClause379 (baseVal q)

theorem counterClause380 (q : Nat → Bool) : valuationOf q 283 = false ∨ valuationOf q 285 = true := by
  have hs : count285 q = (countLit q [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131]) + (countLit q [132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145]) := List.countP_append (p := literal q) (l₁ := [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131]) (l₂ := [132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145])
  have hm := merge_right (literal (valuationOf q) (283)) (literal (valuationOf q) (285)) (countLit q [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131]) (countLit q [132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145]) (count285 q) 1 (meaning283 q) (meaning285 q) hs
  change valuationOf q 283 = false ∨ valuationOf q 285 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause380 (q : Snake 81) (h : Conditions q) : valuation q 283 = false ∨ valuation q 285 = true := counterClause380 (baseVal q)

theorem counterClause381 (q : Nat → Bool) : valuationOf q 257 = false ∨ valuationOf q 285 = true := by
  have hs : count285 q = (countLit q [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131]) + (countLit q [132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145]) := List.countP_append (p := literal q) (l₁ := [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131]) (l₂ := [132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145])
  have hm := merge_left (literal (valuationOf q) (257)) (literal (valuationOf q) (285)) (countLit q [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131]) (countLit q [132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145]) (count285 q) 1 (meaning257 q) (meaning285 q) hs
  change valuationOf q 257 = false ∨ valuationOf q 285 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause381 (q : Snake 81) (h : Conditions q) : valuation q 257 = false ∨ valuation q 285 = true := counterClause381 (baseVal q)

theorem counterClause382 (q : Nat → Bool) : valuationOf q 150 = false ∨ valuationOf q 291 = true := by
  have hs : count291 q = (countLit q [149]) + (countLit q [150]) := List.countP_append (p := literal q) (l₁ := [149]) (l₂ := [150])
  have hm := merge_right (literal (valuationOf q) (150)) (literal (valuationOf q) (291)) (countLit q [149]) (countLit q [150]) (count291 q) 1 (meaning150 q) (meaning291 q) hs
  change valuationOf q 150 = false ∨ valuationOf q 291 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause382 (q : Snake 81) (h : Conditions q) : valuation q 150 = false ∨ valuation q 291 = true := counterClause382 (baseVal q)

theorem counterClause383 (q : Nat → Bool) : valuationOf q 291 = false ∨ valuationOf q 295 = true := by
  have hs : count295 q = (countLit q [149, 150]) + (countLit q [151, 152]) := List.countP_append (p := literal q) (l₁ := [149, 150]) (l₂ := [151, 152])
  have hm := merge_left (literal (valuationOf q) (291)) (literal (valuationOf q) (295)) (countLit q [149, 150]) (countLit q [151, 152]) (count295 q) 1 (meaning291 q) (meaning295 q) hs
  change valuationOf q 291 = false ∨ valuationOf q 295 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause383 (q : Snake 81) (h : Conditions q) : valuation q 291 = false ∨ valuation q 295 = true := counterClause383 (baseVal q)

theorem counterClause384 (q : Nat → Bool) : valuationOf q 295 = false ∨ valuationOf q 297 = true := by
  have hs : count297 q = (countLit q [146, 147, 148]) + (countLit q [149, 150, 151, 152]) := List.countP_append (p := literal q) (l₁ := [146, 147, 148]) (l₂ := [149, 150, 151, 152])
  have hm := merge_right (literal (valuationOf q) (295)) (literal (valuationOf q) (297)) (countLit q [146, 147, 148]) (countLit q [149, 150, 151, 152]) (count297 q) 1 (meaning295 q) (meaning297 q) hs
  change valuationOf q 295 = false ∨ valuationOf q 297 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause384 (q : Snake 81) (h : Conditions q) : valuation q 295 = false ∨ valuation q 297 = true := counterClause384 (baseVal q)

theorem block11 (q : Snake 81) (h : Conditions q) : B112E120.Block11 (valuation q) :=
  ⟨clause353 q h, clause354 q h, clause355 q h, clause356 q h, clause357 q h, clause358 q h, clause359 q h, clause360 q h, clause361 q h, clause362 q h, clause363 q h, clause364 q h, clause365 q h, clause366 q h, clause367 q h, clause368 q h, clause369 q h, clause370 q h, clause371 q h, clause372 q h, clause373 q h, clause374 q h, clause375 q h, clause376 q h, clause377 q h, clause378 q h, clause379 q h, clause380 q h, clause381 q h, clause382 q h, clause383 q h, clause384 q h⟩

end
end Snake9.Regrowth.E112120
