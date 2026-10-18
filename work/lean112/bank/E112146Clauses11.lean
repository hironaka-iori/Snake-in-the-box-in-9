import E112146Semantics
import B112E146Inputs
namespace Snake9.Regrowth.E112146
noncomputable section
local instance blockDec11 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause353 (q : Snake 81) (h : Conditions q) : valuation q 211 = false := by
  rw [value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (425 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause354 (q : Snake 81) (h : Conditions q) : valuation q 215 = false := by
  rw [value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (484 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause355 (q : Snake 81) (h : Conditions q) : valuation q 218 = false := by
  rw [value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (491 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause356 (q : Snake 81) (h : Conditions q) : valuation q 223 = false := by
  rw [value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (502 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause357 (q : Snake 81) (h : Conditions q) : valuation q 227 = false := by
  rw [value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (506 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem counterClause358 (q : Nat → Bool) : valuationOf q 115 = false ∨ valuationOf q 231 = true := by
  have hs : count231 q = (countLit q [115]) + (countLit q [116, 117]) := List.countP_append (p := literal q) (l₁ := [115]) (l₂ := [116, 117])
  have hm := merge_left (literal (valuationOf q) (115)) (literal (valuationOf q) (231)) (countLit q [115]) (countLit q [116, 117]) (count231 q) 1 (meaning115 q) (meaning231 q) hs
  change valuationOf q 115 = false ∨ valuationOf q 231 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause358 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 231 = true := counterClause358 (baseVal q)

theorem counterClause359 (q : Nat → Bool) : valuationOf q 118 = false ∨ valuationOf q 233 = true := by
  have hs : count233 q = (countLit q [118]) + (countLit q [119]) := List.countP_append (p := literal q) (l₁ := [118]) (l₂ := [119])
  have hm := merge_left (literal (valuationOf q) (118)) (literal (valuationOf q) (233)) (countLit q [118]) (countLit q [119]) (count233 q) 1 (meaning118 q) (meaning233 q) hs
  change valuationOf q 118 = false ∨ valuationOf q 233 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause359 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 233 = true := counterClause359 (baseVal q)

theorem counterClause360 (q : Nat → Bool) : valuationOf q 121 = false ∨ valuationOf q 235 = true := by
  have hs : count235 q = (countLit q [120]) + (countLit q [121]) := List.countP_append (p := literal q) (l₁ := [120]) (l₂ := [121])
  have hm := merge_right (literal (valuationOf q) (121)) (literal (valuationOf q) (235)) (countLit q [120]) (countLit q [121]) (count235 q) 1 (meaning121 q) (meaning235 q) hs
  change valuationOf q 121 = false ∨ valuationOf q 235 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause360 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 235 = true := counterClause360 (baseVal q)

theorem counterClause361 (q : Nat → Bool) : valuationOf q 235 = false ∨ valuationOf q 237 = true := by
  have hs : count237 q = (countLit q [118, 119]) + (countLit q [120, 121]) := List.countP_append (p := literal q) (l₁ := [118, 119]) (l₂ := [120, 121])
  have hm := merge_right (literal (valuationOf q) (235)) (literal (valuationOf q) (237)) (countLit q [118, 119]) (countLit q [120, 121]) (count237 q) 1 (meaning235 q) (meaning237 q) hs
  change valuationOf q 235 = false ∨ valuationOf q 237 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause361 (q : Snake 81) (h : Conditions q) : valuation q 235 = false ∨ valuation q 237 = true := counterClause361 (baseVal q)

theorem counterClause362 (q : Nat → Bool) : valuationOf q 233 = false ∨ valuationOf q 237 = true := by
  have hs : count237 q = (countLit q [118, 119]) + (countLit q [120, 121]) := List.countP_append (p := literal q) (l₁ := [118, 119]) (l₂ := [120, 121])
  have hm := merge_left (literal (valuationOf q) (233)) (literal (valuationOf q) (237)) (countLit q [118, 119]) (countLit q [120, 121]) (count237 q) 1 (meaning233 q) (meaning237 q) hs
  change valuationOf q 233 = false ∨ valuationOf q 237 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause362 (q : Snake 81) (h : Conditions q) : valuation q 233 = false ∨ valuation q 237 = true := counterClause362 (baseVal q)

theorem counterClause363 (q : Nat → Bool) : valuationOf q 237 = false ∨ valuationOf q 239 = true := by
  have hs : count239 q = (countLit q [115, 116, 117]) + (countLit q [118, 119, 120, 121]) := List.countP_append (p := literal q) (l₁ := [115, 116, 117]) (l₂ := [118, 119, 120, 121])
  have hm := merge_right (literal (valuationOf q) (237)) (literal (valuationOf q) (239)) (countLit q [115, 116, 117]) (countLit q [118, 119, 120, 121]) (count239 q) 1 (meaning237 q) (meaning239 q) hs
  change valuationOf q 237 = false ∨ valuationOf q 239 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause363 (q : Snake 81) (h : Conditions q) : valuation q 237 = false ∨ valuation q 239 = true := counterClause363 (baseVal q)

theorem counterClause364 (q : Nat → Bool) : valuationOf q 231 = false ∨ valuationOf q 239 = true := by
  have hs : count239 q = (countLit q [115, 116, 117]) + (countLit q [118, 119, 120, 121]) := List.countP_append (p := literal q) (l₁ := [115, 116, 117]) (l₂ := [118, 119, 120, 121])
  have hm := merge_left (literal (valuationOf q) (231)) (literal (valuationOf q) (239)) (countLit q [115, 116, 117]) (countLit q [118, 119, 120, 121]) (count239 q) 1 (meaning231 q) (meaning239 q) hs
  change valuationOf q 231 = false ∨ valuationOf q 239 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause364 (q : Snake 81) (h : Conditions q) : valuation q 231 = false ∨ valuation q 239 = true := counterClause364 (baseVal q)

theorem counterClause365 (q : Nat → Bool) : valuationOf q 231 = false ∨ valuationOf q 237 = false ∨ valuationOf q 240 = true := by
  have hs : count239 q = (countLit q [115, 116, 117]) + (countLit q [118, 119, 120, 121]) := List.countP_append (p := literal q) (l₁ := [115, 116, 117]) (l₂ := [118, 119, 120, 121])
  have hm := merge_two (literal (valuationOf q) (231)) (literal (valuationOf q) (237)) (literal (valuationOf q) (240)) (countLit q [115, 116, 117]) (countLit q [118, 119, 120, 121]) (count239 q) 1 1 (meaning231 q) (meaning237 q) (meaning240 q) hs
  change valuationOf q 231 = false ∨ valuationOf q 237 = false ∨ valuationOf q 240 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause365 (q : Snake 81) (h : Conditions q) : valuation q 231 = false ∨ valuation q 237 = false ∨ valuation q 240 = true := counterClause365 (baseVal q)

theorem counterClause366 (q : Nat → Bool) : valuationOf q 125 = false ∨ valuationOf q 245 = true := by
  have hs : count245 q = (countLit q [125]) + (countLit q [126]) := List.countP_append (p := literal q) (l₁ := [125]) (l₂ := [126])
  have hm := merge_left (literal (valuationOf q) (125)) (literal (valuationOf q) (245)) (countLit q [125]) (countLit q [126]) (count245 q) 1 (meaning125 q) (meaning245 q) hs
  change valuationOf q 125 = false ∨ valuationOf q 245 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause366 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 245 = true := counterClause366 (baseVal q)

theorem counterClause367 (q : Nat → Bool) : valuationOf q 245 = false ∨ valuationOf q 249 = true := by
  have hs : count249 q = (countLit q [125, 126]) + (countLit q [127, 128]) := List.countP_append (p := literal q) (l₁ := [125, 126]) (l₂ := [127, 128])
  have hm := merge_left (literal (valuationOf q) (245)) (literal (valuationOf q) (249)) (countLit q [125, 126]) (countLit q [127, 128]) (count249 q) 1 (meaning245 q) (meaning249 q) hs
  change valuationOf q 245 = false ∨ valuationOf q 249 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause367 (q : Snake 81) (h : Conditions q) : valuation q 245 = false ∨ valuation q 249 = true := counterClause367 (baseVal q)

theorem counterClause368 (q : Nat → Bool) : valuationOf q 249 = false ∨ valuationOf q 251 = true := by
  have hs : count251 q = (countLit q [122, 123, 124]) + (countLit q [125, 126, 127, 128]) := List.countP_append (p := literal q) (l₁ := [122, 123, 124]) (l₂ := [125, 126, 127, 128])
  have hm := merge_right (literal (valuationOf q) (249)) (literal (valuationOf q) (251)) (countLit q [122, 123, 124]) (countLit q [125, 126, 127, 128]) (count251 q) 1 (meaning249 q) (meaning251 q) hs
  change valuationOf q 249 = false ∨ valuationOf q 251 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause368 (q : Snake 81) (h : Conditions q) : valuation q 249 = false ∨ valuation q 251 = true := counterClause368 (baseVal q)

theorem counterClause369 (q : Nat → Bool) : valuationOf q 251 = false ∨ valuationOf q 253 = true := by
  have hs : count253 q = (countLit q [115, 116, 117, 118, 119, 120, 121]) + (countLit q [122, 123, 124, 125, 126, 127, 128]) := List.countP_append (p := literal q) (l₁ := [115, 116, 117, 118, 119, 120, 121]) (l₂ := [122, 123, 124, 125, 126, 127, 128])
  have hm := merge_right (literal (valuationOf q) (251)) (literal (valuationOf q) (253)) (countLit q [115, 116, 117, 118, 119, 120, 121]) (countLit q [122, 123, 124, 125, 126, 127, 128]) (count253 q) 1 (meaning251 q) (meaning253 q) hs
  change valuationOf q 251 = false ∨ valuationOf q 253 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause369 (q : Snake 81) (h : Conditions q) : valuation q 251 = false ∨ valuation q 253 = true := counterClause369 (baseVal q)

theorem counterClause370 (q : Nat → Bool) : valuationOf q 239 = false ∨ valuationOf q 253 = true := by
  have hs : count253 q = (countLit q [115, 116, 117, 118, 119, 120, 121]) + (countLit q [122, 123, 124, 125, 126, 127, 128]) := List.countP_append (p := literal q) (l₁ := [115, 116, 117, 118, 119, 120, 121]) (l₂ := [122, 123, 124, 125, 126, 127, 128])
  have hm := merge_left (literal (valuationOf q) (239)) (literal (valuationOf q) (253)) (countLit q [115, 116, 117, 118, 119, 120, 121]) (countLit q [122, 123, 124, 125, 126, 127, 128]) (count253 q) 1 (meaning239 q) (meaning253 q) hs
  change valuationOf q 239 = false ∨ valuationOf q 253 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause370 (q : Snake 81) (h : Conditions q) : valuation q 239 = false ∨ valuation q 253 = true := counterClause370 (baseVal q)

theorem counterClause371 (q : Nat → Bool) : valuationOf q 239 = false ∨ valuationOf q 251 = false ∨ valuationOf q 254 = true := by
  have hs : count253 q = (countLit q [115, 116, 117, 118, 119, 120, 121]) + (countLit q [122, 123, 124, 125, 126, 127, 128]) := List.countP_append (p := literal q) (l₁ := [115, 116, 117, 118, 119, 120, 121]) (l₂ := [122, 123, 124, 125, 126, 127, 128])
  have hm := merge_two (literal (valuationOf q) (239)) (literal (valuationOf q) (251)) (literal (valuationOf q) (254)) (countLit q [115, 116, 117, 118, 119, 120, 121]) (countLit q [122, 123, 124, 125, 126, 127, 128]) (count253 q) 1 1 (meaning239 q) (meaning251 q) (meaning254 q) hs
  change valuationOf q 239 = false ∨ valuationOf q 251 = false ∨ valuationOf q 254 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause371 (q : Snake 81) (h : Conditions q) : valuation q 239 = false ∨ valuation q 251 = false ∨ valuation q 254 = true := counterClause371 (baseVal q)

theorem counterClause372 (q : Nat → Bool) : valuationOf q 240 = false ∨ valuationOf q 254 = true := by
  have hs : count253 q = (countLit q [115, 116, 117, 118, 119, 120, 121]) + (countLit q [122, 123, 124, 125, 126, 127, 128]) := List.countP_append (p := literal q) (l₁ := [115, 116, 117, 118, 119, 120, 121]) (l₂ := [122, 123, 124, 125, 126, 127, 128])
  have hm := merge_left (literal (valuationOf q) (240)) (literal (valuationOf q) (254)) (countLit q [115, 116, 117, 118, 119, 120, 121]) (countLit q [122, 123, 124, 125, 126, 127, 128]) (count253 q) 2 (meaning240 q) (meaning254 q) hs
  change valuationOf q 240 = false ∨ valuationOf q 254 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause372 (q : Snake 81) (h : Conditions q) : valuation q 240 = false ∨ valuation q 254 = true := counterClause372 (baseVal q)

theorem counterClause373 (q : Nat → Bool) : valuationOf q 142 = false ∨ valuationOf q 273 = true := by
  have hs : count273 q = (countLit q [141]) + (countLit q [142]) := List.countP_append (p := literal q) (l₁ := [141]) (l₂ := [142])
  have hm := merge_right (literal (valuationOf q) (142)) (literal (valuationOf q) (273)) (countLit q [141]) (countLit q [142]) (count273 q) 1 (meaning142 q) (meaning273 q) hs
  change valuationOf q 142 = false ∨ valuationOf q 273 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause373 (q : Snake 81) (h : Conditions q) : valuation q 142 = false ∨ valuation q 273 = true := counterClause373 (baseVal q)

theorem counterClause374 (q : Nat → Bool) : valuationOf q 273 = false ∨ valuationOf q 275 = true := by
  have hs : count275 q = (countLit q [139, 140]) + (countLit q [141, 142]) := List.countP_append (p := literal q) (l₁ := [139, 140]) (l₂ := [141, 142])
  have hm := merge_right (literal (valuationOf q) (273)) (literal (valuationOf q) (275)) (countLit q [139, 140]) (countLit q [141, 142]) (count275 q) 1 (meaning273 q) (meaning275 q) hs
  change valuationOf q 273 = false ∨ valuationOf q 275 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause374 (q : Snake 81) (h : Conditions q) : valuation q 273 = false ∨ valuation q 275 = true := counterClause374 (baseVal q)

theorem counterClause375 (q : Nat → Bool) : valuationOf q 275 = false ∨ valuationOf q 277 = true := by
  have hs : count277 q = (countLit q [136, 137, 138]) + (countLit q [139, 140, 141, 142]) := List.countP_append (p := literal q) (l₁ := [136, 137, 138]) (l₂ := [139, 140, 141, 142])
  have hm := merge_right (literal (valuationOf q) (275)) (literal (valuationOf q) (277)) (countLit q [136, 137, 138]) (countLit q [139, 140, 141, 142]) (count277 q) 1 (meaning275 q) (meaning277 q) hs
  change valuationOf q 275 = false ∨ valuationOf q 277 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause375 (q : Snake 81) (h : Conditions q) : valuation q 275 = false ∨ valuation q 277 = true := counterClause375 (baseVal q)

theorem counterClause376 (q : Nat → Bool) : valuationOf q 277 = false ∨ valuationOf q 279 = true := by
  have hs : count279 q = (countLit q [129, 130, 131, 132, 133, 134, 135]) + (countLit q [136, 137, 138, 139, 140, 141, 142]) := List.countP_append (p := literal q) (l₁ := [129, 130, 131, 132, 133, 134, 135]) (l₂ := [136, 137, 138, 139, 140, 141, 142])
  have hm := merge_right (literal (valuationOf q) (277)) (literal (valuationOf q) (279)) (countLit q [129, 130, 131, 132, 133, 134, 135]) (countLit q [136, 137, 138, 139, 140, 141, 142]) (count279 q) 1 (meaning277 q) (meaning279 q) hs
  change valuationOf q 277 = false ∨ valuationOf q 279 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause376 (q : Snake 81) (h : Conditions q) : valuation q 277 = false ∨ valuation q 279 = true := counterClause376 (baseVal q)

theorem counterClause377 (q : Nat → Bool) : valuationOf q 279 = false ∨ valuationOf q 281 = true := by
  have hs : count281 q = (countLit q [115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128]) + (countLit q [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) := List.countP_append (p := literal q) (l₁ := [115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128]) (l₂ := [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142])
  have hm := merge_right (literal (valuationOf q) (279)) (literal (valuationOf q) (281)) (countLit q [115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128]) (countLit q [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) (count281 q) 1 (meaning279 q) (meaning281 q) hs
  change valuationOf q 279 = false ∨ valuationOf q 281 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause377 (q : Snake 81) (h : Conditions q) : valuation q 279 = false ∨ valuation q 281 = true := counterClause377 (baseVal q)

theorem counterClause378 (q : Nat → Bool) : valuationOf q 253 = false ∨ valuationOf q 281 = true := by
  have hs : count281 q = (countLit q [115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128]) + (countLit q [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) := List.countP_append (p := literal q) (l₁ := [115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128]) (l₂ := [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142])
  have hm := merge_left (literal (valuationOf q) (253)) (literal (valuationOf q) (281)) (countLit q [115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128]) (countLit q [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) (count281 q) 1 (meaning253 q) (meaning281 q) hs
  change valuationOf q 253 = false ∨ valuationOf q 281 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause378 (q : Snake 81) (h : Conditions q) : valuation q 253 = false ∨ valuation q 281 = true := counterClause378 (baseVal q)

theorem counterClause379 (q : Nat → Bool) : valuationOf q 253 = false ∨ valuationOf q 279 = false ∨ valuationOf q 282 = true := by
  have hs : count281 q = (countLit q [115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128]) + (countLit q [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) := List.countP_append (p := literal q) (l₁ := [115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128]) (l₂ := [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142])
  have hm := merge_two (literal (valuationOf q) (253)) (literal (valuationOf q) (279)) (literal (valuationOf q) (282)) (countLit q [115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128]) (countLit q [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) (count281 q) 1 1 (meaning253 q) (meaning279 q) (meaning282 q) hs
  change valuationOf q 253 = false ∨ valuationOf q 279 = false ∨ valuationOf q 282 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause379 (q : Snake 81) (h : Conditions q) : valuation q 253 = false ∨ valuation q 279 = false ∨ valuation q 282 = true := counterClause379 (baseVal q)

theorem counterClause380 (q : Nat → Bool) : valuationOf q 254 = false ∨ valuationOf q 282 = true := by
  have hs : count281 q = (countLit q [115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128]) + (countLit q [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) := List.countP_append (p := literal q) (l₁ := [115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128]) (l₂ := [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142])
  have hm := merge_left (literal (valuationOf q) (254)) (literal (valuationOf q) (282)) (countLit q [115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128]) (countLit q [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) (count281 q) 2 (meaning254 q) (meaning282 q) hs
  change valuationOf q 254 = false ∨ valuationOf q 282 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause380 (q : Snake 81) (h : Conditions q) : valuation q 254 = false ∨ valuation q 282 = true := counterClause380 (baseVal q)

theorem counterClause381 (q : Nat → Bool) : valuationOf q 146 = false ∨ valuationOf q 287 = true := by
  have hs : count287 q = (countLit q [146]) + (countLit q [147]) := List.countP_append (p := literal q) (l₁ := [146]) (l₂ := [147])
  have hm := merge_left (literal (valuationOf q) (146)) (literal (valuationOf q) (287)) (countLit q [146]) (countLit q [147]) (count287 q) 1 (meaning146 q) (meaning287 q) hs
  change valuationOf q 146 = false ∨ valuationOf q 287 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause381 (q : Snake 81) (h : Conditions q) : valuation q 146 = false ∨ valuation q 287 = true := counterClause381 (baseVal q)

theorem counterClause382 (q : Nat → Bool) : valuationOf q 148 = false ∨ valuationOf q 289 = true := by
  have hs : count289 q = (countLit q [148]) + (countLit q [149]) := List.countP_append (p := literal q) (l₁ := [148]) (l₂ := [149])
  have hm := merge_left (literal (valuationOf q) (148)) (literal (valuationOf q) (289)) (countLit q [148]) (countLit q [149]) (count289 q) 1 (meaning148 q) (meaning289 q) hs
  change valuationOf q 148 = false ∨ valuationOf q 289 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause382 (q : Snake 81) (h : Conditions q) : valuation q 148 = false ∨ valuation q 289 = true := counterClause382 (baseVal q)

theorem counterClause383 (q : Nat → Bool) : valuationOf q 289 = false ∨ valuationOf q 291 = true := by
  have hs : count291 q = (countLit q [146, 147]) + (countLit q [148, 149]) := List.countP_append (p := literal q) (l₁ := [146, 147]) (l₂ := [148, 149])
  have hm := merge_right (literal (valuationOf q) (289)) (literal (valuationOf q) (291)) (countLit q [146, 147]) (countLit q [148, 149]) (count291 q) 1 (meaning289 q) (meaning291 q) hs
  change valuationOf q 289 = false ∨ valuationOf q 291 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause383 (q : Snake 81) (h : Conditions q) : valuation q 289 = false ∨ valuation q 291 = true := counterClause383 (baseVal q)

theorem counterClause384 (q : Nat → Bool) : valuationOf q 287 = false ∨ valuationOf q 291 = true := by
  have hs : count291 q = (countLit q [146, 147]) + (countLit q [148, 149]) := List.countP_append (p := literal q) (l₁ := [146, 147]) (l₂ := [148, 149])
  have hm := merge_left (literal (valuationOf q) (287)) (literal (valuationOf q) (291)) (countLit q [146, 147]) (countLit q [148, 149]) (count291 q) 1 (meaning287 q) (meaning291 q) hs
  change valuationOf q 287 = false ∨ valuationOf q 291 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause384 (q : Snake 81) (h : Conditions q) : valuation q 287 = false ∨ valuation q 291 = true := counterClause384 (baseVal q)

theorem block11 (q : Snake 81) (h : Conditions q) : B112E146.Block11 (valuation q) :=
  ⟨clause353 q h, clause354 q h, clause355 q h, clause356 q h, clause357 q h, clause358 q h, clause359 q h, clause360 q h, clause361 q h, clause362 q h, clause363 q h, clause364 q h, clause365 q h, clause366 q h, clause367 q h, clause368 q h, clause369 q h, clause370 q h, clause371 q h, clause372 q h, clause373 q h, clause374 q h, clause375 q h, clause376 q h, clause377 q h, clause378 q h, clause379 q h, clause380 q h, clause381 q h, clause382 q h, clause383 q h, clause384 q h⟩

end
end Snake9.Regrowth.E112146
