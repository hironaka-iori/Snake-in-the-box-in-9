import E112171Semantics
import B112E171Inputs
namespace Snake9.Regrowth.E112171
noncomputable section
local instance blockDec15 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause481 (q : Nat → Bool) : valuationOf q 141 = false ∨ valuationOf q 271 = true := by
  have hs : count271 q = (countLit q [140]) + (countLit q [141]) := List.countP_append (p := literal q) (l₁ := [140]) (l₂ := [141])
  have hm := merge_right (literal (valuationOf q) (141)) (literal (valuationOf q) (271)) (countLit q [140]) (countLit q [141]) (count271 q) 1 (meaning141 q) (meaning271 q) hs
  change valuationOf q 141 = false ∨ valuationOf q 271 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause481 (q : Snake 81) (h : Conditions q) : valuation q 141 = false ∨ valuation q 271 = true := counterClause481 (baseVal q)

theorem counterClause482 (q : Nat → Bool) : valuationOf q 140 = false ∨ valuationOf q 271 = true := by
  have hs : count271 q = (countLit q [140]) + (countLit q [141]) := List.countP_append (p := literal q) (l₁ := [140]) (l₂ := [141])
  have hm := merge_left (literal (valuationOf q) (140)) (literal (valuationOf q) (271)) (countLit q [140]) (countLit q [141]) (count271 q) 1 (meaning140 q) (meaning271 q) hs
  change valuationOf q 140 = false ∨ valuationOf q 271 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause482 (q : Snake 81) (h : Conditions q) : valuation q 140 = false ∨ valuation q 271 = true := counterClause482 (baseVal q)

theorem counterClause483 (q : Nat → Bool) : valuationOf q 271 = false ∨ valuationOf q 275 = true := by
  have hs : count275 q = (countLit q [140, 141]) + (countLit q [142, 143]) := List.countP_append (p := literal q) (l₁ := [140, 141]) (l₂ := [142, 143])
  have hm := merge_left (literal (valuationOf q) (271)) (literal (valuationOf q) (275)) (countLit q [140, 141]) (countLit q [142, 143]) (count275 q) 1 (meaning271 q) (meaning275 q) hs
  change valuationOf q 271 = false ∨ valuationOf q 275 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause483 (q : Snake 81) (h : Conditions q) : valuation q 271 = false ∨ valuation q 275 = true := counterClause483 (baseVal q)

theorem counterClause484 (q : Nat → Bool) : valuationOf q 275 = false ∨ valuationOf q 277 = true := by
  have hs : count277 q = (countLit q [137, 138, 139]) + (countLit q [140, 141, 142, 143]) := List.countP_append (p := literal q) (l₁ := [137, 138, 139]) (l₂ := [140, 141, 142, 143])
  have hm := merge_right (literal (valuationOf q) (275)) (literal (valuationOf q) (277)) (countLit q [137, 138, 139]) (countLit q [140, 141, 142, 143]) (count277 q) 1 (meaning275 q) (meaning277 q) hs
  change valuationOf q 275 = false ∨ valuationOf q 277 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause484 (q : Snake 81) (h : Conditions q) : valuation q 275 = false ∨ valuation q 277 = true := counterClause484 (baseVal q)

theorem counterClause485 (q : Nat → Bool) : valuationOf q 269 = false ∨ valuationOf q 277 = true := by
  have hs : count277 q = (countLit q [137, 138, 139]) + (countLit q [140, 141, 142, 143]) := List.countP_append (p := literal q) (l₁ := [137, 138, 139]) (l₂ := [140, 141, 142, 143])
  have hm := merge_left (literal (valuationOf q) (269)) (literal (valuationOf q) (277)) (countLit q [137, 138, 139]) (countLit q [140, 141, 142, 143]) (count277 q) 1 (meaning269 q) (meaning277 q) hs
  change valuationOf q 269 = false ∨ valuationOf q 277 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause485 (q : Snake 81) (h : Conditions q) : valuation q 269 = false ∨ valuation q 277 = true := counterClause485 (baseVal q)

theorem counterClause486 (q : Nat → Bool) : valuationOf q 277 = false ∨ valuationOf q 279 = true := by
  have hs : count279 q = (countLit q [130, 131, 132, 133, 134, 135, 136]) + (countLit q [137, 138, 139, 140, 141, 142, 143]) := List.countP_append (p := literal q) (l₁ := [130, 131, 132, 133, 134, 135, 136]) (l₂ := [137, 138, 139, 140, 141, 142, 143])
  have hm := merge_right (literal (valuationOf q) (277)) (literal (valuationOf q) (279)) (countLit q [130, 131, 132, 133, 134, 135, 136]) (countLit q [137, 138, 139, 140, 141, 142, 143]) (count279 q) 1 (meaning277 q) (meaning279 q) hs
  change valuationOf q 277 = false ∨ valuationOf q 279 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause486 (q : Snake 81) (h : Conditions q) : valuation q 277 = false ∨ valuation q 279 = true := counterClause486 (baseVal q)

theorem counterClause487 (q : Nat → Bool) : valuationOf q 265 = false ∨ valuationOf q 279 = true := by
  have hs : count279 q = (countLit q [130, 131, 132, 133, 134, 135, 136]) + (countLit q [137, 138, 139, 140, 141, 142, 143]) := List.countP_append (p := literal q) (l₁ := [130, 131, 132, 133, 134, 135, 136]) (l₂ := [137, 138, 139, 140, 141, 142, 143])
  have hm := merge_left (literal (valuationOf q) (265)) (literal (valuationOf q) (279)) (countLit q [130, 131, 132, 133, 134, 135, 136]) (countLit q [137, 138, 139, 140, 141, 142, 143]) (count279 q) 1 (meaning265 q) (meaning279 q) hs
  change valuationOf q 265 = false ∨ valuationOf q 279 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause487 (q : Snake 81) (h : Conditions q) : valuation q 265 = false ∨ valuation q 279 = true := counterClause487 (baseVal q)

theorem counterClause488 (q : Nat → Bool) : valuationOf q 265 = false ∨ valuationOf q 277 = false ∨ valuationOf q 280 = true := by
  have hs : count279 q = (countLit q [130, 131, 132, 133, 134, 135, 136]) + (countLit q [137, 138, 139, 140, 141, 142, 143]) := List.countP_append (p := literal q) (l₁ := [130, 131, 132, 133, 134, 135, 136]) (l₂ := [137, 138, 139, 140, 141, 142, 143])
  have hm := merge_two (literal (valuationOf q) (265)) (literal (valuationOf q) (277)) (literal (valuationOf q) (280)) (countLit q [130, 131, 132, 133, 134, 135, 136]) (countLit q [137, 138, 139, 140, 141, 142, 143]) (count279 q) 1 1 (meaning265 q) (meaning277 q) (meaning280 q) hs
  change valuationOf q 265 = false ∨ valuationOf q 277 = false ∨ valuationOf q 280 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause488 (q : Snake 81) (h : Conditions q) : valuation q 265 = false ∨ valuation q 277 = false ∨ valuation q 280 = true := counterClause488 (baseVal q)

theorem counterClause489 (q : Nat → Bool) : valuationOf q 266 = false ∨ valuationOf q 280 = true := by
  have hs : count279 q = (countLit q [130, 131, 132, 133, 134, 135, 136]) + (countLit q [137, 138, 139, 140, 141, 142, 143]) := List.countP_append (p := literal q) (l₁ := [130, 131, 132, 133, 134, 135, 136]) (l₂ := [137, 138, 139, 140, 141, 142, 143])
  have hm := merge_left (literal (valuationOf q) (266)) (literal (valuationOf q) (280)) (countLit q [130, 131, 132, 133, 134, 135, 136]) (countLit q [137, 138, 139, 140, 141, 142, 143]) (count279 q) 2 (meaning266 q) (meaning280 q) hs
  change valuationOf q 266 = false ∨ valuationOf q 280 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause489 (q : Snake 81) (h : Conditions q) : valuation q 266 = false ∨ valuation q 280 = true := counterClause489 (baseVal q)

theorem counterClause490 (q : Nat → Bool) : valuationOf q 279 = false ∨ valuationOf q 281 = true := by
  have hs : count281 q = (countLit q [115, 116, 117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129]) + (countLit q [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143]) := List.countP_append (p := literal q) (l₁ := [115, 116, 117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129]) (l₂ := [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143])
  have hm := merge_right (literal (valuationOf q) (279)) (literal (valuationOf q) (281)) (countLit q [115, 116, 117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129]) (countLit q [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143]) (count281 q) 1 (meaning279 q) (meaning281 q) hs
  change valuationOf q 279 = false ∨ valuationOf q 281 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause490 (q : Snake 81) (h : Conditions q) : valuation q 279 = false ∨ valuation q 281 = true := counterClause490 (baseVal q)

theorem counterClause491 (q : Nat → Bool) : valuationOf q 280 = false ∨ valuationOf q 282 = true := by
  have hs : count281 q = (countLit q [115, 116, 117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129]) + (countLit q [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143]) := List.countP_append (p := literal q) (l₁ := [115, 116, 117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129]) (l₂ := [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143])
  have hm := merge_right (literal (valuationOf q) (280)) (literal (valuationOf q) (282)) (countLit q [115, 116, 117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129]) (countLit q [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143]) (count281 q) 2 (meaning280 q) (meaning282 q) hs
  change valuationOf q 280 = false ∨ valuationOf q 282 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause491 (q : Snake 81) (h : Conditions q) : valuation q 280 = false ∨ valuation q 282 = true := counterClause491 (baseVal q)

theorem counterClause492 (q : Nat → Bool) : valuationOf q 253 = false ∨ valuationOf q 281 = true := by
  have hs : count281 q = (countLit q [115, 116, 117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129]) + (countLit q [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143]) := List.countP_append (p := literal q) (l₁ := [115, 116, 117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129]) (l₂ := [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143])
  have hm := merge_left (literal (valuationOf q) (253)) (literal (valuationOf q) (281)) (countLit q [115, 116, 117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129]) (countLit q [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143]) (count281 q) 1 (meaning253 q) (meaning281 q) hs
  change valuationOf q 253 = false ∨ valuationOf q 281 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause492 (q : Snake 81) (h : Conditions q) : valuation q 253 = false ∨ valuation q 281 = true := counterClause492 (baseVal q)

theorem counterClause493 (q : Nat → Bool) : valuationOf q 253 = false ∨ valuationOf q 279 = false ∨ valuationOf q 282 = true := by
  have hs : count281 q = (countLit q [115, 116, 117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129]) + (countLit q [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143]) := List.countP_append (p := literal q) (l₁ := [115, 116, 117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129]) (l₂ := [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143])
  have hm := merge_two (literal (valuationOf q) (253)) (literal (valuationOf q) (279)) (literal (valuationOf q) (282)) (countLit q [115, 116, 117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129]) (countLit q [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143]) (count281 q) 1 1 (meaning253 q) (meaning279 q) (meaning282 q) hs
  change valuationOf q 253 = false ∨ valuationOf q 279 = false ∨ valuationOf q 282 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause493 (q : Snake 81) (h : Conditions q) : valuation q 253 = false ∨ valuation q 279 = false ∨ valuation q 282 = true := counterClause493 (baseVal q)

theorem counterClause494 (q : Nat → Bool) : valuationOf q 254 = false ∨ valuationOf q 282 = true := by
  have hs : count281 q = (countLit q [115, 116, 117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129]) + (countLit q [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143]) := List.countP_append (p := literal q) (l₁ := [115, 116, 117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129]) (l₂ := [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143])
  have hm := merge_left (literal (valuationOf q) (254)) (literal (valuationOf q) (282)) (countLit q [115, 116, 117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129]) (countLit q [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143]) (count281 q) 2 (meaning254 q) (meaning282 q) hs
  change valuationOf q 254 = false ∨ valuationOf q 282 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause494 (q : Snake 81) (h : Conditions q) : valuation q 254 = false ∨ valuation q 282 = true := counterClause494 (baseVal q)

theorem counterClause495 (q : Nat → Bool) : valuationOf q 146 = false ∨ valuationOf q 283 = true := by
  have hs : count283 q = (countLit q [145]) + (countLit q [146]) := List.countP_append (p := literal q) (l₁ := [145]) (l₂ := [146])
  have hm := merge_right (literal (valuationOf q) (146)) (literal (valuationOf q) (283)) (countLit q [145]) (countLit q [146]) (count283 q) 1 (meaning146 q) (meaning283 q) hs
  change valuationOf q 146 = false ∨ valuationOf q 283 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause495 (q : Snake 81) (h : Conditions q) : valuation q 146 = false ∨ valuation q 283 = true := counterClause495 (baseVal q)

theorem counterClause496 (q : Nat → Bool) : valuationOf q 283 = false ∨ valuationOf q 285 = true := by
  have hs : count285 q = (countLit q [144]) + (countLit q [145, 146]) := List.countP_append (p := literal q) (l₁ := [144]) (l₂ := [145, 146])
  have hm := merge_right (literal (valuationOf q) (283)) (literal (valuationOf q) (285)) (countLit q [144]) (countLit q [145, 146]) (count285 q) 1 (meaning283 q) (meaning285 q) hs
  change valuationOf q 283 = false ∨ valuationOf q 285 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause496 (q : Snake 81) (h : Conditions q) : valuation q 283 = false ∨ valuation q 285 = true := counterClause496 (baseVal q)

theorem counterClause497 (q : Nat → Bool) : valuationOf q 144 = false ∨ valuationOf q 285 = true := by
  have hs : count285 q = (countLit q [144]) + (countLit q [145, 146]) := List.countP_append (p := literal q) (l₁ := [144]) (l₂ := [145, 146])
  have hm := merge_left (literal (valuationOf q) (144)) (literal (valuationOf q) (285)) (countLit q [144]) (countLit q [145, 146]) (count285 q) 1 (meaning144 q) (meaning285 q) hs
  change valuationOf q 144 = false ∨ valuationOf q 285 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause497 (q : Snake 81) (h : Conditions q) : valuation q 144 = false ∨ valuation q 285 = true := counterClause497 (baseVal q)

theorem counterClause498 (q : Nat → Bool) : valuationOf q 148 = false ∨ valuationOf q 287 = true := by
  have hs : count287 q = (countLit q [147]) + (countLit q [148]) := List.countP_append (p := literal q) (l₁ := [147]) (l₂ := [148])
  have hm := merge_right (literal (valuationOf q) (148)) (literal (valuationOf q) (287)) (countLit q [147]) (countLit q [148]) (count287 q) 1 (meaning148 q) (meaning287 q) hs
  change valuationOf q 148 = false ∨ valuationOf q 287 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause498 (q : Snake 81) (h : Conditions q) : valuation q 148 = false ∨ valuation q 287 = true := counterClause498 (baseVal q)

theorem counterClause499 (q : Nat → Bool) : valuationOf q 150 = false ∨ valuationOf q 289 = true := by
  have hs : count289 q = (countLit q [149]) + (countLit q [150]) := List.countP_append (p := literal q) (l₁ := [149]) (l₂ := [150])
  have hm := merge_right (literal (valuationOf q) (150)) (literal (valuationOf q) (289)) (countLit q [149]) (countLit q [150]) (count289 q) 1 (meaning150 q) (meaning289 q) hs
  change valuationOf q 150 = false ∨ valuationOf q 289 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause499 (q : Snake 81) (h : Conditions q) : valuation q 150 = false ∨ valuation q 289 = true := counterClause499 (baseVal q)

theorem counterClause500 (q : Nat → Bool) : valuationOf q 149 = false ∨ valuationOf q 289 = true := by
  have hs : count289 q = (countLit q [149]) + (countLit q [150]) := List.countP_append (p := literal q) (l₁ := [149]) (l₂ := [150])
  have hm := merge_left (literal (valuationOf q) (149)) (literal (valuationOf q) (289)) (countLit q [149]) (countLit q [150]) (count289 q) 1 (meaning149 q) (meaning289 q) hs
  change valuationOf q 149 = false ∨ valuationOf q 289 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause500 (q : Snake 81) (h : Conditions q) : valuation q 149 = false ∨ valuation q 289 = true := counterClause500 (baseVal q)

theorem counterClause501 (q : Nat → Bool) : valuationOf q 149 = false ∨ valuationOf q 150 = false ∨ valuationOf q 290 = true := by
  have hs : count289 q = (countLit q [149]) + (countLit q [150]) := List.countP_append (p := literal q) (l₁ := [149]) (l₂ := [150])
  have hm := merge_two (literal (valuationOf q) (149)) (literal (valuationOf q) (150)) (literal (valuationOf q) (290)) (countLit q [149]) (countLit q [150]) (count289 q) 1 1 (meaning149 q) (meaning150 q) (meaning290 q) hs
  change valuationOf q 149 = false ∨ valuationOf q 150 = false ∨ valuationOf q 290 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause501 (q : Snake 81) (h : Conditions q) : valuation q 149 = false ∨ valuation q 150 = false ∨ valuation q 290 = true := counterClause501 (baseVal q)

theorem counterClause502 (q : Nat → Bool) : valuationOf q 289 = false ∨ valuationOf q 291 = true := by
  have hs : count291 q = (countLit q [147, 148]) + (countLit q [149, 150]) := List.countP_append (p := literal q) (l₁ := [147, 148]) (l₂ := [149, 150])
  have hm := merge_right (literal (valuationOf q) (289)) (literal (valuationOf q) (291)) (countLit q [147, 148]) (countLit q [149, 150]) (count291 q) 1 (meaning289 q) (meaning291 q) hs
  change valuationOf q 289 = false ∨ valuationOf q 291 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause502 (q : Snake 81) (h : Conditions q) : valuation q 289 = false ∨ valuation q 291 = true := counterClause502 (baseVal q)

theorem counterClause503 (q : Nat → Bool) : valuationOf q 290 = false ∨ valuationOf q 292 = true := by
  have hs : count291 q = (countLit q [147, 148]) + (countLit q [149, 150]) := List.countP_append (p := literal q) (l₁ := [147, 148]) (l₂ := [149, 150])
  have hm := merge_right (literal (valuationOf q) (290)) (literal (valuationOf q) (292)) (countLit q [147, 148]) (countLit q [149, 150]) (count291 q) 2 (meaning290 q) (meaning292 q) hs
  change valuationOf q 290 = false ∨ valuationOf q 292 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause503 (q : Snake 81) (h : Conditions q) : valuation q 290 = false ∨ valuation q 292 = true := counterClause503 (baseVal q)

theorem counterClause504 (q : Nat → Bool) : valuationOf q 287 = false ∨ valuationOf q 291 = true := by
  have hs : count291 q = (countLit q [147, 148]) + (countLit q [149, 150]) := List.countP_append (p := literal q) (l₁ := [147, 148]) (l₂ := [149, 150])
  have hm := merge_left (literal (valuationOf q) (287)) (literal (valuationOf q) (291)) (countLit q [147, 148]) (countLit q [149, 150]) (count291 q) 1 (meaning287 q) (meaning291 q) hs
  change valuationOf q 287 = false ∨ valuationOf q 291 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause504 (q : Snake 81) (h : Conditions q) : valuation q 287 = false ∨ valuation q 291 = true := counterClause504 (baseVal q)

theorem counterClause505 (q : Nat → Bool) : valuationOf q 291 = false ∨ valuationOf q 293 = true := by
  have hs : count293 q = (countLit q [144, 145, 146]) + (countLit q [147, 148, 149, 150]) := List.countP_append (p := literal q) (l₁ := [144, 145, 146]) (l₂ := [147, 148, 149, 150])
  have hm := merge_right (literal (valuationOf q) (291)) (literal (valuationOf q) (293)) (countLit q [144, 145, 146]) (countLit q [147, 148, 149, 150]) (count293 q) 1 (meaning291 q) (meaning293 q) hs
  change valuationOf q 291 = false ∨ valuationOf q 293 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause505 (q : Snake 81) (h : Conditions q) : valuation q 291 = false ∨ valuation q 293 = true := counterClause505 (baseVal q)

theorem counterClause506 (q : Nat → Bool) : valuationOf q 292 = false ∨ valuationOf q 294 = true := by
  have hs : count293 q = (countLit q [144, 145, 146]) + (countLit q [147, 148, 149, 150]) := List.countP_append (p := literal q) (l₁ := [144, 145, 146]) (l₂ := [147, 148, 149, 150])
  have hm := merge_right (literal (valuationOf q) (292)) (literal (valuationOf q) (294)) (countLit q [144, 145, 146]) (countLit q [147, 148, 149, 150]) (count293 q) 2 (meaning292 q) (meaning294 q) hs
  change valuationOf q 292 = false ∨ valuationOf q 294 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause506 (q : Snake 81) (h : Conditions q) : valuation q 292 = false ∨ valuation q 294 = true := counterClause506 (baseVal q)

theorem counterClause507 (q : Nat → Bool) : valuationOf q 285 = false ∨ valuationOf q 293 = true := by
  have hs : count293 q = (countLit q [144, 145, 146]) + (countLit q [147, 148, 149, 150]) := List.countP_append (p := literal q) (l₁ := [144, 145, 146]) (l₂ := [147, 148, 149, 150])
  have hm := merge_left (literal (valuationOf q) (285)) (literal (valuationOf q) (293)) (countLit q [144, 145, 146]) (countLit q [147, 148, 149, 150]) (count293 q) 1 (meaning285 q) (meaning293 q) hs
  change valuationOf q 285 = false ∨ valuationOf q 293 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause507 (q : Snake 81) (h : Conditions q) : valuation q 285 = false ∨ valuation q 293 = true := counterClause507 (baseVal q)

theorem counterClause508 (q : Nat → Bool) : valuationOf q 285 = false ∨ valuationOf q 291 = false ∨ valuationOf q 294 = true := by
  have hs : count293 q = (countLit q [144, 145, 146]) + (countLit q [147, 148, 149, 150]) := List.countP_append (p := literal q) (l₁ := [144, 145, 146]) (l₂ := [147, 148, 149, 150])
  have hm := merge_two (literal (valuationOf q) (285)) (literal (valuationOf q) (291)) (literal (valuationOf q) (294)) (countLit q [144, 145, 146]) (countLit q [147, 148, 149, 150]) (count293 q) 1 1 (meaning285 q) (meaning291 q) (meaning294 q) hs
  change valuationOf q 285 = false ∨ valuationOf q 291 = false ∨ valuationOf q 294 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause508 (q : Snake 81) (h : Conditions q) : valuation q 285 = false ∨ valuation q 291 = false ∨ valuation q 294 = true := counterClause508 (baseVal q)

theorem counterClause509 (q : Nat → Bool) : valuationOf q 154 = false ∨ valuationOf q 299 = true := by
  have hs : count299 q = (countLit q [154]) + (countLit q [155]) := List.countP_append (p := literal q) (l₁ := [154]) (l₂ := [155])
  have hm := merge_left (literal (valuationOf q) (154)) (literal (valuationOf q) (299)) (countLit q [154]) (countLit q [155]) (count299 q) 1 (meaning154 q) (meaning299 q) hs
  change valuationOf q 154 = false ∨ valuationOf q 299 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause509 (q : Snake 81) (h : Conditions q) : valuation q 154 = false ∨ valuation q 299 = true := counterClause509 (baseVal q)

theorem counterClause510 (q : Nat → Bool) : valuationOf q 156 = false ∨ valuationOf q 301 = true := by
  have hs : count301 q = (countLit q [156]) + (countLit q [157]) := List.countP_append (p := literal q) (l₁ := [156]) (l₂ := [157])
  have hm := merge_left (literal (valuationOf q) (156)) (literal (valuationOf q) (301)) (countLit q [156]) (countLit q [157]) (count301 q) 1 (meaning156 q) (meaning301 q) hs
  change valuationOf q 156 = false ∨ valuationOf q 301 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause510 (q : Snake 81) (h : Conditions q) : valuation q 156 = false ∨ valuation q 301 = true := counterClause510 (baseVal q)

theorem counterClause511 (q : Nat → Bool) : valuationOf q 301 = false ∨ valuationOf q 303 = true := by
  have hs : count303 q = (countLit q [154, 155]) + (countLit q [156, 157]) := List.countP_append (p := literal q) (l₁ := [154, 155]) (l₂ := [156, 157])
  have hm := merge_right (literal (valuationOf q) (301)) (literal (valuationOf q) (303)) (countLit q [154, 155]) (countLit q [156, 157]) (count303 q) 1 (meaning301 q) (meaning303 q) hs
  change valuationOf q 301 = false ∨ valuationOf q 303 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause511 (q : Snake 81) (h : Conditions q) : valuation q 301 = false ∨ valuation q 303 = true := counterClause511 (baseVal q)

theorem counterClause512 (q : Nat → Bool) : valuationOf q 299 = false ∨ valuationOf q 303 = true := by
  have hs : count303 q = (countLit q [154, 155]) + (countLit q [156, 157]) := List.countP_append (p := literal q) (l₁ := [154, 155]) (l₂ := [156, 157])
  have hm := merge_left (literal (valuationOf q) (299)) (literal (valuationOf q) (303)) (countLit q [154, 155]) (countLit q [156, 157]) (count303 q) 1 (meaning299 q) (meaning303 q) hs
  change valuationOf q 299 = false ∨ valuationOf q 303 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause512 (q : Snake 81) (h : Conditions q) : valuation q 299 = false ∨ valuation q 303 = true := counterClause512 (baseVal q)

theorem block15 (q : Snake 81) (h : Conditions q) : B112E171.Block15 (valuation q) :=
  ⟨clause481 q h, clause482 q h, clause483 q h, clause484 q h, clause485 q h, clause486 q h, clause487 q h, clause488 q h, clause489 q h, clause490 q h, clause491 q h, clause492 q h, clause493 q h, clause494 q h, clause495 q h, clause496 q h, clause497 q h, clause498 q h, clause499 q h, clause500 q h, clause501 q h, clause502 q h, clause503 q h, clause504 q h, clause505 q h, clause506 q h, clause507 q h, clause508 q h, clause509 q h, clause510 q h, clause511 q h, clause512 q h⟩

end
end Snake9.Regrowth.E112171
