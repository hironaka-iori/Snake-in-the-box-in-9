import E112078Semantics
import B112E078Inputs
namespace Snake9.Regrowth.E112078
noncomputable section
local instance blockDec19 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause609 (q : Nat → Bool) : valuationOf q 271 = false ∨ valuationOf q 273 = true := by
  have hs : count273 q = (countLit q [137, 138]) + (countLit q [139, 140]) := List.countP_append (p := literal q) (l₁ := [137, 138]) (l₂ := [139, 140])
  have hm := merge_right (literal (valuationOf q) (271)) (literal (valuationOf q) (273)) (countLit q [137, 138]) (countLit q [139, 140]) (count273 q) 1 (meaning271 q) (meaning273 q) hs
  change valuationOf q 271 = false ∨ valuationOf q 273 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause609 (q : Snake 81) (h : Conditions q) : valuation q 271 = false ∨ valuation q 273 = true := counterClause609 (baseVal q)

theorem counterClause610 (q : Nat → Bool) : valuationOf q 269 = false ∨ valuationOf q 273 = true := by
  have hs : count273 q = (countLit q [137, 138]) + (countLit q [139, 140]) := List.countP_append (p := literal q) (l₁ := [137, 138]) (l₂ := [139, 140])
  have hm := merge_left (literal (valuationOf q) (269)) (literal (valuationOf q) (273)) (countLit q [137, 138]) (countLit q [139, 140]) (count273 q) 1 (meaning269 q) (meaning273 q) hs
  change valuationOf q 269 = false ∨ valuationOf q 273 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause610 (q : Snake 81) (h : Conditions q) : valuation q 269 = false ∨ valuation q 273 = true := counterClause610 (baseVal q)

theorem counterClause611 (q : Nat → Bool) : valuationOf q 269 = false ∨ valuationOf q 271 = false ∨ valuationOf q 274 = true := by
  have hs : count273 q = (countLit q [137, 138]) + (countLit q [139, 140]) := List.countP_append (p := literal q) (l₁ := [137, 138]) (l₂ := [139, 140])
  have hm := merge_two (literal (valuationOf q) (269)) (literal (valuationOf q) (271)) (literal (valuationOf q) (274)) (countLit q [137, 138]) (countLit q [139, 140]) (count273 q) 1 1 (meaning269 q) (meaning271 q) (meaning274 q) hs
  change valuationOf q 269 = false ∨ valuationOf q 271 = false ∨ valuationOf q 274 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause611 (q : Snake 81) (h : Conditions q) : valuation q 269 = false ∨ valuation q 271 = false ∨ valuation q 274 = true := counterClause611 (baseVal q)

theorem counterClause612 (q : Nat → Bool) : valuationOf q 270 = false ∨ valuationOf q 274 = true := by
  have hs : count273 q = (countLit q [137, 138]) + (countLit q [139, 140]) := List.countP_append (p := literal q) (l₁ := [137, 138]) (l₂ := [139, 140])
  have hm := merge_left (literal (valuationOf q) (270)) (literal (valuationOf q) (274)) (countLit q [137, 138]) (countLit q [139, 140]) (count273 q) 2 (meaning270 q) (meaning274 q) hs
  change valuationOf q 270 = false ∨ valuationOf q 274 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause612 (q : Snake 81) (h : Conditions q) : valuation q 270 = false ∨ valuation q 274 = true := counterClause612 (baseVal q)

theorem counterClause613 (q : Nat → Bool) : valuationOf q 273 = false ∨ valuationOf q 275 = true := by
  have hs : count275 q = (countLit q [134, 135, 136]) + (countLit q [137, 138, 139, 140]) := List.countP_append (p := literal q) (l₁ := [134, 135, 136]) (l₂ := [137, 138, 139, 140])
  have hm := merge_right (literal (valuationOf q) (273)) (literal (valuationOf q) (275)) (countLit q [134, 135, 136]) (countLit q [137, 138, 139, 140]) (count275 q) 1 (meaning273 q) (meaning275 q) hs
  change valuationOf q 273 = false ∨ valuationOf q 275 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause613 (q : Snake 81) (h : Conditions q) : valuation q 273 = false ∨ valuation q 275 = true := counterClause613 (baseVal q)

theorem counterClause614 (q : Nat → Bool) : valuationOf q 274 = false ∨ valuationOf q 276 = true := by
  have hs : count275 q = (countLit q [134, 135, 136]) + (countLit q [137, 138, 139, 140]) := List.countP_append (p := literal q) (l₁ := [134, 135, 136]) (l₂ := [137, 138, 139, 140])
  have hm := merge_right (literal (valuationOf q) (274)) (literal (valuationOf q) (276)) (countLit q [134, 135, 136]) (countLit q [137, 138, 139, 140]) (count275 q) 2 (meaning274 q) (meaning276 q) hs
  change valuationOf q 274 = false ∨ valuationOf q 276 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause614 (q : Snake 81) (h : Conditions q) : valuation q 274 = false ∨ valuation q 276 = true := counterClause614 (baseVal q)

theorem counterClause615 (q : Nat → Bool) : valuationOf q 267 = false ∨ valuationOf q 275 = true := by
  have hs : count275 q = (countLit q [134, 135, 136]) + (countLit q [137, 138, 139, 140]) := List.countP_append (p := literal q) (l₁ := [134, 135, 136]) (l₂ := [137, 138, 139, 140])
  have hm := merge_left (literal (valuationOf q) (267)) (literal (valuationOf q) (275)) (countLit q [134, 135, 136]) (countLit q [137, 138, 139, 140]) (count275 q) 1 (meaning267 q) (meaning275 q) hs
  change valuationOf q 267 = false ∨ valuationOf q 275 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause615 (q : Snake 81) (h : Conditions q) : valuation q 267 = false ∨ valuation q 275 = true := counterClause615 (baseVal q)

theorem counterClause616 (q : Nat → Bool) : valuationOf q 267 = false ∨ valuationOf q 273 = false ∨ valuationOf q 276 = true := by
  have hs : count275 q = (countLit q [134, 135, 136]) + (countLit q [137, 138, 139, 140]) := List.countP_append (p := literal q) (l₁ := [134, 135, 136]) (l₂ := [137, 138, 139, 140])
  have hm := merge_two (literal (valuationOf q) (267)) (literal (valuationOf q) (273)) (literal (valuationOf q) (276)) (countLit q [134, 135, 136]) (countLit q [137, 138, 139, 140]) (count275 q) 1 1 (meaning267 q) (meaning273 q) (meaning276 q) hs
  change valuationOf q 267 = false ∨ valuationOf q 273 = false ∨ valuationOf q 276 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause616 (q : Snake 81) (h : Conditions q) : valuation q 267 = false ∨ valuation q 273 = false ∨ valuation q 276 = true := counterClause616 (baseVal q)

theorem counterClause617 (q : Nat → Bool) : valuationOf q 148 = false ∨ valuationOf q 285 = true := by
  have hs : count285 q = (countLit q [147]) + (countLit q [148]) := List.countP_append (p := literal q) (l₁ := [147]) (l₂ := [148])
  have hm := merge_right (literal (valuationOf q) (148)) (literal (valuationOf q) (285)) (countLit q [147]) (countLit q [148]) (count285 q) 1 (meaning148 q) (meaning285 q) hs
  change valuationOf q 148 = false ∨ valuationOf q 285 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause617 (q : Snake 81) (h : Conditions q) : valuation q 148 = false ∨ valuation q 285 = true := counterClause617 (baseVal q)

theorem counterClause618 (q : Nat → Bool) : valuationOf q 147 = false ∨ valuationOf q 285 = true := by
  have hs : count285 q = (countLit q [147]) + (countLit q [148]) := List.countP_append (p := literal q) (l₁ := [147]) (l₂ := [148])
  have hm := merge_left (literal (valuationOf q) (147)) (literal (valuationOf q) (285)) (countLit q [147]) (countLit q [148]) (count285 q) 1 (meaning147 q) (meaning285 q) hs
  change valuationOf q 147 = false ∨ valuationOf q 285 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause618 (q : Snake 81) (h : Conditions q) : valuation q 147 = false ∨ valuation q 285 = true := counterClause618 (baseVal q)

theorem counterClause619 (q : Nat → Bool) : valuationOf q 285 = false ∨ valuationOf q 287 = true := by
  have hs : count287 q = (countLit q [145, 146]) + (countLit q [147, 148]) := List.countP_append (p := literal q) (l₁ := [145, 146]) (l₂ := [147, 148])
  have hm := merge_right (literal (valuationOf q) (285)) (literal (valuationOf q) (287)) (countLit q [145, 146]) (countLit q [147, 148]) (count287 q) 1 (meaning285 q) (meaning287 q) hs
  change valuationOf q 285 = false ∨ valuationOf q 287 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause619 (q : Snake 81) (h : Conditions q) : valuation q 285 = false ∨ valuation q 287 = true := counterClause619 (baseVal q)

theorem counterClause620 (q : Nat → Bool) : valuationOf q 287 = false ∨ valuationOf q 289 = true := by
  have hs : count289 q = (countLit q [141, 142, 143, 144]) + (countLit q [145, 146, 147, 148]) := List.countP_append (p := literal q) (l₁ := [141, 142, 143, 144]) (l₂ := [145, 146, 147, 148])
  have hm := merge_right (literal (valuationOf q) (287)) (literal (valuationOf q) (289)) (countLit q [141, 142, 143, 144]) (countLit q [145, 146, 147, 148]) (count289 q) 1 (meaning287 q) (meaning289 q) hs
  change valuationOf q 287 = false ∨ valuationOf q 289 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause620 (q : Snake 81) (h : Conditions q) : valuation q 287 = false ∨ valuation q 289 = true := counterClause620 (baseVal q)

theorem counterClause621 (q : Nat → Bool) : valuationOf q 289 = false ∨ valuationOf q 291 = true := by
  have hs : count291 q = (countLit q [134, 135, 136, 137, 138, 139, 140]) + (countLit q [141, 142, 143, 144, 145, 146, 147, 148]) := List.countP_append (p := literal q) (l₁ := [134, 135, 136, 137, 138, 139, 140]) (l₂ := [141, 142, 143, 144, 145, 146, 147, 148])
  have hm := merge_right (literal (valuationOf q) (289)) (literal (valuationOf q) (291)) (countLit q [134, 135, 136, 137, 138, 139, 140]) (countLit q [141, 142, 143, 144, 145, 146, 147, 148]) (count291 q) 1 (meaning289 q) (meaning291 q) hs
  change valuationOf q 289 = false ∨ valuationOf q 291 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause621 (q : Snake 81) (h : Conditions q) : valuation q 289 = false ∨ valuation q 291 = true := counterClause621 (baseVal q)

theorem counterClause622 (q : Nat → Bool) : valuationOf q 275 = false ∨ valuationOf q 291 = true := by
  have hs : count291 q = (countLit q [134, 135, 136, 137, 138, 139, 140]) + (countLit q [141, 142, 143, 144, 145, 146, 147, 148]) := List.countP_append (p := literal q) (l₁ := [134, 135, 136, 137, 138, 139, 140]) (l₂ := [141, 142, 143, 144, 145, 146, 147, 148])
  have hm := merge_left (literal (valuationOf q) (275)) (literal (valuationOf q) (291)) (countLit q [134, 135, 136, 137, 138, 139, 140]) (countLit q [141, 142, 143, 144, 145, 146, 147, 148]) (count291 q) 1 (meaning275 q) (meaning291 q) hs
  change valuationOf q 275 = false ∨ valuationOf q 291 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause622 (q : Snake 81) (h : Conditions q) : valuation q 275 = false ∨ valuation q 291 = true := counterClause622 (baseVal q)

theorem counterClause623 (q : Nat → Bool) : valuationOf q 275 = false ∨ valuationOf q 289 = false ∨ valuationOf q 292 = true := by
  have hs : count291 q = (countLit q [134, 135, 136, 137, 138, 139, 140]) + (countLit q [141, 142, 143, 144, 145, 146, 147, 148]) := List.countP_append (p := literal q) (l₁ := [134, 135, 136, 137, 138, 139, 140]) (l₂ := [141, 142, 143, 144, 145, 146, 147, 148])
  have hm := merge_two (literal (valuationOf q) (275)) (literal (valuationOf q) (289)) (literal (valuationOf q) (292)) (countLit q [134, 135, 136, 137, 138, 139, 140]) (countLit q [141, 142, 143, 144, 145, 146, 147, 148]) (count291 q) 1 1 (meaning275 q) (meaning289 q) (meaning292 q) hs
  change valuationOf q 275 = false ∨ valuationOf q 289 = false ∨ valuationOf q 292 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause623 (q : Snake 81) (h : Conditions q) : valuation q 275 = false ∨ valuation q 289 = false ∨ valuation q 292 = true := counterClause623 (baseVal q)

theorem counterClause624 (q : Nat → Bool) : valuationOf q 276 = false ∨ valuationOf q 292 = true := by
  have hs : count291 q = (countLit q [134, 135, 136, 137, 138, 139, 140]) + (countLit q [141, 142, 143, 144, 145, 146, 147, 148]) := List.countP_append (p := literal q) (l₁ := [134, 135, 136, 137, 138, 139, 140]) (l₂ := [141, 142, 143, 144, 145, 146, 147, 148])
  have hm := merge_left (literal (valuationOf q) (276)) (literal (valuationOf q) (292)) (countLit q [134, 135, 136, 137, 138, 139, 140]) (countLit q [141, 142, 143, 144, 145, 146, 147, 148]) (count291 q) 2 (meaning276 q) (meaning292 q) hs
  change valuationOf q 276 = false ∨ valuationOf q 292 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause624 (q : Snake 81) (h : Conditions q) : valuation q 276 = false ∨ valuation q 292 = true := counterClause624 (baseVal q)

theorem counterClause625 (q : Nat → Bool) : valuationOf q 291 = false ∨ valuationOf q 293 = true := by
  have hs : count293 q = (countLit q [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133]) + (countLit q [134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) := List.countP_append (p := literal q) (l₁ := [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133]) (l₂ := [134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148])
  have hm := merge_right (literal (valuationOf q) (291)) (literal (valuationOf q) (293)) (countLit q [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133]) (countLit q [134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) (count293 q) 1 (meaning291 q) (meaning293 q) hs
  change valuationOf q 291 = false ∨ valuationOf q 293 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause625 (q : Snake 81) (h : Conditions q) : valuation q 291 = false ∨ valuation q 293 = true := counterClause625 (baseVal q)

theorem counterClause626 (q : Nat → Bool) : valuationOf q 292 = false ∨ valuationOf q 294 = true := by
  have hs : count293 q = (countLit q [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133]) + (countLit q [134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) := List.countP_append (p := literal q) (l₁ := [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133]) (l₂ := [134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148])
  have hm := merge_right (literal (valuationOf q) (292)) (literal (valuationOf q) (294)) (countLit q [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133]) (countLit q [134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) (count293 q) 2 (meaning292 q) (meaning294 q) hs
  change valuationOf q 292 = false ∨ valuationOf q 294 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause626 (q : Snake 81) (h : Conditions q) : valuation q 292 = false ∨ valuation q 294 = true := counterClause626 (baseVal q)

theorem counterClause627 (q : Nat → Bool) : valuationOf q 263 = false ∨ valuationOf q 293 = true := by
  have hs : count293 q = (countLit q [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133]) + (countLit q [134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) := List.countP_append (p := literal q) (l₁ := [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133]) (l₂ := [134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148])
  have hm := merge_left (literal (valuationOf q) (263)) (literal (valuationOf q) (293)) (countLit q [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133]) (countLit q [134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) (count293 q) 1 (meaning263 q) (meaning293 q) hs
  change valuationOf q 263 = false ∨ valuationOf q 293 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause627 (q : Snake 81) (h : Conditions q) : valuation q 263 = false ∨ valuation q 293 = true := counterClause627 (baseVal q)

theorem counterClause628 (q : Nat → Bool) : valuationOf q 263 = false ∨ valuationOf q 291 = false ∨ valuationOf q 294 = true := by
  have hs : count293 q = (countLit q [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133]) + (countLit q [134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) := List.countP_append (p := literal q) (l₁ := [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133]) (l₂ := [134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148])
  have hm := merge_two (literal (valuationOf q) (263)) (literal (valuationOf q) (291)) (literal (valuationOf q) (294)) (countLit q [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133]) (countLit q [134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) (count293 q) 1 1 (meaning263 q) (meaning291 q) (meaning294 q) hs
  change valuationOf q 263 = false ∨ valuationOf q 291 = false ∨ valuationOf q 294 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause628 (q : Snake 81) (h : Conditions q) : valuation q 263 = false ∨ valuation q 291 = false ∨ valuation q 294 = true := counterClause628 (baseVal q)

theorem counterClause629 (q : Nat → Bool) : valuationOf q 264 = false ∨ valuationOf q 294 = true := by
  have hs : count293 q = (countLit q [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133]) + (countLit q [134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) := List.countP_append (p := literal q) (l₁ := [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133]) (l₂ := [134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148])
  have hm := merge_left (literal (valuationOf q) (264)) (literal (valuationOf q) (294)) (countLit q [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133]) (countLit q [134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) (count293 q) 2 (meaning264 q) (meaning294 q) hs
  change valuationOf q 264 = false ∨ valuationOf q 294 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause629 (q : Snake 81) (h : Conditions q) : valuation q 264 = false ∨ valuation q 294 = true := counterClause629 (baseVal q)

theorem counterClause630 (q : Nat → Bool) : valuationOf q 150 = false ∨ valuationOf q 295 = true := by
  have hs : count295 q = (countLit q [150]) + (countLit q [151]) := List.countP_append (p := literal q) (l₁ := [150]) (l₂ := [151])
  have hm := merge_left (literal (valuationOf q) (150)) (literal (valuationOf q) (295)) (countLit q [150]) (countLit q [151]) (count295 q) 1 (meaning150 q) (meaning295 q) hs
  change valuationOf q 150 = false ∨ valuationOf q 295 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause630 (q : Snake 81) (h : Conditions q) : valuation q 150 = false ∨ valuation q 295 = true := counterClause630 (baseVal q)

theorem counterClause631 (q : Nat → Bool) : valuationOf q 295 = false ∨ valuationOf q 297 = true := by
  have hs : count297 q = (countLit q [149]) + (countLit q [150, 151]) := List.countP_append (p := literal q) (l₁ := [149]) (l₂ := [150, 151])
  have hm := merge_right (literal (valuationOf q) (295)) (literal (valuationOf q) (297)) (countLit q [149]) (countLit q [150, 151]) (count297 q) 1 (meaning295 q) (meaning297 q) hs
  change valuationOf q 295 = false ∨ valuationOf q 297 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause631 (q : Snake 81) (h : Conditions q) : valuation q 295 = false ∨ valuation q 297 = true := counterClause631 (baseVal q)

theorem counterClause632 (q : Nat → Bool) : valuationOf q 152 = false ∨ valuationOf q 299 = true := by
  have hs : count299 q = (countLit q [152]) + (countLit q [153]) := List.countP_append (p := literal q) (l₁ := [152]) (l₂ := [153])
  have hm := merge_left (literal (valuationOf q) (152)) (literal (valuationOf q) (299)) (countLit q [152]) (countLit q [153]) (count299 q) 1 (meaning152 q) (meaning299 q) hs
  change valuationOf q 152 = false ∨ valuationOf q 299 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause632 (q : Snake 81) (h : Conditions q) : valuation q 152 = false ∨ valuation q 299 = true := counterClause632 (baseVal q)

theorem counterClause633 (q : Nat → Bool) : valuationOf q 155 = false ∨ valuationOf q 301 = true := by
  have hs : count301 q = (countLit q [154]) + (countLit q [155]) := List.countP_append (p := literal q) (l₁ := [154]) (l₂ := [155])
  have hm := merge_right (literal (valuationOf q) (155)) (literal (valuationOf q) (301)) (countLit q [154]) (countLit q [155]) (count301 q) 1 (meaning155 q) (meaning301 q) hs
  change valuationOf q 155 = false ∨ valuationOf q 301 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause633 (q : Snake 81) (h : Conditions q) : valuation q 155 = false ∨ valuation q 301 = true := counterClause633 (baseVal q)

theorem counterClause634 (q : Nat → Bool) : valuationOf q 301 = false ∨ valuationOf q 303 = true := by
  have hs : count303 q = (countLit q [152, 153]) + (countLit q [154, 155]) := List.countP_append (p := literal q) (l₁ := [152, 153]) (l₂ := [154, 155])
  have hm := merge_right (literal (valuationOf q) (301)) (literal (valuationOf q) (303)) (countLit q [152, 153]) (countLit q [154, 155]) (count303 q) 1 (meaning301 q) (meaning303 q) hs
  change valuationOf q 301 = false ∨ valuationOf q 303 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause634 (q : Snake 81) (h : Conditions q) : valuation q 301 = false ∨ valuation q 303 = true := counterClause634 (baseVal q)

theorem counterClause635 (q : Nat → Bool) : valuationOf q 299 = false ∨ valuationOf q 303 = true := by
  have hs : count303 q = (countLit q [152, 153]) + (countLit q [154, 155]) := List.countP_append (p := literal q) (l₁ := [152, 153]) (l₂ := [154, 155])
  have hm := merge_left (literal (valuationOf q) (299)) (literal (valuationOf q) (303)) (countLit q [152, 153]) (countLit q [154, 155]) (count303 q) 1 (meaning299 q) (meaning303 q) hs
  change valuationOf q 299 = false ∨ valuationOf q 303 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause635 (q : Snake 81) (h : Conditions q) : valuation q 299 = false ∨ valuation q 303 = true := counterClause635 (baseVal q)

theorem counterClause636 (q : Nat → Bool) : valuationOf q 303 = false ∨ valuationOf q 305 = true := by
  have hs : count305 q = (countLit q [149, 150, 151]) + (countLit q [152, 153, 154, 155]) := List.countP_append (p := literal q) (l₁ := [149, 150, 151]) (l₂ := [152, 153, 154, 155])
  have hm := merge_right (literal (valuationOf q) (303)) (literal (valuationOf q) (305)) (countLit q [149, 150, 151]) (countLit q [152, 153, 154, 155]) (count305 q) 1 (meaning303 q) (meaning305 q) hs
  change valuationOf q 303 = false ∨ valuationOf q 305 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause636 (q : Snake 81) (h : Conditions q) : valuation q 303 = false ∨ valuation q 305 = true := counterClause636 (baseVal q)

theorem counterClause637 (q : Nat → Bool) : valuationOf q 297 = false ∨ valuationOf q 305 = true := by
  have hs : count305 q = (countLit q [149, 150, 151]) + (countLit q [152, 153, 154, 155]) := List.countP_append (p := literal q) (l₁ := [149, 150, 151]) (l₂ := [152, 153, 154, 155])
  have hm := merge_left (literal (valuationOf q) (297)) (literal (valuationOf q) (305)) (countLit q [149, 150, 151]) (countLit q [152, 153, 154, 155]) (count305 q) 1 (meaning297 q) (meaning305 q) hs
  change valuationOf q 297 = false ∨ valuationOf q 305 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause637 (q : Snake 81) (h : Conditions q) : valuation q 297 = false ∨ valuation q 305 = true := counterClause637 (baseVal q)

theorem counterClause638 (q : Nat → Bool) : valuationOf q 156 = false ∨ valuationOf q 307 = true := by
  have hs : count307 q = (countLit q [156]) + (countLit q [157]) := List.countP_append (p := literal q) (l₁ := [156]) (l₂ := [157])
  have hm := merge_left (literal (valuationOf q) (156)) (literal (valuationOf q) (307)) (countLit q [156]) (countLit q [157]) (count307 q) 1 (meaning156 q) (meaning307 q) hs
  change valuationOf q 156 = false ∨ valuationOf q 307 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause638 (q : Snake 81) (h : Conditions q) : valuation q 156 = false ∨ valuation q 307 = true := counterClause638 (baseVal q)

theorem counterClause639 (q : Nat → Bool) : valuationOf q 159 = false ∨ valuationOf q 309 = true := by
  have hs : count309 q = (countLit q [158]) + (countLit q [159]) := List.countP_append (p := literal q) (l₁ := [158]) (l₂ := [159])
  have hm := merge_right (literal (valuationOf q) (159)) (literal (valuationOf q) (309)) (countLit q [158]) (countLit q [159]) (count309 q) 1 (meaning159 q) (meaning309 q) hs
  change valuationOf q 159 = false ∨ valuationOf q 309 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause639 (q : Snake 81) (h : Conditions q) : valuation q 159 = false ∨ valuation q 309 = true := counterClause639 (baseVal q)

theorem counterClause640 (q : Nat → Bool) : valuationOf q 309 = false ∨ valuationOf q 311 = true := by
  have hs : count311 q = (countLit q [156, 157]) + (countLit q [158, 159]) := List.countP_append (p := literal q) (l₁ := [156, 157]) (l₂ := [158, 159])
  have hm := merge_right (literal (valuationOf q) (309)) (literal (valuationOf q) (311)) (countLit q [156, 157]) (countLit q [158, 159]) (count311 q) 1 (meaning309 q) (meaning311 q) hs
  change valuationOf q 309 = false ∨ valuationOf q 311 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause640 (q : Snake 81) (h : Conditions q) : valuation q 309 = false ∨ valuation q 311 = true := counterClause640 (baseVal q)

theorem block19 (q : Snake 81) (h : Conditions q) : B112E078.Block19 (valuation q) :=
  ⟨clause609 q h, clause610 q h, clause611 q h, clause612 q h, clause613 q h, clause614 q h, clause615 q h, clause616 q h, clause617 q h, clause618 q h, clause619 q h, clause620 q h, clause621 q h, clause622 q h, clause623 q h, clause624 q h, clause625 q h, clause626 q h, clause627 q h, clause628 q h, clause629 q h, clause630 q h, clause631 q h, clause632 q h, clause633 q h, clause634 q h, clause635 q h, clause636 q h, clause637 q h, clause638 q h, clause639 q h, clause640 q h⟩

end
end Snake9.Regrowth.E112078
