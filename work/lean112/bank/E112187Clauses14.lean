import E112187Semantics
import B112E187Inputs
namespace Snake9.Regrowth.E112187
noncomputable section
local instance blockDec14 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause449 (q : Nat → Bool) : valuationOf q 267 = false ∨ valuationOf q 275 = true := by
  have hs : count275 q = (countLit q [134, 135, 136]) + (countLit q [137, 138, 139, 140]) := List.countP_append (p := literal q) (l₁ := [134, 135, 136]) (l₂ := [137, 138, 139, 140])
  have hm := merge_left (literal (valuationOf q) (267)) (literal (valuationOf q) (275)) (countLit q [134, 135, 136]) (countLit q [137, 138, 139, 140]) (count275 q) 1 (meaning267 q) (meaning275 q) hs
  change valuationOf q 267 = false ∨ valuationOf q 275 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause449 (q : Snake 81) (h : Conditions q) : valuation q 267 = false ∨ valuation q 275 = true := counterClause449 (baseVal q)

theorem counterClause450 (q : Nat → Bool) : valuationOf q 142 = false ∨ valuationOf q 277 = true := by
  have hs : count277 q = (countLit q [141]) + (countLit q [142]) := List.countP_append (p := literal q) (l₁ := [141]) (l₂ := [142])
  have hm := merge_right (literal (valuationOf q) (142)) (literal (valuationOf q) (277)) (countLit q [141]) (countLit q [142]) (count277 q) 1 (meaning142 q) (meaning277 q) hs
  change valuationOf q 142 = false ∨ valuationOf q 277 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause450 (q : Snake 81) (h : Conditions q) : valuation q 142 = false ∨ valuation q 277 = true := counterClause450 (baseVal q)

theorem counterClause451 (q : Nat → Bool) : valuationOf q 144 = false ∨ valuationOf q 279 = true := by
  have hs : count279 q = (countLit q [143]) + (countLit q [144]) := List.countP_append (p := literal q) (l₁ := [143]) (l₂ := [144])
  have hm := merge_right (literal (valuationOf q) (144)) (literal (valuationOf q) (279)) (countLit q [143]) (countLit q [144]) (count279 q) 1 (meaning144 q) (meaning279 q) hs
  change valuationOf q 144 = false ∨ valuationOf q 279 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause451 (q : Snake 81) (h : Conditions q) : valuation q 144 = false ∨ valuation q 279 = true := counterClause451 (baseVal q)

theorem counterClause452 (q : Nat → Bool) : valuationOf q 143 = false ∨ valuationOf q 279 = true := by
  have hs : count279 q = (countLit q [143]) + (countLit q [144]) := List.countP_append (p := literal q) (l₁ := [143]) (l₂ := [144])
  have hm := merge_left (literal (valuationOf q) (143)) (literal (valuationOf q) (279)) (countLit q [143]) (countLit q [144]) (count279 q) 1 (meaning143 q) (meaning279 q) hs
  change valuationOf q 143 = false ∨ valuationOf q 279 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause452 (q : Snake 81) (h : Conditions q) : valuation q 143 = false ∨ valuation q 279 = true := counterClause452 (baseVal q)

theorem counterClause453 (q : Nat → Bool) : valuationOf q 143 = false ∨ valuationOf q 144 = false ∨ valuationOf q 280 = true := by
  have hs : count279 q = (countLit q [143]) + (countLit q [144]) := List.countP_append (p := literal q) (l₁ := [143]) (l₂ := [144])
  have hm := merge_two (literal (valuationOf q) (143)) (literal (valuationOf q) (144)) (literal (valuationOf q) (280)) (countLit q [143]) (countLit q [144]) (count279 q) 1 1 (meaning143 q) (meaning144 q) (meaning280 q) hs
  change valuationOf q 143 = false ∨ valuationOf q 144 = false ∨ valuationOf q 280 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause453 (q : Snake 81) (h : Conditions q) : valuation q 143 = false ∨ valuation q 144 = false ∨ valuation q 280 = true := counterClause453 (baseVal q)

theorem counterClause454 (q : Nat → Bool) : valuationOf q 279 = false ∨ valuationOf q 281 = true := by
  have hs : count281 q = (countLit q [141, 142]) + (countLit q [143, 144]) := List.countP_append (p := literal q) (l₁ := [141, 142]) (l₂ := [143, 144])
  have hm := merge_right (literal (valuationOf q) (279)) (literal (valuationOf q) (281)) (countLit q [141, 142]) (countLit q [143, 144]) (count281 q) 1 (meaning279 q) (meaning281 q) hs
  change valuationOf q 279 = false ∨ valuationOf q 281 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause454 (q : Snake 81) (h : Conditions q) : valuation q 279 = false ∨ valuation q 281 = true := counterClause454 (baseVal q)

theorem counterClause455 (q : Nat → Bool) : valuationOf q 280 = false ∨ valuationOf q 282 = true := by
  have hs : count281 q = (countLit q [141, 142]) + (countLit q [143, 144]) := List.countP_append (p := literal q) (l₁ := [141, 142]) (l₂ := [143, 144])
  have hm := merge_right (literal (valuationOf q) (280)) (literal (valuationOf q) (282)) (countLit q [141, 142]) (countLit q [143, 144]) (count281 q) 2 (meaning280 q) (meaning282 q) hs
  change valuationOf q 280 = false ∨ valuationOf q 282 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause455 (q : Snake 81) (h : Conditions q) : valuation q 280 = false ∨ valuation q 282 = true := counterClause455 (baseVal q)

theorem counterClause456 (q : Nat → Bool) : valuationOf q 277 = false ∨ valuationOf q 281 = true := by
  have hs : count281 q = (countLit q [141, 142]) + (countLit q [143, 144]) := List.countP_append (p := literal q) (l₁ := [141, 142]) (l₂ := [143, 144])
  have hm := merge_left (literal (valuationOf q) (277)) (literal (valuationOf q) (281)) (countLit q [141, 142]) (countLit q [143, 144]) (count281 q) 1 (meaning277 q) (meaning281 q) hs
  change valuationOf q 277 = false ∨ valuationOf q 281 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause456 (q : Snake 81) (h : Conditions q) : valuation q 277 = false ∨ valuation q 281 = true := counterClause456 (baseVal q)

theorem counterClause457 (q : Nat → Bool) : valuationOf q 148 = false ∨ valuationOf q 285 = true := by
  have hs : count285 q = (countLit q [147]) + (countLit q [148]) := List.countP_append (p := literal q) (l₁ := [147]) (l₂ := [148])
  have hm := merge_right (literal (valuationOf q) (148)) (literal (valuationOf q) (285)) (countLit q [147]) (countLit q [148]) (count285 q) 1 (meaning148 q) (meaning285 q) hs
  change valuationOf q 148 = false ∨ valuationOf q 285 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause457 (q : Snake 81) (h : Conditions q) : valuation q 148 = false ∨ valuation q 285 = true := counterClause457 (baseVal q)

theorem counterClause458 (q : Nat → Bool) : valuationOf q 285 = false ∨ valuationOf q 287 = true := by
  have hs : count287 q = (countLit q [145, 146]) + (countLit q [147, 148]) := List.countP_append (p := literal q) (l₁ := [145, 146]) (l₂ := [147, 148])
  have hm := merge_right (literal (valuationOf q) (285)) (literal (valuationOf q) (287)) (countLit q [145, 146]) (countLit q [147, 148]) (count287 q) 1 (meaning285 q) (meaning287 q) hs
  change valuationOf q 285 = false ∨ valuationOf q 287 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause458 (q : Snake 81) (h : Conditions q) : valuation q 285 = false ∨ valuation q 287 = true := counterClause458 (baseVal q)

theorem counterClause459 (q : Nat → Bool) : valuationOf q 287 = false ∨ valuationOf q 289 = true := by
  have hs : count289 q = (countLit q [141, 142, 143, 144]) + (countLit q [145, 146, 147, 148]) := List.countP_append (p := literal q) (l₁ := [141, 142, 143, 144]) (l₂ := [145, 146, 147, 148])
  have hm := merge_right (literal (valuationOf q) (287)) (literal (valuationOf q) (289)) (countLit q [141, 142, 143, 144]) (countLit q [145, 146, 147, 148]) (count289 q) 1 (meaning287 q) (meaning289 q) hs
  change valuationOf q 287 = false ∨ valuationOf q 289 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause459 (q : Snake 81) (h : Conditions q) : valuation q 287 = false ∨ valuation q 289 = true := counterClause459 (baseVal q)

theorem counterClause460 (q : Nat → Bool) : valuationOf q 281 = false ∨ valuationOf q 289 = true := by
  have hs : count289 q = (countLit q [141, 142, 143, 144]) + (countLit q [145, 146, 147, 148]) := List.countP_append (p := literal q) (l₁ := [141, 142, 143, 144]) (l₂ := [145, 146, 147, 148])
  have hm := merge_left (literal (valuationOf q) (281)) (literal (valuationOf q) (289)) (countLit q [141, 142, 143, 144]) (countLit q [145, 146, 147, 148]) (count289 q) 1 (meaning281 q) (meaning289 q) hs
  change valuationOf q 281 = false ∨ valuationOf q 289 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause460 (q : Snake 81) (h : Conditions q) : valuation q 281 = false ∨ valuation q 289 = true := counterClause460 (baseVal q)

theorem counterClause461 (q : Nat → Bool) : valuationOf q 282 = false ∨ valuationOf q 290 = true := by
  have hs : count289 q = (countLit q [141, 142, 143, 144]) + (countLit q [145, 146, 147, 148]) := List.countP_append (p := literal q) (l₁ := [141, 142, 143, 144]) (l₂ := [145, 146, 147, 148])
  have hm := merge_left (literal (valuationOf q) (282)) (literal (valuationOf q) (290)) (countLit q [141, 142, 143, 144]) (countLit q [145, 146, 147, 148]) (count289 q) 2 (meaning282 q) (meaning290 q) hs
  change valuationOf q 282 = false ∨ valuationOf q 290 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause461 (q : Snake 81) (h : Conditions q) : valuation q 282 = false ∨ valuation q 290 = true := counterClause461 (baseVal q)

theorem counterClause462 (q : Nat → Bool) : valuationOf q 289 = false ∨ valuationOf q 291 = true := by
  have hs : count291 q = (countLit q [134, 135, 136, 137, 138, 139, 140]) + (countLit q [141, 142, 143, 144, 145, 146, 147, 148]) := List.countP_append (p := literal q) (l₁ := [134, 135, 136, 137, 138, 139, 140]) (l₂ := [141, 142, 143, 144, 145, 146, 147, 148])
  have hm := merge_right (literal (valuationOf q) (289)) (literal (valuationOf q) (291)) (countLit q [134, 135, 136, 137, 138, 139, 140]) (countLit q [141, 142, 143, 144, 145, 146, 147, 148]) (count291 q) 1 (meaning289 q) (meaning291 q) hs
  change valuationOf q 289 = false ∨ valuationOf q 291 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause462 (q : Snake 81) (h : Conditions q) : valuation q 289 = false ∨ valuation q 291 = true := counterClause462 (baseVal q)

theorem counterClause463 (q : Nat → Bool) : valuationOf q 290 = false ∨ valuationOf q 292 = true := by
  have hs : count291 q = (countLit q [134, 135, 136, 137, 138, 139, 140]) + (countLit q [141, 142, 143, 144, 145, 146, 147, 148]) := List.countP_append (p := literal q) (l₁ := [134, 135, 136, 137, 138, 139, 140]) (l₂ := [141, 142, 143, 144, 145, 146, 147, 148])
  have hm := merge_right (literal (valuationOf q) (290)) (literal (valuationOf q) (292)) (countLit q [134, 135, 136, 137, 138, 139, 140]) (countLit q [141, 142, 143, 144, 145, 146, 147, 148]) (count291 q) 2 (meaning290 q) (meaning292 q) hs
  change valuationOf q 290 = false ∨ valuationOf q 292 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause463 (q : Snake 81) (h : Conditions q) : valuation q 290 = false ∨ valuation q 292 = true := counterClause463 (baseVal q)

theorem counterClause464 (q : Nat → Bool) : valuationOf q 275 = false ∨ valuationOf q 291 = true := by
  have hs : count291 q = (countLit q [134, 135, 136, 137, 138, 139, 140]) + (countLit q [141, 142, 143, 144, 145, 146, 147, 148]) := List.countP_append (p := literal q) (l₁ := [134, 135, 136, 137, 138, 139, 140]) (l₂ := [141, 142, 143, 144, 145, 146, 147, 148])
  have hm := merge_left (literal (valuationOf q) (275)) (literal (valuationOf q) (291)) (countLit q [134, 135, 136, 137, 138, 139, 140]) (countLit q [141, 142, 143, 144, 145, 146, 147, 148]) (count291 q) 1 (meaning275 q) (meaning291 q) hs
  change valuationOf q 275 = false ∨ valuationOf q 291 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause464 (q : Snake 81) (h : Conditions q) : valuation q 275 = false ∨ valuation q 291 = true := counterClause464 (baseVal q)

theorem counterClause465 (q : Nat → Bool) : valuationOf q 291 = false ∨ valuationOf q 293 = true := by
  have hs : count293 q = (countLit q [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133]) + (countLit q [134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) := List.countP_append (p := literal q) (l₁ := [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133]) (l₂ := [134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148])
  have hm := merge_right (literal (valuationOf q) (291)) (literal (valuationOf q) (293)) (countLit q [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133]) (countLit q [134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) (count293 q) 1 (meaning291 q) (meaning293 q) hs
  change valuationOf q 291 = false ∨ valuationOf q 293 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause465 (q : Snake 81) (h : Conditions q) : valuation q 291 = false ∨ valuation q 293 = true := counterClause465 (baseVal q)

theorem counterClause466 (q : Nat → Bool) : valuationOf q 292 = false ∨ valuationOf q 294 = true := by
  have hs : count293 q = (countLit q [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133]) + (countLit q [134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) := List.countP_append (p := literal q) (l₁ := [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133]) (l₂ := [134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148])
  have hm := merge_right (literal (valuationOf q) (292)) (literal (valuationOf q) (294)) (countLit q [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133]) (countLit q [134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) (count293 q) 2 (meaning292 q) (meaning294 q) hs
  change valuationOf q 292 = false ∨ valuationOf q 294 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause466 (q : Snake 81) (h : Conditions q) : valuation q 292 = false ∨ valuation q 294 = true := counterClause466 (baseVal q)

theorem counterClause467 (q : Nat → Bool) : valuationOf q 263 = false ∨ valuationOf q 293 = true := by
  have hs : count293 q = (countLit q [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133]) + (countLit q [134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) := List.countP_append (p := literal q) (l₁ := [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133]) (l₂ := [134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148])
  have hm := merge_left (literal (valuationOf q) (263)) (literal (valuationOf q) (293)) (countLit q [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133]) (countLit q [134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) (count293 q) 1 (meaning263 q) (meaning293 q) hs
  change valuationOf q 263 = false ∨ valuationOf q 293 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause467 (q : Snake 81) (h : Conditions q) : valuation q 263 = false ∨ valuation q 293 = true := counterClause467 (baseVal q)

theorem counterClause468 (q : Nat → Bool) : valuationOf q 263 = false ∨ valuationOf q 291 = false ∨ valuationOf q 294 = true := by
  have hs : count293 q = (countLit q [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133]) + (countLit q [134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) := List.countP_append (p := literal q) (l₁ := [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133]) (l₂ := [134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148])
  have hm := merge_two (literal (valuationOf q) (263)) (literal (valuationOf q) (291)) (literal (valuationOf q) (294)) (countLit q [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133]) (countLit q [134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) (count293 q) 1 1 (meaning263 q) (meaning291 q) (meaning294 q) hs
  change valuationOf q 263 = false ∨ valuationOf q 291 = false ∨ valuationOf q 294 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause468 (q : Snake 81) (h : Conditions q) : valuation q 263 = false ∨ valuation q 291 = false ∨ valuation q 294 = true := counterClause468 (baseVal q)

theorem counterClause469 (q : Nat → Bool) : valuationOf q 151 = false ∨ valuationOf q 295 = true := by
  have hs : count295 q = (countLit q [150]) + (countLit q [151]) := List.countP_append (p := literal q) (l₁ := [150]) (l₂ := [151])
  have hm := merge_right (literal (valuationOf q) (151)) (literal (valuationOf q) (295)) (countLit q [150]) (countLit q [151]) (count295 q) 1 (meaning151 q) (meaning295 q) hs
  change valuationOf q 151 = false ∨ valuationOf q 295 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause469 (q : Snake 81) (h : Conditions q) : valuation q 151 = false ∨ valuation q 295 = true := counterClause469 (baseVal q)

theorem counterClause470 (q : Nat → Bool) : valuationOf q 150 = false ∨ valuationOf q 295 = true := by
  have hs : count295 q = (countLit q [150]) + (countLit q [151]) := List.countP_append (p := literal q) (l₁ := [150]) (l₂ := [151])
  have hm := merge_left (literal (valuationOf q) (150)) (literal (valuationOf q) (295)) (countLit q [150]) (countLit q [151]) (count295 q) 1 (meaning150 q) (meaning295 q) hs
  change valuationOf q 150 = false ∨ valuationOf q 295 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause470 (q : Snake 81) (h : Conditions q) : valuation q 150 = false ∨ valuation q 295 = true := counterClause470 (baseVal q)

theorem counterClause471 (q : Nat → Bool) : valuationOf q 150 = false ∨ valuationOf q 151 = false ∨ valuationOf q 296 = true := by
  have hs : count295 q = (countLit q [150]) + (countLit q [151]) := List.countP_append (p := literal q) (l₁ := [150]) (l₂ := [151])
  have hm := merge_two (literal (valuationOf q) (150)) (literal (valuationOf q) (151)) (literal (valuationOf q) (296)) (countLit q [150]) (countLit q [151]) (count295 q) 1 1 (meaning150 q) (meaning151 q) (meaning296 q) hs
  change valuationOf q 150 = false ∨ valuationOf q 151 = false ∨ valuationOf q 296 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause471 (q : Snake 81) (h : Conditions q) : valuation q 150 = false ∨ valuation q 151 = false ∨ valuation q 296 = true := counterClause471 (baseVal q)

theorem counterClause472 (q : Nat → Bool) : valuationOf q 295 = false ∨ valuationOf q 297 = true := by
  have hs : count297 q = (countLit q [149]) + (countLit q [150, 151]) := List.countP_append (p := literal q) (l₁ := [149]) (l₂ := [150, 151])
  have hm := merge_right (literal (valuationOf q) (295)) (literal (valuationOf q) (297)) (countLit q [149]) (countLit q [150, 151]) (count297 q) 1 (meaning295 q) (meaning297 q) hs
  change valuationOf q 295 = false ∨ valuationOf q 297 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause472 (q : Snake 81) (h : Conditions q) : valuation q 295 = false ∨ valuation q 297 = true := counterClause472 (baseVal q)

theorem counterClause473 (q : Nat → Bool) : valuationOf q 296 = false ∨ valuationOf q 298 = true := by
  have hs : count297 q = (countLit q [149]) + (countLit q [150, 151]) := List.countP_append (p := literal q) (l₁ := [149]) (l₂ := [150, 151])
  have hm := merge_right (literal (valuationOf q) (296)) (literal (valuationOf q) (298)) (countLit q [149]) (countLit q [150, 151]) (count297 q) 2 (meaning296 q) (meaning298 q) hs
  change valuationOf q 296 = false ∨ valuationOf q 298 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause473 (q : Snake 81) (h : Conditions q) : valuation q 296 = false ∨ valuation q 298 = true := counterClause473 (baseVal q)

theorem counterClause474 (q : Nat → Bool) : valuationOf q 153 = false ∨ valuationOf q 299 = true := by
  have hs : count299 q = (countLit q [152]) + (countLit q [153]) := List.countP_append (p := literal q) (l₁ := [152]) (l₂ := [153])
  have hm := merge_right (literal (valuationOf q) (153)) (literal (valuationOf q) (299)) (countLit q [152]) (countLit q [153]) (count299 q) 1 (meaning153 q) (meaning299 q) hs
  change valuationOf q 153 = false ∨ valuationOf q 299 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause474 (q : Snake 81) (h : Conditions q) : valuation q 153 = false ∨ valuation q 299 = true := counterClause474 (baseVal q)

theorem counterClause475 (q : Nat → Bool) : valuationOf q 154 = false ∨ valuationOf q 301 = true := by
  have hs : count301 q = (countLit q [154]) + (countLit q [155]) := List.countP_append (p := literal q) (l₁ := [154]) (l₂ := [155])
  have hm := merge_left (literal (valuationOf q) (154)) (literal (valuationOf q) (301)) (countLit q [154]) (countLit q [155]) (count301 q) 1 (meaning154 q) (meaning301 q) hs
  change valuationOf q 154 = false ∨ valuationOf q 301 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause475 (q : Snake 81) (h : Conditions q) : valuation q 154 = false ∨ valuation q 301 = true := counterClause475 (baseVal q)

theorem counterClause476 (q : Nat → Bool) : valuationOf q 301 = false ∨ valuationOf q 303 = true := by
  have hs : count303 q = (countLit q [152, 153]) + (countLit q [154, 155]) := List.countP_append (p := literal q) (l₁ := [152, 153]) (l₂ := [154, 155])
  have hm := merge_right (literal (valuationOf q) (301)) (literal (valuationOf q) (303)) (countLit q [152, 153]) (countLit q [154, 155]) (count303 q) 1 (meaning301 q) (meaning303 q) hs
  change valuationOf q 301 = false ∨ valuationOf q 303 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause476 (q : Snake 81) (h : Conditions q) : valuation q 301 = false ∨ valuation q 303 = true := counterClause476 (baseVal q)

theorem counterClause477 (q : Nat → Bool) : valuationOf q 299 = false ∨ valuationOf q 303 = true := by
  have hs : count303 q = (countLit q [152, 153]) + (countLit q [154, 155]) := List.countP_append (p := literal q) (l₁ := [152, 153]) (l₂ := [154, 155])
  have hm := merge_left (literal (valuationOf q) (299)) (literal (valuationOf q) (303)) (countLit q [152, 153]) (countLit q [154, 155]) (count303 q) 1 (meaning299 q) (meaning303 q) hs
  change valuationOf q 299 = false ∨ valuationOf q 303 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause477 (q : Snake 81) (h : Conditions q) : valuation q 299 = false ∨ valuation q 303 = true := counterClause477 (baseVal q)

theorem counterClause478 (q : Nat → Bool) : valuationOf q 299 = false ∨ valuationOf q 301 = false ∨ valuationOf q 304 = true := by
  have hs : count303 q = (countLit q [152, 153]) + (countLit q [154, 155]) := List.countP_append (p := literal q) (l₁ := [152, 153]) (l₂ := [154, 155])
  have hm := merge_two (literal (valuationOf q) (299)) (literal (valuationOf q) (301)) (literal (valuationOf q) (304)) (countLit q [152, 153]) (countLit q [154, 155]) (count303 q) 1 1 (meaning299 q) (meaning301 q) (meaning304 q) hs
  change valuationOf q 299 = false ∨ valuationOf q 301 = false ∨ valuationOf q 304 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause478 (q : Snake 81) (h : Conditions q) : valuation q 299 = false ∨ valuation q 301 = false ∨ valuation q 304 = true := counterClause478 (baseVal q)

theorem counterClause479 (q : Nat → Bool) : valuationOf q 303 = false ∨ valuationOf q 305 = true := by
  have hs : count305 q = (countLit q [149, 150, 151]) + (countLit q [152, 153, 154, 155]) := List.countP_append (p := literal q) (l₁ := [149, 150, 151]) (l₂ := [152, 153, 154, 155])
  have hm := merge_right (literal (valuationOf q) (303)) (literal (valuationOf q) (305)) (countLit q [149, 150, 151]) (countLit q [152, 153, 154, 155]) (count305 q) 1 (meaning303 q) (meaning305 q) hs
  change valuationOf q 303 = false ∨ valuationOf q 305 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause479 (q : Snake 81) (h : Conditions q) : valuation q 303 = false ∨ valuation q 305 = true := counterClause479 (baseVal q)

theorem counterClause480 (q : Nat → Bool) : valuationOf q 304 = false ∨ valuationOf q 306 = true := by
  have hs : count305 q = (countLit q [149, 150, 151]) + (countLit q [152, 153, 154, 155]) := List.countP_append (p := literal q) (l₁ := [149, 150, 151]) (l₂ := [152, 153, 154, 155])
  have hm := merge_right (literal (valuationOf q) (304)) (literal (valuationOf q) (306)) (countLit q [149, 150, 151]) (countLit q [152, 153, 154, 155]) (count305 q) 2 (meaning304 q) (meaning306 q) hs
  change valuationOf q 304 = false ∨ valuationOf q 306 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause480 (q : Snake 81) (h : Conditions q) : valuation q 304 = false ∨ valuation q 306 = true := counterClause480 (baseVal q)

theorem block14 (q : Snake 81) (h : Conditions q) : B112E187.Block14 (valuation q) :=
  ⟨clause449 q h, clause450 q h, clause451 q h, clause452 q h, clause453 q h, clause454 q h, clause455 q h, clause456 q h, clause457 q h, clause458 q h, clause459 q h, clause460 q h, clause461 q h, clause462 q h, clause463 q h, clause464 q h, clause465 q h, clause466 q h, clause467 q h, clause468 q h, clause469 q h, clause470 q h, clause471 q h, clause472 q h, clause473 q h, clause474 q h, clause475 q h, clause476 q h, clause477 q h, clause478 q h, clause479 q h, clause480 q h⟩

end
end Snake9.Regrowth.E112187
