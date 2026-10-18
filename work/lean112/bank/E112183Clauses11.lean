import E112183Semantics
import B112E183Inputs
namespace Snake9.Regrowth.E112183
noncomputable section
local instance blockDec11 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause353 (q : Nat → Bool) : valuationOf q 269 = false ∨ valuationOf q 271 = true := by
  have hs : count271 q = (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) + (countLit q [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) := List.countP_append (p := literal q) (l₁ := [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) (l₂ := [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137])
  have hm := merge_right (literal (valuationOf q) (269)) (literal (valuationOf q) (271)) (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) (countLit q [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) (count271 q) 1 (meaning269 q) (meaning271 q) hs
  change valuationOf q 269 = false ∨ valuationOf q 271 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause353 (q : Snake 81) (h : Conditions q) : valuation q 269 = false ∨ valuation q 271 = true := counterClause353 (baseVal q)

theorem counterClause354 (q : Nat → Bool) : valuationOf q 270 = false ∨ valuationOf q 272 = true := by
  have hs : count271 q = (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) + (countLit q [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) := List.countP_append (p := literal q) (l₁ := [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) (l₂ := [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137])
  have hm := merge_right (literal (valuationOf q) (270)) (literal (valuationOf q) (272)) (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) (countLit q [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) (count271 q) 2 (meaning270 q) (meaning272 q) hs
  change valuationOf q 270 = false ∨ valuationOf q 272 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause354 (q : Snake 81) (h : Conditions q) : valuation q 270 = false ∨ valuation q 272 = true := counterClause354 (baseVal q)

theorem counterClause355 (q : Nat → Bool) : valuationOf q 243 = false ∨ valuationOf q 271 = true := by
  have hs : count271 q = (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) + (countLit q [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) := List.countP_append (p := literal q) (l₁ := [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) (l₂ := [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137])
  have hm := merge_left (literal (valuationOf q) (243)) (literal (valuationOf q) (271)) (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) (countLit q [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) (count271 q) 1 (meaning243 q) (meaning271 q) hs
  change valuationOf q 243 = false ∨ valuationOf q 271 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause355 (q : Snake 81) (h : Conditions q) : valuation q 243 = false ∨ valuation q 271 = true := counterClause355 (baseVal q)

theorem counterClause356 (q : Nat → Bool) : valuationOf q 243 = false ∨ valuationOf q 269 = false ∨ valuationOf q 272 = true := by
  have hs : count271 q = (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) + (countLit q [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) := List.countP_append (p := literal q) (l₁ := [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) (l₂ := [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137])
  have hm := merge_two (literal (valuationOf q) (243)) (literal (valuationOf q) (269)) (literal (valuationOf q) (272)) (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) (countLit q [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) (count271 q) 1 1 (meaning243 q) (meaning269 q) (meaning272 q) hs
  change valuationOf q 243 = false ∨ valuationOf q 269 = false ∨ valuationOf q 272 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause356 (q : Snake 81) (h : Conditions q) : valuation q 243 = false ∨ valuation q 269 = false ∨ valuation q 272 = true := counterClause356 (baseVal q)

theorem counterClause357 (q : Nat → Bool) : valuationOf q 139 = false ∨ valuationOf q 273 = true := by
  have hs : count273 q = (countLit q [139]) + (countLit q [140]) := List.countP_append (p := literal q) (l₁ := [139]) (l₂ := [140])
  have hm := merge_left (literal (valuationOf q) (139)) (literal (valuationOf q) (273)) (countLit q [139]) (countLit q [140]) (count273 q) 1 (meaning139 q) (meaning273 q) hs
  change valuationOf q 139 = false ∨ valuationOf q 273 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause357 (q : Snake 81) (h : Conditions q) : valuation q 139 = false ∨ valuation q 273 = true := counterClause357 (baseVal q)

theorem counterClause358 (q : Nat → Bool) : valuationOf q 273 = false ∨ valuationOf q 275 = true := by
  have hs : count275 q = (countLit q [138]) + (countLit q [139, 140]) := List.countP_append (p := literal q) (l₁ := [138]) (l₂ := [139, 140])
  have hm := merge_right (literal (valuationOf q) (273)) (literal (valuationOf q) (275)) (countLit q [138]) (countLit q [139, 140]) (count275 q) 1 (meaning273 q) (meaning275 q) hs
  change valuationOf q 273 = false ∨ valuationOf q 275 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause358 (q : Snake 81) (h : Conditions q) : valuation q 273 = false ∨ valuation q 275 = true := counterClause358 (baseVal q)

theorem counterClause359 (q : Nat → Bool) : valuationOf q 142 = false ∨ valuationOf q 277 = true := by
  have hs : count277 q = (countLit q [142]) + (countLit q [143]) := List.countP_append (p := literal q) (l₁ := [142]) (l₂ := [143])
  have hm := merge_left (literal (valuationOf q) (142)) (literal (valuationOf q) (277)) (countLit q [142]) (countLit q [143]) (count277 q) 1 (meaning142 q) (meaning277 q) hs
  change valuationOf q 142 = false ∨ valuationOf q 277 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause359 (q : Snake 81) (h : Conditions q) : valuation q 142 = false ∨ valuation q 277 = true := counterClause359 (baseVal q)

theorem counterClause360 (q : Nat → Bool) : valuationOf q 277 = false ∨ valuationOf q 279 = true := by
  have hs : count279 q = (countLit q [141]) + (countLit q [142, 143]) := List.countP_append (p := literal q) (l₁ := [141]) (l₂ := [142, 143])
  have hm := merge_right (literal (valuationOf q) (277)) (literal (valuationOf q) (279)) (countLit q [141]) (countLit q [142, 143]) (count279 q) 1 (meaning277 q) (meaning279 q) hs
  change valuationOf q 277 = false ∨ valuationOf q 279 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause360 (q : Snake 81) (h : Conditions q) : valuation q 277 = false ∨ valuation q 279 = true := counterClause360 (baseVal q)

theorem counterClause361 (q : Nat → Bool) : valuationOf q 141 = false ∨ valuationOf q 279 = true := by
  have hs : count279 q = (countLit q [141]) + (countLit q [142, 143]) := List.countP_append (p := literal q) (l₁ := [141]) (l₂ := [142, 143])
  have hm := merge_left (literal (valuationOf q) (141)) (literal (valuationOf q) (279)) (countLit q [141]) (countLit q [142, 143]) (count279 q) 1 (meaning141 q) (meaning279 q) hs
  change valuationOf q 141 = false ∨ valuationOf q 279 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause361 (q : Snake 81) (h : Conditions q) : valuation q 141 = false ∨ valuation q 279 = true := counterClause361 (baseVal q)

theorem counterClause362 (q : Nat → Bool) : valuationOf q 141 = false ∨ valuationOf q 277 = false ∨ valuationOf q 280 = true := by
  have hs : count279 q = (countLit q [141]) + (countLit q [142, 143]) := List.countP_append (p := literal q) (l₁ := [141]) (l₂ := [142, 143])
  have hm := merge_two (literal (valuationOf q) (141)) (literal (valuationOf q) (277)) (literal (valuationOf q) (280)) (countLit q [141]) (countLit q [142, 143]) (count279 q) 1 1 (meaning141 q) (meaning277 q) (meaning280 q) hs
  change valuationOf q 141 = false ∨ valuationOf q 277 = false ∨ valuationOf q 280 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause362 (q : Snake 81) (h : Conditions q) : valuation q 141 = false ∨ valuation q 277 = false ∨ valuation q 280 = true := counterClause362 (baseVal q)

theorem counterClause363 (q : Nat → Bool) : valuationOf q 279 = false ∨ valuationOf q 281 = true := by
  have hs : count281 q = (countLit q [138, 139, 140]) + (countLit q [141, 142, 143]) := List.countP_append (p := literal q) (l₁ := [138, 139, 140]) (l₂ := [141, 142, 143])
  have hm := merge_right (literal (valuationOf q) (279)) (literal (valuationOf q) (281)) (countLit q [138, 139, 140]) (countLit q [141, 142, 143]) (count281 q) 1 (meaning279 q) (meaning281 q) hs
  change valuationOf q 279 = false ∨ valuationOf q 281 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause363 (q : Snake 81) (h : Conditions q) : valuation q 279 = false ∨ valuation q 281 = true := counterClause363 (baseVal q)

theorem counterClause364 (q : Nat → Bool) : valuationOf q 280 = false ∨ valuationOf q 282 = true := by
  have hs : count281 q = (countLit q [138, 139, 140]) + (countLit q [141, 142, 143]) := List.countP_append (p := literal q) (l₁ := [138, 139, 140]) (l₂ := [141, 142, 143])
  have hm := merge_right (literal (valuationOf q) (280)) (literal (valuationOf q) (282)) (countLit q [138, 139, 140]) (countLit q [141, 142, 143]) (count281 q) 2 (meaning280 q) (meaning282 q) hs
  change valuationOf q 280 = false ∨ valuationOf q 282 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause364 (q : Snake 81) (h : Conditions q) : valuation q 280 = false ∨ valuation q 282 = true := counterClause364 (baseVal q)

theorem counterClause365 (q : Nat → Bool) : valuationOf q 275 = false ∨ valuationOf q 281 = true := by
  have hs : count281 q = (countLit q [138, 139, 140]) + (countLit q [141, 142, 143]) := List.countP_append (p := literal q) (l₁ := [138, 139, 140]) (l₂ := [141, 142, 143])
  have hm := merge_left (literal (valuationOf q) (275)) (literal (valuationOf q) (281)) (countLit q [138, 139, 140]) (countLit q [141, 142, 143]) (count281 q) 1 (meaning275 q) (meaning281 q) hs
  change valuationOf q 275 = false ∨ valuationOf q 281 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause365 (q : Snake 81) (h : Conditions q) : valuation q 275 = false ∨ valuation q 281 = true := counterClause365 (baseVal q)

theorem counterClause366 (q : Nat → Bool) : valuationOf q 145 = false ∨ valuationOf q 283 = true := by
  have hs : count283 q = (countLit q [145]) + (countLit q [146]) := List.countP_append (p := literal q) (l₁ := [145]) (l₂ := [146])
  have hm := merge_left (literal (valuationOf q) (145)) (literal (valuationOf q) (283)) (countLit q [145]) (countLit q [146]) (count283 q) 1 (meaning145 q) (meaning283 q) hs
  change valuationOf q 145 = false ∨ valuationOf q 283 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause366 (q : Snake 81) (h : Conditions q) : valuation q 145 = false ∨ valuation q 283 = true := counterClause366 (baseVal q)

theorem counterClause367 (q : Nat → Bool) : valuationOf q 283 = false ∨ valuationOf q 285 = true := by
  have hs : count285 q = (countLit q [144]) + (countLit q [145, 146]) := List.countP_append (p := literal q) (l₁ := [144]) (l₂ := [145, 146])
  have hm := merge_right (literal (valuationOf q) (283)) (literal (valuationOf q) (285)) (countLit q [144]) (countLit q [145, 146]) (count285 q) 1 (meaning283 q) (meaning285 q) hs
  change valuationOf q 283 = false ∨ valuationOf q 285 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause367 (q : Snake 81) (h : Conditions q) : valuation q 283 = false ∨ valuation q 285 = true := counterClause367 (baseVal q)

theorem counterClause368 (q : Nat → Bool) : valuationOf q 148 = false ∨ valuationOf q 287 = true := by
  have hs : count287 q = (countLit q [147]) + (countLit q [148]) := List.countP_append (p := literal q) (l₁ := [147]) (l₂ := [148])
  have hm := merge_right (literal (valuationOf q) (148)) (literal (valuationOf q) (287)) (countLit q [147]) (countLit q [148]) (count287 q) 1 (meaning148 q) (meaning287 q) hs
  change valuationOf q 148 = false ∨ valuationOf q 287 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause368 (q : Snake 81) (h : Conditions q) : valuation q 148 = false ∨ valuation q 287 = true := counterClause368 (baseVal q)

theorem counterClause369 (q : Nat → Bool) : valuationOf q 150 = false ∨ valuationOf q 289 = true := by
  have hs : count289 q = (countLit q [149]) + (countLit q [150]) := List.countP_append (p := literal q) (l₁ := [149]) (l₂ := [150])
  have hm := merge_right (literal (valuationOf q) (150)) (literal (valuationOf q) (289)) (countLit q [149]) (countLit q [150]) (count289 q) 1 (meaning150 q) (meaning289 q) hs
  change valuationOf q 150 = false ∨ valuationOf q 289 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause369 (q : Snake 81) (h : Conditions q) : valuation q 150 = false ∨ valuation q 289 = true := counterClause369 (baseVal q)

theorem counterClause370 (q : Nat → Bool) : valuationOf q 289 = false ∨ valuationOf q 291 = true := by
  have hs : count291 q = (countLit q [147, 148]) + (countLit q [149, 150]) := List.countP_append (p := literal q) (l₁ := [147, 148]) (l₂ := [149, 150])
  have hm := merge_right (literal (valuationOf q) (289)) (literal (valuationOf q) (291)) (countLit q [147, 148]) (countLit q [149, 150]) (count291 q) 1 (meaning289 q) (meaning291 q) hs
  change valuationOf q 289 = false ∨ valuationOf q 291 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause370 (q : Snake 81) (h : Conditions q) : valuation q 289 = false ∨ valuation q 291 = true := counterClause370 (baseVal q)

theorem counterClause371 (q : Nat → Bool) : valuationOf q 287 = false ∨ valuationOf q 291 = true := by
  have hs : count291 q = (countLit q [147, 148]) + (countLit q [149, 150]) := List.countP_append (p := literal q) (l₁ := [147, 148]) (l₂ := [149, 150])
  have hm := merge_left (literal (valuationOf q) (287)) (literal (valuationOf q) (291)) (countLit q [147, 148]) (countLit q [149, 150]) (count291 q) 1 (meaning287 q) (meaning291 q) hs
  change valuationOf q 287 = false ∨ valuationOf q 291 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause371 (q : Snake 81) (h : Conditions q) : valuation q 287 = false ∨ valuation q 291 = true := counterClause371 (baseVal q)

theorem counterClause372 (q : Nat → Bool) : valuationOf q 291 = false ∨ valuationOf q 293 = true := by
  have hs : count293 q = (countLit q [144, 145, 146]) + (countLit q [147, 148, 149, 150]) := List.countP_append (p := literal q) (l₁ := [144, 145, 146]) (l₂ := [147, 148, 149, 150])
  have hm := merge_right (literal (valuationOf q) (291)) (literal (valuationOf q) (293)) (countLit q [144, 145, 146]) (countLit q [147, 148, 149, 150]) (count293 q) 1 (meaning291 q) (meaning293 q) hs
  change valuationOf q 291 = false ∨ valuationOf q 293 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause372 (q : Snake 81) (h : Conditions q) : valuation q 291 = false ∨ valuation q 293 = true := counterClause372 (baseVal q)

theorem counterClause373 (q : Nat → Bool) : valuationOf q 285 = false ∨ valuationOf q 293 = true := by
  have hs : count293 q = (countLit q [144, 145, 146]) + (countLit q [147, 148, 149, 150]) := List.countP_append (p := literal q) (l₁ := [144, 145, 146]) (l₂ := [147, 148, 149, 150])
  have hm := merge_left (literal (valuationOf q) (285)) (literal (valuationOf q) (293)) (countLit q [144, 145, 146]) (countLit q [147, 148, 149, 150]) (count293 q) 1 (meaning285 q) (meaning293 q) hs
  change valuationOf q 285 = false ∨ valuationOf q 293 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause373 (q : Snake 81) (h : Conditions q) : valuation q 285 = false ∨ valuation q 293 = true := counterClause373 (baseVal q)

theorem counterClause374 (q : Nat → Bool) : valuationOf q 293 = false ∨ valuationOf q 295 = true := by
  have hs : count295 q = (countLit q [138, 139, 140, 141, 142, 143]) + (countLit q [144, 145, 146, 147, 148, 149, 150]) := List.countP_append (p := literal q) (l₁ := [138, 139, 140, 141, 142, 143]) (l₂ := [144, 145, 146, 147, 148, 149, 150])
  have hm := merge_right (literal (valuationOf q) (293)) (literal (valuationOf q) (295)) (countLit q [138, 139, 140, 141, 142, 143]) (countLit q [144, 145, 146, 147, 148, 149, 150]) (count295 q) 1 (meaning293 q) (meaning295 q) hs
  change valuationOf q 293 = false ∨ valuationOf q 295 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause374 (q : Snake 81) (h : Conditions q) : valuation q 293 = false ∨ valuation q 295 = true := counterClause374 (baseVal q)

theorem counterClause375 (q : Nat → Bool) : valuationOf q 281 = false ∨ valuationOf q 295 = true := by
  have hs : count295 q = (countLit q [138, 139, 140, 141, 142, 143]) + (countLit q [144, 145, 146, 147, 148, 149, 150]) := List.countP_append (p := literal q) (l₁ := [138, 139, 140, 141, 142, 143]) (l₂ := [144, 145, 146, 147, 148, 149, 150])
  have hm := merge_left (literal (valuationOf q) (281)) (literal (valuationOf q) (295)) (countLit q [138, 139, 140, 141, 142, 143]) (countLit q [144, 145, 146, 147, 148, 149, 150]) (count295 q) 1 (meaning281 q) (meaning295 q) hs
  change valuationOf q 281 = false ∨ valuationOf q 295 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause375 (q : Snake 81) (h : Conditions q) : valuation q 281 = false ∨ valuation q 295 = true := counterClause375 (baseVal q)

theorem counterClause376 (q : Nat → Bool) : valuationOf q 281 = false ∨ valuationOf q 293 = false ∨ valuationOf q 296 = true := by
  have hs : count295 q = (countLit q [138, 139, 140, 141, 142, 143]) + (countLit q [144, 145, 146, 147, 148, 149, 150]) := List.countP_append (p := literal q) (l₁ := [138, 139, 140, 141, 142, 143]) (l₂ := [144, 145, 146, 147, 148, 149, 150])
  have hm := merge_two (literal (valuationOf q) (281)) (literal (valuationOf q) (293)) (literal (valuationOf q) (296)) (countLit q [138, 139, 140, 141, 142, 143]) (countLit q [144, 145, 146, 147, 148, 149, 150]) (count295 q) 1 1 (meaning281 q) (meaning293 q) (meaning296 q) hs
  change valuationOf q 281 = false ∨ valuationOf q 293 = false ∨ valuationOf q 296 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause376 (q : Snake 81) (h : Conditions q) : valuation q 281 = false ∨ valuation q 293 = false ∨ valuation q 296 = true := counterClause376 (baseVal q)

theorem counterClause377 (q : Nat → Bool) : valuationOf q 282 = false ∨ valuationOf q 296 = true := by
  have hs : count295 q = (countLit q [138, 139, 140, 141, 142, 143]) + (countLit q [144, 145, 146, 147, 148, 149, 150]) := List.countP_append (p := literal q) (l₁ := [138, 139, 140, 141, 142, 143]) (l₂ := [144, 145, 146, 147, 148, 149, 150])
  have hm := merge_left (literal (valuationOf q) (282)) (literal (valuationOf q) (296)) (countLit q [138, 139, 140, 141, 142, 143]) (countLit q [144, 145, 146, 147, 148, 149, 150]) (count295 q) 2 (meaning282 q) (meaning296 q) hs
  change valuationOf q 282 = false ∨ valuationOf q 296 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause377 (q : Snake 81) (h : Conditions q) : valuation q 282 = false ∨ valuation q 296 = true := counterClause377 (baseVal q)

theorem counterClause378 (q : Nat → Bool) : valuationOf q 151 = false ∨ valuationOf q 299 = true := by
  have hs : count299 q = (countLit q [151]) + (countLit q [152, 153]) := List.countP_append (p := literal q) (l₁ := [151]) (l₂ := [152, 153])
  have hm := merge_left (literal (valuationOf q) (151)) (literal (valuationOf q) (299)) (countLit q [151]) (countLit q [152, 153]) (count299 q) 1 (meaning151 q) (meaning299 q) hs
  change valuationOf q 151 = false ∨ valuationOf q 299 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause378 (q : Snake 81) (h : Conditions q) : valuation q 151 = false ∨ valuation q 299 = true := counterClause378 (baseVal q)

theorem counterClause379 (q : Nat → Bool) : valuationOf q 157 = false ∨ valuationOf q 303 = true := by
  have hs : count303 q = (countLit q [156]) + (countLit q [157]) := List.countP_append (p := literal q) (l₁ := [156]) (l₂ := [157])
  have hm := merge_right (literal (valuationOf q) (157)) (literal (valuationOf q) (303)) (countLit q [156]) (countLit q [157]) (count303 q) 1 (meaning157 q) (meaning303 q) hs
  change valuationOf q 157 = false ∨ valuationOf q 303 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause379 (q : Snake 81) (h : Conditions q) : valuation q 157 = false ∨ valuation q 303 = true := counterClause379 (baseVal q)

theorem counterClause380 (q : Nat → Bool) : valuationOf q 156 = false ∨ valuationOf q 303 = true := by
  have hs : count303 q = (countLit q [156]) + (countLit q [157]) := List.countP_append (p := literal q) (l₁ := [156]) (l₂ := [157])
  have hm := merge_left (literal (valuationOf q) (156)) (literal (valuationOf q) (303)) (countLit q [156]) (countLit q [157]) (count303 q) 1 (meaning156 q) (meaning303 q) hs
  change valuationOf q 156 = false ∨ valuationOf q 303 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause380 (q : Snake 81) (h : Conditions q) : valuation q 156 = false ∨ valuation q 303 = true := counterClause380 (baseVal q)

theorem counterClause381 (q : Nat → Bool) : valuationOf q 303 = false ∨ valuationOf q 305 = true := by
  have hs : count305 q = (countLit q [154, 155]) + (countLit q [156, 157]) := List.countP_append (p := literal q) (l₁ := [154, 155]) (l₂ := [156, 157])
  have hm := merge_right (literal (valuationOf q) (303)) (literal (valuationOf q) (305)) (countLit q [154, 155]) (countLit q [156, 157]) (count305 q) 1 (meaning303 q) (meaning305 q) hs
  change valuationOf q 303 = false ∨ valuationOf q 305 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause381 (q : Snake 81) (h : Conditions q) : valuation q 303 = false ∨ valuation q 305 = true := counterClause381 (baseVal q)

theorem counterClause382 (q : Nat → Bool) : valuationOf q 305 = false ∨ valuationOf q 307 = true := by
  have hs : count307 q = (countLit q [151, 152, 153]) + (countLit q [154, 155, 156, 157]) := List.countP_append (p := literal q) (l₁ := [151, 152, 153]) (l₂ := [154, 155, 156, 157])
  have hm := merge_right (literal (valuationOf q) (305)) (literal (valuationOf q) (307)) (countLit q [151, 152, 153]) (countLit q [154, 155, 156, 157]) (count307 q) 1 (meaning305 q) (meaning307 q) hs
  change valuationOf q 305 = false ∨ valuationOf q 307 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause382 (q : Snake 81) (h : Conditions q) : valuation q 305 = false ∨ valuation q 307 = true := counterClause382 (baseVal q)

theorem counterClause383 (q : Nat → Bool) : valuationOf q 299 = false ∨ valuationOf q 307 = true := by
  have hs : count307 q = (countLit q [151, 152, 153]) + (countLit q [154, 155, 156, 157]) := List.countP_append (p := literal q) (l₁ := [151, 152, 153]) (l₂ := [154, 155, 156, 157])
  have hm := merge_left (literal (valuationOf q) (299)) (literal (valuationOf q) (307)) (countLit q [151, 152, 153]) (countLit q [154, 155, 156, 157]) (count307 q) 1 (meaning299 q) (meaning307 q) hs
  change valuationOf q 299 = false ∨ valuationOf q 307 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause383 (q : Snake 81) (h : Conditions q) : valuation q 299 = false ∨ valuation q 307 = true := counterClause383 (baseVal q)

theorem counterClause384 (q : Nat → Bool) : valuationOf q 299 = false ∨ valuationOf q 305 = false ∨ valuationOf q 308 = true := by
  have hs : count307 q = (countLit q [151, 152, 153]) + (countLit q [154, 155, 156, 157]) := List.countP_append (p := literal q) (l₁ := [151, 152, 153]) (l₂ := [154, 155, 156, 157])
  have hm := merge_two (literal (valuationOf q) (299)) (literal (valuationOf q) (305)) (literal (valuationOf q) (308)) (countLit q [151, 152, 153]) (countLit q [154, 155, 156, 157]) (count307 q) 1 1 (meaning299 q) (meaning305 q) (meaning308 q) hs
  change valuationOf q 299 = false ∨ valuationOf q 305 = false ∨ valuationOf q 308 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause384 (q : Snake 81) (h : Conditions q) : valuation q 299 = false ∨ valuation q 305 = false ∨ valuation q 308 = true := counterClause384 (baseVal q)

theorem block11 (q : Snake 81) (h : Conditions q) : B112E183.Block11 (valuation q) :=
  ⟨clause353 q h, clause354 q h, clause355 q h, clause356 q h, clause357 q h, clause358 q h, clause359 q h, clause360 q h, clause361 q h, clause362 q h, clause363 q h, clause364 q h, clause365 q h, clause366 q h, clause367 q h, clause368 q h, clause369 q h, clause370 q h, clause371 q h, clause372 q h, clause373 q h, clause374 q h, clause375 q h, clause376 q h, clause377 q h, clause378 q h, clause379 q h, clause380 q h, clause381 q h, clause382 q h, clause383 q h, clause384 q h⟩

end
end Snake9.Regrowth.E112183
