import E112161Semantics
import B112E161Inputs
namespace Snake9.Regrowth.E112161
noncomputable section
local instance blockDec16 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause513 (q : Nat → Bool) : valuationOf q 135 = false ∨ valuationOf q 259 = true := by
  have hs : count259 q = (countLit q [134]) + (countLit q [135]) := List.countP_append (p := literal q) (l₁ := [134]) (l₂ := [135])
  have hm := merge_right (literal (valuationOf q) (135)) (literal (valuationOf q) (259)) (countLit q [134]) (countLit q [135]) (count259 q) 1 (meaning135 q) (meaning259 q) hs
  change valuationOf q 135 = false ∨ valuationOf q 259 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause513 (q : Snake 81) (h : Conditions q) : valuation q 135 = false ∨ valuation q 259 = true := counterClause513 (baseVal q)

theorem counterClause514 (q : Nat → Bool) : valuationOf q 259 = false ∨ valuationOf q 261 = true := by
  have hs : count261 q = (countLit q [133]) + (countLit q [134, 135]) := List.countP_append (p := literal q) (l₁ := [133]) (l₂ := [134, 135])
  have hm := merge_right (literal (valuationOf q) (259)) (literal (valuationOf q) (261)) (countLit q [133]) (countLit q [134, 135]) (count261 q) 1 (meaning259 q) (meaning261 q) hs
  change valuationOf q 259 = false ∨ valuationOf q 261 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause514 (q : Snake 81) (h : Conditions q) : valuation q 259 = false ∨ valuation q 261 = true := counterClause514 (baseVal q)

theorem counterClause515 (q : Nat → Bool) : valuationOf q 133 = false ∨ valuationOf q 261 = true := by
  have hs : count261 q = (countLit q [133]) + (countLit q [134, 135]) := List.countP_append (p := literal q) (l₁ := [133]) (l₂ := [134, 135])
  have hm := merge_left (literal (valuationOf q) (133)) (literal (valuationOf q) (261)) (countLit q [133]) (countLit q [134, 135]) (count261 q) 1 (meaning133 q) (meaning261 q) hs
  change valuationOf q 133 = false ∨ valuationOf q 261 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause515 (q : Snake 81) (h : Conditions q) : valuation q 133 = false ∨ valuation q 261 = true := counterClause515 (baseVal q)

theorem counterClause516 (q : Nat → Bool) : valuationOf q 136 = false ∨ valuationOf q 263 = true := by
  have hs : count263 q = (countLit q [136]) + (countLit q [137]) := List.countP_append (p := literal q) (l₁ := [136]) (l₂ := [137])
  have hm := merge_left (literal (valuationOf q) (136)) (literal (valuationOf q) (263)) (countLit q [136]) (countLit q [137]) (count263 q) 1 (meaning136 q) (meaning263 q) hs
  change valuationOf q 136 = false ∨ valuationOf q 263 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause516 (q : Snake 81) (h : Conditions q) : valuation q 136 = false ∨ valuation q 263 = true := counterClause516 (baseVal q)

theorem counterClause517 (q : Nat → Bool) : valuationOf q 263 = false ∨ valuationOf q 267 = true := by
  have hs : count267 q = (countLit q [136, 137]) + (countLit q [138, 139]) := List.countP_append (p := literal q) (l₁ := [136, 137]) (l₂ := [138, 139])
  have hm := merge_left (literal (valuationOf q) (263)) (literal (valuationOf q) (267)) (countLit q [136, 137]) (countLit q [138, 139]) (count267 q) 1 (meaning263 q) (meaning267 q) hs
  change valuationOf q 263 = false ∨ valuationOf q 267 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause517 (q : Snake 81) (h : Conditions q) : valuation q 263 = false ∨ valuation q 267 = true := counterClause517 (baseVal q)

theorem counterClause518 (q : Nat → Bool) : valuationOf q 267 = false ∨ valuationOf q 269 = true := by
  have hs : count269 q = (countLit q [133, 134, 135]) + (countLit q [136, 137, 138, 139]) := List.countP_append (p := literal q) (l₁ := [133, 134, 135]) (l₂ := [136, 137, 138, 139])
  have hm := merge_right (literal (valuationOf q) (267)) (literal (valuationOf q) (269)) (countLit q [133, 134, 135]) (countLit q [136, 137, 138, 139]) (count269 q) 1 (meaning267 q) (meaning269 q) hs
  change valuationOf q 267 = false ∨ valuationOf q 269 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause518 (q : Snake 81) (h : Conditions q) : valuation q 267 = false ∨ valuation q 269 = true := counterClause518 (baseVal q)

theorem counterClause519 (q : Nat → Bool) : valuationOf q 261 = false ∨ valuationOf q 269 = true := by
  have hs : count269 q = (countLit q [133, 134, 135]) + (countLit q [136, 137, 138, 139]) := List.countP_append (p := literal q) (l₁ := [133, 134, 135]) (l₂ := [136, 137, 138, 139])
  have hm := merge_left (literal (valuationOf q) (261)) (literal (valuationOf q) (269)) (countLit q [133, 134, 135]) (countLit q [136, 137, 138, 139]) (count269 q) 1 (meaning261 q) (meaning269 q) hs
  change valuationOf q 261 = false ∨ valuationOf q 269 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause519 (q : Snake 81) (h : Conditions q) : valuation q 261 = false ∨ valuation q 269 = true := counterClause519 (baseVal q)

theorem counterClause520 (q : Nat → Bool) : valuationOf q 261 = false ∨ valuationOf q 267 = false ∨ valuationOf q 270 = true := by
  have hs : count269 q = (countLit q [133, 134, 135]) + (countLit q [136, 137, 138, 139]) := List.countP_append (p := literal q) (l₁ := [133, 134, 135]) (l₂ := [136, 137, 138, 139])
  have hm := merge_two (literal (valuationOf q) (261)) (literal (valuationOf q) (267)) (literal (valuationOf q) (270)) (countLit q [133, 134, 135]) (countLit q [136, 137, 138, 139]) (count269 q) 1 1 (meaning261 q) (meaning267 q) (meaning270 q) hs
  change valuationOf q 261 = false ∨ valuationOf q 267 = false ∨ valuationOf q 270 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause520 (q : Snake 81) (h : Conditions q) : valuation q 261 = false ∨ valuation q 267 = false ∨ valuation q 270 = true := counterClause520 (baseVal q)

theorem counterClause521 (q : Nat → Bool) : valuationOf q 269 = false ∨ valuationOf q 271 = true := by
  have hs : count271 q = (countLit q [126, 127, 128, 129, 130, 131, 132]) + (countLit q [133, 134, 135, 136, 137, 138, 139]) := List.countP_append (p := literal q) (l₁ := [126, 127, 128, 129, 130, 131, 132]) (l₂ := [133, 134, 135, 136, 137, 138, 139])
  have hm := merge_right (literal (valuationOf q) (269)) (literal (valuationOf q) (271)) (countLit q [126, 127, 128, 129, 130, 131, 132]) (countLit q [133, 134, 135, 136, 137, 138, 139]) (count271 q) 1 (meaning269 q) (meaning271 q) hs
  change valuationOf q 269 = false ∨ valuationOf q 271 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause521 (q : Snake 81) (h : Conditions q) : valuation q 269 = false ∨ valuation q 271 = true := counterClause521 (baseVal q)

theorem counterClause522 (q : Nat → Bool) : valuationOf q 270 = false ∨ valuationOf q 272 = true := by
  have hs : count271 q = (countLit q [126, 127, 128, 129, 130, 131, 132]) + (countLit q [133, 134, 135, 136, 137, 138, 139]) := List.countP_append (p := literal q) (l₁ := [126, 127, 128, 129, 130, 131, 132]) (l₂ := [133, 134, 135, 136, 137, 138, 139])
  have hm := merge_right (literal (valuationOf q) (270)) (literal (valuationOf q) (272)) (countLit q [126, 127, 128, 129, 130, 131, 132]) (countLit q [133, 134, 135, 136, 137, 138, 139]) (count271 q) 2 (meaning270 q) (meaning272 q) hs
  change valuationOf q 270 = false ∨ valuationOf q 272 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause522 (q : Snake 81) (h : Conditions q) : valuation q 270 = false ∨ valuation q 272 = true := counterClause522 (baseVal q)

theorem counterClause523 (q : Nat → Bool) : valuationOf q 257 = false ∨ valuationOf q 271 = true := by
  have hs : count271 q = (countLit q [126, 127, 128, 129, 130, 131, 132]) + (countLit q [133, 134, 135, 136, 137, 138, 139]) := List.countP_append (p := literal q) (l₁ := [126, 127, 128, 129, 130, 131, 132]) (l₂ := [133, 134, 135, 136, 137, 138, 139])
  have hm := merge_left (literal (valuationOf q) (257)) (literal (valuationOf q) (271)) (countLit q [126, 127, 128, 129, 130, 131, 132]) (countLit q [133, 134, 135, 136, 137, 138, 139]) (count271 q) 1 (meaning257 q) (meaning271 q) hs
  change valuationOf q 257 = false ∨ valuationOf q 271 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause523 (q : Snake 81) (h : Conditions q) : valuation q 257 = false ∨ valuation q 271 = true := counterClause523 (baseVal q)

theorem counterClause524 (q : Nat → Bool) : valuationOf q 257 = false ∨ valuationOf q 269 = false ∨ valuationOf q 272 = true := by
  have hs : count271 q = (countLit q [126, 127, 128, 129, 130, 131, 132]) + (countLit q [133, 134, 135, 136, 137, 138, 139]) := List.countP_append (p := literal q) (l₁ := [126, 127, 128, 129, 130, 131, 132]) (l₂ := [133, 134, 135, 136, 137, 138, 139])
  have hm := merge_two (literal (valuationOf q) (257)) (literal (valuationOf q) (269)) (literal (valuationOf q) (272)) (countLit q [126, 127, 128, 129, 130, 131, 132]) (countLit q [133, 134, 135, 136, 137, 138, 139]) (count271 q) 1 1 (meaning257 q) (meaning269 q) (meaning272 q) hs
  change valuationOf q 257 = false ∨ valuationOf q 269 = false ∨ valuationOf q 272 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause524 (q : Snake 81) (h : Conditions q) : valuation q 257 = false ∨ valuation q 269 = false ∨ valuation q 272 = true := counterClause524 (baseVal q)

theorem counterClause525 (q : Nat → Bool) : valuationOf q 258 = false ∨ valuationOf q 272 = true := by
  have hs : count271 q = (countLit q [126, 127, 128, 129, 130, 131, 132]) + (countLit q [133, 134, 135, 136, 137, 138, 139]) := List.countP_append (p := literal q) (l₁ := [126, 127, 128, 129, 130, 131, 132]) (l₂ := [133, 134, 135, 136, 137, 138, 139])
  have hm := merge_left (literal (valuationOf q) (258)) (literal (valuationOf q) (272)) (countLit q [126, 127, 128, 129, 130, 131, 132]) (countLit q [133, 134, 135, 136, 137, 138, 139]) (count271 q) 2 (meaning258 q) (meaning272 q) hs
  change valuationOf q 258 = false ∨ valuationOf q 272 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause525 (q : Snake 81) (h : Conditions q) : valuation q 258 = false ∨ valuation q 272 = true := counterClause525 (baseVal q)

theorem counterClause526 (q : Nat → Bool) : valuationOf q 271 = false ∨ valuationOf q 273 = true := by
  have hs : count273 q = (countLit q [112, 113, 114, 115, 116, 117, 119, 120, 121, 122, 123, 124, 125]) + (countLit q [126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139]) := List.countP_append (p := literal q) (l₁ := [112, 113, 114, 115, 116, 117, 119, 120, 121, 122, 123, 124, 125]) (l₂ := [126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139])
  have hm := merge_right (literal (valuationOf q) (271)) (literal (valuationOf q) (273)) (countLit q [112, 113, 114, 115, 116, 117, 119, 120, 121, 122, 123, 124, 125]) (countLit q [126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139]) (count273 q) 1 (meaning271 q) (meaning273 q) hs
  change valuationOf q 271 = false ∨ valuationOf q 273 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause526 (q : Snake 81) (h : Conditions q) : valuation q 271 = false ∨ valuation q 273 = true := counterClause526 (baseVal q)

theorem counterClause527 (q : Nat → Bool) : valuationOf q 272 = false ∨ valuationOf q 274 = true := by
  have hs : count273 q = (countLit q [112, 113, 114, 115, 116, 117, 119, 120, 121, 122, 123, 124, 125]) + (countLit q [126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139]) := List.countP_append (p := literal q) (l₁ := [112, 113, 114, 115, 116, 117, 119, 120, 121, 122, 123, 124, 125]) (l₂ := [126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139])
  have hm := merge_right (literal (valuationOf q) (272)) (literal (valuationOf q) (274)) (countLit q [112, 113, 114, 115, 116, 117, 119, 120, 121, 122, 123, 124, 125]) (countLit q [126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139]) (count273 q) 2 (meaning272 q) (meaning274 q) hs
  change valuationOf q 272 = false ∨ valuationOf q 274 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause527 (q : Snake 81) (h : Conditions q) : valuation q 272 = false ∨ valuation q 274 = true := counterClause527 (baseVal q)

theorem counterClause528 (q : Nat → Bool) : valuationOf q 245 = false ∨ valuationOf q 273 = true := by
  have hs : count273 q = (countLit q [112, 113, 114, 115, 116, 117, 119, 120, 121, 122, 123, 124, 125]) + (countLit q [126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139]) := List.countP_append (p := literal q) (l₁ := [112, 113, 114, 115, 116, 117, 119, 120, 121, 122, 123, 124, 125]) (l₂ := [126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139])
  have hm := merge_left (literal (valuationOf q) (245)) (literal (valuationOf q) (273)) (countLit q [112, 113, 114, 115, 116, 117, 119, 120, 121, 122, 123, 124, 125]) (countLit q [126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139]) (count273 q) 1 (meaning245 q) (meaning273 q) hs
  change valuationOf q 245 = false ∨ valuationOf q 273 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause528 (q : Snake 81) (h : Conditions q) : valuation q 245 = false ∨ valuation q 273 = true := counterClause528 (baseVal q)

theorem counterClause529 (q : Nat → Bool) : valuationOf q 245 = false ∨ valuationOf q 271 = false ∨ valuationOf q 274 = true := by
  have hs : count273 q = (countLit q [112, 113, 114, 115, 116, 117, 119, 120, 121, 122, 123, 124, 125]) + (countLit q [126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139]) := List.countP_append (p := literal q) (l₁ := [112, 113, 114, 115, 116, 117, 119, 120, 121, 122, 123, 124, 125]) (l₂ := [126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139])
  have hm := merge_two (literal (valuationOf q) (245)) (literal (valuationOf q) (271)) (literal (valuationOf q) (274)) (countLit q [112, 113, 114, 115, 116, 117, 119, 120, 121, 122, 123, 124, 125]) (countLit q [126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139]) (count273 q) 1 1 (meaning245 q) (meaning271 q) (meaning274 q) hs
  change valuationOf q 245 = false ∨ valuationOf q 271 = false ∨ valuationOf q 274 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause529 (q : Snake 81) (h : Conditions q) : valuation q 245 = false ∨ valuation q 271 = false ∨ valuation q 274 = true := counterClause529 (baseVal q)

theorem counterClause530 (q : Nat → Bool) : valuationOf q 246 = false ∨ valuationOf q 274 = true := by
  have hs : count273 q = (countLit q [112, 113, 114, 115, 116, 117, 119, 120, 121, 122, 123, 124, 125]) + (countLit q [126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139]) := List.countP_append (p := literal q) (l₁ := [112, 113, 114, 115, 116, 117, 119, 120, 121, 122, 123, 124, 125]) (l₂ := [126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139])
  have hm := merge_left (literal (valuationOf q) (246)) (literal (valuationOf q) (274)) (countLit q [112, 113, 114, 115, 116, 117, 119, 120, 121, 122, 123, 124, 125]) (countLit q [126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139]) (count273 q) 2 (meaning246 q) (meaning274 q) hs
  change valuationOf q 246 = false ∨ valuationOf q 274 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause530 (q : Snake 81) (h : Conditions q) : valuation q 246 = false ∨ valuation q 274 = true := counterClause530 (baseVal q)

theorem counterClause531 (q : Nat → Bool) : valuationOf q 141 = false ∨ valuationOf q 275 = true := by
  have hs : count275 q = (countLit q [141]) + (countLit q [142]) := List.countP_append (p := literal q) (l₁ := [141]) (l₂ := [142])
  have hm := merge_left (literal (valuationOf q) (141)) (literal (valuationOf q) (275)) (countLit q [141]) (countLit q [142]) (count275 q) 1 (meaning141 q) (meaning275 q) hs
  change valuationOf q 141 = false ∨ valuationOf q 275 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause531 (q : Snake 81) (h : Conditions q) : valuation q 141 = false ∨ valuation q 275 = true := counterClause531 (baseVal q)

theorem counterClause532 (q : Nat → Bool) : valuationOf q 275 = false ∨ valuationOf q 277 = true := by
  have hs : count277 q = (countLit q [140]) + (countLit q [141, 142]) := List.countP_append (p := literal q) (l₁ := [140]) (l₂ := [141, 142])
  have hm := merge_right (literal (valuationOf q) (275)) (literal (valuationOf q) (277)) (countLit q [140]) (countLit q [141, 142]) (count277 q) 1 (meaning275 q) (meaning277 q) hs
  change valuationOf q 275 = false ∨ valuationOf q 277 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause532 (q : Snake 81) (h : Conditions q) : valuation q 275 = false ∨ valuation q 277 = true := counterClause532 (baseVal q)

theorem counterClause533 (q : Nat → Bool) : valuationOf q 140 = false ∨ valuationOf q 277 = true := by
  have hs : count277 q = (countLit q [140]) + (countLit q [141, 142]) := List.countP_append (p := literal q) (l₁ := [140]) (l₂ := [141, 142])
  have hm := merge_left (literal (valuationOf q) (140)) (literal (valuationOf q) (277)) (countLit q [140]) (countLit q [141, 142]) (count277 q) 1 (meaning140 q) (meaning277 q) hs
  change valuationOf q 140 = false ∨ valuationOf q 277 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause533 (q : Snake 81) (h : Conditions q) : valuation q 140 = false ∨ valuation q 277 = true := counterClause533 (baseVal q)

theorem counterClause534 (q : Nat → Bool) : valuationOf q 140 = false ∨ valuationOf q 275 = false ∨ valuationOf q 278 = true := by
  have hs : count277 q = (countLit q [140]) + (countLit q [141, 142]) := List.countP_append (p := literal q) (l₁ := [140]) (l₂ := [141, 142])
  have hm := merge_two (literal (valuationOf q) (140)) (literal (valuationOf q) (275)) (literal (valuationOf q) (278)) (countLit q [140]) (countLit q [141, 142]) (count277 q) 1 1 (meaning140 q) (meaning275 q) (meaning278 q) hs
  change valuationOf q 140 = false ∨ valuationOf q 275 = false ∨ valuationOf q 278 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause534 (q : Snake 81) (h : Conditions q) : valuation q 140 = false ∨ valuation q 275 = false ∨ valuation q 278 = true := counterClause534 (baseVal q)

theorem counterClause535 (q : Nat → Bool) : valuationOf q 144 = false ∨ valuationOf q 279 = true := by
  have hs : count279 q = (countLit q [143]) + (countLit q [144]) := List.countP_append (p := literal q) (l₁ := [143]) (l₂ := [144])
  have hm := merge_right (literal (valuationOf q) (144)) (literal (valuationOf q) (279)) (countLit q [143]) (countLit q [144]) (count279 q) 1 (meaning144 q) (meaning279 q) hs
  change valuationOf q 144 = false ∨ valuationOf q 279 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause535 (q : Snake 81) (h : Conditions q) : valuation q 144 = false ∨ valuation q 279 = true := counterClause535 (baseVal q)

theorem counterClause536 (q : Nat → Bool) : valuationOf q 143 = false ∨ valuationOf q 279 = true := by
  have hs : count279 q = (countLit q [143]) + (countLit q [144]) := List.countP_append (p := literal q) (l₁ := [143]) (l₂ := [144])
  have hm := merge_left (literal (valuationOf q) (143)) (literal (valuationOf q) (279)) (countLit q [143]) (countLit q [144]) (count279 q) 1 (meaning143 q) (meaning279 q) hs
  change valuationOf q 143 = false ∨ valuationOf q 279 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause536 (q : Snake 81) (h : Conditions q) : valuation q 143 = false ∨ valuation q 279 = true := counterClause536 (baseVal q)

theorem counterClause537 (q : Nat → Bool) : valuationOf q 143 = false ∨ valuationOf q 144 = false ∨ valuationOf q 280 = true := by
  have hs : count279 q = (countLit q [143]) + (countLit q [144]) := List.countP_append (p := literal q) (l₁ := [143]) (l₂ := [144])
  have hm := merge_two (literal (valuationOf q) (143)) (literal (valuationOf q) (144)) (literal (valuationOf q) (280)) (countLit q [143]) (countLit q [144]) (count279 q) 1 1 (meaning143 q) (meaning144 q) (meaning280 q) hs
  change valuationOf q 143 = false ∨ valuationOf q 144 = false ∨ valuationOf q 280 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause537 (q : Snake 81) (h : Conditions q) : valuation q 143 = false ∨ valuation q 144 = false ∨ valuation q 280 = true := counterClause537 (baseVal q)

theorem counterClause538 (q : Nat → Bool) : valuationOf q 146 = false ∨ valuationOf q 281 = true := by
  have hs : count281 q = (countLit q [145]) + (countLit q [146]) := List.countP_append (p := literal q) (l₁ := [145]) (l₂ := [146])
  have hm := merge_right (literal (valuationOf q) (146)) (literal (valuationOf q) (281)) (countLit q [145]) (countLit q [146]) (count281 q) 1 (meaning146 q) (meaning281 q) hs
  change valuationOf q 146 = false ∨ valuationOf q 281 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause538 (q : Snake 81) (h : Conditions q) : valuation q 146 = false ∨ valuation q 281 = true := counterClause538 (baseVal q)

theorem counterClause539 (q : Nat → Bool) : valuationOf q 281 = false ∨ valuationOf q 283 = true := by
  have hs : count283 q = (countLit q [143, 144]) + (countLit q [145, 146]) := List.countP_append (p := literal q) (l₁ := [143, 144]) (l₂ := [145, 146])
  have hm := merge_right (literal (valuationOf q) (281)) (literal (valuationOf q) (283)) (countLit q [143, 144]) (countLit q [145, 146]) (count283 q) 1 (meaning281 q) (meaning283 q) hs
  change valuationOf q 281 = false ∨ valuationOf q 283 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause539 (q : Snake 81) (h : Conditions q) : valuation q 281 = false ∨ valuation q 283 = true := counterClause539 (baseVal q)

theorem counterClause540 (q : Nat → Bool) : valuationOf q 279 = false ∨ valuationOf q 283 = true := by
  have hs : count283 q = (countLit q [143, 144]) + (countLit q [145, 146]) := List.countP_append (p := literal q) (l₁ := [143, 144]) (l₂ := [145, 146])
  have hm := merge_left (literal (valuationOf q) (279)) (literal (valuationOf q) (283)) (countLit q [143, 144]) (countLit q [145, 146]) (count283 q) 1 (meaning279 q) (meaning283 q) hs
  change valuationOf q 279 = false ∨ valuationOf q 283 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause540 (q : Snake 81) (h : Conditions q) : valuation q 279 = false ∨ valuation q 283 = true := counterClause540 (baseVal q)

theorem counterClause541 (q : Nat → Bool) : valuationOf q 280 = false ∨ valuationOf q 284 = true := by
  have hs : count283 q = (countLit q [143, 144]) + (countLit q [145, 146]) := List.countP_append (p := literal q) (l₁ := [143, 144]) (l₂ := [145, 146])
  have hm := merge_left (literal (valuationOf q) (280)) (literal (valuationOf q) (284)) (countLit q [143, 144]) (countLit q [145, 146]) (count283 q) 2 (meaning280 q) (meaning284 q) hs
  change valuationOf q 280 = false ∨ valuationOf q 284 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause541 (q : Snake 81) (h : Conditions q) : valuation q 280 = false ∨ valuation q 284 = true := counterClause541 (baseVal q)

theorem counterClause542 (q : Nat → Bool) : valuationOf q 283 = false ∨ valuationOf q 285 = true := by
  have hs : count285 q = (countLit q [140, 141, 142]) + (countLit q [143, 144, 145, 146]) := List.countP_append (p := literal q) (l₁ := [140, 141, 142]) (l₂ := [143, 144, 145, 146])
  have hm := merge_right (literal (valuationOf q) (283)) (literal (valuationOf q) (285)) (countLit q [140, 141, 142]) (countLit q [143, 144, 145, 146]) (count285 q) 1 (meaning283 q) (meaning285 q) hs
  change valuationOf q 283 = false ∨ valuationOf q 285 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause542 (q : Snake 81) (h : Conditions q) : valuation q 283 = false ∨ valuation q 285 = true := counterClause542 (baseVal q)

theorem counterClause543 (q : Nat → Bool) : valuationOf q 284 = false ∨ valuationOf q 286 = true := by
  have hs : count285 q = (countLit q [140, 141, 142]) + (countLit q [143, 144, 145, 146]) := List.countP_append (p := literal q) (l₁ := [140, 141, 142]) (l₂ := [143, 144, 145, 146])
  have hm := merge_right (literal (valuationOf q) (284)) (literal (valuationOf q) (286)) (countLit q [140, 141, 142]) (countLit q [143, 144, 145, 146]) (count285 q) 2 (meaning284 q) (meaning286 q) hs
  change valuationOf q 284 = false ∨ valuationOf q 286 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause543 (q : Snake 81) (h : Conditions q) : valuation q 284 = false ∨ valuation q 286 = true := counterClause543 (baseVal q)

theorem counterClause544 (q : Nat → Bool) : valuationOf q 277 = false ∨ valuationOf q 285 = true := by
  have hs : count285 q = (countLit q [140, 141, 142]) + (countLit q [143, 144, 145, 146]) := List.countP_append (p := literal q) (l₁ := [140, 141, 142]) (l₂ := [143, 144, 145, 146])
  have hm := merge_left (literal (valuationOf q) (277)) (literal (valuationOf q) (285)) (countLit q [140, 141, 142]) (countLit q [143, 144, 145, 146]) (count285 q) 1 (meaning277 q) (meaning285 q) hs
  change valuationOf q 277 = false ∨ valuationOf q 285 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause544 (q : Snake 81) (h : Conditions q) : valuation q 277 = false ∨ valuation q 285 = true := counterClause544 (baseVal q)

theorem block16 (q : Snake 81) (h : Conditions q) : B112E161.Block16 (valuation q) :=
  ⟨clause513 q h, clause514 q h, clause515 q h, clause516 q h, clause517 q h, clause518 q h, clause519 q h, clause520 q h, clause521 q h, clause522 q h, clause523 q h, clause524 q h, clause525 q h, clause526 q h, clause527 q h, clause528 q h, clause529 q h, clause530 q h, clause531 q h, clause532 q h, clause533 q h, clause534 q h, clause535 q h, clause536 q h, clause537 q h, clause538 q h, clause539 q h, clause540 q h, clause541 q h, clause542 q h, clause543 q h, clause544 q h⟩

end
end Snake9.Regrowth.E112161
