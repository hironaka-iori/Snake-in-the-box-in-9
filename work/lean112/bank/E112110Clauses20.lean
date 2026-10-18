import E112110Semantics
import B112E110Inputs
namespace Snake9.Regrowth.E112110
noncomputable section
local instance blockDec20 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause641 (q : Nat → Bool) : valuationOf q 263 = false ∨ valuationOf q 265 = true := by
  have hs : count265 q = (countLit q [133]) + (countLit q [134, 135]) := List.countP_append (p := literal q) (l₁ := [133]) (l₂ := [134, 135])
  have hm := merge_right (literal (valuationOf q) (263)) (literal (valuationOf q) (265)) (countLit q [133]) (countLit q [134, 135]) (count265 q) 1 (meaning263 q) (meaning265 q) hs
  change valuationOf q 263 = false ∨ valuationOf q 265 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause641 (q : Snake 81) (h : Conditions q) : valuation q 263 = false ∨ valuation q 265 = true := counterClause641 (baseVal q)

theorem counterClause642 (q : Nat → Bool) : valuationOf q 133 = false ∨ valuationOf q 265 = true := by
  have hs : count265 q = (countLit q [133]) + (countLit q [134, 135]) := List.countP_append (p := literal q) (l₁ := [133]) (l₂ := [134, 135])
  have hm := merge_left (literal (valuationOf q) (133)) (literal (valuationOf q) (265)) (countLit q [133]) (countLit q [134, 135]) (count265 q) 1 (meaning133 q) (meaning265 q) hs
  change valuationOf q 133 = false ∨ valuationOf q 265 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause642 (q : Snake 81) (h : Conditions q) : valuation q 133 = false ∨ valuation q 265 = true := counterClause642 (baseVal q)

theorem counterClause643 (q : Nat → Bool) : valuationOf q 136 = false ∨ valuationOf q 267 = true := by
  have hs : count267 q = (countLit q [136]) + (countLit q [137]) := List.countP_append (p := literal q) (l₁ := [136]) (l₂ := [137])
  have hm := merge_left (literal (valuationOf q) (136)) (literal (valuationOf q) (267)) (countLit q [136]) (countLit q [137]) (count267 q) 1 (meaning136 q) (meaning267 q) hs
  change valuationOf q 136 = false ∨ valuationOf q 267 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause643 (q : Snake 81) (h : Conditions q) : valuation q 136 = false ∨ valuation q 267 = true := counterClause643 (baseVal q)

theorem counterClause644 (q : Nat → Bool) : valuationOf q 267 = false ∨ valuationOf q 271 = true := by
  have hs : count271 q = (countLit q [136, 137]) + (countLit q [138, 139]) := List.countP_append (p := literal q) (l₁ := [136, 137]) (l₂ := [138, 139])
  have hm := merge_left (literal (valuationOf q) (267)) (literal (valuationOf q) (271)) (countLit q [136, 137]) (countLit q [138, 139]) (count271 q) 1 (meaning267 q) (meaning271 q) hs
  change valuationOf q 267 = false ∨ valuationOf q 271 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause644 (q : Snake 81) (h : Conditions q) : valuation q 267 = false ∨ valuation q 271 = true := counterClause644 (baseVal q)

theorem counterClause645 (q : Nat → Bool) : valuationOf q 271 = false ∨ valuationOf q 273 = true := by
  have hs : count273 q = (countLit q [133, 134, 135]) + (countLit q [136, 137, 138, 139]) := List.countP_append (p := literal q) (l₁ := [133, 134, 135]) (l₂ := [136, 137, 138, 139])
  have hm := merge_right (literal (valuationOf q) (271)) (literal (valuationOf q) (273)) (countLit q [133, 134, 135]) (countLit q [136, 137, 138, 139]) (count273 q) 1 (meaning271 q) (meaning273 q) hs
  change valuationOf q 271 = false ∨ valuationOf q 273 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause645 (q : Snake 81) (h : Conditions q) : valuation q 271 = false ∨ valuation q 273 = true := counterClause645 (baseVal q)

theorem counterClause646 (q : Nat → Bool) : valuationOf q 265 = false ∨ valuationOf q 273 = true := by
  have hs : count273 q = (countLit q [133, 134, 135]) + (countLit q [136, 137, 138, 139]) := List.countP_append (p := literal q) (l₁ := [133, 134, 135]) (l₂ := [136, 137, 138, 139])
  have hm := merge_left (literal (valuationOf q) (265)) (literal (valuationOf q) (273)) (countLit q [133, 134, 135]) (countLit q [136, 137, 138, 139]) (count273 q) 1 (meaning265 q) (meaning273 q) hs
  change valuationOf q 265 = false ∨ valuationOf q 273 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause646 (q : Snake 81) (h : Conditions q) : valuation q 265 = false ∨ valuation q 273 = true := counterClause646 (baseVal q)

theorem counterClause647 (q : Nat → Bool) : valuationOf q 265 = false ∨ valuationOf q 271 = false ∨ valuationOf q 274 = true := by
  have hs : count273 q = (countLit q [133, 134, 135]) + (countLit q [136, 137, 138, 139]) := List.countP_append (p := literal q) (l₁ := [133, 134, 135]) (l₂ := [136, 137, 138, 139])
  have hm := merge_two (literal (valuationOf q) (265)) (literal (valuationOf q) (271)) (literal (valuationOf q) (274)) (countLit q [133, 134, 135]) (countLit q [136, 137, 138, 139]) (count273 q) 1 1 (meaning265 q) (meaning271 q) (meaning274 q) hs
  change valuationOf q 265 = false ∨ valuationOf q 271 = false ∨ valuationOf q 274 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause647 (q : Snake 81) (h : Conditions q) : valuation q 265 = false ∨ valuation q 271 = false ∨ valuation q 274 = true := counterClause647 (baseVal q)

theorem counterClause648 (q : Nat → Bool) : valuationOf q 141 = false ∨ valuationOf q 275 = true := by
  have hs : count275 q = (countLit q [140]) + (countLit q [141]) := List.countP_append (p := literal q) (l₁ := [140]) (l₂ := [141])
  have hm := merge_right (literal (valuationOf q) (141)) (literal (valuationOf q) (275)) (countLit q [140]) (countLit q [141]) (count275 q) 1 (meaning141 q) (meaning275 q) hs
  change valuationOf q 141 = false ∨ valuationOf q 275 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause648 (q : Snake 81) (h : Conditions q) : valuation q 141 = false ∨ valuation q 275 = true := counterClause648 (baseVal q)

theorem counterClause649 (q : Nat → Bool) : valuationOf q 142 = false ∨ valuationOf q 277 = true := by
  have hs : count277 q = (countLit q [142]) + (countLit q [143]) := List.countP_append (p := literal q) (l₁ := [142]) (l₂ := [143])
  have hm := merge_left (literal (valuationOf q) (142)) (literal (valuationOf q) (277)) (countLit q [142]) (countLit q [143]) (count277 q) 1 (meaning142 q) (meaning277 q) hs
  change valuationOf q 142 = false ∨ valuationOf q 277 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause649 (q : Snake 81) (h : Conditions q) : valuation q 142 = false ∨ valuation q 277 = true := counterClause649 (baseVal q)

theorem counterClause650 (q : Nat → Bool) : valuationOf q 277 = false ∨ valuationOf q 279 = true := by
  have hs : count279 q = (countLit q [140, 141]) + (countLit q [142, 143]) := List.countP_append (p := literal q) (l₁ := [140, 141]) (l₂ := [142, 143])
  have hm := merge_right (literal (valuationOf q) (277)) (literal (valuationOf q) (279)) (countLit q [140, 141]) (countLit q [142, 143]) (count279 q) 1 (meaning277 q) (meaning279 q) hs
  change valuationOf q 277 = false ∨ valuationOf q 279 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause650 (q : Snake 81) (h : Conditions q) : valuation q 277 = false ∨ valuation q 279 = true := counterClause650 (baseVal q)

theorem counterClause651 (q : Nat → Bool) : valuationOf q 275 = false ∨ valuationOf q 279 = true := by
  have hs : count279 q = (countLit q [140, 141]) + (countLit q [142, 143]) := List.countP_append (p := literal q) (l₁ := [140, 141]) (l₂ := [142, 143])
  have hm := merge_left (literal (valuationOf q) (275)) (literal (valuationOf q) (279)) (countLit q [140, 141]) (countLit q [142, 143]) (count279 q) 1 (meaning275 q) (meaning279 q) hs
  change valuationOf q 275 = false ∨ valuationOf q 279 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause651 (q : Snake 81) (h : Conditions q) : valuation q 275 = false ∨ valuation q 279 = true := counterClause651 (baseVal q)

theorem counterClause652 (q : Nat → Bool) : valuationOf q 144 = false ∨ valuationOf q 281 = true := by
  have hs : count281 q = (countLit q [144]) + (countLit q [145]) := List.countP_append (p := literal q) (l₁ := [144]) (l₂ := [145])
  have hm := merge_left (literal (valuationOf q) (144)) (literal (valuationOf q) (281)) (countLit q [144]) (countLit q [145]) (count281 q) 1 (meaning144 q) (meaning281 q) hs
  change valuationOf q 144 = false ∨ valuationOf q 281 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause652 (q : Snake 81) (h : Conditions q) : valuation q 144 = false ∨ valuation q 281 = true := counterClause652 (baseVal q)

theorem counterClause653 (q : Nat → Bool) : valuationOf q 146 = false ∨ valuationOf q 283 = true := by
  have hs : count283 q = (countLit q [146]) + (countLit q [147]) := List.countP_append (p := literal q) (l₁ := [146]) (l₂ := [147])
  have hm := merge_left (literal (valuationOf q) (146)) (literal (valuationOf q) (283)) (countLit q [146]) (countLit q [147]) (count283 q) 1 (meaning146 q) (meaning283 q) hs
  change valuationOf q 146 = false ∨ valuationOf q 283 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause653 (q : Snake 81) (h : Conditions q) : valuation q 146 = false ∨ valuation q 283 = true := counterClause653 (baseVal q)

theorem counterClause654 (q : Nat → Bool) : valuationOf q 283 = false ∨ valuationOf q 285 = true := by
  have hs : count285 q = (countLit q [144, 145]) + (countLit q [146, 147]) := List.countP_append (p := literal q) (l₁ := [144, 145]) (l₂ := [146, 147])
  have hm := merge_right (literal (valuationOf q) (283)) (literal (valuationOf q) (285)) (countLit q [144, 145]) (countLit q [146, 147]) (count285 q) 1 (meaning283 q) (meaning285 q) hs
  change valuationOf q 283 = false ∨ valuationOf q 285 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause654 (q : Snake 81) (h : Conditions q) : valuation q 283 = false ∨ valuation q 285 = true := counterClause654 (baseVal q)

theorem counterClause655 (q : Nat → Bool) : valuationOf q 281 = false ∨ valuationOf q 285 = true := by
  have hs : count285 q = (countLit q [144, 145]) + (countLit q [146, 147]) := List.countP_append (p := literal q) (l₁ := [144, 145]) (l₂ := [146, 147])
  have hm := merge_left (literal (valuationOf q) (281)) (literal (valuationOf q) (285)) (countLit q [144, 145]) (countLit q [146, 147]) (count285 q) 1 (meaning281 q) (meaning285 q) hs
  change valuationOf q 281 = false ∨ valuationOf q 285 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause655 (q : Snake 81) (h : Conditions q) : valuation q 281 = false ∨ valuation q 285 = true := counterClause655 (baseVal q)

theorem counterClause656 (q : Nat → Bool) : valuationOf q 285 = false ∨ valuationOf q 287 = true := by
  have hs : count287 q = (countLit q [140, 141, 142, 143]) + (countLit q [144, 145, 146, 147]) := List.countP_append (p := literal q) (l₁ := [140, 141, 142, 143]) (l₂ := [144, 145, 146, 147])
  have hm := merge_right (literal (valuationOf q) (285)) (literal (valuationOf q) (287)) (countLit q [140, 141, 142, 143]) (countLit q [144, 145, 146, 147]) (count287 q) 1 (meaning285 q) (meaning287 q) hs
  change valuationOf q 285 = false ∨ valuationOf q 287 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause656 (q : Snake 81) (h : Conditions q) : valuation q 285 = false ∨ valuation q 287 = true := counterClause656 (baseVal q)

theorem counterClause657 (q : Nat → Bool) : valuationOf q 279 = false ∨ valuationOf q 287 = true := by
  have hs : count287 q = (countLit q [140, 141, 142, 143]) + (countLit q [144, 145, 146, 147]) := List.countP_append (p := literal q) (l₁ := [140, 141, 142, 143]) (l₂ := [144, 145, 146, 147])
  have hm := merge_left (literal (valuationOf q) (279)) (literal (valuationOf q) (287)) (countLit q [140, 141, 142, 143]) (countLit q [144, 145, 146, 147]) (count287 q) 1 (meaning279 q) (meaning287 q) hs
  change valuationOf q 279 = false ∨ valuationOf q 287 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause657 (q : Snake 81) (h : Conditions q) : valuation q 279 = false ∨ valuation q 287 = true := counterClause657 (baseVal q)

theorem counterClause658 (q : Nat → Bool) : valuationOf q 287 = false ∨ valuationOf q 289 = true := by
  have hs : count289 q = (countLit q [133, 134, 135, 136, 137, 138, 139]) + (countLit q [140, 141, 142, 143, 144, 145, 146, 147]) := List.countP_append (p := literal q) (l₁ := [133, 134, 135, 136, 137, 138, 139]) (l₂ := [140, 141, 142, 143, 144, 145, 146, 147])
  have hm := merge_right (literal (valuationOf q) (287)) (literal (valuationOf q) (289)) (countLit q [133, 134, 135, 136, 137, 138, 139]) (countLit q [140, 141, 142, 143, 144, 145, 146, 147]) (count289 q) 1 (meaning287 q) (meaning289 q) hs
  change valuationOf q 287 = false ∨ valuationOf q 289 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause658 (q : Snake 81) (h : Conditions q) : valuation q 287 = false ∨ valuation q 289 = true := counterClause658 (baseVal q)

theorem counterClause659 (q : Nat → Bool) : valuationOf q 273 = false ∨ valuationOf q 289 = true := by
  have hs : count289 q = (countLit q [133, 134, 135, 136, 137, 138, 139]) + (countLit q [140, 141, 142, 143, 144, 145, 146, 147]) := List.countP_append (p := literal q) (l₁ := [133, 134, 135, 136, 137, 138, 139]) (l₂ := [140, 141, 142, 143, 144, 145, 146, 147])
  have hm := merge_left (literal (valuationOf q) (273)) (literal (valuationOf q) (289)) (countLit q [133, 134, 135, 136, 137, 138, 139]) (countLit q [140, 141, 142, 143, 144, 145, 146, 147]) (count289 q) 1 (meaning273 q) (meaning289 q) hs
  change valuationOf q 273 = false ∨ valuationOf q 289 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause659 (q : Snake 81) (h : Conditions q) : valuation q 273 = false ∨ valuation q 289 = true := counterClause659 (baseVal q)

theorem counterClause660 (q : Nat → Bool) : valuationOf q 273 = false ∨ valuationOf q 287 = false ∨ valuationOf q 290 = true := by
  have hs : count289 q = (countLit q [133, 134, 135, 136, 137, 138, 139]) + (countLit q [140, 141, 142, 143, 144, 145, 146, 147]) := List.countP_append (p := literal q) (l₁ := [133, 134, 135, 136, 137, 138, 139]) (l₂ := [140, 141, 142, 143, 144, 145, 146, 147])
  have hm := merge_two (literal (valuationOf q) (273)) (literal (valuationOf q) (287)) (literal (valuationOf q) (290)) (countLit q [133, 134, 135, 136, 137, 138, 139]) (countLit q [140, 141, 142, 143, 144, 145, 146, 147]) (count289 q) 1 1 (meaning273 q) (meaning287 q) (meaning290 q) hs
  change valuationOf q 273 = false ∨ valuationOf q 287 = false ∨ valuationOf q 290 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause660 (q : Snake 81) (h : Conditions q) : valuation q 273 = false ∨ valuation q 287 = false ∨ valuation q 290 = true := counterClause660 (baseVal q)

theorem counterClause661 (q : Nat → Bool) : valuationOf q 274 = false ∨ valuationOf q 290 = true := by
  have hs : count289 q = (countLit q [133, 134, 135, 136, 137, 138, 139]) + (countLit q [140, 141, 142, 143, 144, 145, 146, 147]) := List.countP_append (p := literal q) (l₁ := [133, 134, 135, 136, 137, 138, 139]) (l₂ := [140, 141, 142, 143, 144, 145, 146, 147])
  have hm := merge_left (literal (valuationOf q) (274)) (literal (valuationOf q) (290)) (countLit q [133, 134, 135, 136, 137, 138, 139]) (countLit q [140, 141, 142, 143, 144, 145, 146, 147]) (count289 q) 2 (meaning274 q) (meaning290 q) hs
  change valuationOf q 274 = false ∨ valuationOf q 290 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause661 (q : Snake 81) (h : Conditions q) : valuation q 274 = false ∨ valuation q 290 = true := counterClause661 (baseVal q)

theorem counterClause662 (q : Nat → Bool) : valuationOf q 289 = false ∨ valuationOf q 291 = true := by
  have hs : count291 q = (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) + (countLit q [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) (l₂ := [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147])
  have hm := merge_right (literal (valuationOf q) (289)) (literal (valuationOf q) (291)) (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) (countLit q [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) (count291 q) 1 (meaning289 q) (meaning291 q) hs
  change valuationOf q 289 = false ∨ valuationOf q 291 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause662 (q : Snake 81) (h : Conditions q) : valuation q 289 = false ∨ valuation q 291 = true := counterClause662 (baseVal q)

theorem counterClause663 (q : Nat → Bool) : valuationOf q 290 = false ∨ valuationOf q 292 = true := by
  have hs : count291 q = (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) + (countLit q [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) (l₂ := [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147])
  have hm := merge_right (literal (valuationOf q) (290)) (literal (valuationOf q) (292)) (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) (countLit q [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) (count291 q) 2 (meaning290 q) (meaning292 q) hs
  change valuationOf q 290 = false ∨ valuationOf q 292 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause663 (q : Snake 81) (h : Conditions q) : valuation q 290 = false ∨ valuation q 292 = true := counterClause663 (baseVal q)

theorem counterClause664 (q : Nat → Bool) : valuationOf q 261 = false ∨ valuationOf q 291 = true := by
  have hs : count291 q = (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) + (countLit q [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) (l₂ := [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147])
  have hm := merge_left (literal (valuationOf q) (261)) (literal (valuationOf q) (291)) (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) (countLit q [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) (count291 q) 1 (meaning261 q) (meaning291 q) hs
  change valuationOf q 261 = false ∨ valuationOf q 291 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause664 (q : Snake 81) (h : Conditions q) : valuation q 261 = false ∨ valuation q 291 = true := counterClause664 (baseVal q)

theorem counterClause665 (q : Nat → Bool) : valuationOf q 261 = false ∨ valuationOf q 289 = false ∨ valuationOf q 292 = true := by
  have hs : count291 q = (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) + (countLit q [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) (l₂ := [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147])
  have hm := merge_two (literal (valuationOf q) (261)) (literal (valuationOf q) (289)) (literal (valuationOf q) (292)) (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) (countLit q [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) (count291 q) 1 1 (meaning261 q) (meaning289 q) (meaning292 q) hs
  change valuationOf q 261 = false ∨ valuationOf q 289 = false ∨ valuationOf q 292 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause665 (q : Snake 81) (h : Conditions q) : valuation q 261 = false ∨ valuation q 289 = false ∨ valuation q 292 = true := counterClause665 (baseVal q)

theorem counterClause666 (q : Nat → Bool) : valuationOf q 262 = false ∨ valuationOf q 292 = true := by
  have hs : count291 q = (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) + (countLit q [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) (l₂ := [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147])
  have hm := merge_left (literal (valuationOf q) (262)) (literal (valuationOf q) (292)) (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) (countLit q [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) (count291 q) 2 (meaning262 q) (meaning292 q) hs
  change valuationOf q 262 = false ∨ valuationOf q 292 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause666 (q : Snake 81) (h : Conditions q) : valuation q 262 = false ∨ valuation q 292 = true := counterClause666 (baseVal q)

theorem counterClause667 (q : Nat → Bool) : valuationOf q 149 = false ∨ valuationOf q 293 = true := by
  have hs : count293 q = (countLit q [149]) + (countLit q [150]) := List.countP_append (p := literal q) (l₁ := [149]) (l₂ := [150])
  have hm := merge_left (literal (valuationOf q) (149)) (literal (valuationOf q) (293)) (countLit q [149]) (countLit q [150]) (count293 q) 1 (meaning149 q) (meaning293 q) hs
  change valuationOf q 149 = false ∨ valuationOf q 293 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause667 (q : Snake 81) (h : Conditions q) : valuation q 149 = false ∨ valuation q 293 = true := counterClause667 (baseVal q)

theorem counterClause668 (q : Nat → Bool) : valuationOf q 293 = false ∨ valuationOf q 295 = true := by
  have hs : count295 q = (countLit q [148]) + (countLit q [149, 150]) := List.countP_append (p := literal q) (l₁ := [148]) (l₂ := [149, 150])
  have hm := merge_right (literal (valuationOf q) (293)) (literal (valuationOf q) (295)) (countLit q [148]) (countLit q [149, 150]) (count295 q) 1 (meaning293 q) (meaning295 q) hs
  change valuationOf q 293 = false ∨ valuationOf q 295 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause668 (q : Snake 81) (h : Conditions q) : valuation q 293 = false ∨ valuation q 295 = true := counterClause668 (baseVal q)

theorem counterClause669 (q : Nat → Bool) : valuationOf q 152 = false ∨ valuationOf q 297 = true := by
  have hs : count297 q = (countLit q [151]) + (countLit q [152]) := List.countP_append (p := literal q) (l₁ := [151]) (l₂ := [152])
  have hm := merge_right (literal (valuationOf q) (152)) (literal (valuationOf q) (297)) (countLit q [151]) (countLit q [152]) (count297 q) 1 (meaning152 q) (meaning297 q) hs
  change valuationOf q 152 = false ∨ valuationOf q 297 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause669 (q : Snake 81) (h : Conditions q) : valuation q 152 = false ∨ valuation q 297 = true := counterClause669 (baseVal q)

theorem counterClause670 (q : Nat → Bool) : valuationOf q 151 = false ∨ valuationOf q 297 = true := by
  have hs : count297 q = (countLit q [151]) + (countLit q [152]) := List.countP_append (p := literal q) (l₁ := [151]) (l₂ := [152])
  have hm := merge_left (literal (valuationOf q) (151)) (literal (valuationOf q) (297)) (countLit q [151]) (countLit q [152]) (count297 q) 1 (meaning151 q) (meaning297 q) hs
  change valuationOf q 151 = false ∨ valuationOf q 297 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause670 (q : Snake 81) (h : Conditions q) : valuation q 151 = false ∨ valuation q 297 = true := counterClause670 (baseVal q)

theorem counterClause671 (q : Nat → Bool) : valuationOf q 297 = false ∨ valuationOf q 301 = true := by
  have hs : count301 q = (countLit q [151, 152]) + (countLit q [153, 154]) := List.countP_append (p := literal q) (l₁ := [151, 152]) (l₂ := [153, 154])
  have hm := merge_left (literal (valuationOf q) (297)) (literal (valuationOf q) (301)) (countLit q [151, 152]) (countLit q [153, 154]) (count301 q) 1 (meaning297 q) (meaning301 q) hs
  change valuationOf q 297 = false ∨ valuationOf q 301 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause671 (q : Snake 81) (h : Conditions q) : valuation q 297 = false ∨ valuation q 301 = true := counterClause671 (baseVal q)

theorem counterClause672 (q : Nat → Bool) : valuationOf q 301 = false ∨ valuationOf q 303 = true := by
  have hs : count303 q = (countLit q [148, 149, 150]) + (countLit q [151, 152, 153, 154]) := List.countP_append (p := literal q) (l₁ := [148, 149, 150]) (l₂ := [151, 152, 153, 154])
  have hm := merge_right (literal (valuationOf q) (301)) (literal (valuationOf q) (303)) (countLit q [148, 149, 150]) (countLit q [151, 152, 153, 154]) (count303 q) 1 (meaning301 q) (meaning303 q) hs
  change valuationOf q 301 = false ∨ valuationOf q 303 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause672 (q : Snake 81) (h : Conditions q) : valuation q 301 = false ∨ valuation q 303 = true := counterClause672 (baseVal q)

theorem block20 (q : Snake 81) (h : Conditions q) : B112E110.Block20 (valuation q) :=
  ⟨clause641 q h, clause642 q h, clause643 q h, clause644 q h, clause645 q h, clause646 q h, clause647 q h, clause648 q h, clause649 q h, clause650 q h, clause651 q h, clause652 q h, clause653 q h, clause654 q h, clause655 q h, clause656 q h, clause657 q h, clause658 q h, clause659 q h, clause660 q h, clause661 q h, clause662 q h, clause663 q h, clause664 q h, clause665 q h, clause666 q h, clause667 q h, clause668 q h, clause669 q h, clause670 q h, clause671 q h, clause672 q h⟩

end
end Snake9.Regrowth.E112110
