import E112007Semantics
import B112E007Inputs
namespace Snake9.Regrowth.E112007
noncomputable section
local instance blockDec19 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause609 (q : Nat → Bool) : valuationOf q 243 = false ∨ valuationOf q 245 = true := by
  have hs : count245 q = (countLit q [122, 123]) + (countLit q [124, 125]) := List.countP_append (p := literal q) (l₁ := [122, 123]) (l₂ := [124, 125])
  have hm := merge_right (literal (valuationOf q) (243)) (literal (valuationOf q) (245)) (countLit q [122, 123]) (countLit q [124, 125]) (count245 q) 1 (meaning243 q) (meaning245 q) hs
  change valuationOf q 243 = false ∨ valuationOf q 245 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause609 (q : Snake 81) (h : Conditions q) : valuation q 243 = false ∨ valuation q 245 = true := counterClause609 (baseVal q)

theorem counterClause610 (q : Nat → Bool) : valuationOf q 241 = false ∨ valuationOf q 245 = true := by
  have hs : count245 q = (countLit q [122, 123]) + (countLit q [124, 125]) := List.countP_append (p := literal q) (l₁ := [122, 123]) (l₂ := [124, 125])
  have hm := merge_left (literal (valuationOf q) (241)) (literal (valuationOf q) (245)) (countLit q [122, 123]) (countLit q [124, 125]) (count245 q) 1 (meaning241 q) (meaning245 q) hs
  change valuationOf q 241 = false ∨ valuationOf q 245 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause610 (q : Snake 81) (h : Conditions q) : valuation q 241 = false ∨ valuation q 245 = true := counterClause610 (baseVal q)

theorem counterClause611 (q : Nat → Bool) : valuationOf q 245 = false ∨ valuationOf q 247 = true := by
  have hs : count247 q = (countLit q [119, 120, 121]) + (countLit q [122, 123, 124, 125]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121]) (l₂ := [122, 123, 124, 125])
  have hm := merge_right (literal (valuationOf q) (245)) (literal (valuationOf q) (247)) (countLit q [119, 120, 121]) (countLit q [122, 123, 124, 125]) (count247 q) 1 (meaning245 q) (meaning247 q) hs
  change valuationOf q 245 = false ∨ valuationOf q 247 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause611 (q : Snake 81) (h : Conditions q) : valuation q 245 = false ∨ valuation q 247 = true := counterClause611 (baseVal q)

theorem counterClause612 (q : Nat → Bool) : valuationOf q 239 = false ∨ valuationOf q 247 = true := by
  have hs : count247 q = (countLit q [119, 120, 121]) + (countLit q [122, 123, 124, 125]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121]) (l₂ := [122, 123, 124, 125])
  have hm := merge_left (literal (valuationOf q) (239)) (literal (valuationOf q) (247)) (countLit q [119, 120, 121]) (countLit q [122, 123, 124, 125]) (count247 q) 1 (meaning239 q) (meaning247 q) hs
  change valuationOf q 239 = false ∨ valuationOf q 247 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause612 (q : Snake 81) (h : Conditions q) : valuation q 239 = false ∨ valuation q 247 = true := counterClause612 (baseVal q)

theorem counterClause613 (q : Nat → Bool) : valuationOf q 130 = false ∨ valuationOf q 253 = true := by
  have hs : count253 q = (countLit q [129]) + (countLit q [130]) := List.countP_append (p := literal q) (l₁ := [129]) (l₂ := [130])
  have hm := merge_right (literal (valuationOf q) (130)) (literal (valuationOf q) (253)) (countLit q [129]) (countLit q [130]) (count253 q) 1 (meaning130 q) (meaning253 q) hs
  change valuationOf q 130 = false ∨ valuationOf q 253 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause613 (q : Snake 81) (h : Conditions q) : valuation q 130 = false ∨ valuation q 253 = true := counterClause613 (baseVal q)

theorem counterClause614 (q : Nat → Bool) : valuationOf q 129 = false ∨ valuationOf q 253 = true := by
  have hs : count253 q = (countLit q [129]) + (countLit q [130]) := List.countP_append (p := literal q) (l₁ := [129]) (l₂ := [130])
  have hm := merge_left (literal (valuationOf q) (129)) (literal (valuationOf q) (253)) (countLit q [129]) (countLit q [130]) (count253 q) 1 (meaning129 q) (meaning253 q) hs
  change valuationOf q 129 = false ∨ valuationOf q 253 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause614 (q : Snake 81) (h : Conditions q) : valuation q 129 = false ∨ valuation q 253 = true := counterClause614 (baseVal q)

theorem counterClause615 (q : Nat → Bool) : valuationOf q 132 = false ∨ valuationOf q 255 = true := by
  have hs : count255 q = (countLit q [131]) + (countLit q [132]) := List.countP_append (p := literal q) (l₁ := [131]) (l₂ := [132])
  have hm := merge_right (literal (valuationOf q) (132)) (literal (valuationOf q) (255)) (countLit q [131]) (countLit q [132]) (count255 q) 1 (meaning132 q) (meaning255 q) hs
  change valuationOf q 132 = false ∨ valuationOf q 255 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause615 (q : Snake 81) (h : Conditions q) : valuation q 132 = false ∨ valuation q 255 = true := counterClause615 (baseVal q)

theorem counterClause616 (q : Nat → Bool) : valuationOf q 255 = false ∨ valuationOf q 257 = true := by
  have hs : count257 q = (countLit q [129, 130]) + (countLit q [131, 132]) := List.countP_append (p := literal q) (l₁ := [129, 130]) (l₂ := [131, 132])
  have hm := merge_right (literal (valuationOf q) (255)) (literal (valuationOf q) (257)) (countLit q [129, 130]) (countLit q [131, 132]) (count257 q) 1 (meaning255 q) (meaning257 q) hs
  change valuationOf q 255 = false ∨ valuationOf q 257 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause616 (q : Snake 81) (h : Conditions q) : valuation q 255 = false ∨ valuation q 257 = true := counterClause616 (baseVal q)

theorem counterClause617 (q : Nat → Bool) : valuationOf q 253 = false ∨ valuationOf q 257 = true := by
  have hs : count257 q = (countLit q [129, 130]) + (countLit q [131, 132]) := List.countP_append (p := literal q) (l₁ := [129, 130]) (l₂ := [131, 132])
  have hm := merge_left (literal (valuationOf q) (253)) (literal (valuationOf q) (257)) (countLit q [129, 130]) (countLit q [131, 132]) (count257 q) 1 (meaning253 q) (meaning257 q) hs
  change valuationOf q 253 = false ∨ valuationOf q 257 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause617 (q : Snake 81) (h : Conditions q) : valuation q 253 = false ∨ valuation q 257 = true := counterClause617 (baseVal q)

theorem counterClause618 (q : Nat → Bool) : valuationOf q 257 = false ∨ valuationOf q 259 = true := by
  have hs : count259 q = (countLit q [126, 127, 128]) + (countLit q [129, 130, 131, 132]) := List.countP_append (p := literal q) (l₁ := [126, 127, 128]) (l₂ := [129, 130, 131, 132])
  have hm := merge_right (literal (valuationOf q) (257)) (literal (valuationOf q) (259)) (countLit q [126, 127, 128]) (countLit q [129, 130, 131, 132]) (count259 q) 1 (meaning257 q) (meaning259 q) hs
  change valuationOf q 257 = false ∨ valuationOf q 259 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause618 (q : Snake 81) (h : Conditions q) : valuation q 257 = false ∨ valuation q 259 = true := counterClause618 (baseVal q)

theorem counterClause619 (q : Nat → Bool) : valuationOf q 259 = false ∨ valuationOf q 261 = true := by
  have hs : count261 q = (countLit q [119, 120, 121, 122, 123, 124, 125]) + (countLit q [126, 127, 128, 129, 130, 131, 132]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121, 122, 123, 124, 125]) (l₂ := [126, 127, 128, 129, 130, 131, 132])
  have hm := merge_right (literal (valuationOf q) (259)) (literal (valuationOf q) (261)) (countLit q [119, 120, 121, 122, 123, 124, 125]) (countLit q [126, 127, 128, 129, 130, 131, 132]) (count261 q) 1 (meaning259 q) (meaning261 q) hs
  change valuationOf q 259 = false ∨ valuationOf q 261 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause619 (q : Snake 81) (h : Conditions q) : valuation q 259 = false ∨ valuation q 261 = true := counterClause619 (baseVal q)

theorem counterClause620 (q : Nat → Bool) : valuationOf q 247 = false ∨ valuationOf q 261 = true := by
  have hs : count261 q = (countLit q [119, 120, 121, 122, 123, 124, 125]) + (countLit q [126, 127, 128, 129, 130, 131, 132]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121, 122, 123, 124, 125]) (l₂ := [126, 127, 128, 129, 130, 131, 132])
  have hm := merge_left (literal (valuationOf q) (247)) (literal (valuationOf q) (261)) (countLit q [119, 120, 121, 122, 123, 124, 125]) (countLit q [126, 127, 128, 129, 130, 131, 132]) (count261 q) 1 (meaning247 q) (meaning261 q) hs
  change valuationOf q 247 = false ∨ valuationOf q 261 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause620 (q : Snake 81) (h : Conditions q) : valuation q 247 = false ∨ valuation q 261 = true := counterClause620 (baseVal q)

theorem counterClause621 (q : Nat → Bool) : valuationOf q 135 = false ∨ valuationOf q 263 = true := by
  have hs : count263 q = (countLit q [134]) + (countLit q [135]) := List.countP_append (p := literal q) (l₁ := [134]) (l₂ := [135])
  have hm := merge_right (literal (valuationOf q) (135)) (literal (valuationOf q) (263)) (countLit q [134]) (countLit q [135]) (count263 q) 1 (meaning135 q) (meaning263 q) hs
  change valuationOf q 135 = false ∨ valuationOf q 263 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause621 (q : Snake 81) (h : Conditions q) : valuation q 135 = false ∨ valuation q 263 = true := counterClause621 (baseVal q)

theorem counterClause622 (q : Nat → Bool) : valuationOf q 263 = false ∨ valuationOf q 265 = true := by
  have hs : count265 q = (countLit q [133]) + (countLit q [134, 135]) := List.countP_append (p := literal q) (l₁ := [133]) (l₂ := [134, 135])
  have hm := merge_right (literal (valuationOf q) (263)) (literal (valuationOf q) (265)) (countLit q [133]) (countLit q [134, 135]) (count265 q) 1 (meaning263 q) (meaning265 q) hs
  change valuationOf q 263 = false ∨ valuationOf q 265 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause622 (q : Snake 81) (h : Conditions q) : valuation q 263 = false ∨ valuation q 265 = true := counterClause622 (baseVal q)

theorem counterClause623 (q : Nat → Bool) : valuationOf q 139 = false ∨ valuationOf q 269 = true := by
  have hs : count269 q = (countLit q [138]) + (countLit q [139]) := List.countP_append (p := literal q) (l₁ := [138]) (l₂ := [139])
  have hm := merge_right (literal (valuationOf q) (139)) (literal (valuationOf q) (269)) (countLit q [138]) (countLit q [139]) (count269 q) 1 (meaning139 q) (meaning269 q) hs
  change valuationOf q 139 = false ∨ valuationOf q 269 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause623 (q : Snake 81) (h : Conditions q) : valuation q 139 = false ∨ valuation q 269 = true := counterClause623 (baseVal q)

theorem counterClause624 (q : Nat → Bool) : valuationOf q 138 = false ∨ valuationOf q 269 = true := by
  have hs : count269 q = (countLit q [138]) + (countLit q [139]) := List.countP_append (p := literal q) (l₁ := [138]) (l₂ := [139])
  have hm := merge_left (literal (valuationOf q) (138)) (literal (valuationOf q) (269)) (countLit q [138]) (countLit q [139]) (count269 q) 1 (meaning138 q) (meaning269 q) hs
  change valuationOf q 138 = false ∨ valuationOf q 269 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause624 (q : Snake 81) (h : Conditions q) : valuation q 138 = false ∨ valuation q 269 = true := counterClause624 (baseVal q)

theorem counterClause625 (q : Nat → Bool) : valuationOf q 138 = false ∨ valuationOf q 139 = false ∨ valuationOf q 270 = true := by
  have hs : count269 q = (countLit q [138]) + (countLit q [139]) := List.countP_append (p := literal q) (l₁ := [138]) (l₂ := [139])
  have hm := merge_two (literal (valuationOf q) (138)) (literal (valuationOf q) (139)) (literal (valuationOf q) (270)) (countLit q [138]) (countLit q [139]) (count269 q) 1 1 (meaning138 q) (meaning139 q) (meaning270 q) hs
  change valuationOf q 138 = false ∨ valuationOf q 139 = false ∨ valuationOf q 270 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause625 (q : Snake 81) (h : Conditions q) : valuation q 138 = false ∨ valuation q 139 = false ∨ valuation q 270 = true := counterClause625 (baseVal q)

theorem counterClause626 (q : Nat → Bool) : valuationOf q 269 = false ∨ valuationOf q 271 = true := by
  have hs : count271 q = (countLit q [136, 137]) + (countLit q [138, 139]) := List.countP_append (p := literal q) (l₁ := [136, 137]) (l₂ := [138, 139])
  have hm := merge_right (literal (valuationOf q) (269)) (literal (valuationOf q) (271)) (countLit q [136, 137]) (countLit q [138, 139]) (count271 q) 1 (meaning269 q) (meaning271 q) hs
  change valuationOf q 269 = false ∨ valuationOf q 271 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause626 (q : Snake 81) (h : Conditions q) : valuation q 269 = false ∨ valuation q 271 = true := counterClause626 (baseVal q)

theorem counterClause627 (q : Nat → Bool) : valuationOf q 270 = false ∨ valuationOf q 272 = true := by
  have hs : count271 q = (countLit q [136, 137]) + (countLit q [138, 139]) := List.countP_append (p := literal q) (l₁ := [136, 137]) (l₂ := [138, 139])
  have hm := merge_right (literal (valuationOf q) (270)) (literal (valuationOf q) (272)) (countLit q [136, 137]) (countLit q [138, 139]) (count271 q) 2 (meaning270 q) (meaning272 q) hs
  change valuationOf q 270 = false ∨ valuationOf q 272 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause627 (q : Snake 81) (h : Conditions q) : valuation q 270 = false ∨ valuation q 272 = true := counterClause627 (baseVal q)

theorem counterClause628 (q : Nat → Bool) : valuationOf q 271 = false ∨ valuationOf q 273 = true := by
  have hs : count273 q = (countLit q [133, 134, 135]) + (countLit q [136, 137, 138, 139]) := List.countP_append (p := literal q) (l₁ := [133, 134, 135]) (l₂ := [136, 137, 138, 139])
  have hm := merge_right (literal (valuationOf q) (271)) (literal (valuationOf q) (273)) (countLit q [133, 134, 135]) (countLit q [136, 137, 138, 139]) (count273 q) 1 (meaning271 q) (meaning273 q) hs
  change valuationOf q 271 = false ∨ valuationOf q 273 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause628 (q : Snake 81) (h : Conditions q) : valuation q 271 = false ∨ valuation q 273 = true := counterClause628 (baseVal q)

theorem counterClause629 (q : Nat → Bool) : valuationOf q 272 = false ∨ valuationOf q 274 = true := by
  have hs : count273 q = (countLit q [133, 134, 135]) + (countLit q [136, 137, 138, 139]) := List.countP_append (p := literal q) (l₁ := [133, 134, 135]) (l₂ := [136, 137, 138, 139])
  have hm := merge_right (literal (valuationOf q) (272)) (literal (valuationOf q) (274)) (countLit q [133, 134, 135]) (countLit q [136, 137, 138, 139]) (count273 q) 2 (meaning272 q) (meaning274 q) hs
  change valuationOf q 272 = false ∨ valuationOf q 274 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause629 (q : Snake 81) (h : Conditions q) : valuation q 272 = false ∨ valuation q 274 = true := counterClause629 (baseVal q)

theorem counterClause630 (q : Nat → Bool) : valuationOf q 265 = false ∨ valuationOf q 273 = true := by
  have hs : count273 q = (countLit q [133, 134, 135]) + (countLit q [136, 137, 138, 139]) := List.countP_append (p := literal q) (l₁ := [133, 134, 135]) (l₂ := [136, 137, 138, 139])
  have hm := merge_left (literal (valuationOf q) (265)) (literal (valuationOf q) (273)) (countLit q [133, 134, 135]) (countLit q [136, 137, 138, 139]) (count273 q) 1 (meaning265 q) (meaning273 q) hs
  change valuationOf q 265 = false ∨ valuationOf q 273 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause630 (q : Snake 81) (h : Conditions q) : valuation q 265 = false ∨ valuation q 273 = true := counterClause630 (baseVal q)

theorem counterClause631 (q : Nat → Bool) : valuationOf q 265 = false ∨ valuationOf q 271 = false ∨ valuationOf q 274 = true := by
  have hs : count273 q = (countLit q [133, 134, 135]) + (countLit q [136, 137, 138, 139]) := List.countP_append (p := literal q) (l₁ := [133, 134, 135]) (l₂ := [136, 137, 138, 139])
  have hm := merge_two (literal (valuationOf q) (265)) (literal (valuationOf q) (271)) (literal (valuationOf q) (274)) (countLit q [133, 134, 135]) (countLit q [136, 137, 138, 139]) (count273 q) 1 1 (meaning265 q) (meaning271 q) (meaning274 q) hs
  change valuationOf q 265 = false ∨ valuationOf q 271 = false ∨ valuationOf q 274 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause631 (q : Snake 81) (h : Conditions q) : valuation q 265 = false ∨ valuation q 271 = false ∨ valuation q 274 = true := counterClause631 (baseVal q)

theorem counterClause632 (q : Nat → Bool) : valuationOf q 141 = false ∨ valuationOf q 275 = true := by
  have hs : count275 q = (countLit q [140]) + (countLit q [141]) := List.countP_append (p := literal q) (l₁ := [140]) (l₂ := [141])
  have hm := merge_right (literal (valuationOf q) (141)) (literal (valuationOf q) (275)) (countLit q [140]) (countLit q [141]) (count275 q) 1 (meaning141 q) (meaning275 q) hs
  change valuationOf q 141 = false ∨ valuationOf q 275 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause632 (q : Snake 81) (h : Conditions q) : valuation q 141 = false ∨ valuation q 275 = true := counterClause632 (baseVal q)

theorem counterClause633 (q : Nat → Bool) : valuationOf q 143 = false ∨ valuationOf q 277 = true := by
  have hs : count277 q = (countLit q [142]) + (countLit q [143]) := List.countP_append (p := literal q) (l₁ := [142]) (l₂ := [143])
  have hm := merge_right (literal (valuationOf q) (143)) (literal (valuationOf q) (277)) (countLit q [142]) (countLit q [143]) (count277 q) 1 (meaning143 q) (meaning277 q) hs
  change valuationOf q 143 = false ∨ valuationOf q 277 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause633 (q : Snake 81) (h : Conditions q) : valuation q 143 = false ∨ valuation q 277 = true := counterClause633 (baseVal q)

theorem counterClause634 (q : Nat → Bool) : valuationOf q 277 = false ∨ valuationOf q 279 = true := by
  have hs : count279 q = (countLit q [140, 141]) + (countLit q [142, 143]) := List.countP_append (p := literal q) (l₁ := [140, 141]) (l₂ := [142, 143])
  have hm := merge_right (literal (valuationOf q) (277)) (literal (valuationOf q) (279)) (countLit q [140, 141]) (countLit q [142, 143]) (count279 q) 1 (meaning277 q) (meaning279 q) hs
  change valuationOf q 277 = false ∨ valuationOf q 279 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause634 (q : Snake 81) (h : Conditions q) : valuation q 277 = false ∨ valuation q 279 = true := counterClause634 (baseVal q)

theorem counterClause635 (q : Nat → Bool) : valuationOf q 275 = false ∨ valuationOf q 279 = true := by
  have hs : count279 q = (countLit q [140, 141]) + (countLit q [142, 143]) := List.countP_append (p := literal q) (l₁ := [140, 141]) (l₂ := [142, 143])
  have hm := merge_left (literal (valuationOf q) (275)) (literal (valuationOf q) (279)) (countLit q [140, 141]) (countLit q [142, 143]) (count279 q) 1 (meaning275 q) (meaning279 q) hs
  change valuationOf q 275 = false ∨ valuationOf q 279 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause635 (q : Snake 81) (h : Conditions q) : valuation q 275 = false ∨ valuation q 279 = true := counterClause635 (baseVal q)

theorem counterClause636 (q : Nat → Bool) : valuationOf q 144 = false ∨ valuationOf q 281 = true := by
  have hs : count281 q = (countLit q [144]) + (countLit q [145]) := List.countP_append (p := literal q) (l₁ := [144]) (l₂ := [145])
  have hm := merge_left (literal (valuationOf q) (144)) (literal (valuationOf q) (281)) (countLit q [144]) (countLit q [145]) (count281 q) 1 (meaning144 q) (meaning281 q) hs
  change valuationOf q 144 = false ∨ valuationOf q 281 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause636 (q : Snake 81) (h : Conditions q) : valuation q 144 = false ∨ valuation q 281 = true := counterClause636 (baseVal q)

theorem counterClause637 (q : Nat → Bool) : valuationOf q 146 = false ∨ valuationOf q 283 = true := by
  have hs : count283 q = (countLit q [146]) + (countLit q [147]) := List.countP_append (p := literal q) (l₁ := [146]) (l₂ := [147])
  have hm := merge_left (literal (valuationOf q) (146)) (literal (valuationOf q) (283)) (countLit q [146]) (countLit q [147]) (count283 q) 1 (meaning146 q) (meaning283 q) hs
  change valuationOf q 146 = false ∨ valuationOf q 283 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause637 (q : Snake 81) (h : Conditions q) : valuation q 146 = false ∨ valuation q 283 = true := counterClause637 (baseVal q)

theorem counterClause638 (q : Nat → Bool) : valuationOf q 283 = false ∨ valuationOf q 285 = true := by
  have hs : count285 q = (countLit q [144, 145]) + (countLit q [146, 147]) := List.countP_append (p := literal q) (l₁ := [144, 145]) (l₂ := [146, 147])
  have hm := merge_right (literal (valuationOf q) (283)) (literal (valuationOf q) (285)) (countLit q [144, 145]) (countLit q [146, 147]) (count285 q) 1 (meaning283 q) (meaning285 q) hs
  change valuationOf q 283 = false ∨ valuationOf q 285 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause638 (q : Snake 81) (h : Conditions q) : valuation q 283 = false ∨ valuation q 285 = true := counterClause638 (baseVal q)

theorem counterClause639 (q : Nat → Bool) : valuationOf q 281 = false ∨ valuationOf q 285 = true := by
  have hs : count285 q = (countLit q [144, 145]) + (countLit q [146, 147]) := List.countP_append (p := literal q) (l₁ := [144, 145]) (l₂ := [146, 147])
  have hm := merge_left (literal (valuationOf q) (281)) (literal (valuationOf q) (285)) (countLit q [144, 145]) (countLit q [146, 147]) (count285 q) 1 (meaning281 q) (meaning285 q) hs
  change valuationOf q 281 = false ∨ valuationOf q 285 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause639 (q : Snake 81) (h : Conditions q) : valuation q 281 = false ∨ valuation q 285 = true := counterClause639 (baseVal q)

theorem counterClause640 (q : Nat → Bool) : valuationOf q 281 = false ∨ valuationOf q 283 = false ∨ valuationOf q 286 = true := by
  have hs : count285 q = (countLit q [144, 145]) + (countLit q [146, 147]) := List.countP_append (p := literal q) (l₁ := [144, 145]) (l₂ := [146, 147])
  have hm := merge_two (literal (valuationOf q) (281)) (literal (valuationOf q) (283)) (literal (valuationOf q) (286)) (countLit q [144, 145]) (countLit q [146, 147]) (count285 q) 1 1 (meaning281 q) (meaning283 q) (meaning286 q) hs
  change valuationOf q 281 = false ∨ valuationOf q 283 = false ∨ valuationOf q 286 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause640 (q : Snake 81) (h : Conditions q) : valuation q 281 = false ∨ valuation q 283 = false ∨ valuation q 286 = true := counterClause640 (baseVal q)

theorem block19 (q : Snake 81) (h : Conditions q) : B112E007.Block19 (valuation q) :=
  ⟨clause609 q h, clause610 q h, clause611 q h, clause612 q h, clause613 q h, clause614 q h, clause615 q h, clause616 q h, clause617 q h, clause618 q h, clause619 q h, clause620 q h, clause621 q h, clause622 q h, clause623 q h, clause624 q h, clause625 q h, clause626 q h, clause627 q h, clause628 q h, clause629 q h, clause630 q h, clause631 q h, clause632 q h, clause633 q h, clause634 q h, clause635 q h, clause636 q h, clause637 q h, clause638 q h, clause639 q h, clause640 q h⟩

end
end Snake9.Regrowth.E112007
