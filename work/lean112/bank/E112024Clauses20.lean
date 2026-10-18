import E112024Semantics
import B112E024Inputs
namespace Snake9.Regrowth.E112024
noncomputable section
local instance blockDec20 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause641 (q : Nat → Bool) : valuationOf q 257 = false ∨ valuationOf q 259 = true := by
  have hs : count259 q = (countLit q [130, 131]) + (countLit q [132, 133]) := List.countP_append (p := literal q) (l₁ := [130, 131]) (l₂ := [132, 133])
  have hm := merge_right (literal (valuationOf q) (257)) (literal (valuationOf q) (259)) (countLit q [130, 131]) (countLit q [132, 133]) (count259 q) 1 (meaning257 q) (meaning259 q) hs
  change valuationOf q 257 = false ∨ valuationOf q 259 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause641 (q : Snake 81) (h : Conditions q) : valuation q 257 = false ∨ valuation q 259 = true := counterClause641 (baseVal q)

theorem counterClause642 (q : Nat → Bool) : valuationOf q 255 = false ∨ valuationOf q 259 = true := by
  have hs : count259 q = (countLit q [130, 131]) + (countLit q [132, 133]) := List.countP_append (p := literal q) (l₁ := [130, 131]) (l₂ := [132, 133])
  have hm := merge_left (literal (valuationOf q) (255)) (literal (valuationOf q) (259)) (countLit q [130, 131]) (countLit q [132, 133]) (count259 q) 1 (meaning255 q) (meaning259 q) hs
  change valuationOf q 255 = false ∨ valuationOf q 259 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause642 (q : Snake 81) (h : Conditions q) : valuation q 255 = false ∨ valuation q 259 = true := counterClause642 (baseVal q)

theorem counterClause643 (q : Nat → Bool) : valuationOf q 259 = false ∨ valuationOf q 267 = true := by
  have hs : count267 q = (countLit q [130, 131, 132, 133]) + (countLit q [134, 135, 136, 137]) := List.countP_append (p := literal q) (l₁ := [130, 131, 132, 133]) (l₂ := [134, 135, 136, 137])
  have hm := merge_left (literal (valuationOf q) (259)) (literal (valuationOf q) (267)) (countLit q [130, 131, 132, 133]) (countLit q [134, 135, 136, 137]) (count267 q) 1 (meaning259 q) (meaning267 q) hs
  change valuationOf q 259 = false ∨ valuationOf q 267 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause643 (q : Snake 81) (h : Conditions q) : valuation q 259 = false ∨ valuation q 267 = true := counterClause643 (baseVal q)

theorem counterClause644 (q : Nat → Bool) : valuationOf q 267 = false ∨ valuationOf q 269 = true := by
  have hs : count269 q = (countLit q [122, 123, 124, 125, 127, 128, 129]) + (countLit q [130, 131, 132, 133, 134, 135, 136, 137]) := List.countP_append (p := literal q) (l₁ := [122, 123, 124, 125, 127, 128, 129]) (l₂ := [130, 131, 132, 133, 134, 135, 136, 137])
  have hm := merge_right (literal (valuationOf q) (267)) (literal (valuationOf q) (269)) (countLit q [122, 123, 124, 125, 127, 128, 129]) (countLit q [130, 131, 132, 133, 134, 135, 136, 137]) (count269 q) 1 (meaning267 q) (meaning269 q) hs
  change valuationOf q 267 = false ∨ valuationOf q 269 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause644 (q : Snake 81) (h : Conditions q) : valuation q 267 = false ∨ valuation q 269 = true := counterClause644 (baseVal q)

theorem counterClause645 (q : Nat → Bool) : valuationOf q 253 = false ∨ valuationOf q 269 = true := by
  have hs : count269 q = (countLit q [122, 123, 124, 125, 127, 128, 129]) + (countLit q [130, 131, 132, 133, 134, 135, 136, 137]) := List.countP_append (p := literal q) (l₁ := [122, 123, 124, 125, 127, 128, 129]) (l₂ := [130, 131, 132, 133, 134, 135, 136, 137])
  have hm := merge_left (literal (valuationOf q) (253)) (literal (valuationOf q) (269)) (countLit q [122, 123, 124, 125, 127, 128, 129]) (countLit q [130, 131, 132, 133, 134, 135, 136, 137]) (count269 q) 1 (meaning253 q) (meaning269 q) hs
  change valuationOf q 253 = false ∨ valuationOf q 269 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause645 (q : Snake 81) (h : Conditions q) : valuation q 253 = false ∨ valuation q 269 = true := counterClause645 (baseVal q)

theorem counterClause646 (q : Nat → Bool) : valuationOf q 138 = false ∨ valuationOf q 273 = true := by
  have hs : count273 q = (countLit q [138]) + (countLit q [139, 140]) := List.countP_append (p := literal q) (l₁ := [138]) (l₂ := [139, 140])
  have hm := merge_left (literal (valuationOf q) (138)) (literal (valuationOf q) (273)) (countLit q [138]) (countLit q [139, 140]) (count273 q) 1 (meaning138 q) (meaning273 q) hs
  change valuationOf q 138 = false ∨ valuationOf q 273 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause646 (q : Snake 81) (h : Conditions q) : valuation q 138 = false ∨ valuation q 273 = true := counterClause646 (baseVal q)

theorem counterClause647 (q : Nat → Bool) : valuationOf q 142 = false ∨ valuationOf q 275 = true := by
  have hs : count275 q = (countLit q [141]) + (countLit q [142]) := List.countP_append (p := literal q) (l₁ := [141]) (l₂ := [142])
  have hm := merge_right (literal (valuationOf q) (142)) (literal (valuationOf q) (275)) (countLit q [141]) (countLit q [142]) (count275 q) 1 (meaning142 q) (meaning275 q) hs
  change valuationOf q 142 = false ∨ valuationOf q 275 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause647 (q : Snake 81) (h : Conditions q) : valuation q 142 = false ∨ valuation q 275 = true := counterClause647 (baseVal q)

theorem counterClause648 (q : Nat → Bool) : valuationOf q 144 = false ∨ valuationOf q 277 = true := by
  have hs : count277 q = (countLit q [143]) + (countLit q [144]) := List.countP_append (p := literal q) (l₁ := [143]) (l₂ := [144])
  have hm := merge_right (literal (valuationOf q) (144)) (literal (valuationOf q) (277)) (countLit q [143]) (countLit q [144]) (count277 q) 1 (meaning144 q) (meaning277 q) hs
  change valuationOf q 144 = false ∨ valuationOf q 277 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause648 (q : Snake 81) (h : Conditions q) : valuation q 144 = false ∨ valuation q 277 = true := counterClause648 (baseVal q)

theorem counterClause649 (q : Nat → Bool) : valuationOf q 277 = false ∨ valuationOf q 279 = true := by
  have hs : count279 q = (countLit q [141, 142]) + (countLit q [143, 144]) := List.countP_append (p := literal q) (l₁ := [141, 142]) (l₂ := [143, 144])
  have hm := merge_right (literal (valuationOf q) (277)) (literal (valuationOf q) (279)) (countLit q [141, 142]) (countLit q [143, 144]) (count279 q) 1 (meaning277 q) (meaning279 q) hs
  change valuationOf q 277 = false ∨ valuationOf q 279 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause649 (q : Snake 81) (h : Conditions q) : valuation q 277 = false ∨ valuation q 279 = true := counterClause649 (baseVal q)

theorem counterClause650 (q : Nat → Bool) : valuationOf q 275 = false ∨ valuationOf q 279 = true := by
  have hs : count279 q = (countLit q [141, 142]) + (countLit q [143, 144]) := List.countP_append (p := literal q) (l₁ := [141, 142]) (l₂ := [143, 144])
  have hm := merge_left (literal (valuationOf q) (275)) (literal (valuationOf q) (279)) (countLit q [141, 142]) (countLit q [143, 144]) (count279 q) 1 (meaning275 q) (meaning279 q) hs
  change valuationOf q 275 = false ∨ valuationOf q 279 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause650 (q : Snake 81) (h : Conditions q) : valuation q 275 = false ∨ valuation q 279 = true := counterClause650 (baseVal q)

theorem counterClause651 (q : Nat → Bool) : valuationOf q 279 = false ∨ valuationOf q 281 = true := by
  have hs : count281 q = (countLit q [138, 139, 140]) + (countLit q [141, 142, 143, 144]) := List.countP_append (p := literal q) (l₁ := [138, 139, 140]) (l₂ := [141, 142, 143, 144])
  have hm := merge_right (literal (valuationOf q) (279)) (literal (valuationOf q) (281)) (countLit q [138, 139, 140]) (countLit q [141, 142, 143, 144]) (count281 q) 1 (meaning279 q) (meaning281 q) hs
  change valuationOf q 279 = false ∨ valuationOf q 281 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause651 (q : Snake 81) (h : Conditions q) : valuation q 279 = false ∨ valuation q 281 = true := counterClause651 (baseVal q)

theorem counterClause652 (q : Nat → Bool) : valuationOf q 273 = false ∨ valuationOf q 281 = true := by
  have hs : count281 q = (countLit q [138, 139, 140]) + (countLit q [141, 142, 143, 144]) := List.countP_append (p := literal q) (l₁ := [138, 139, 140]) (l₂ := [141, 142, 143, 144])
  have hm := merge_left (literal (valuationOf q) (273)) (literal (valuationOf q) (281)) (countLit q [138, 139, 140]) (countLit q [141, 142, 143, 144]) (count281 q) 1 (meaning273 q) (meaning281 q) hs
  change valuationOf q 273 = false ∨ valuationOf q 281 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause652 (q : Snake 81) (h : Conditions q) : valuation q 273 = false ∨ valuation q 281 = true := counterClause652 (baseVal q)

theorem counterClause653 (q : Nat → Bool) : valuationOf q 145 = false ∨ valuationOf q 283 = true := by
  have hs : count283 q = (countLit q [145]) + (countLit q [146]) := List.countP_append (p := literal q) (l₁ := [145]) (l₂ := [146])
  have hm := merge_left (literal (valuationOf q) (145)) (literal (valuationOf q) (283)) (countLit q [145]) (countLit q [146]) (count283 q) 1 (meaning145 q) (meaning283 q) hs
  change valuationOf q 145 = false ∨ valuationOf q 283 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause653 (q : Snake 81) (h : Conditions q) : valuation q 145 = false ∨ valuation q 283 = true := counterClause653 (baseVal q)

theorem counterClause654 (q : Nat → Bool) : valuationOf q 283 = false ∨ valuationOf q 287 = true := by
  have hs : count287 q = (countLit q [145, 146]) + (countLit q [147, 148]) := List.countP_append (p := literal q) (l₁ := [145, 146]) (l₂ := [147, 148])
  have hm := merge_left (literal (valuationOf q) (283)) (literal (valuationOf q) (287)) (countLit q [145, 146]) (countLit q [147, 148]) (count287 q) 1 (meaning283 q) (meaning287 q) hs
  change valuationOf q 283 = false ∨ valuationOf q 287 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause654 (q : Snake 81) (h : Conditions q) : valuation q 283 = false ∨ valuation q 287 = true := counterClause654 (baseVal q)

theorem counterClause655 (q : Nat → Bool) : valuationOf q 150 = false ∨ valuationOf q 289 = true := by
  have hs : count289 q = (countLit q [149]) + (countLit q [150]) := List.countP_append (p := literal q) (l₁ := [149]) (l₂ := [150])
  have hm := merge_right (literal (valuationOf q) (150)) (literal (valuationOf q) (289)) (countLit q [149]) (countLit q [150]) (count289 q) 1 (meaning150 q) (meaning289 q) hs
  change valuationOf q 150 = false ∨ valuationOf q 289 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause655 (q : Snake 81) (h : Conditions q) : valuation q 150 = false ∨ valuation q 289 = true := counterClause655 (baseVal q)

theorem counterClause656 (q : Nat → Bool) : valuationOf q 151 = false ∨ valuationOf q 291 = true := by
  have hs : count291 q = (countLit q [151]) + (countLit q [152]) := List.countP_append (p := literal q) (l₁ := [151]) (l₂ := [152])
  have hm := merge_left (literal (valuationOf q) (151)) (literal (valuationOf q) (291)) (countLit q [151]) (countLit q [152]) (count291 q) 1 (meaning151 q) (meaning291 q) hs
  change valuationOf q 151 = false ∨ valuationOf q 291 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause656 (q : Snake 81) (h : Conditions q) : valuation q 151 = false ∨ valuation q 291 = true := counterClause656 (baseVal q)

theorem counterClause657 (q : Nat → Bool) : valuationOf q 291 = false ∨ valuationOf q 293 = true := by
  have hs : count293 q = (countLit q [149, 150]) + (countLit q [151, 152]) := List.countP_append (p := literal q) (l₁ := [149, 150]) (l₂ := [151, 152])
  have hm := merge_right (literal (valuationOf q) (291)) (literal (valuationOf q) (293)) (countLit q [149, 150]) (countLit q [151, 152]) (count293 q) 1 (meaning291 q) (meaning293 q) hs
  change valuationOf q 291 = false ∨ valuationOf q 293 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause657 (q : Snake 81) (h : Conditions q) : valuation q 291 = false ∨ valuation q 293 = true := counterClause657 (baseVal q)

theorem counterClause658 (q : Nat → Bool) : valuationOf q 289 = false ∨ valuationOf q 293 = true := by
  have hs : count293 q = (countLit q [149, 150]) + (countLit q [151, 152]) := List.countP_append (p := literal q) (l₁ := [149, 150]) (l₂ := [151, 152])
  have hm := merge_left (literal (valuationOf q) (289)) (literal (valuationOf q) (293)) (countLit q [149, 150]) (countLit q [151, 152]) (count293 q) 1 (meaning289 q) (meaning293 q) hs
  change valuationOf q 289 = false ∨ valuationOf q 293 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause658 (q : Snake 81) (h : Conditions q) : valuation q 289 = false ∨ valuation q 293 = true := counterClause658 (baseVal q)

theorem counterClause659 (q : Nat → Bool) : valuationOf q 289 = false ∨ valuationOf q 291 = false ∨ valuationOf q 294 = true := by
  have hs : count293 q = (countLit q [149, 150]) + (countLit q [151, 152]) := List.countP_append (p := literal q) (l₁ := [149, 150]) (l₂ := [151, 152])
  have hm := merge_two (literal (valuationOf q) (289)) (literal (valuationOf q) (291)) (literal (valuationOf q) (294)) (countLit q [149, 150]) (countLit q [151, 152]) (count293 q) 1 1 (meaning289 q) (meaning291 q) (meaning294 q) hs
  change valuationOf q 289 = false ∨ valuationOf q 291 = false ∨ valuationOf q 294 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause659 (q : Snake 81) (h : Conditions q) : valuation q 289 = false ∨ valuation q 291 = false ∨ valuation q 294 = true := counterClause659 (baseVal q)

theorem counterClause660 (q : Nat → Bool) : valuationOf q 293 = false ∨ valuationOf q 295 = true := by
  have hs : count295 q = (countLit q [145, 146, 147, 148]) + (countLit q [149, 150, 151, 152]) := List.countP_append (p := literal q) (l₁ := [145, 146, 147, 148]) (l₂ := [149, 150, 151, 152])
  have hm := merge_right (literal (valuationOf q) (293)) (literal (valuationOf q) (295)) (countLit q [145, 146, 147, 148]) (countLit q [149, 150, 151, 152]) (count295 q) 1 (meaning293 q) (meaning295 q) hs
  change valuationOf q 293 = false ∨ valuationOf q 295 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause660 (q : Snake 81) (h : Conditions q) : valuation q 293 = false ∨ valuation q 295 = true := counterClause660 (baseVal q)

theorem counterClause661 (q : Nat → Bool) : valuationOf q 294 = false ∨ valuationOf q 296 = true := by
  have hs : count295 q = (countLit q [145, 146, 147, 148]) + (countLit q [149, 150, 151, 152]) := List.countP_append (p := literal q) (l₁ := [145, 146, 147, 148]) (l₂ := [149, 150, 151, 152])
  have hm := merge_right (literal (valuationOf q) (294)) (literal (valuationOf q) (296)) (countLit q [145, 146, 147, 148]) (countLit q [149, 150, 151, 152]) (count295 q) 2 (meaning294 q) (meaning296 q) hs
  change valuationOf q 294 = false ∨ valuationOf q 296 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause661 (q : Snake 81) (h : Conditions q) : valuation q 294 = false ∨ valuation q 296 = true := counterClause661 (baseVal q)

theorem counterClause662 (q : Nat → Bool) : valuationOf q 287 = false ∨ valuationOf q 293 = false ∨ valuationOf q 296 = true := by
  have hs : count295 q = (countLit q [145, 146, 147, 148]) + (countLit q [149, 150, 151, 152]) := List.countP_append (p := literal q) (l₁ := [145, 146, 147, 148]) (l₂ := [149, 150, 151, 152])
  have hm := merge_two (literal (valuationOf q) (287)) (literal (valuationOf q) (293)) (literal (valuationOf q) (296)) (countLit q [145, 146, 147, 148]) (countLit q [149, 150, 151, 152]) (count295 q) 1 1 (meaning287 q) (meaning293 q) (meaning296 q) hs
  change valuationOf q 287 = false ∨ valuationOf q 293 = false ∨ valuationOf q 296 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause662 (q : Snake 81) (h : Conditions q) : valuation q 287 = false ∨ valuation q 293 = false ∨ valuation q 296 = true := counterClause662 (baseVal q)

theorem counterClause663 (q : Nat → Bool) : valuationOf q 295 = false ∨ valuationOf q 297 = true := by
  have hs : count297 q = (countLit q [138, 139, 140, 141, 142, 143, 144]) + (countLit q [145, 146, 147, 148, 149, 150, 151, 152]) := List.countP_append (p := literal q) (l₁ := [138, 139, 140, 141, 142, 143, 144]) (l₂ := [145, 146, 147, 148, 149, 150, 151, 152])
  have hm := merge_right (literal (valuationOf q) (295)) (literal (valuationOf q) (297)) (countLit q [138, 139, 140, 141, 142, 143, 144]) (countLit q [145, 146, 147, 148, 149, 150, 151, 152]) (count297 q) 1 (meaning295 q) (meaning297 q) hs
  change valuationOf q 295 = false ∨ valuationOf q 297 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause663 (q : Snake 81) (h : Conditions q) : valuation q 295 = false ∨ valuation q 297 = true := counterClause663 (baseVal q)

theorem counterClause664 (q : Nat → Bool) : valuationOf q 296 = false ∨ valuationOf q 298 = true := by
  have hs : count297 q = (countLit q [138, 139, 140, 141, 142, 143, 144]) + (countLit q [145, 146, 147, 148, 149, 150, 151, 152]) := List.countP_append (p := literal q) (l₁ := [138, 139, 140, 141, 142, 143, 144]) (l₂ := [145, 146, 147, 148, 149, 150, 151, 152])
  have hm := merge_right (literal (valuationOf q) (296)) (literal (valuationOf q) (298)) (countLit q [138, 139, 140, 141, 142, 143, 144]) (countLit q [145, 146, 147, 148, 149, 150, 151, 152]) (count297 q) 2 (meaning296 q) (meaning298 q) hs
  change valuationOf q 296 = false ∨ valuationOf q 298 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause664 (q : Snake 81) (h : Conditions q) : valuation q 296 = false ∨ valuation q 298 = true := counterClause664 (baseVal q)

theorem counterClause665 (q : Nat → Bool) : valuationOf q 281 = false ∨ valuationOf q 297 = true := by
  have hs : count297 q = (countLit q [138, 139, 140, 141, 142, 143, 144]) + (countLit q [145, 146, 147, 148, 149, 150, 151, 152]) := List.countP_append (p := literal q) (l₁ := [138, 139, 140, 141, 142, 143, 144]) (l₂ := [145, 146, 147, 148, 149, 150, 151, 152])
  have hm := merge_left (literal (valuationOf q) (281)) (literal (valuationOf q) (297)) (countLit q [138, 139, 140, 141, 142, 143, 144]) (countLit q [145, 146, 147, 148, 149, 150, 151, 152]) (count297 q) 1 (meaning281 q) (meaning297 q) hs
  change valuationOf q 281 = false ∨ valuationOf q 297 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause665 (q : Snake 81) (h : Conditions q) : valuation q 281 = false ∨ valuation q 297 = true := counterClause665 (baseVal q)

theorem counterClause666 (q : Nat → Bool) : valuationOf q 281 = false ∨ valuationOf q 295 = false ∨ valuationOf q 298 = true := by
  have hs : count297 q = (countLit q [138, 139, 140, 141, 142, 143, 144]) + (countLit q [145, 146, 147, 148, 149, 150, 151, 152]) := List.countP_append (p := literal q) (l₁ := [138, 139, 140, 141, 142, 143, 144]) (l₂ := [145, 146, 147, 148, 149, 150, 151, 152])
  have hm := merge_two (literal (valuationOf q) (281)) (literal (valuationOf q) (295)) (literal (valuationOf q) (298)) (countLit q [138, 139, 140, 141, 142, 143, 144]) (countLit q [145, 146, 147, 148, 149, 150, 151, 152]) (count297 q) 1 1 (meaning281 q) (meaning295 q) (meaning298 q) hs
  change valuationOf q 281 = false ∨ valuationOf q 295 = false ∨ valuationOf q 298 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause666 (q : Snake 81) (h : Conditions q) : valuation q 281 = false ∨ valuation q 295 = false ∨ valuation q 298 = true := counterClause666 (baseVal q)

theorem counterClause667 (q : Nat → Bool) : valuationOf q 297 = false ∨ valuationOf q 299 = true := by
  have hs : count299 q = (countLit q [122, 123, 124, 125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) + (countLit q [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]) := List.countP_append (p := literal q) (l₁ := [122, 123, 124, 125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) (l₂ := [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152])
  have hm := merge_right (literal (valuationOf q) (297)) (literal (valuationOf q) (299)) (countLit q [122, 123, 124, 125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) (countLit q [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]) (count299 q) 1 (meaning297 q) (meaning299 q) hs
  change valuationOf q 297 = false ∨ valuationOf q 299 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause667 (q : Snake 81) (h : Conditions q) : valuation q 297 = false ∨ valuation q 299 = true := counterClause667 (baseVal q)

theorem counterClause668 (q : Nat → Bool) : valuationOf q 298 = false ∨ valuationOf q 300 = true := by
  have hs : count299 q = (countLit q [122, 123, 124, 125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) + (countLit q [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]) := List.countP_append (p := literal q) (l₁ := [122, 123, 124, 125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) (l₂ := [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152])
  have hm := merge_right (literal (valuationOf q) (298)) (literal (valuationOf q) (300)) (countLit q [122, 123, 124, 125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) (countLit q [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]) (count299 q) 2 (meaning298 q) (meaning300 q) hs
  change valuationOf q 298 = false ∨ valuationOf q 300 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause668 (q : Snake 81) (h : Conditions q) : valuation q 298 = false ∨ valuation q 300 = true := counterClause668 (baseVal q)

theorem counterClause669 (q : Nat → Bool) : valuationOf q 269 = false ∨ valuationOf q 299 = true := by
  have hs : count299 q = (countLit q [122, 123, 124, 125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) + (countLit q [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]) := List.countP_append (p := literal q) (l₁ := [122, 123, 124, 125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) (l₂ := [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152])
  have hm := merge_left (literal (valuationOf q) (269)) (literal (valuationOf q) (299)) (countLit q [122, 123, 124, 125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) (countLit q [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]) (count299 q) 1 (meaning269 q) (meaning299 q) hs
  change valuationOf q 269 = false ∨ valuationOf q 299 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause669 (q : Snake 81) (h : Conditions q) : valuation q 269 = false ∨ valuation q 299 = true := counterClause669 (baseVal q)

theorem counterClause670 (q : Nat → Bool) : valuationOf q 269 = false ∨ valuationOf q 297 = false ∨ valuationOf q 300 = true := by
  have hs : count299 q = (countLit q [122, 123, 124, 125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) + (countLit q [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]) := List.countP_append (p := literal q) (l₁ := [122, 123, 124, 125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) (l₂ := [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152])
  have hm := merge_two (literal (valuationOf q) (269)) (literal (valuationOf q) (297)) (literal (valuationOf q) (300)) (countLit q [122, 123, 124, 125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) (countLit q [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]) (count299 q) 1 1 (meaning269 q) (meaning297 q) (meaning300 q) hs
  change valuationOf q 269 = false ∨ valuationOf q 297 = false ∨ valuationOf q 300 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause670 (q : Snake 81) (h : Conditions q) : valuation q 269 = false ∨ valuation q 297 = false ∨ valuation q 300 = true := counterClause670 (baseVal q)

theorem counterClause671 (q : Nat → Bool) : valuationOf q 153 = false ∨ valuationOf q 303 = true := by
  have hs : count303 q = (countLit q [153]) + (countLit q [154, 155]) := List.countP_append (p := literal q) (l₁ := [153]) (l₂ := [154, 155])
  have hm := merge_left (literal (valuationOf q) (153)) (literal (valuationOf q) (303)) (countLit q [153]) (countLit q [154, 155]) (count303 q) 1 (meaning153 q) (meaning303 q) hs
  change valuationOf q 153 = false ∨ valuationOf q 303 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause671 (q : Snake 81) (h : Conditions q) : valuation q 153 = false ∨ valuation q 303 = true := counterClause671 (baseVal q)

theorem counterClause672 (q : Nat → Bool) : valuationOf q 303 = false ∨ valuationOf q 311 = true := by
  have hs : count311 q = (countLit q [153, 154, 155]) + (countLit q [156, 157, 158, 159]) := List.countP_append (p := literal q) (l₁ := [153, 154, 155]) (l₂ := [156, 157, 158, 159])
  have hm := merge_left (literal (valuationOf q) (303)) (literal (valuationOf q) (311)) (countLit q [153, 154, 155]) (countLit q [156, 157, 158, 159]) (count311 q) 1 (meaning303 q) (meaning311 q) hs
  change valuationOf q 303 = false ∨ valuationOf q 311 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause672 (q : Snake 81) (h : Conditions q) : valuation q 303 = false ∨ valuation q 311 = true := counterClause672 (baseVal q)

theorem block20 (q : Snake 81) (h : Conditions q) : B112E024.Block20 (valuation q) :=
  ⟨clause641 q h, clause642 q h, clause643 q h, clause644 q h, clause645 q h, clause646 q h, clause647 q h, clause648 q h, clause649 q h, clause650 q h, clause651 q h, clause652 q h, clause653 q h, clause654 q h, clause655 q h, clause656 q h, clause657 q h, clause658 q h, clause659 q h, clause660 q h, clause661 q h, clause662 q h, clause663 q h, clause664 q h, clause665 q h, clause666 q h, clause667 q h, clause668 q h, clause669 q h, clause670 q h, clause671 q h, clause672 q h⟩

end
end Snake9.Regrowth.E112024
