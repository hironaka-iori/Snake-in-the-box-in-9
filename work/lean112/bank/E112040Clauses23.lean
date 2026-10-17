import E112040Semantics
import B112E040Inputs
namespace Snake9.Regrowth.E112040
noncomputable section
local instance blockDec23 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause737 (q : Nat → Bool) : valuationOf q 255 = false ∨ valuationOf q 263 = true := by
  have hs : count263 q = (countLit q [128, 129, 130]) + (countLit q [131, 132, 133, 134]) := List.countP_append (p := literal q) (l₁ := [128, 129, 130]) (l₂ := [131, 132, 133, 134])
  have hm := merge_left (literal (valuationOf q) (255)) (literal (valuationOf q) (263)) (countLit q [128, 129, 130]) (countLit q [131, 132, 133, 134]) (count263 q) 1 (meaning255 q) (meaning263 q) hs
  change valuationOf q 255 = false ∨ valuationOf q 263 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause737 (q : Snake 81) (h : Conditions q) : valuation q 255 = false ∨ valuation q 263 = true := counterClause737 (baseVal q)

theorem counterClause738 (q : Nat → Bool) : valuationOf q 255 = false ∨ valuationOf q 261 = false ∨ valuationOf q 264 = true := by
  have hs : count263 q = (countLit q [128, 129, 130]) + (countLit q [131, 132, 133, 134]) := List.countP_append (p := literal q) (l₁ := [128, 129, 130]) (l₂ := [131, 132, 133, 134])
  have hm := merge_two (literal (valuationOf q) (255)) (literal (valuationOf q) (261)) (literal (valuationOf q) (264)) (countLit q [128, 129, 130]) (countLit q [131, 132, 133, 134]) (count263 q) 1 1 (meaning255 q) (meaning261 q) (meaning264 q) hs
  change valuationOf q 255 = false ∨ valuationOf q 261 = false ∨ valuationOf q 264 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause738 (q : Snake 81) (h : Conditions q) : valuation q 255 = false ∨ valuation q 261 = false ∨ valuation q 264 = true := counterClause738 (baseVal q)

theorem counterClause739 (q : Nat → Bool) : valuationOf q 263 = false ∨ valuationOf q 265 = true := by
  have hs : count265 q = (countLit q [121, 122, 123, 124, 125, 126, 127]) + (countLit q [128, 129, 130, 131, 132, 133, 134]) := List.countP_append (p := literal q) (l₁ := [121, 122, 123, 124, 125, 126, 127]) (l₂ := [128, 129, 130, 131, 132, 133, 134])
  have hm := merge_right (literal (valuationOf q) (263)) (literal (valuationOf q) (265)) (countLit q [121, 122, 123, 124, 125, 126, 127]) (countLit q [128, 129, 130, 131, 132, 133, 134]) (count265 q) 1 (meaning263 q) (meaning265 q) hs
  change valuationOf q 263 = false ∨ valuationOf q 265 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause739 (q : Snake 81) (h : Conditions q) : valuation q 263 = false ∨ valuation q 265 = true := counterClause739 (baseVal q)

theorem counterClause740 (q : Nat → Bool) : valuationOf q 264 = false ∨ valuationOf q 266 = true := by
  have hs : count265 q = (countLit q [121, 122, 123, 124, 125, 126, 127]) + (countLit q [128, 129, 130, 131, 132, 133, 134]) := List.countP_append (p := literal q) (l₁ := [121, 122, 123, 124, 125, 126, 127]) (l₂ := [128, 129, 130, 131, 132, 133, 134])
  have hm := merge_right (literal (valuationOf q) (264)) (literal (valuationOf q) (266)) (countLit q [121, 122, 123, 124, 125, 126, 127]) (countLit q [128, 129, 130, 131, 132, 133, 134]) (count265 q) 2 (meaning264 q) (meaning266 q) hs
  change valuationOf q 264 = false ∨ valuationOf q 266 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause740 (q : Snake 81) (h : Conditions q) : valuation q 264 = false ∨ valuation q 266 = true := counterClause740 (baseVal q)

theorem counterClause741 (q : Nat → Bool) : valuationOf q 251 = false ∨ valuationOf q 265 = true := by
  have hs : count265 q = (countLit q [121, 122, 123, 124, 125, 126, 127]) + (countLit q [128, 129, 130, 131, 132, 133, 134]) := List.countP_append (p := literal q) (l₁ := [121, 122, 123, 124, 125, 126, 127]) (l₂ := [128, 129, 130, 131, 132, 133, 134])
  have hm := merge_left (literal (valuationOf q) (251)) (literal (valuationOf q) (265)) (countLit q [121, 122, 123, 124, 125, 126, 127]) (countLit q [128, 129, 130, 131, 132, 133, 134]) (count265 q) 1 (meaning251 q) (meaning265 q) hs
  change valuationOf q 251 = false ∨ valuationOf q 265 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause741 (q : Snake 81) (h : Conditions q) : valuation q 251 = false ∨ valuation q 265 = true := counterClause741 (baseVal q)

theorem counterClause742 (q : Nat → Bool) : valuationOf q 137 = false ∨ valuationOf q 267 = true := by
  have hs : count267 q = (countLit q [136]) + (countLit q [137]) := List.countP_append (p := literal q) (l₁ := [136]) (l₂ := [137])
  have hm := merge_right (literal (valuationOf q) (137)) (literal (valuationOf q) (267)) (countLit q [136]) (countLit q [137]) (count267 q) 1 (meaning137 q) (meaning267 q) hs
  change valuationOf q 137 = false ∨ valuationOf q 267 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause742 (q : Snake 81) (h : Conditions q) : valuation q 137 = false ∨ valuation q 267 = true := counterClause742 (baseVal q)

theorem counterClause743 (q : Nat → Bool) : valuationOf q 267 = false ∨ valuationOf q 269 = true := by
  have hs : count269 q = (countLit q [135]) + (countLit q [136, 137]) := List.countP_append (p := literal q) (l₁ := [135]) (l₂ := [136, 137])
  have hm := merge_right (literal (valuationOf q) (267)) (literal (valuationOf q) (269)) (countLit q [135]) (countLit q [136, 137]) (count269 q) 1 (meaning267 q) (meaning269 q) hs
  change valuationOf q 267 = false ∨ valuationOf q 269 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause743 (q : Snake 81) (h : Conditions q) : valuation q 267 = false ∨ valuation q 269 = true := counterClause743 (baseVal q)

theorem counterClause744 (q : Nat → Bool) : valuationOf q 139 = false ∨ valuationOf q 271 = true := by
  have hs : count271 q = (countLit q [138]) + (countLit q [139]) := List.countP_append (p := literal q) (l₁ := [138]) (l₂ := [139])
  have hm := merge_right (literal (valuationOf q) (139)) (literal (valuationOf q) (271)) (countLit q [138]) (countLit q [139]) (count271 q) 1 (meaning139 q) (meaning271 q) hs
  change valuationOf q 139 = false ∨ valuationOf q 271 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause744 (q : Snake 81) (h : Conditions q) : valuation q 139 = false ∨ valuation q 271 = true := counterClause744 (baseVal q)

theorem counterClause745 (q : Nat → Bool) : valuationOf q 140 = false ∨ valuationOf q 273 = true := by
  have hs : count273 q = (countLit q [140]) + (countLit q [141]) := List.countP_append (p := literal q) (l₁ := [140]) (l₂ := [141])
  have hm := merge_left (literal (valuationOf q) (140)) (literal (valuationOf q) (273)) (countLit q [140]) (countLit q [141]) (count273 q) 1 (meaning140 q) (meaning273 q) hs
  change valuationOf q 140 = false ∨ valuationOf q 273 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause745 (q : Snake 81) (h : Conditions q) : valuation q 140 = false ∨ valuation q 273 = true := counterClause745 (baseVal q)

theorem counterClause746 (q : Nat → Bool) : valuationOf q 273 = false ∨ valuationOf q 275 = true := by
  have hs : count275 q = (countLit q [138, 139]) + (countLit q [140, 141]) := List.countP_append (p := literal q) (l₁ := [138, 139]) (l₂ := [140, 141])
  have hm := merge_right (literal (valuationOf q) (273)) (literal (valuationOf q) (275)) (countLit q [138, 139]) (countLit q [140, 141]) (count275 q) 1 (meaning273 q) (meaning275 q) hs
  change valuationOf q 273 = false ∨ valuationOf q 275 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause746 (q : Snake 81) (h : Conditions q) : valuation q 273 = false ∨ valuation q 275 = true := counterClause746 (baseVal q)

theorem counterClause747 (q : Nat → Bool) : valuationOf q 271 = false ∨ valuationOf q 275 = true := by
  have hs : count275 q = (countLit q [138, 139]) + (countLit q [140, 141]) := List.countP_append (p := literal q) (l₁ := [138, 139]) (l₂ := [140, 141])
  have hm := merge_left (literal (valuationOf q) (271)) (literal (valuationOf q) (275)) (countLit q [138, 139]) (countLit q [140, 141]) (count275 q) 1 (meaning271 q) (meaning275 q) hs
  change valuationOf q 271 = false ∨ valuationOf q 275 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause747 (q : Snake 81) (h : Conditions q) : valuation q 271 = false ∨ valuation q 275 = true := counterClause747 (baseVal q)

theorem counterClause748 (q : Nat → Bool) : valuationOf q 275 = false ∨ valuationOf q 277 = true := by
  have hs : count277 q = (countLit q [135, 136, 137]) + (countLit q [138, 139, 140, 141]) := List.countP_append (p := literal q) (l₁ := [135, 136, 137]) (l₂ := [138, 139, 140, 141])
  have hm := merge_right (literal (valuationOf q) (275)) (literal (valuationOf q) (277)) (countLit q [135, 136, 137]) (countLit q [138, 139, 140, 141]) (count277 q) 1 (meaning275 q) (meaning277 q) hs
  change valuationOf q 275 = false ∨ valuationOf q 277 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause748 (q : Snake 81) (h : Conditions q) : valuation q 275 = false ∨ valuation q 277 = true := counterClause748 (baseVal q)

theorem counterClause749 (q : Nat → Bool) : valuationOf q 269 = false ∨ valuationOf q 277 = true := by
  have hs : count277 q = (countLit q [135, 136, 137]) + (countLit q [138, 139, 140, 141]) := List.countP_append (p := literal q) (l₁ := [135, 136, 137]) (l₂ := [138, 139, 140, 141])
  have hm := merge_left (literal (valuationOf q) (269)) (literal (valuationOf q) (277)) (countLit q [135, 136, 137]) (countLit q [138, 139, 140, 141]) (count277 q) 1 (meaning269 q) (meaning277 q) hs
  change valuationOf q 269 = false ∨ valuationOf q 277 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause749 (q : Snake 81) (h : Conditions q) : valuation q 269 = false ∨ valuation q 277 = true := counterClause749 (baseVal q)

theorem counterClause750 (q : Nat → Bool) : valuationOf q 147 = false ∨ valuationOf q 285 = true := by
  have hs : count285 q = (countLit q [146]) + (countLit q [147]) := List.countP_append (p := literal q) (l₁ := [146]) (l₂ := [147])
  have hm := merge_right (literal (valuationOf q) (147)) (literal (valuationOf q) (285)) (countLit q [146]) (countLit q [147]) (count285 q) 1 (meaning147 q) (meaning285 q) hs
  change valuationOf q 147 = false ∨ valuationOf q 285 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause750 (q : Snake 81) (h : Conditions q) : valuation q 147 = false ∨ valuation q 285 = true := counterClause750 (baseVal q)

theorem counterClause751 (q : Nat → Bool) : valuationOf q 149 = false ∨ valuationOf q 287 = true := by
  have hs : count287 q = (countLit q [148]) + (countLit q [149]) := List.countP_append (p := literal q) (l₁ := [148]) (l₂ := [149])
  have hm := merge_right (literal (valuationOf q) (149)) (literal (valuationOf q) (287)) (countLit q [148]) (countLit q [149]) (count287 q) 1 (meaning149 q) (meaning287 q) hs
  change valuationOf q 149 = false ∨ valuationOf q 287 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause751 (q : Snake 81) (h : Conditions q) : valuation q 149 = false ∨ valuation q 287 = true := counterClause751 (baseVal q)

theorem counterClause752 (q : Nat → Bool) : valuationOf q 287 = false ∨ valuationOf q 289 = true := by
  have hs : count289 q = (countLit q [146, 147]) + (countLit q [148, 149]) := List.countP_append (p := literal q) (l₁ := [146, 147]) (l₂ := [148, 149])
  have hm := merge_right (literal (valuationOf q) (287)) (literal (valuationOf q) (289)) (countLit q [146, 147]) (countLit q [148, 149]) (count289 q) 1 (meaning287 q) (meaning289 q) hs
  change valuationOf q 287 = false ∨ valuationOf q 289 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause752 (q : Snake 81) (h : Conditions q) : valuation q 287 = false ∨ valuation q 289 = true := counterClause752 (baseVal q)

theorem counterClause753 (q : Nat → Bool) : valuationOf q 285 = false ∨ valuationOf q 289 = true := by
  have hs : count289 q = (countLit q [146, 147]) + (countLit q [148, 149]) := List.countP_append (p := literal q) (l₁ := [146, 147]) (l₂ := [148, 149])
  have hm := merge_left (literal (valuationOf q) (285)) (literal (valuationOf q) (289)) (countLit q [146, 147]) (countLit q [148, 149]) (count289 q) 1 (meaning285 q) (meaning289 q) hs
  change valuationOf q 285 = false ∨ valuationOf q 289 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause753 (q : Snake 81) (h : Conditions q) : valuation q 285 = false ∨ valuation q 289 = true := counterClause753 (baseVal q)

theorem counterClause754 (q : Nat → Bool) : valuationOf q 289 = false ∨ valuationOf q 291 = true := by
  have hs : count291 q = (countLit q [142, 143, 144, 145]) + (countLit q [146, 147, 148, 149]) := List.countP_append (p := literal q) (l₁ := [142, 143, 144, 145]) (l₂ := [146, 147, 148, 149])
  have hm := merge_right (literal (valuationOf q) (289)) (literal (valuationOf q) (291)) (countLit q [142, 143, 144, 145]) (countLit q [146, 147, 148, 149]) (count291 q) 1 (meaning289 q) (meaning291 q) hs
  change valuationOf q 289 = false ∨ valuationOf q 291 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause754 (q : Snake 81) (h : Conditions q) : valuation q 289 = false ∨ valuation q 291 = true := counterClause754 (baseVal q)

theorem counterClause755 (q : Nat → Bool) : valuationOf q 291 = false ∨ valuationOf q 293 = true := by
  have hs : count293 q = (countLit q [135, 136, 137, 138, 139, 140, 141]) + (countLit q [142, 143, 144, 145, 146, 147, 148, 149]) := List.countP_append (p := literal q) (l₁ := [135, 136, 137, 138, 139, 140, 141]) (l₂ := [142, 143, 144, 145, 146, 147, 148, 149])
  have hm := merge_right (literal (valuationOf q) (291)) (literal (valuationOf q) (293)) (countLit q [135, 136, 137, 138, 139, 140, 141]) (countLit q [142, 143, 144, 145, 146, 147, 148, 149]) (count293 q) 1 (meaning291 q) (meaning293 q) hs
  change valuationOf q 291 = false ∨ valuationOf q 293 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause755 (q : Snake 81) (h : Conditions q) : valuation q 291 = false ∨ valuation q 293 = true := counterClause755 (baseVal q)

theorem counterClause756 (q : Nat → Bool) : valuationOf q 277 = false ∨ valuationOf q 293 = true := by
  have hs : count293 q = (countLit q [135, 136, 137, 138, 139, 140, 141]) + (countLit q [142, 143, 144, 145, 146, 147, 148, 149]) := List.countP_append (p := literal q) (l₁ := [135, 136, 137, 138, 139, 140, 141]) (l₂ := [142, 143, 144, 145, 146, 147, 148, 149])
  have hm := merge_left (literal (valuationOf q) (277)) (literal (valuationOf q) (293)) (countLit q [135, 136, 137, 138, 139, 140, 141]) (countLit q [142, 143, 144, 145, 146, 147, 148, 149]) (count293 q) 1 (meaning277 q) (meaning293 q) hs
  change valuationOf q 277 = false ∨ valuationOf q 293 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause756 (q : Snake 81) (h : Conditions q) : valuation q 277 = false ∨ valuation q 293 = true := counterClause756 (baseVal q)

theorem counterClause757 (q : Nat → Bool) : valuationOf q 277 = false ∨ valuationOf q 291 = false ∨ valuationOf q 294 = true := by
  have hs : count293 q = (countLit q [135, 136, 137, 138, 139, 140, 141]) + (countLit q [142, 143, 144, 145, 146, 147, 148, 149]) := List.countP_append (p := literal q) (l₁ := [135, 136, 137, 138, 139, 140, 141]) (l₂ := [142, 143, 144, 145, 146, 147, 148, 149])
  have hm := merge_two (literal (valuationOf q) (277)) (literal (valuationOf q) (291)) (literal (valuationOf q) (294)) (countLit q [135, 136, 137, 138, 139, 140, 141]) (countLit q [142, 143, 144, 145, 146, 147, 148, 149]) (count293 q) 1 1 (meaning277 q) (meaning291 q) (meaning294 q) hs
  change valuationOf q 277 = false ∨ valuationOf q 291 = false ∨ valuationOf q 294 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause757 (q : Snake 81) (h : Conditions q) : valuation q 277 = false ∨ valuation q 291 = false ∨ valuation q 294 = true := counterClause757 (baseVal q)

theorem counterClause758 (q : Nat → Bool) : valuationOf q 293 = false ∨ valuationOf q 295 = true := by
  have hs : count295 q = (countLit q [121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134]) + (countLit q [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]) := List.countP_append (p := literal q) (l₁ := [121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134]) (l₂ := [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149])
  have hm := merge_right (literal (valuationOf q) (293)) (literal (valuationOf q) (295)) (countLit q [121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134]) (countLit q [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]) (count295 q) 1 (meaning293 q) (meaning295 q) hs
  change valuationOf q 293 = false ∨ valuationOf q 295 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause758 (q : Snake 81) (h : Conditions q) : valuation q 293 = false ∨ valuation q 295 = true := counterClause758 (baseVal q)

theorem counterClause759 (q : Nat → Bool) : valuationOf q 294 = false ∨ valuationOf q 296 = true := by
  have hs : count295 q = (countLit q [121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134]) + (countLit q [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]) := List.countP_append (p := literal q) (l₁ := [121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134]) (l₂ := [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149])
  have hm := merge_right (literal (valuationOf q) (294)) (literal (valuationOf q) (296)) (countLit q [121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134]) (countLit q [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]) (count295 q) 2 (meaning294 q) (meaning296 q) hs
  change valuationOf q 294 = false ∨ valuationOf q 296 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause759 (q : Snake 81) (h : Conditions q) : valuation q 294 = false ∨ valuation q 296 = true := counterClause759 (baseVal q)

theorem counterClause760 (q : Nat → Bool) : valuationOf q 265 = false ∨ valuationOf q 295 = true := by
  have hs : count295 q = (countLit q [121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134]) + (countLit q [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]) := List.countP_append (p := literal q) (l₁ := [121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134]) (l₂ := [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149])
  have hm := merge_left (literal (valuationOf q) (265)) (literal (valuationOf q) (295)) (countLit q [121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134]) (countLit q [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]) (count295 q) 1 (meaning265 q) (meaning295 q) hs
  change valuationOf q 265 = false ∨ valuationOf q 295 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause760 (q : Snake 81) (h : Conditions q) : valuation q 265 = false ∨ valuation q 295 = true := counterClause760 (baseVal q)

theorem counterClause761 (q : Nat → Bool) : valuationOf q 265 = false ∨ valuationOf q 293 = false ∨ valuationOf q 296 = true := by
  have hs : count295 q = (countLit q [121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134]) + (countLit q [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]) := List.countP_append (p := literal q) (l₁ := [121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134]) (l₂ := [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149])
  have hm := merge_two (literal (valuationOf q) (265)) (literal (valuationOf q) (293)) (literal (valuationOf q) (296)) (countLit q [121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134]) (countLit q [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]) (count295 q) 1 1 (meaning265 q) (meaning293 q) (meaning296 q) hs
  change valuationOf q 265 = false ∨ valuationOf q 293 = false ∨ valuationOf q 296 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause761 (q : Snake 81) (h : Conditions q) : valuation q 265 = false ∨ valuation q 293 = false ∨ valuation q 296 = true := counterClause761 (baseVal q)

theorem counterClause762 (q : Nat → Bool) : valuationOf q 266 = false ∨ valuationOf q 296 = true := by
  have hs : count295 q = (countLit q [121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134]) + (countLit q [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]) := List.countP_append (p := literal q) (l₁ := [121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134]) (l₂ := [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149])
  have hm := merge_left (literal (valuationOf q) (266)) (literal (valuationOf q) (296)) (countLit q [121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134]) (countLit q [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]) (count295 q) 2 (meaning266 q) (meaning296 q) hs
  change valuationOf q 266 = false ∨ valuationOf q 296 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause762 (q : Snake 81) (h : Conditions q) : valuation q 266 = false ∨ valuation q 296 = true := counterClause762 (baseVal q)

theorem counterClause763 (q : Nat → Bool) : valuationOf q 160 = false ∨ valuationOf q 311 = true := by
  have hs : count311 q = (countLit q [159]) + (countLit q [160]) := List.countP_append (p := literal q) (l₁ := [159]) (l₂ := [160])
  have hm := merge_right (literal (valuationOf q) (160)) (literal (valuationOf q) (311)) (countLit q [159]) (countLit q [160]) (count311 q) 1 (meaning160 q) (meaning311 q) hs
  change valuationOf q 160 = false ∨ valuationOf q 311 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause763 (q : Snake 81) (h : Conditions q) : valuation q 160 = false ∨ valuation q 311 = true := counterClause763 (baseVal q)

theorem counterClause764 (q : Nat → Bool) : valuationOf q 311 = false ∨ valuationOf q 313 = true := by
  have hs : count313 q = (countLit q [157, 158]) + (countLit q [159, 160]) := List.countP_append (p := literal q) (l₁ := [157, 158]) (l₂ := [159, 160])
  have hm := merge_right (literal (valuationOf q) (311)) (literal (valuationOf q) (313)) (countLit q [157, 158]) (countLit q [159, 160]) (count313 q) 1 (meaning311 q) (meaning313 q) hs
  change valuationOf q 311 = false ∨ valuationOf q 313 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause764 (q : Snake 81) (h : Conditions q) : valuation q 311 = false ∨ valuation q 313 = true := counterClause764 (baseVal q)

theorem counterClause765 (q : Nat → Bool) : valuationOf q 161 = false ∨ valuationOf q 315 = true := by
  have hs : count315 q = (countLit q [161]) + (countLit q [162]) := List.countP_append (p := literal q) (l₁ := [161]) (l₂ := [162])
  have hm := merge_left (literal (valuationOf q) (161)) (literal (valuationOf q) (315)) (countLit q [161]) (countLit q [162]) (count315 q) 1 (meaning161 q) (meaning315 q) hs
  change valuationOf q 161 = false ∨ valuationOf q 315 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause765 (q : Snake 81) (h : Conditions q) : valuation q 161 = false ∨ valuation q 315 = true := counterClause765 (baseVal q)

theorem counterClause766 (q : Nat → Bool) : valuationOf q 163 = false ∨ valuationOf q 317 = true := by
  have hs : count317 q = (countLit q [163]) + (countLit q [164]) := List.countP_append (p := literal q) (l₁ := [163]) (l₂ := [164])
  have hm := merge_left (literal (valuationOf q) (163)) (literal (valuationOf q) (317)) (countLit q [163]) (countLit q [164]) (count317 q) 1 (meaning163 q) (meaning317 q) hs
  change valuationOf q 163 = false ∨ valuationOf q 317 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause766 (q : Snake 81) (h : Conditions q) : valuation q 163 = false ∨ valuation q 317 = true := counterClause766 (baseVal q)

theorem counterClause767 (q : Nat → Bool) : valuationOf q 317 = false ∨ valuationOf q 319 = true := by
  have hs : count319 q = (countLit q [161, 162]) + (countLit q [163, 164]) := List.countP_append (p := literal q) (l₁ := [161, 162]) (l₂ := [163, 164])
  have hm := merge_right (literal (valuationOf q) (317)) (literal (valuationOf q) (319)) (countLit q [161, 162]) (countLit q [163, 164]) (count319 q) 1 (meaning317 q) (meaning319 q) hs
  change valuationOf q 317 = false ∨ valuationOf q 319 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause767 (q : Snake 81) (h : Conditions q) : valuation q 317 = false ∨ valuation q 319 = true := counterClause767 (baseVal q)

theorem counterClause768 (q : Nat → Bool) : valuationOf q 315 = false ∨ valuationOf q 319 = true := by
  have hs : count319 q = (countLit q [161, 162]) + (countLit q [163, 164]) := List.countP_append (p := literal q) (l₁ := [161, 162]) (l₂ := [163, 164])
  have hm := merge_left (literal (valuationOf q) (315)) (literal (valuationOf q) (319)) (countLit q [161, 162]) (countLit q [163, 164]) (count319 q) 1 (meaning315 q) (meaning319 q) hs
  change valuationOf q 315 = false ∨ valuationOf q 319 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause768 (q : Snake 81) (h : Conditions q) : valuation q 315 = false ∨ valuation q 319 = true := counterClause768 (baseVal q)

theorem block23 (q : Snake 81) (h : Conditions q) : B112E040.Block23 (valuation q) :=
  ⟨clause737 q h, clause738 q h, clause739 q h, clause740 q h, clause741 q h, clause742 q h, clause743 q h, clause744 q h, clause745 q h, clause746 q h, clause747 q h, clause748 q h, clause749 q h, clause750 q h, clause751 q h, clause752 q h, clause753 q h, clause754 q h, clause755 q h, clause756 q h, clause757 q h, clause758 q h, clause759 q h, clause760 q h, clause761 q h, clause762 q h, clause763 q h, clause764 q h, clause765 q h, clause766 q h, clause767 q h, clause768 q h⟩

end
end Snake9.Regrowth.E112040
