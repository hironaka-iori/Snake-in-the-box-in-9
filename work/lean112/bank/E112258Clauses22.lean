import E112258Semantics
import B112E258Inputs
namespace Snake9.Regrowth.E112258
noncomputable section
local instance blockDec22 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause705 (q : Nat → Bool) : valuationOf q 254 = false ∨ valuationOf q 256 = true := by
  have hs : count255 q = (countLit q [123, 124, 125]) + (countLit q [126, 127, 128, 129]) := List.countP_append (p := literal q) (l₁ := [123, 124, 125]) (l₂ := [126, 127, 128, 129])
  have hm := merge_right (literal (valuationOf q) (254)) (literal (valuationOf q) (256)) (countLit q [123, 124, 125]) (countLit q [126, 127, 128, 129]) (count255 q) 2 (meaning254 q) (meaning256 q) hs
  change valuationOf q 254 = false ∨ valuationOf q 256 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause705 (q : Snake 81) (h : Conditions q) : valuation q 254 = false ∨ valuation q 256 = true := counterClause705 (baseVal q)

theorem counterClause706 (q : Nat → Bool) : valuationOf q 247 = false ∨ valuationOf q 255 = true := by
  have hs : count255 q = (countLit q [123, 124, 125]) + (countLit q [126, 127, 128, 129]) := List.countP_append (p := literal q) (l₁ := [123, 124, 125]) (l₂ := [126, 127, 128, 129])
  have hm := merge_left (literal (valuationOf q) (247)) (literal (valuationOf q) (255)) (countLit q [123, 124, 125]) (countLit q [126, 127, 128, 129]) (count255 q) 1 (meaning247 q) (meaning255 q) hs
  change valuationOf q 247 = false ∨ valuationOf q 255 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause706 (q : Snake 81) (h : Conditions q) : valuation q 247 = false ∨ valuation q 255 = true := counterClause706 (baseVal q)

theorem counterClause707 (q : Nat → Bool) : valuationOf q 247 = false ∨ valuationOf q 253 = false ∨ valuationOf q 256 = true := by
  have hs : count255 q = (countLit q [123, 124, 125]) + (countLit q [126, 127, 128, 129]) := List.countP_append (p := literal q) (l₁ := [123, 124, 125]) (l₂ := [126, 127, 128, 129])
  have hm := merge_two (literal (valuationOf q) (247)) (literal (valuationOf q) (253)) (literal (valuationOf q) (256)) (countLit q [123, 124, 125]) (countLit q [126, 127, 128, 129]) (count255 q) 1 1 (meaning247 q) (meaning253 q) (meaning256 q) hs
  change valuationOf q 247 = false ∨ valuationOf q 253 = false ∨ valuationOf q 256 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause707 (q : Snake 81) (h : Conditions q) : valuation q 247 = false ∨ valuation q 253 = false ∨ valuation q 256 = true := counterClause707 (baseVal q)

theorem counterClause708 (q : Nat → Bool) : valuationOf q 131 = false ∨ valuationOf q 257 = true := by
  have hs : count257 q = (countLit q [130]) + (countLit q [131]) := List.countP_append (p := literal q) (l₁ := [130]) (l₂ := [131])
  have hm := merge_right (literal (valuationOf q) (131)) (literal (valuationOf q) (257)) (countLit q [130]) (countLit q [131]) (count257 q) 1 (meaning131 q) (meaning257 q) hs
  change valuationOf q 131 = false ∨ valuationOf q 257 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause708 (q : Snake 81) (h : Conditions q) : valuation q 131 = false ∨ valuation q 257 = true := counterClause708 (baseVal q)

theorem counterClause709 (q : Nat → Bool) : valuationOf q 133 = false ∨ valuationOf q 259 = true := by
  have hs : count259 q = (countLit q [132]) + (countLit q [133]) := List.countP_append (p := literal q) (l₁ := [132]) (l₂ := [133])
  have hm := merge_right (literal (valuationOf q) (133)) (literal (valuationOf q) (259)) (countLit q [132]) (countLit q [133]) (count259 q) 1 (meaning133 q) (meaning259 q) hs
  change valuationOf q 133 = false ∨ valuationOf q 259 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause709 (q : Snake 81) (h : Conditions q) : valuation q 133 = false ∨ valuation q 259 = true := counterClause709 (baseVal q)

theorem counterClause710 (q : Nat → Bool) : valuationOf q 132 = false ∨ valuationOf q 259 = true := by
  have hs : count259 q = (countLit q [132]) + (countLit q [133]) := List.countP_append (p := literal q) (l₁ := [132]) (l₂ := [133])
  have hm := merge_left (literal (valuationOf q) (132)) (literal (valuationOf q) (259)) (countLit q [132]) (countLit q [133]) (count259 q) 1 (meaning132 q) (meaning259 q) hs
  change valuationOf q 132 = false ∨ valuationOf q 259 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause710 (q : Snake 81) (h : Conditions q) : valuation q 132 = false ∨ valuation q 259 = true := counterClause710 (baseVal q)

theorem counterClause711 (q : Nat → Bool) : valuationOf q 259 = false ∨ valuationOf q 261 = true := by
  have hs : count261 q = (countLit q [130, 131]) + (countLit q [132, 133]) := List.countP_append (p := literal q) (l₁ := [130, 131]) (l₂ := [132, 133])
  have hm := merge_right (literal (valuationOf q) (259)) (literal (valuationOf q) (261)) (countLit q [130, 131]) (countLit q [132, 133]) (count261 q) 1 (meaning259 q) (meaning261 q) hs
  change valuationOf q 259 = false ∨ valuationOf q 261 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause711 (q : Snake 81) (h : Conditions q) : valuation q 259 = false ∨ valuation q 261 = true := counterClause711 (baseVal q)

theorem counterClause712 (q : Nat → Bool) : valuationOf q 257 = false ∨ valuationOf q 261 = true := by
  have hs : count261 q = (countLit q [130, 131]) + (countLit q [132, 133]) := List.countP_append (p := literal q) (l₁ := [130, 131]) (l₂ := [132, 133])
  have hm := merge_left (literal (valuationOf q) (257)) (literal (valuationOf q) (261)) (countLit q [130, 131]) (countLit q [132, 133]) (count261 q) 1 (meaning257 q) (meaning261 q) hs
  change valuationOf q 257 = false ∨ valuationOf q 261 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause712 (q : Snake 81) (h : Conditions q) : valuation q 257 = false ∨ valuation q 261 = true := counterClause712 (baseVal q)

theorem counterClause713 (q : Nat → Bool) : valuationOf q 136 = false ∨ valuationOf q 265 = true := by
  have hs : count265 q = (countLit q [136]) + (countLit q [137]) := List.countP_append (p := literal q) (l₁ := [136]) (l₂ := [137])
  have hm := merge_left (literal (valuationOf q) (136)) (literal (valuationOf q) (265)) (countLit q [136]) (countLit q [137]) (count265 q) 1 (meaning136 q) (meaning265 q) hs
  change valuationOf q 136 = false ∨ valuationOf q 265 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause713 (q : Snake 81) (h : Conditions q) : valuation q 136 = false ∨ valuation q 265 = true := counterClause713 (baseVal q)

theorem counterClause714 (q : Nat → Bool) : valuationOf q 265 = false ∨ valuationOf q 267 = true := by
  have hs : count267 q = (countLit q [134, 135]) + (countLit q [136, 137]) := List.countP_append (p := literal q) (l₁ := [134, 135]) (l₂ := [136, 137])
  have hm := merge_right (literal (valuationOf q) (265)) (literal (valuationOf q) (267)) (countLit q [134, 135]) (countLit q [136, 137]) (count267 q) 1 (meaning265 q) (meaning267 q) hs
  change valuationOf q 265 = false ∨ valuationOf q 267 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause714 (q : Snake 81) (h : Conditions q) : valuation q 265 = false ∨ valuation q 267 = true := counterClause714 (baseVal q)

theorem counterClause715 (q : Nat → Bool) : valuationOf q 267 = false ∨ valuationOf q 269 = true := by
  have hs : count269 q = (countLit q [130, 131, 132, 133]) + (countLit q [134, 135, 136, 137]) := List.countP_append (p := literal q) (l₁ := [130, 131, 132, 133]) (l₂ := [134, 135, 136, 137])
  have hm := merge_right (literal (valuationOf q) (267)) (literal (valuationOf q) (269)) (countLit q [130, 131, 132, 133]) (countLit q [134, 135, 136, 137]) (count269 q) 1 (meaning267 q) (meaning269 q) hs
  change valuationOf q 267 = false ∨ valuationOf q 269 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause715 (q : Snake 81) (h : Conditions q) : valuation q 267 = false ∨ valuation q 269 = true := counterClause715 (baseVal q)

theorem counterClause716 (q : Nat → Bool) : valuationOf q 261 = false ∨ valuationOf q 269 = true := by
  have hs : count269 q = (countLit q [130, 131, 132, 133]) + (countLit q [134, 135, 136, 137]) := List.countP_append (p := literal q) (l₁ := [130, 131, 132, 133]) (l₂ := [134, 135, 136, 137])
  have hm := merge_left (literal (valuationOf q) (261)) (literal (valuationOf q) (269)) (countLit q [130, 131, 132, 133]) (countLit q [134, 135, 136, 137]) (count269 q) 1 (meaning261 q) (meaning269 q) hs
  change valuationOf q 261 = false ∨ valuationOf q 269 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause716 (q : Snake 81) (h : Conditions q) : valuation q 261 = false ∨ valuation q 269 = true := counterClause716 (baseVal q)

theorem counterClause717 (q : Nat → Bool) : valuationOf q 269 = false ∨ valuationOf q 271 = true := by
  have hs : count271 q = (countLit q [123, 124, 125, 126, 127, 128, 129]) + (countLit q [130, 131, 132, 133, 134, 135, 136, 137]) := List.countP_append (p := literal q) (l₁ := [123, 124, 125, 126, 127, 128, 129]) (l₂ := [130, 131, 132, 133, 134, 135, 136, 137])
  have hm := merge_right (literal (valuationOf q) (269)) (literal (valuationOf q) (271)) (countLit q [123, 124, 125, 126, 127, 128, 129]) (countLit q [130, 131, 132, 133, 134, 135, 136, 137]) (count271 q) 1 (meaning269 q) (meaning271 q) hs
  change valuationOf q 269 = false ∨ valuationOf q 271 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause717 (q : Snake 81) (h : Conditions q) : valuation q 269 = false ∨ valuation q 271 = true := counterClause717 (baseVal q)

theorem counterClause718 (q : Nat → Bool) : valuationOf q 255 = false ∨ valuationOf q 271 = true := by
  have hs : count271 q = (countLit q [123, 124, 125, 126, 127, 128, 129]) + (countLit q [130, 131, 132, 133, 134, 135, 136, 137]) := List.countP_append (p := literal q) (l₁ := [123, 124, 125, 126, 127, 128, 129]) (l₂ := [130, 131, 132, 133, 134, 135, 136, 137])
  have hm := merge_left (literal (valuationOf q) (255)) (literal (valuationOf q) (271)) (countLit q [123, 124, 125, 126, 127, 128, 129]) (countLit q [130, 131, 132, 133, 134, 135, 136, 137]) (count271 q) 1 (meaning255 q) (meaning271 q) hs
  change valuationOf q 255 = false ∨ valuationOf q 271 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause718 (q : Snake 81) (h : Conditions q) : valuation q 255 = false ∨ valuation q 271 = true := counterClause718 (baseVal q)

theorem counterClause719 (q : Nat → Bool) : valuationOf q 255 = false ∨ valuationOf q 269 = false ∨ valuationOf q 272 = true := by
  have hs : count271 q = (countLit q [123, 124, 125, 126, 127, 128, 129]) + (countLit q [130, 131, 132, 133, 134, 135, 136, 137]) := List.countP_append (p := literal q) (l₁ := [123, 124, 125, 126, 127, 128, 129]) (l₂ := [130, 131, 132, 133, 134, 135, 136, 137])
  have hm := merge_two (literal (valuationOf q) (255)) (literal (valuationOf q) (269)) (literal (valuationOf q) (272)) (countLit q [123, 124, 125, 126, 127, 128, 129]) (countLit q [130, 131, 132, 133, 134, 135, 136, 137]) (count271 q) 1 1 (meaning255 q) (meaning269 q) (meaning272 q) hs
  change valuationOf q 255 = false ∨ valuationOf q 269 = false ∨ valuationOf q 272 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause719 (q : Snake 81) (h : Conditions q) : valuation q 255 = false ∨ valuation q 269 = false ∨ valuation q 272 = true := counterClause719 (baseVal q)

theorem counterClause720 (q : Nat → Bool) : valuationOf q 256 = false ∨ valuationOf q 272 = true := by
  have hs : count271 q = (countLit q [123, 124, 125, 126, 127, 128, 129]) + (countLit q [130, 131, 132, 133, 134, 135, 136, 137]) := List.countP_append (p := literal q) (l₁ := [123, 124, 125, 126, 127, 128, 129]) (l₂ := [130, 131, 132, 133, 134, 135, 136, 137])
  have hm := merge_left (literal (valuationOf q) (256)) (literal (valuationOf q) (272)) (countLit q [123, 124, 125, 126, 127, 128, 129]) (countLit q [130, 131, 132, 133, 134, 135, 136, 137]) (count271 q) 2 (meaning256 q) (meaning272 q) hs
  change valuationOf q 256 = false ∨ valuationOf q 272 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause720 (q : Snake 81) (h : Conditions q) : valuation q 256 = false ∨ valuation q 272 = true := counterClause720 (baseVal q)

theorem counterClause721 (q : Nat → Bool) : valuationOf q 138 = false ∨ valuationOf q 275 = true := by
  have hs : count275 q = (countLit q [138]) + (countLit q [139, 140]) := List.countP_append (p := literal q) (l₁ := [138]) (l₂ := [139, 140])
  have hm := merge_left (literal (valuationOf q) (138)) (literal (valuationOf q) (275)) (countLit q [138]) (countLit q [139, 140]) (count275 q) 1 (meaning138 q) (meaning275 q) hs
  change valuationOf q 138 = false ∨ valuationOf q 275 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause721 (q : Snake 81) (h : Conditions q) : valuation q 138 = false ∨ valuation q 275 = true := counterClause721 (baseVal q)

theorem counterClause722 (q : Nat → Bool) : valuationOf q 142 = false ∨ valuationOf q 277 = true := by
  have hs : count277 q = (countLit q [141]) + (countLit q [142]) := List.countP_append (p := literal q) (l₁ := [141]) (l₂ := [142])
  have hm := merge_right (literal (valuationOf q) (142)) (literal (valuationOf q) (277)) (countLit q [141]) (countLit q [142]) (count277 q) 1 (meaning142 q) (meaning277 q) hs
  change valuationOf q 142 = false ∨ valuationOf q 277 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause722 (q : Snake 81) (h : Conditions q) : valuation q 142 = false ∨ valuation q 277 = true := counterClause722 (baseVal q)

theorem counterClause723 (q : Nat → Bool) : valuationOf q 141 = false ∨ valuationOf q 277 = true := by
  have hs : count277 q = (countLit q [141]) + (countLit q [142]) := List.countP_append (p := literal q) (l₁ := [141]) (l₂ := [142])
  have hm := merge_left (literal (valuationOf q) (141)) (literal (valuationOf q) (277)) (countLit q [141]) (countLit q [142]) (count277 q) 1 (meaning141 q) (meaning277 q) hs
  change valuationOf q 141 = false ∨ valuationOf q 277 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause723 (q : Snake 81) (h : Conditions q) : valuation q 141 = false ∨ valuation q 277 = true := counterClause723 (baseVal q)

theorem counterClause724 (q : Nat → Bool) : valuationOf q 141 = false ∨ valuationOf q 142 = false ∨ valuationOf q 278 = true := by
  have hs : count277 q = (countLit q [141]) + (countLit q [142]) := List.countP_append (p := literal q) (l₁ := [141]) (l₂ := [142])
  have hm := merge_two (literal (valuationOf q) (141)) (literal (valuationOf q) (142)) (literal (valuationOf q) (278)) (countLit q [141]) (countLit q [142]) (count277 q) 1 1 (meaning141 q) (meaning142 q) (meaning278 q) hs
  change valuationOf q 141 = false ∨ valuationOf q 142 = false ∨ valuationOf q 278 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause724 (q : Snake 81) (h : Conditions q) : valuation q 141 = false ∨ valuation q 142 = false ∨ valuation q 278 = true := counterClause724 (baseVal q)

theorem counterClause725 (q : Nat → Bool) : valuationOf q 277 = false ∨ valuationOf q 281 = true := by
  have hs : count281 q = (countLit q [141, 142]) + (countLit q [143, 144]) := List.countP_append (p := literal q) (l₁ := [141, 142]) (l₂ := [143, 144])
  have hm := merge_left (literal (valuationOf q) (277)) (literal (valuationOf q) (281)) (countLit q [141, 142]) (countLit q [143, 144]) (count281 q) 1 (meaning277 q) (meaning281 q) hs
  change valuationOf q 277 = false ∨ valuationOf q 281 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause725 (q : Snake 81) (h : Conditions q) : valuation q 277 = false ∨ valuation q 281 = true := counterClause725 (baseVal q)

theorem counterClause726 (q : Nat → Bool) : valuationOf q 278 = false ∨ valuationOf q 282 = true := by
  have hs : count281 q = (countLit q [141, 142]) + (countLit q [143, 144]) := List.countP_append (p := literal q) (l₁ := [141, 142]) (l₂ := [143, 144])
  have hm := merge_left (literal (valuationOf q) (278)) (literal (valuationOf q) (282)) (countLit q [141, 142]) (countLit q [143, 144]) (count281 q) 2 (meaning278 q) (meaning282 q) hs
  change valuationOf q 278 = false ∨ valuationOf q 282 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause726 (q : Snake 81) (h : Conditions q) : valuation q 278 = false ∨ valuation q 282 = true := counterClause726 (baseVal q)

theorem counterClause727 (q : Nat → Bool) : valuationOf q 281 = false ∨ valuationOf q 283 = true := by
  have hs : count283 q = (countLit q [138, 139, 140]) + (countLit q [141, 142, 143, 144]) := List.countP_append (p := literal q) (l₁ := [138, 139, 140]) (l₂ := [141, 142, 143, 144])
  have hm := merge_right (literal (valuationOf q) (281)) (literal (valuationOf q) (283)) (countLit q [138, 139, 140]) (countLit q [141, 142, 143, 144]) (count283 q) 1 (meaning281 q) (meaning283 q) hs
  change valuationOf q 281 = false ∨ valuationOf q 283 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause727 (q : Snake 81) (h : Conditions q) : valuation q 281 = false ∨ valuation q 283 = true := counterClause727 (baseVal q)

theorem counterClause728 (q : Nat → Bool) : valuationOf q 282 = false ∨ valuationOf q 284 = true := by
  have hs : count283 q = (countLit q [138, 139, 140]) + (countLit q [141, 142, 143, 144]) := List.countP_append (p := literal q) (l₁ := [138, 139, 140]) (l₂ := [141, 142, 143, 144])
  have hm := merge_right (literal (valuationOf q) (282)) (literal (valuationOf q) (284)) (countLit q [138, 139, 140]) (countLit q [141, 142, 143, 144]) (count283 q) 2 (meaning282 q) (meaning284 q) hs
  change valuationOf q 282 = false ∨ valuationOf q 284 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause728 (q : Snake 81) (h : Conditions q) : valuation q 282 = false ∨ valuation q 284 = true := counterClause728 (baseVal q)

theorem counterClause729 (q : Nat → Bool) : valuationOf q 275 = false ∨ valuationOf q 283 = true := by
  have hs : count283 q = (countLit q [138, 139, 140]) + (countLit q [141, 142, 143, 144]) := List.countP_append (p := literal q) (l₁ := [138, 139, 140]) (l₂ := [141, 142, 143, 144])
  have hm := merge_left (literal (valuationOf q) (275)) (literal (valuationOf q) (283)) (countLit q [138, 139, 140]) (countLit q [141, 142, 143, 144]) (count283 q) 1 (meaning275 q) (meaning283 q) hs
  change valuationOf q 275 = false ∨ valuationOf q 283 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause729 (q : Snake 81) (h : Conditions q) : valuation q 275 = false ∨ valuation q 283 = true := counterClause729 (baseVal q)

theorem counterClause730 (q : Nat → Bool) : valuationOf q 275 = false ∨ valuationOf q 281 = false ∨ valuationOf q 284 = true := by
  have hs : count283 q = (countLit q [138, 139, 140]) + (countLit q [141, 142, 143, 144]) := List.countP_append (p := literal q) (l₁ := [138, 139, 140]) (l₂ := [141, 142, 143, 144])
  have hm := merge_two (literal (valuationOf q) (275)) (literal (valuationOf q) (281)) (literal (valuationOf q) (284)) (countLit q [138, 139, 140]) (countLit q [141, 142, 143, 144]) (count283 q) 1 1 (meaning275 q) (meaning281 q) (meaning284 q) hs
  change valuationOf q 275 = false ∨ valuationOf q 281 = false ∨ valuationOf q 284 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause730 (q : Snake 81) (h : Conditions q) : valuation q 275 = false ∨ valuation q 281 = false ∨ valuation q 284 = true := counterClause730 (baseVal q)

theorem counterClause731 (q : Nat → Bool) : valuationOf q 146 = false ∨ valuationOf q 285 = true := by
  have hs : count285 q = (countLit q [145]) + (countLit q [146]) := List.countP_append (p := literal q) (l₁ := [145]) (l₂ := [146])
  have hm := merge_right (literal (valuationOf q) (146)) (literal (valuationOf q) (285)) (countLit q [145]) (countLit q [146]) (count285 q) 1 (meaning146 q) (meaning285 q) hs
  change valuationOf q 146 = false ∨ valuationOf q 285 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause731 (q : Snake 81) (h : Conditions q) : valuation q 146 = false ∨ valuation q 285 = true := counterClause731 (baseVal q)

theorem counterClause732 (q : Nat → Bool) : valuationOf q 145 = false ∨ valuationOf q 285 = true := by
  have hs : count285 q = (countLit q [145]) + (countLit q [146]) := List.countP_append (p := literal q) (l₁ := [145]) (l₂ := [146])
  have hm := merge_left (literal (valuationOf q) (145)) (literal (valuationOf q) (285)) (countLit q [145]) (countLit q [146]) (count285 q) 1 (meaning145 q) (meaning285 q) hs
  change valuationOf q 145 = false ∨ valuationOf q 285 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause732 (q : Snake 81) (h : Conditions q) : valuation q 145 = false ∨ valuation q 285 = true := counterClause732 (baseVal q)

theorem counterClause733 (q : Nat → Bool) : valuationOf q 148 = false ∨ valuationOf q 287 = true := by
  have hs : count287 q = (countLit q [147]) + (countLit q [148]) := List.countP_append (p := literal q) (l₁ := [147]) (l₂ := [148])
  have hm := merge_right (literal (valuationOf q) (148)) (literal (valuationOf q) (287)) (countLit q [147]) (countLit q [148]) (count287 q) 1 (meaning148 q) (meaning287 q) hs
  change valuationOf q 148 = false ∨ valuationOf q 287 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause733 (q : Snake 81) (h : Conditions q) : valuation q 148 = false ∨ valuation q 287 = true := counterClause733 (baseVal q)

theorem counterClause734 (q : Nat → Bool) : valuationOf q 287 = false ∨ valuationOf q 289 = true := by
  have hs : count289 q = (countLit q [145, 146]) + (countLit q [147, 148]) := List.countP_append (p := literal q) (l₁ := [145, 146]) (l₂ := [147, 148])
  have hm := merge_right (literal (valuationOf q) (287)) (literal (valuationOf q) (289)) (countLit q [145, 146]) (countLit q [147, 148]) (count289 q) 1 (meaning287 q) (meaning289 q) hs
  change valuationOf q 287 = false ∨ valuationOf q 289 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause734 (q : Snake 81) (h : Conditions q) : valuation q 287 = false ∨ valuation q 289 = true := counterClause734 (baseVal q)

theorem counterClause735 (q : Nat → Bool) : valuationOf q 285 = false ∨ valuationOf q 289 = true := by
  have hs : count289 q = (countLit q [145, 146]) + (countLit q [147, 148]) := List.countP_append (p := literal q) (l₁ := [145, 146]) (l₂ := [147, 148])
  have hm := merge_left (literal (valuationOf q) (285)) (literal (valuationOf q) (289)) (countLit q [145, 146]) (countLit q [147, 148]) (count289 q) 1 (meaning285 q) (meaning289 q) hs
  change valuationOf q 285 = false ∨ valuationOf q 289 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause735 (q : Snake 81) (h : Conditions q) : valuation q 285 = false ∨ valuation q 289 = true := counterClause735 (baseVal q)

theorem counterClause736 (q : Nat → Bool) : valuationOf q 149 = false ∨ valuationOf q 291 = true := by
  have hs : count291 q = (countLit q [149]) + (countLit q [150]) := List.countP_append (p := literal q) (l₁ := [149]) (l₂ := [150])
  have hm := merge_left (literal (valuationOf q) (149)) (literal (valuationOf q) (291)) (countLit q [149]) (countLit q [150]) (count291 q) 1 (meaning149 q) (meaning291 q) hs
  change valuationOf q 149 = false ∨ valuationOf q 291 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause736 (q : Snake 81) (h : Conditions q) : valuation q 149 = false ∨ valuation q 291 = true := counterClause736 (baseVal q)

theorem block22 (q : Snake 81) (h : Conditions q) : B112E258.Block22 (valuation q) :=
  ⟨clause705 q h, clause706 q h, clause707 q h, clause708 q h, clause709 q h, clause710 q h, clause711 q h, clause712 q h, clause713 q h, clause714 q h, clause715 q h, clause716 q h, clause717 q h, clause718 q h, clause719 q h, clause720 q h, clause721 q h, clause722 q h, clause723 q h, clause724 q h, clause725 q h, clause726 q h, clause727 q h, clause728 q h, clause729 q h, clause730 q h, clause731 q h, clause732 q h, clause733 q h, clause734 q h, clause735 q h, clause736 q h⟩

end
end Snake9.Regrowth.E112258
