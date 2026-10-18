import E112213Semantics
import B112E213Inputs
namespace Snake9.Regrowth.E112213
noncomputable section
local instance blockDec18 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause577 (q : Nat → Bool) : valuationOf q 247 = false ∨ valuationOf q 249 = true := by
  have hs : count249 q = (countLit q [125]) + (countLit q [126, 127]) := List.countP_append (p := literal q) (l₁ := [125]) (l₂ := [126, 127])
  have hm := merge_right (literal (valuationOf q) (247)) (literal (valuationOf q) (249)) (countLit q [125]) (countLit q [126, 127]) (count249 q) 1 (meaning247 q) (meaning249 q) hs
  change valuationOf q 247 = false ∨ valuationOf q 249 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause577 (q : Snake 81) (h : Conditions q) : valuation q 247 = false ∨ valuation q 249 = true := counterClause577 (baseVal q)

theorem counterClause578 (q : Nat → Bool) : valuationOf q 129 = false ∨ valuationOf q 251 = true := by
  have hs : count251 q = (countLit q [128]) + (countLit q [129]) := List.countP_append (p := literal q) (l₁ := [128]) (l₂ := [129])
  have hm := merge_right (literal (valuationOf q) (129)) (literal (valuationOf q) (251)) (countLit q [128]) (countLit q [129]) (count251 q) 1 (meaning129 q) (meaning251 q) hs
  change valuationOf q 129 = false ∨ valuationOf q 251 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause578 (q : Snake 81) (h : Conditions q) : valuation q 129 = false ∨ valuation q 251 = true := counterClause578 (baseVal q)

theorem counterClause579 (q : Nat → Bool) : valuationOf q 251 = false ∨ valuationOf q 255 = true := by
  have hs : count255 q = (countLit q [128, 129]) + (countLit q [130, 131]) := List.countP_append (p := literal q) (l₁ := [128, 129]) (l₂ := [130, 131])
  have hm := merge_left (literal (valuationOf q) (251)) (literal (valuationOf q) (255)) (countLit q [128, 129]) (countLit q [130, 131]) (count255 q) 1 (meaning251 q) (meaning255 q) hs
  change valuationOf q 251 = false ∨ valuationOf q 255 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause579 (q : Snake 81) (h : Conditions q) : valuation q 251 = false ∨ valuation q 255 = true := counterClause579 (baseVal q)

theorem counterClause580 (q : Nat → Bool) : valuationOf q 255 = false ∨ valuationOf q 257 = true := by
  have hs : count257 q = (countLit q [125, 126, 127]) + (countLit q [128, 129, 130, 131]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127]) (l₂ := [128, 129, 130, 131])
  have hm := merge_right (literal (valuationOf q) (255)) (literal (valuationOf q) (257)) (countLit q [125, 126, 127]) (countLit q [128, 129, 130, 131]) (count257 q) 1 (meaning255 q) (meaning257 q) hs
  change valuationOf q 255 = false ∨ valuationOf q 257 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause580 (q : Snake 81) (h : Conditions q) : valuation q 255 = false ∨ valuation q 257 = true := counterClause580 (baseVal q)

theorem counterClause581 (q : Nat → Bool) : valuationOf q 249 = false ∨ valuationOf q 257 = true := by
  have hs : count257 q = (countLit q [125, 126, 127]) + (countLit q [128, 129, 130, 131]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127]) (l₂ := [128, 129, 130, 131])
  have hm := merge_left (literal (valuationOf q) (249)) (literal (valuationOf q) (257)) (countLit q [125, 126, 127]) (countLit q [128, 129, 130, 131]) (count257 q) 1 (meaning249 q) (meaning257 q) hs
  change valuationOf q 249 = false ∨ valuationOf q 257 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause581 (q : Snake 81) (h : Conditions q) : valuation q 249 = false ∨ valuation q 257 = true := counterClause581 (baseVal q)

theorem counterClause582 (q : Nat → Bool) : valuationOf q 249 = false ∨ valuationOf q 255 = false ∨ valuationOf q 258 = true := by
  have hs : count257 q = (countLit q [125, 126, 127]) + (countLit q [128, 129, 130, 131]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127]) (l₂ := [128, 129, 130, 131])
  have hm := merge_two (literal (valuationOf q) (249)) (literal (valuationOf q) (255)) (literal (valuationOf q) (258)) (countLit q [125, 126, 127]) (countLit q [128, 129, 130, 131]) (count257 q) 1 1 (meaning249 q) (meaning255 q) (meaning258 q) hs
  change valuationOf q 249 = false ∨ valuationOf q 255 = false ∨ valuationOf q 258 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause582 (q : Snake 81) (h : Conditions q) : valuation q 249 = false ∨ valuation q 255 = false ∨ valuation q 258 = true := counterClause582 (baseVal q)

theorem counterClause583 (q : Nat → Bool) : valuationOf q 257 = false ∨ valuationOf q 259 = true := by
  have hs : count259 q = (countLit q [118, 119, 120, 121, 122, 123, 124]) + (countLit q [125, 126, 127, 128, 129, 130, 131]) := List.countP_append (p := literal q) (l₁ := [118, 119, 120, 121, 122, 123, 124]) (l₂ := [125, 126, 127, 128, 129, 130, 131])
  have hm := merge_right (literal (valuationOf q) (257)) (literal (valuationOf q) (259)) (countLit q [118, 119, 120, 121, 122, 123, 124]) (countLit q [125, 126, 127, 128, 129, 130, 131]) (count259 q) 1 (meaning257 q) (meaning259 q) hs
  change valuationOf q 257 = false ∨ valuationOf q 259 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause583 (q : Snake 81) (h : Conditions q) : valuation q 257 = false ∨ valuation q 259 = true := counterClause583 (baseVal q)

theorem counterClause584 (q : Nat → Bool) : valuationOf q 258 = false ∨ valuationOf q 260 = true := by
  have hs : count259 q = (countLit q [118, 119, 120, 121, 122, 123, 124]) + (countLit q [125, 126, 127, 128, 129, 130, 131]) := List.countP_append (p := literal q) (l₁ := [118, 119, 120, 121, 122, 123, 124]) (l₂ := [125, 126, 127, 128, 129, 130, 131])
  have hm := merge_right (literal (valuationOf q) (258)) (literal (valuationOf q) (260)) (countLit q [118, 119, 120, 121, 122, 123, 124]) (countLit q [125, 126, 127, 128, 129, 130, 131]) (count259 q) 2 (meaning258 q) (meaning260 q) hs
  change valuationOf q 258 = false ∨ valuationOf q 260 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause584 (q : Snake 81) (h : Conditions q) : valuation q 258 = false ∨ valuation q 260 = true := counterClause584 (baseVal q)

theorem counterClause585 (q : Nat → Bool) : valuationOf q 245 = false ∨ valuationOf q 259 = true := by
  have hs : count259 q = (countLit q [118, 119, 120, 121, 122, 123, 124]) + (countLit q [125, 126, 127, 128, 129, 130, 131]) := List.countP_append (p := literal q) (l₁ := [118, 119, 120, 121, 122, 123, 124]) (l₂ := [125, 126, 127, 128, 129, 130, 131])
  have hm := merge_left (literal (valuationOf q) (245)) (literal (valuationOf q) (259)) (countLit q [118, 119, 120, 121, 122, 123, 124]) (countLit q [125, 126, 127, 128, 129, 130, 131]) (count259 q) 1 (meaning245 q) (meaning259 q) hs
  change valuationOf q 245 = false ∨ valuationOf q 259 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause585 (q : Snake 81) (h : Conditions q) : valuation q 245 = false ∨ valuation q 259 = true := counterClause585 (baseVal q)

theorem counterClause586 (q : Nat → Bool) : valuationOf q 245 = false ∨ valuationOf q 257 = false ∨ valuationOf q 260 = true := by
  have hs : count259 q = (countLit q [118, 119, 120, 121, 122, 123, 124]) + (countLit q [125, 126, 127, 128, 129, 130, 131]) := List.countP_append (p := literal q) (l₁ := [118, 119, 120, 121, 122, 123, 124]) (l₂ := [125, 126, 127, 128, 129, 130, 131])
  have hm := merge_two (literal (valuationOf q) (245)) (literal (valuationOf q) (257)) (literal (valuationOf q) (260)) (countLit q [118, 119, 120, 121, 122, 123, 124]) (countLit q [125, 126, 127, 128, 129, 130, 131]) (count259 q) 1 1 (meaning245 q) (meaning257 q) (meaning260 q) hs
  change valuationOf q 245 = false ∨ valuationOf q 257 = false ∨ valuationOf q 260 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause586 (q : Snake 81) (h : Conditions q) : valuation q 245 = false ∨ valuation q 257 = false ∨ valuation q 260 = true := counterClause586 (baseVal q)

theorem counterClause587 (q : Nat → Bool) : valuationOf q 246 = false ∨ valuationOf q 260 = true := by
  have hs : count259 q = (countLit q [118, 119, 120, 121, 122, 123, 124]) + (countLit q [125, 126, 127, 128, 129, 130, 131]) := List.countP_append (p := literal q) (l₁ := [118, 119, 120, 121, 122, 123, 124]) (l₂ := [125, 126, 127, 128, 129, 130, 131])
  have hm := merge_left (literal (valuationOf q) (246)) (literal (valuationOf q) (260)) (countLit q [118, 119, 120, 121, 122, 123, 124]) (countLit q [125, 126, 127, 128, 129, 130, 131]) (count259 q) 2 (meaning246 q) (meaning260 q) hs
  change valuationOf q 246 = false ∨ valuationOf q 260 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause587 (q : Snake 81) (h : Conditions q) : valuation q 246 = false ∨ valuation q 260 = true := counterClause587 (baseVal q)

theorem counterClause588 (q : Nat → Bool) : valuationOf q 136 = false ∨ valuationOf q 265 = true := by
  have hs : count265 q = (countLit q [135]) + (countLit q [136]) := List.countP_append (p := literal q) (l₁ := [135]) (l₂ := [136])
  have hm := merge_right (literal (valuationOf q) (136)) (literal (valuationOf q) (265)) (countLit q [135]) (countLit q [136]) (count265 q) 1 (meaning136 q) (meaning265 q) hs
  change valuationOf q 136 = false ∨ valuationOf q 265 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause588 (q : Snake 81) (h : Conditions q) : valuation q 136 = false ∨ valuation q 265 = true := counterClause588 (baseVal q)

theorem counterClause589 (q : Nat → Bool) : valuationOf q 135 = false ∨ valuationOf q 265 = true := by
  have hs : count265 q = (countLit q [135]) + (countLit q [136]) := List.countP_append (p := literal q) (l₁ := [135]) (l₂ := [136])
  have hm := merge_left (literal (valuationOf q) (135)) (literal (valuationOf q) (265)) (countLit q [135]) (countLit q [136]) (count265 q) 1 (meaning135 q) (meaning265 q) hs
  change valuationOf q 135 = false ∨ valuationOf q 265 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause589 (q : Snake 81) (h : Conditions q) : valuation q 135 = false ∨ valuation q 265 = true := counterClause589 (baseVal q)

theorem counterClause590 (q : Nat → Bool) : valuationOf q 135 = false ∨ valuationOf q 136 = false ∨ valuationOf q 266 = true := by
  have hs : count265 q = (countLit q [135]) + (countLit q [136]) := List.countP_append (p := literal q) (l₁ := [135]) (l₂ := [136])
  have hm := merge_two (literal (valuationOf q) (135)) (literal (valuationOf q) (136)) (literal (valuationOf q) (266)) (countLit q [135]) (countLit q [136]) (count265 q) 1 1 (meaning135 q) (meaning136 q) (meaning266 q) hs
  change valuationOf q 135 = false ∨ valuationOf q 136 = false ∨ valuationOf q 266 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause590 (q : Snake 81) (h : Conditions q) : valuation q 135 = false ∨ valuation q 136 = false ∨ valuation q 266 = true := counterClause590 (baseVal q)

theorem counterClause591 (q : Nat → Bool) : valuationOf q 265 = false ∨ valuationOf q 269 = true := by
  have hs : count269 q = (countLit q [135, 136]) + (countLit q [137, 138]) := List.countP_append (p := literal q) (l₁ := [135, 136]) (l₂ := [137, 138])
  have hm := merge_left (literal (valuationOf q) (265)) (literal (valuationOf q) (269)) (countLit q [135, 136]) (countLit q [137, 138]) (count269 q) 1 (meaning265 q) (meaning269 q) hs
  change valuationOf q 265 = false ∨ valuationOf q 269 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause591 (q : Snake 81) (h : Conditions q) : valuation q 265 = false ∨ valuation q 269 = true := counterClause591 (baseVal q)

theorem counterClause592 (q : Nat → Bool) : valuationOf q 266 = false ∨ valuationOf q 270 = true := by
  have hs : count269 q = (countLit q [135, 136]) + (countLit q [137, 138]) := List.countP_append (p := literal q) (l₁ := [135, 136]) (l₂ := [137, 138])
  have hm := merge_left (literal (valuationOf q) (266)) (literal (valuationOf q) (270)) (countLit q [135, 136]) (countLit q [137, 138]) (count269 q) 2 (meaning266 q) (meaning270 q) hs
  change valuationOf q 266 = false ∨ valuationOf q 270 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause592 (q : Snake 81) (h : Conditions q) : valuation q 266 = false ∨ valuation q 270 = true := counterClause592 (baseVal q)

theorem counterClause593 (q : Nat → Bool) : valuationOf q 269 = false ∨ valuationOf q 271 = true := by
  have hs : count271 q = (countLit q [132, 133, 134]) + (countLit q [135, 136, 137, 138]) := List.countP_append (p := literal q) (l₁ := [132, 133, 134]) (l₂ := [135, 136, 137, 138])
  have hm := merge_right (literal (valuationOf q) (269)) (literal (valuationOf q) (271)) (countLit q [132, 133, 134]) (countLit q [135, 136, 137, 138]) (count271 q) 1 (meaning269 q) (meaning271 q) hs
  change valuationOf q 269 = false ∨ valuationOf q 271 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause593 (q : Snake 81) (h : Conditions q) : valuation q 269 = false ∨ valuation q 271 = true := counterClause593 (baseVal q)

theorem counterClause594 (q : Nat → Bool) : valuationOf q 270 = false ∨ valuationOf q 272 = true := by
  have hs : count271 q = (countLit q [132, 133, 134]) + (countLit q [135, 136, 137, 138]) := List.countP_append (p := literal q) (l₁ := [132, 133, 134]) (l₂ := [135, 136, 137, 138])
  have hm := merge_right (literal (valuationOf q) (270)) (literal (valuationOf q) (272)) (countLit q [132, 133, 134]) (countLit q [135, 136, 137, 138]) (count271 q) 2 (meaning270 q) (meaning272 q) hs
  change valuationOf q 270 = false ∨ valuationOf q 272 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause594 (q : Snake 81) (h : Conditions q) : valuation q 270 = false ∨ valuation q 272 = true := counterClause594 (baseVal q)

theorem counterClause595 (q : Nat → Bool) : valuationOf q 143 = false ∨ valuationOf q 279 = true := by
  have hs : count279 q = (countLit q [143]) + (countLit q [144]) := List.countP_append (p := literal q) (l₁ := [143]) (l₂ := [144])
  have hm := merge_left (literal (valuationOf q) (143)) (literal (valuationOf q) (279)) (countLit q [143]) (countLit q [144]) (count279 q) 1 (meaning143 q) (meaning279 q) hs
  change valuationOf q 143 = false ∨ valuationOf q 279 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause595 (q : Snake 81) (h : Conditions q) : valuation q 143 = false ∨ valuation q 279 = true := counterClause595 (baseVal q)

theorem counterClause596 (q : Nat → Bool) : valuationOf q 145 = false ∨ valuationOf q 281 = true := by
  have hs : count281 q = (countLit q [145]) + (countLit q [146]) := List.countP_append (p := literal q) (l₁ := [145]) (l₂ := [146])
  have hm := merge_left (literal (valuationOf q) (145)) (literal (valuationOf q) (281)) (countLit q [145]) (countLit q [146]) (count281 q) 1 (meaning145 q) (meaning281 q) hs
  change valuationOf q 145 = false ∨ valuationOf q 281 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause596 (q : Snake 81) (h : Conditions q) : valuation q 145 = false ∨ valuation q 281 = true := counterClause596 (baseVal q)

theorem counterClause597 (q : Nat → Bool) : valuationOf q 281 = false ∨ valuationOf q 283 = true := by
  have hs : count283 q = (countLit q [143, 144]) + (countLit q [145, 146]) := List.countP_append (p := literal q) (l₁ := [143, 144]) (l₂ := [145, 146])
  have hm := merge_right (literal (valuationOf q) (281)) (literal (valuationOf q) (283)) (countLit q [143, 144]) (countLit q [145, 146]) (count283 q) 1 (meaning281 q) (meaning283 q) hs
  change valuationOf q 281 = false ∨ valuationOf q 283 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause597 (q : Snake 81) (h : Conditions q) : valuation q 281 = false ∨ valuation q 283 = true := counterClause597 (baseVal q)

theorem counterClause598 (q : Nat → Bool) : valuationOf q 279 = false ∨ valuationOf q 283 = true := by
  have hs : count283 q = (countLit q [143, 144]) + (countLit q [145, 146]) := List.countP_append (p := literal q) (l₁ := [143, 144]) (l₂ := [145, 146])
  have hm := merge_left (literal (valuationOf q) (279)) (literal (valuationOf q) (283)) (countLit q [143, 144]) (countLit q [145, 146]) (count283 q) 1 (meaning279 q) (meaning283 q) hs
  change valuationOf q 279 = false ∨ valuationOf q 283 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause598 (q : Snake 81) (h : Conditions q) : valuation q 279 = false ∨ valuation q 283 = true := counterClause598 (baseVal q)

theorem counterClause599 (q : Nat → Bool) : valuationOf q 283 = false ∨ valuationOf q 285 = true := by
  have hs : count285 q = (countLit q [139, 140, 141, 142]) + (countLit q [143, 144, 145, 146]) := List.countP_append (p := literal q) (l₁ := [139, 140, 141, 142]) (l₂ := [143, 144, 145, 146])
  have hm := merge_right (literal (valuationOf q) (283)) (literal (valuationOf q) (285)) (countLit q [139, 140, 141, 142]) (countLit q [143, 144, 145, 146]) (count285 q) 1 (meaning283 q) (meaning285 q) hs
  change valuationOf q 283 = false ∨ valuationOf q 285 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause599 (q : Snake 81) (h : Conditions q) : valuation q 283 = false ∨ valuation q 285 = true := counterClause599 (baseVal q)

theorem counterClause600 (q : Nat → Bool) : valuationOf q 285 = false ∨ valuationOf q 287 = true := by
  have hs : count287 q = (countLit q [132, 133, 134, 135, 136, 137, 138]) + (countLit q [139, 140, 141, 142, 143, 144, 145, 146]) := List.countP_append (p := literal q) (l₁ := [132, 133, 134, 135, 136, 137, 138]) (l₂ := [139, 140, 141, 142, 143, 144, 145, 146])
  have hm := merge_right (literal (valuationOf q) (285)) (literal (valuationOf q) (287)) (countLit q [132, 133, 134, 135, 136, 137, 138]) (countLit q [139, 140, 141, 142, 143, 144, 145, 146]) (count287 q) 1 (meaning285 q) (meaning287 q) hs
  change valuationOf q 285 = false ∨ valuationOf q 287 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause600 (q : Snake 81) (h : Conditions q) : valuation q 285 = false ∨ valuation q 287 = true := counterClause600 (baseVal q)

theorem counterClause601 (q : Nat → Bool) : valuationOf q 271 = false ∨ valuationOf q 287 = true := by
  have hs : count287 q = (countLit q [132, 133, 134, 135, 136, 137, 138]) + (countLit q [139, 140, 141, 142, 143, 144, 145, 146]) := List.countP_append (p := literal q) (l₁ := [132, 133, 134, 135, 136, 137, 138]) (l₂ := [139, 140, 141, 142, 143, 144, 145, 146])
  have hm := merge_left (literal (valuationOf q) (271)) (literal (valuationOf q) (287)) (countLit q [132, 133, 134, 135, 136, 137, 138]) (countLit q [139, 140, 141, 142, 143, 144, 145, 146]) (count287 q) 1 (meaning271 q) (meaning287 q) hs
  change valuationOf q 271 = false ∨ valuationOf q 287 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause601 (q : Snake 81) (h : Conditions q) : valuation q 271 = false ∨ valuation q 287 = true := counterClause601 (baseVal q)

theorem counterClause602 (q : Nat → Bool) : valuationOf q 272 = false ∨ valuationOf q 288 = true := by
  have hs : count287 q = (countLit q [132, 133, 134, 135, 136, 137, 138]) + (countLit q [139, 140, 141, 142, 143, 144, 145, 146]) := List.countP_append (p := literal q) (l₁ := [132, 133, 134, 135, 136, 137, 138]) (l₂ := [139, 140, 141, 142, 143, 144, 145, 146])
  have hm := merge_left (literal (valuationOf q) (272)) (literal (valuationOf q) (288)) (countLit q [132, 133, 134, 135, 136, 137, 138]) (countLit q [139, 140, 141, 142, 143, 144, 145, 146]) (count287 q) 2 (meaning272 q) (meaning288 q) hs
  change valuationOf q 272 = false ∨ valuationOf q 288 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause602 (q : Snake 81) (h : Conditions q) : valuation q 272 = false ∨ valuation q 288 = true := counterClause602 (baseVal q)

theorem counterClause603 (q : Nat → Bool) : valuationOf q 287 = false ∨ valuationOf q 289 = true := by
  have hs : count289 q = (countLit q [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131]) + (countLit q [132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146]) := List.countP_append (p := literal q) (l₁ := [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131]) (l₂ := [132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146])
  have hm := merge_right (literal (valuationOf q) (287)) (literal (valuationOf q) (289)) (countLit q [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131]) (countLit q [132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146]) (count289 q) 1 (meaning287 q) (meaning289 q) hs
  change valuationOf q 287 = false ∨ valuationOf q 289 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause603 (q : Snake 81) (h : Conditions q) : valuation q 287 = false ∨ valuation q 289 = true := counterClause603 (baseVal q)

theorem counterClause604 (q : Nat → Bool) : valuationOf q 288 = false ∨ valuationOf q 290 = true := by
  have hs : count289 q = (countLit q [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131]) + (countLit q [132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146]) := List.countP_append (p := literal q) (l₁ := [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131]) (l₂ := [132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146])
  have hm := merge_right (literal (valuationOf q) (288)) (literal (valuationOf q) (290)) (countLit q [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131]) (countLit q [132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146]) (count289 q) 2 (meaning288 q) (meaning290 q) hs
  change valuationOf q 288 = false ∨ valuationOf q 290 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause604 (q : Snake 81) (h : Conditions q) : valuation q 288 = false ∨ valuation q 290 = true := counterClause604 (baseVal q)

theorem counterClause605 (q : Nat → Bool) : valuationOf q 259 = false ∨ valuationOf q 289 = true := by
  have hs : count289 q = (countLit q [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131]) + (countLit q [132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146]) := List.countP_append (p := literal q) (l₁ := [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131]) (l₂ := [132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146])
  have hm := merge_left (literal (valuationOf q) (259)) (literal (valuationOf q) (289)) (countLit q [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131]) (countLit q [132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146]) (count289 q) 1 (meaning259 q) (meaning289 q) hs
  change valuationOf q 259 = false ∨ valuationOf q 289 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause605 (q : Snake 81) (h : Conditions q) : valuation q 259 = false ∨ valuation q 289 = true := counterClause605 (baseVal q)

theorem counterClause606 (q : Nat → Bool) : valuationOf q 259 = false ∨ valuationOf q 287 = false ∨ valuationOf q 290 = true := by
  have hs : count289 q = (countLit q [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131]) + (countLit q [132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146]) := List.countP_append (p := literal q) (l₁ := [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131]) (l₂ := [132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146])
  have hm := merge_two (literal (valuationOf q) (259)) (literal (valuationOf q) (287)) (literal (valuationOf q) (290)) (countLit q [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131]) (countLit q [132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146]) (count289 q) 1 1 (meaning259 q) (meaning287 q) (meaning290 q) hs
  change valuationOf q 259 = false ∨ valuationOf q 287 = false ∨ valuationOf q 290 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause606 (q : Snake 81) (h : Conditions q) : valuation q 259 = false ∨ valuation q 287 = false ∨ valuation q 290 = true := counterClause606 (baseVal q)

theorem counterClause607 (q : Nat → Bool) : valuationOf q 260 = false ∨ valuationOf q 290 = true := by
  have hs : count289 q = (countLit q [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131]) + (countLit q [132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146]) := List.countP_append (p := literal q) (l₁ := [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131]) (l₂ := [132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146])
  have hm := merge_left (literal (valuationOf q) (260)) (literal (valuationOf q) (290)) (countLit q [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131]) (countLit q [132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146]) (count289 q) 2 (meaning260 q) (meaning290 q) hs
  change valuationOf q 260 = false ∨ valuationOf q 290 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause607 (q : Snake 81) (h : Conditions q) : valuation q 260 = false ∨ valuation q 290 = true := counterClause607 (baseVal q)

theorem counterClause608 (q : Nat → Bool) : valuationOf q 148 = false ∨ valuationOf q 291 = true := by
  have hs : count291 q = (countLit q [148]) + (countLit q [149]) := List.countP_append (p := literal q) (l₁ := [148]) (l₂ := [149])
  have hm := merge_left (literal (valuationOf q) (148)) (literal (valuationOf q) (291)) (countLit q [148]) (countLit q [149]) (count291 q) 1 (meaning148 q) (meaning291 q) hs
  change valuationOf q 148 = false ∨ valuationOf q 291 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause608 (q : Snake 81) (h : Conditions q) : valuation q 148 = false ∨ valuation q 291 = true := counterClause608 (baseVal q)

theorem block18 (q : Snake 81) (h : Conditions q) : B112E213.Block18 (valuation q) :=
  ⟨clause577 q h, clause578 q h, clause579 q h, clause580 q h, clause581 q h, clause582 q h, clause583 q h, clause584 q h, clause585 q h, clause586 q h, clause587 q h, clause588 q h, clause589 q h, clause590 q h, clause591 q h, clause592 q h, clause593 q h, clause594 q h, clause595 q h, clause596 q h, clause597 q h, clause598 q h, clause599 q h, clause600 q h, clause601 q h, clause602 q h, clause603 q h, clause604 q h, clause605 q h, clause606 q h, clause607 q h, clause608 q h⟩

end
end Snake9.Regrowth.E112213
