import E112107Semantics
import B112E107Inputs
namespace Snake9.Regrowth.E112107
noncomputable section
local instance blockDec8 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause257 (q : Nat → Bool) : valuationOf q 231 = false ∨ valuationOf q 233 = true := by
  have hs : count233 q = (countLit q [117]) + (countLit q [118, 119]) := List.countP_append (p := literal q) (l₁ := [117]) (l₂ := [118, 119])
  have hm := merge_right (literal (valuationOf q) (231)) (literal (valuationOf q) (233)) (countLit q [117]) (countLit q [118, 119]) (count233 q) 1 (meaning231 q) (meaning233 q) hs
  change valuationOf q 231 = false ∨ valuationOf q 233 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause257 (q : Snake 81) (h : Conditions q) : valuation q 231 = false ∨ valuation q 233 = true := counterClause257 (baseVal q)

theorem counterClause258 (q : Nat → Bool) : valuationOf q 121 = false ∨ valuationOf q 235 = true := by
  have hs : count235 q = (countLit q [120]) + (countLit q [121]) := List.countP_append (p := literal q) (l₁ := [120]) (l₂ := [121])
  have hm := merge_right (literal (valuationOf q) (121)) (literal (valuationOf q) (235)) (countLit q [120]) (countLit q [121]) (count235 q) 1 (meaning121 q) (meaning235 q) hs
  change valuationOf q 121 = false ∨ valuationOf q 235 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause258 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 235 = true := counterClause258 (baseVal q)

theorem counterClause259 (q : Nat → Bool) : valuationOf q 120 = false ∨ valuationOf q 235 = true := by
  have hs : count235 q = (countLit q [120]) + (countLit q [121]) := List.countP_append (p := literal q) (l₁ := [120]) (l₂ := [121])
  have hm := merge_left (literal (valuationOf q) (120)) (literal (valuationOf q) (235)) (countLit q [120]) (countLit q [121]) (count235 q) 1 (meaning120 q) (meaning235 q) hs
  change valuationOf q 120 = false ∨ valuationOf q 235 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause259 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 235 = true := counterClause259 (baseVal q)

theorem counterClause260 (q : Nat → Bool) : valuationOf q 235 = false ∨ valuationOf q 239 = true := by
  have hs : count239 q = (countLit q [120, 121]) + (countLit q [122, 123]) := List.countP_append (p := literal q) (l₁ := [120, 121]) (l₂ := [122, 123])
  have hm := merge_left (literal (valuationOf q) (235)) (literal (valuationOf q) (239)) (countLit q [120, 121]) (countLit q [122, 123]) (count239 q) 1 (meaning235 q) (meaning239 q) hs
  change valuationOf q 235 = false ∨ valuationOf q 239 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause260 (q : Snake 81) (h : Conditions q) : valuation q 235 = false ∨ valuation q 239 = true := counterClause260 (baseVal q)

theorem counterClause261 (q : Nat → Bool) : valuationOf q 239 = false ∨ valuationOf q 241 = true := by
  have hs : count241 q = (countLit q [117, 118, 119]) + (countLit q [120, 121, 122, 123]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119]) (l₂ := [120, 121, 122, 123])
  have hm := merge_right (literal (valuationOf q) (239)) (literal (valuationOf q) (241)) (countLit q [117, 118, 119]) (countLit q [120, 121, 122, 123]) (count241 q) 1 (meaning239 q) (meaning241 q) hs
  change valuationOf q 239 = false ∨ valuationOf q 241 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause261 (q : Snake 81) (h : Conditions q) : valuation q 239 = false ∨ valuation q 241 = true := counterClause261 (baseVal q)

theorem counterClause262 (q : Nat → Bool) : valuationOf q 233 = false ∨ valuationOf q 241 = true := by
  have hs : count241 q = (countLit q [117, 118, 119]) + (countLit q [120, 121, 122, 123]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119]) (l₂ := [120, 121, 122, 123])
  have hm := merge_left (literal (valuationOf q) (233)) (literal (valuationOf q) (241)) (countLit q [117, 118, 119]) (countLit q [120, 121, 122, 123]) (count241 q) 1 (meaning233 q) (meaning241 q) hs
  change valuationOf q 233 = false ∨ valuationOf q 241 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause262 (q : Snake 81) (h : Conditions q) : valuation q 233 = false ∨ valuation q 241 = true := counterClause262 (baseVal q)

theorem counterClause263 (q : Nat → Bool) : valuationOf q 241 = false ∨ valuationOf q 243 = true := by
  have hs : count243 q = (countLit q [111, 112, 113, 114, 115, 116]) + (countLit q [117, 118, 119, 120, 121, 122, 123]) := List.countP_append (p := literal q) (l₁ := [111, 112, 113, 114, 115, 116]) (l₂ := [117, 118, 119, 120, 121, 122, 123])
  have hm := merge_right (literal (valuationOf q) (241)) (literal (valuationOf q) (243)) (countLit q [111, 112, 113, 114, 115, 116]) (countLit q [117, 118, 119, 120, 121, 122, 123]) (count243 q) 1 (meaning241 q) (meaning243 q) hs
  change valuationOf q 241 = false ∨ valuationOf q 243 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause263 (q : Snake 81) (h : Conditions q) : valuation q 241 = false ∨ valuation q 243 = true := counterClause263 (baseVal q)

theorem counterClause264 (q : Nat → Bool) : valuationOf q 229 = false ∨ valuationOf q 243 = true := by
  have hs : count243 q = (countLit q [111, 112, 113, 114, 115, 116]) + (countLit q [117, 118, 119, 120, 121, 122, 123]) := List.countP_append (p := literal q) (l₁ := [111, 112, 113, 114, 115, 116]) (l₂ := [117, 118, 119, 120, 121, 122, 123])
  have hm := merge_left (literal (valuationOf q) (229)) (literal (valuationOf q) (243)) (countLit q [111, 112, 113, 114, 115, 116]) (countLit q [117, 118, 119, 120, 121, 122, 123]) (count243 q) 1 (meaning229 q) (meaning243 q) hs
  change valuationOf q 229 = false ∨ valuationOf q 243 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause264 (q : Snake 81) (h : Conditions q) : valuation q 229 = false ∨ valuation q 243 = true := counterClause264 (baseVal q)

theorem counterClause265 (q : Nat → Bool) : valuationOf q 229 = false ∨ valuationOf q 241 = false ∨ valuationOf q 244 = true := by
  have hs : count243 q = (countLit q [111, 112, 113, 114, 115, 116]) + (countLit q [117, 118, 119, 120, 121, 122, 123]) := List.countP_append (p := literal q) (l₁ := [111, 112, 113, 114, 115, 116]) (l₂ := [117, 118, 119, 120, 121, 122, 123])
  have hm := merge_two (literal (valuationOf q) (229)) (literal (valuationOf q) (241)) (literal (valuationOf q) (244)) (countLit q [111, 112, 113, 114, 115, 116]) (countLit q [117, 118, 119, 120, 121, 122, 123]) (count243 q) 1 1 (meaning229 q) (meaning241 q) (meaning244 q) hs
  change valuationOf q 229 = false ∨ valuationOf q 241 = false ∨ valuationOf q 244 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause265 (q : Snake 81) (h : Conditions q) : valuation q 229 = false ∨ valuation q 241 = false ∨ valuation q 244 = true := counterClause265 (baseVal q)

theorem counterClause266 (q : Nat → Bool) : valuationOf q 127 = false ∨ valuationOf q 245 = true := by
  have hs : count245 q = (countLit q [126]) + (countLit q [127]) := List.countP_append (p := literal q) (l₁ := [126]) (l₂ := [127])
  have hm := merge_right (literal (valuationOf q) (127)) (literal (valuationOf q) (245)) (countLit q [126]) (countLit q [127]) (count245 q) 1 (meaning127 q) (meaning245 q) hs
  change valuationOf q 127 = false ∨ valuationOf q 245 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause266 (q : Snake 81) (h : Conditions q) : valuation q 127 = false ∨ valuation q 245 = true := counterClause266 (baseVal q)

theorem counterClause267 (q : Nat → Bool) : valuationOf q 126 = false ∨ valuationOf q 245 = true := by
  have hs : count245 q = (countLit q [126]) + (countLit q [127]) := List.countP_append (p := literal q) (l₁ := [126]) (l₂ := [127])
  have hm := merge_left (literal (valuationOf q) (126)) (literal (valuationOf q) (245)) (countLit q [126]) (countLit q [127]) (count245 q) 1 (meaning126 q) (meaning245 q) hs
  change valuationOf q 126 = false ∨ valuationOf q 245 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause267 (q : Snake 81) (h : Conditions q) : valuation q 126 = false ∨ valuation q 245 = true := counterClause267 (baseVal q)

theorem counterClause268 (q : Nat → Bool) : valuationOf q 245 = false ∨ valuationOf q 247 = true := by
  have hs : count247 q = (countLit q [125]) + (countLit q [126, 127]) := List.countP_append (p := literal q) (l₁ := [125]) (l₂ := [126, 127])
  have hm := merge_right (literal (valuationOf q) (245)) (literal (valuationOf q) (247)) (countLit q [125]) (countLit q [126, 127]) (count247 q) 1 (meaning245 q) (meaning247 q) hs
  change valuationOf q 245 = false ∨ valuationOf q 247 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause268 (q : Snake 81) (h : Conditions q) : valuation q 245 = false ∨ valuation q 247 = true := counterClause268 (baseVal q)

theorem counterClause269 (q : Nat → Bool) : valuationOf q 131 = false ∨ valuationOf q 251 = true := by
  have hs : count251 q = (countLit q [130]) + (countLit q [131]) := List.countP_append (p := literal q) (l₁ := [130]) (l₂ := [131])
  have hm := merge_right (literal (valuationOf q) (131)) (literal (valuationOf q) (251)) (countLit q [130]) (countLit q [131]) (count251 q) 1 (meaning131 q) (meaning251 q) hs
  change valuationOf q 131 = false ∨ valuationOf q 251 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause269 (q : Snake 81) (h : Conditions q) : valuation q 131 = false ∨ valuation q 251 = true := counterClause269 (baseVal q)

theorem counterClause270 (q : Nat → Bool) : valuationOf q 251 = false ∨ valuationOf q 253 = true := by
  have hs : count253 q = (countLit q [128, 129]) + (countLit q [130, 131]) := List.countP_append (p := literal q) (l₁ := [128, 129]) (l₂ := [130, 131])
  have hm := merge_right (literal (valuationOf q) (251)) (literal (valuationOf q) (253)) (countLit q [128, 129]) (countLit q [130, 131]) (count253 q) 1 (meaning251 q) (meaning253 q) hs
  change valuationOf q 251 = false ∨ valuationOf q 253 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause270 (q : Snake 81) (h : Conditions q) : valuation q 251 = false ∨ valuation q 253 = true := counterClause270 (baseVal q)

theorem counterClause271 (q : Nat → Bool) : valuationOf q 253 = false ∨ valuationOf q 255 = true := by
  have hs : count255 q = (countLit q [125, 126, 127]) + (countLit q [128, 129, 130, 131]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127]) (l₂ := [128, 129, 130, 131])
  have hm := merge_right (literal (valuationOf q) (253)) (literal (valuationOf q) (255)) (countLit q [125, 126, 127]) (countLit q [128, 129, 130, 131]) (count255 q) 1 (meaning253 q) (meaning255 q) hs
  change valuationOf q 253 = false ∨ valuationOf q 255 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause271 (q : Snake 81) (h : Conditions q) : valuation q 253 = false ∨ valuation q 255 = true := counterClause271 (baseVal q)

theorem counterClause272 (q : Nat → Bool) : valuationOf q 247 = false ∨ valuationOf q 255 = true := by
  have hs : count255 q = (countLit q [125, 126, 127]) + (countLit q [128, 129, 130, 131]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127]) (l₂ := [128, 129, 130, 131])
  have hm := merge_left (literal (valuationOf q) (247)) (literal (valuationOf q) (255)) (countLit q [125, 126, 127]) (countLit q [128, 129, 130, 131]) (count255 q) 1 (meaning247 q) (meaning255 q) hs
  change valuationOf q 247 = false ∨ valuationOf q 255 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause272 (q : Snake 81) (h : Conditions q) : valuation q 247 = false ∨ valuation q 255 = true := counterClause272 (baseVal q)

theorem counterClause273 (q : Nat → Bool) : valuationOf q 247 = false ∨ valuationOf q 253 = false ∨ valuationOf q 256 = true := by
  have hs : count255 q = (countLit q [125, 126, 127]) + (countLit q [128, 129, 130, 131]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127]) (l₂ := [128, 129, 130, 131])
  have hm := merge_two (literal (valuationOf q) (247)) (literal (valuationOf q) (253)) (literal (valuationOf q) (256)) (countLit q [125, 126, 127]) (countLit q [128, 129, 130, 131]) (count255 q) 1 1 (meaning247 q) (meaning253 q) (meaning256 q) hs
  change valuationOf q 247 = false ∨ valuationOf q 253 = false ∨ valuationOf q 256 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause273 (q : Snake 81) (h : Conditions q) : valuation q 247 = false ∨ valuation q 253 = false ∨ valuation q 256 = true := counterClause273 (baseVal q)

theorem counterClause274 (q : Nat → Bool) : valuationOf q 134 = false ∨ valuationOf q 257 = true := by
  have hs : count257 q = (countLit q [133]) + (countLit q [134]) := List.countP_append (p := literal q) (l₁ := [133]) (l₂ := [134])
  have hm := merge_right (literal (valuationOf q) (134)) (literal (valuationOf q) (257)) (countLit q [133]) (countLit q [134]) (count257 q) 1 (meaning134 q) (meaning257 q) hs
  change valuationOf q 134 = false ∨ valuationOf q 257 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause274 (q : Snake 81) (h : Conditions q) : valuation q 134 = false ∨ valuation q 257 = true := counterClause274 (baseVal q)

theorem counterClause275 (q : Nat → Bool) : valuationOf q 133 = false ∨ valuationOf q 257 = true := by
  have hs : count257 q = (countLit q [133]) + (countLit q [134]) := List.countP_append (p := literal q) (l₁ := [133]) (l₂ := [134])
  have hm := merge_left (literal (valuationOf q) (133)) (literal (valuationOf q) (257)) (countLit q [133]) (countLit q [134]) (count257 q) 1 (meaning133 q) (meaning257 q) hs
  change valuationOf q 133 = false ∨ valuationOf q 257 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause275 (q : Snake 81) (h : Conditions q) : valuation q 133 = false ∨ valuation q 257 = true := counterClause275 (baseVal q)

theorem counterClause276 (q : Nat → Bool) : valuationOf q 257 = false ∨ valuationOf q 259 = true := by
  have hs : count259 q = (countLit q [132]) + (countLit q [133, 134]) := List.countP_append (p := literal q) (l₁ := [132]) (l₂ := [133, 134])
  have hm := merge_right (literal (valuationOf q) (257)) (literal (valuationOf q) (259)) (countLit q [132]) (countLit q [133, 134]) (count259 q) 1 (meaning257 q) (meaning259 q) hs
  change valuationOf q 257 = false ∨ valuationOf q 259 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause276 (q : Snake 81) (h : Conditions q) : valuation q 257 = false ∨ valuation q 259 = true := counterClause276 (baseVal q)

theorem counterClause277 (q : Nat → Bool) : valuationOf q 132 = false ∨ valuationOf q 259 = true := by
  have hs : count259 q = (countLit q [132]) + (countLit q [133, 134]) := List.countP_append (p := literal q) (l₁ := [132]) (l₂ := [133, 134])
  have hm := merge_left (literal (valuationOf q) (132)) (literal (valuationOf q) (259)) (countLit q [132]) (countLit q [133, 134]) (count259 q) 1 (meaning132 q) (meaning259 q) hs
  change valuationOf q 132 = false ∨ valuationOf q 259 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause277 (q : Snake 81) (h : Conditions q) : valuation q 132 = false ∨ valuation q 259 = true := counterClause277 (baseVal q)

theorem counterClause278 (q : Nat → Bool) : valuationOf q 132 = false ∨ valuationOf q 257 = false ∨ valuationOf q 260 = true := by
  have hs : count259 q = (countLit q [132]) + (countLit q [133, 134]) := List.countP_append (p := literal q) (l₁ := [132]) (l₂ := [133, 134])
  have hm := merge_two (literal (valuationOf q) (132)) (literal (valuationOf q) (257)) (literal (valuationOf q) (260)) (countLit q [132]) (countLit q [133, 134]) (count259 q) 1 1 (meaning132 q) (meaning257 q) (meaning260 q) hs
  change valuationOf q 132 = false ∨ valuationOf q 257 = false ∨ valuationOf q 260 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause278 (q : Snake 81) (h : Conditions q) : valuation q 132 = false ∨ valuation q 257 = false ∨ valuation q 260 = true := counterClause278 (baseVal q)

theorem counterClause279 (q : Nat → Bool) : valuationOf q 138 = false ∨ valuationOf q 263 = true := by
  have hs : count263 q = (countLit q [137]) + (countLit q [138]) := List.countP_append (p := literal q) (l₁ := [137]) (l₂ := [138])
  have hm := merge_right (literal (valuationOf q) (138)) (literal (valuationOf q) (263)) (countLit q [137]) (countLit q [138]) (count263 q) 1 (meaning138 q) (meaning263 q) hs
  change valuationOf q 138 = false ∨ valuationOf q 263 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause279 (q : Snake 81) (h : Conditions q) : valuation q 138 = false ∨ valuation q 263 = true := counterClause279 (baseVal q)

theorem counterClause280 (q : Nat → Bool) : valuationOf q 263 = false ∨ valuationOf q 265 = true := by
  have hs : count265 q = (countLit q [135, 136]) + (countLit q [137, 138]) := List.countP_append (p := literal q) (l₁ := [135, 136]) (l₂ := [137, 138])
  have hm := merge_right (literal (valuationOf q) (263)) (literal (valuationOf q) (265)) (countLit q [135, 136]) (countLit q [137, 138]) (count265 q) 1 (meaning263 q) (meaning265 q) hs
  change valuationOf q 263 = false ∨ valuationOf q 265 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause280 (q : Snake 81) (h : Conditions q) : valuation q 263 = false ∨ valuation q 265 = true := counterClause280 (baseVal q)

theorem counterClause281 (q : Nat → Bool) : valuationOf q 265 = false ∨ valuationOf q 267 = true := by
  have hs : count267 q = (countLit q [132, 133, 134]) + (countLit q [135, 136, 137, 138]) := List.countP_append (p := literal q) (l₁ := [132, 133, 134]) (l₂ := [135, 136, 137, 138])
  have hm := merge_right (literal (valuationOf q) (265)) (literal (valuationOf q) (267)) (countLit q [132, 133, 134]) (countLit q [135, 136, 137, 138]) (count267 q) 1 (meaning265 q) (meaning267 q) hs
  change valuationOf q 265 = false ∨ valuationOf q 267 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause281 (q : Snake 81) (h : Conditions q) : valuation q 265 = false ∨ valuation q 267 = true := counterClause281 (baseVal q)

theorem counterClause282 (q : Nat → Bool) : valuationOf q 259 = false ∨ valuationOf q 267 = true := by
  have hs : count267 q = (countLit q [132, 133, 134]) + (countLit q [135, 136, 137, 138]) := List.countP_append (p := literal q) (l₁ := [132, 133, 134]) (l₂ := [135, 136, 137, 138])
  have hm := merge_left (literal (valuationOf q) (259)) (literal (valuationOf q) (267)) (countLit q [132, 133, 134]) (countLit q [135, 136, 137, 138]) (count267 q) 1 (meaning259 q) (meaning267 q) hs
  change valuationOf q 259 = false ∨ valuationOf q 267 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause282 (q : Snake 81) (h : Conditions q) : valuation q 259 = false ∨ valuation q 267 = true := counterClause282 (baseVal q)

theorem counterClause283 (q : Nat → Bool) : valuationOf q 260 = false ∨ valuationOf q 268 = true := by
  have hs : count267 q = (countLit q [132, 133, 134]) + (countLit q [135, 136, 137, 138]) := List.countP_append (p := literal q) (l₁ := [132, 133, 134]) (l₂ := [135, 136, 137, 138])
  have hm := merge_left (literal (valuationOf q) (260)) (literal (valuationOf q) (268)) (countLit q [132, 133, 134]) (countLit q [135, 136, 137, 138]) (count267 q) 2 (meaning260 q) (meaning268 q) hs
  change valuationOf q 260 = false ∨ valuationOf q 268 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause283 (q : Snake 81) (h : Conditions q) : valuation q 260 = false ∨ valuation q 268 = true := counterClause283 (baseVal q)

theorem counterClause284 (q : Nat → Bool) : valuationOf q 267 = false ∨ valuationOf q 269 = true := by
  have hs : count269 q = (countLit q [125, 126, 127, 128, 129, 130, 131]) + (countLit q [132, 133, 134, 135, 136, 137, 138]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127, 128, 129, 130, 131]) (l₂ := [132, 133, 134, 135, 136, 137, 138])
  have hm := merge_right (literal (valuationOf q) (267)) (literal (valuationOf q) (269)) (countLit q [125, 126, 127, 128, 129, 130, 131]) (countLit q [132, 133, 134, 135, 136, 137, 138]) (count269 q) 1 (meaning267 q) (meaning269 q) hs
  change valuationOf q 267 = false ∨ valuationOf q 269 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause284 (q : Snake 81) (h : Conditions q) : valuation q 267 = false ∨ valuation q 269 = true := counterClause284 (baseVal q)

theorem counterClause285 (q : Nat → Bool) : valuationOf q 268 = false ∨ valuationOf q 270 = true := by
  have hs : count269 q = (countLit q [125, 126, 127, 128, 129, 130, 131]) + (countLit q [132, 133, 134, 135, 136, 137, 138]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127, 128, 129, 130, 131]) (l₂ := [132, 133, 134, 135, 136, 137, 138])
  have hm := merge_right (literal (valuationOf q) (268)) (literal (valuationOf q) (270)) (countLit q [125, 126, 127, 128, 129, 130, 131]) (countLit q [132, 133, 134, 135, 136, 137, 138]) (count269 q) 2 (meaning268 q) (meaning270 q) hs
  change valuationOf q 268 = false ∨ valuationOf q 270 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause285 (q : Snake 81) (h : Conditions q) : valuation q 268 = false ∨ valuation q 270 = true := counterClause285 (baseVal q)

theorem counterClause286 (q : Nat → Bool) : valuationOf q 255 = false ∨ valuationOf q 269 = true := by
  have hs : count269 q = (countLit q [125, 126, 127, 128, 129, 130, 131]) + (countLit q [132, 133, 134, 135, 136, 137, 138]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127, 128, 129, 130, 131]) (l₂ := [132, 133, 134, 135, 136, 137, 138])
  have hm := merge_left (literal (valuationOf q) (255)) (literal (valuationOf q) (269)) (countLit q [125, 126, 127, 128, 129, 130, 131]) (countLit q [132, 133, 134, 135, 136, 137, 138]) (count269 q) 1 (meaning255 q) (meaning269 q) hs
  change valuationOf q 255 = false ∨ valuationOf q 269 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause286 (q : Snake 81) (h : Conditions q) : valuation q 255 = false ∨ valuation q 269 = true := counterClause286 (baseVal q)

theorem counterClause287 (q : Nat → Bool) : valuationOf q 255 = false ∨ valuationOf q 267 = false ∨ valuationOf q 270 = true := by
  have hs : count269 q = (countLit q [125, 126, 127, 128, 129, 130, 131]) + (countLit q [132, 133, 134, 135, 136, 137, 138]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127, 128, 129, 130, 131]) (l₂ := [132, 133, 134, 135, 136, 137, 138])
  have hm := merge_two (literal (valuationOf q) (255)) (literal (valuationOf q) (267)) (literal (valuationOf q) (270)) (countLit q [125, 126, 127, 128, 129, 130, 131]) (countLit q [132, 133, 134, 135, 136, 137, 138]) (count269 q) 1 1 (meaning255 q) (meaning267 q) (meaning270 q) hs
  change valuationOf q 255 = false ∨ valuationOf q 267 = false ∨ valuationOf q 270 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause287 (q : Snake 81) (h : Conditions q) : valuation q 255 = false ∨ valuation q 267 = false ∨ valuation q 270 = true := counterClause287 (baseVal q)

theorem counterClause288 (q : Nat → Bool) : valuationOf q 256 = false ∨ valuationOf q 270 = true := by
  have hs : count269 q = (countLit q [125, 126, 127, 128, 129, 130, 131]) + (countLit q [132, 133, 134, 135, 136, 137, 138]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127, 128, 129, 130, 131]) (l₂ := [132, 133, 134, 135, 136, 137, 138])
  have hm := merge_left (literal (valuationOf q) (256)) (literal (valuationOf q) (270)) (countLit q [125, 126, 127, 128, 129, 130, 131]) (countLit q [132, 133, 134, 135, 136, 137, 138]) (count269 q) 2 (meaning256 q) (meaning270 q) hs
  change valuationOf q 256 = false ∨ valuationOf q 270 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause288 (q : Snake 81) (h : Conditions q) : valuation q 256 = false ∨ valuation q 270 = true := counterClause288 (baseVal q)

theorem block8 (q : Snake 81) (h : Conditions q) : B112E107.Block8 (valuation q) :=
  ⟨clause257 q h, clause258 q h, clause259 q h, clause260 q h, clause261 q h, clause262 q h, clause263 q h, clause264 q h, clause265 q h, clause266 q h, clause267 q h, clause268 q h, clause269 q h, clause270 q h, clause271 q h, clause272 q h, clause273 q h, clause274 q h, clause275 q h, clause276 q h, clause277 q h, clause278 q h, clause279 q h, clause280 q h, clause281 q h, clause282 q h, clause283 q h, clause284 q h, clause285 q h, clause286 q h, clause287 q h, clause288 q h⟩

end
end Snake9.Regrowth.E112107
