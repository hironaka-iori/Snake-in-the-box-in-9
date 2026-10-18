import E112168Semantics
import B112E168Inputs
namespace Snake9.Regrowth.E112168
noncomputable section
local instance blockDec16 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause513 (q : Nat → Bool) : valuationOf q 238 = false ∨ valuationOf q 240 = true := by
  have hs : count239 q = (countLit q [115, 116, 117]) + (countLit q [118, 119, 120, 121]) := List.countP_append (p := literal q) (l₁ := [115, 116, 117]) (l₂ := [118, 119, 120, 121])
  have hm := merge_right (literal (valuationOf q) (238)) (literal (valuationOf q) (240)) (countLit q [115, 116, 117]) (countLit q [118, 119, 120, 121]) (count239 q) 2 (meaning238 q) (meaning240 q) hs
  change valuationOf q 238 = false ∨ valuationOf q 240 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause513 (q : Snake 81) (h : Conditions q) : valuation q 238 = false ∨ valuation q 240 = true := counterClause513 (baseVal q)

theorem counterClause514 (q : Nat → Bool) : valuationOf q 231 = false ∨ valuationOf q 239 = true := by
  have hs : count239 q = (countLit q [115, 116, 117]) + (countLit q [118, 119, 120, 121]) := List.countP_append (p := literal q) (l₁ := [115, 116, 117]) (l₂ := [118, 119, 120, 121])
  have hm := merge_left (literal (valuationOf q) (231)) (literal (valuationOf q) (239)) (countLit q [115, 116, 117]) (countLit q [118, 119, 120, 121]) (count239 q) 1 (meaning231 q) (meaning239 q) hs
  change valuationOf q 231 = false ∨ valuationOf q 239 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause514 (q : Snake 81) (h : Conditions q) : valuation q 231 = false ∨ valuation q 239 = true := counterClause514 (baseVal q)

theorem counterClause515 (q : Nat → Bool) : valuationOf q 231 = false ∨ valuationOf q 237 = false ∨ valuationOf q 240 = true := by
  have hs : count239 q = (countLit q [115, 116, 117]) + (countLit q [118, 119, 120, 121]) := List.countP_append (p := literal q) (l₁ := [115, 116, 117]) (l₂ := [118, 119, 120, 121])
  have hm := merge_two (literal (valuationOf q) (231)) (literal (valuationOf q) (237)) (literal (valuationOf q) (240)) (countLit q [115, 116, 117]) (countLit q [118, 119, 120, 121]) (count239 q) 1 1 (meaning231 q) (meaning237 q) (meaning240 q) hs
  change valuationOf q 231 = false ∨ valuationOf q 237 = false ∨ valuationOf q 240 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause515 (q : Snake 81) (h : Conditions q) : valuation q 231 = false ∨ valuation q 237 = false ∨ valuation q 240 = true := counterClause515 (baseVal q)

theorem counterClause516 (q : Nat → Bool) : valuationOf q 123 = false ∨ valuationOf q 241 = true := by
  have hs : count241 q = (countLit q [123]) + (countLit q [124]) := List.countP_append (p := literal q) (l₁ := [123]) (l₂ := [124])
  have hm := merge_left (literal (valuationOf q) (123)) (literal (valuationOf q) (241)) (countLit q [123]) (countLit q [124]) (count241 q) 1 (meaning123 q) (meaning241 q) hs
  change valuationOf q 123 = false ∨ valuationOf q 241 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause516 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 241 = true := counterClause516 (baseVal q)

theorem counterClause517 (q : Nat → Bool) : valuationOf q 241 = false ∨ valuationOf q 243 = true := by
  have hs : count243 q = (countLit q [122]) + (countLit q [123, 124]) := List.countP_append (p := literal q) (l₁ := [122]) (l₂ := [123, 124])
  have hm := merge_right (literal (valuationOf q) (241)) (literal (valuationOf q) (243)) (countLit q [122]) (countLit q [123, 124]) (count243 q) 1 (meaning241 q) (meaning243 q) hs
  change valuationOf q 241 = false ∨ valuationOf q 243 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause517 (q : Snake 81) (h : Conditions q) : valuation q 241 = false ∨ valuation q 243 = true := counterClause517 (baseVal q)

theorem counterClause518 (q : Nat → Bool) : valuationOf q 128 = false ∨ valuationOf q 247 = true := by
  have hs : count247 q = (countLit q [127]) + (countLit q [128]) := List.countP_append (p := literal q) (l₁ := [127]) (l₂ := [128])
  have hm := merge_right (literal (valuationOf q) (128)) (literal (valuationOf q) (247)) (countLit q [127]) (countLit q [128]) (count247 q) 1 (meaning128 q) (meaning247 q) hs
  change valuationOf q 128 = false ∨ valuationOf q 247 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause518 (q : Snake 81) (h : Conditions q) : valuation q 128 = false ∨ valuation q 247 = true := counterClause518 (baseVal q)

theorem counterClause519 (q : Nat → Bool) : valuationOf q 127 = false ∨ valuationOf q 247 = true := by
  have hs : count247 q = (countLit q [127]) + (countLit q [128]) := List.countP_append (p := literal q) (l₁ := [127]) (l₂ := [128])
  have hm := merge_left (literal (valuationOf q) (127)) (literal (valuationOf q) (247)) (countLit q [127]) (countLit q [128]) (count247 q) 1 (meaning127 q) (meaning247 q) hs
  change valuationOf q 127 = false ∨ valuationOf q 247 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause519 (q : Snake 81) (h : Conditions q) : valuation q 127 = false ∨ valuation q 247 = true := counterClause519 (baseVal q)

theorem counterClause520 (q : Nat → Bool) : valuationOf q 247 = false ∨ valuationOf q 249 = true := by
  have hs : count249 q = (countLit q [125, 126]) + (countLit q [127, 128]) := List.countP_append (p := literal q) (l₁ := [125, 126]) (l₂ := [127, 128])
  have hm := merge_right (literal (valuationOf q) (247)) (literal (valuationOf q) (249)) (countLit q [125, 126]) (countLit q [127, 128]) (count249 q) 1 (meaning247 q) (meaning249 q) hs
  change valuationOf q 247 = false ∨ valuationOf q 249 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause520 (q : Snake 81) (h : Conditions q) : valuation q 247 = false ∨ valuation q 249 = true := counterClause520 (baseVal q)

theorem counterClause521 (q : Nat → Bool) : valuationOf q 249 = false ∨ valuationOf q 251 = true := by
  have hs : count251 q = (countLit q [122, 123, 124]) + (countLit q [125, 126, 127, 128]) := List.countP_append (p := literal q) (l₁ := [122, 123, 124]) (l₂ := [125, 126, 127, 128])
  have hm := merge_right (literal (valuationOf q) (249)) (literal (valuationOf q) (251)) (countLit q [122, 123, 124]) (countLit q [125, 126, 127, 128]) (count251 q) 1 (meaning249 q) (meaning251 q) hs
  change valuationOf q 249 = false ∨ valuationOf q 251 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause521 (q : Snake 81) (h : Conditions q) : valuation q 249 = false ∨ valuation q 251 = true := counterClause521 (baseVal q)

theorem counterClause522 (q : Nat → Bool) : valuationOf q 243 = false ∨ valuationOf q 251 = true := by
  have hs : count251 q = (countLit q [122, 123, 124]) + (countLit q [125, 126, 127, 128]) := List.countP_append (p := literal q) (l₁ := [122, 123, 124]) (l₂ := [125, 126, 127, 128])
  have hm := merge_left (literal (valuationOf q) (243)) (literal (valuationOf q) (251)) (countLit q [122, 123, 124]) (countLit q [125, 126, 127, 128]) (count251 q) 1 (meaning243 q) (meaning251 q) hs
  change valuationOf q 243 = false ∨ valuationOf q 251 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause522 (q : Snake 81) (h : Conditions q) : valuation q 243 = false ∨ valuation q 251 = true := counterClause522 (baseVal q)

theorem counterClause523 (q : Nat → Bool) : valuationOf q 239 = false ∨ valuationOf q 253 = true := by
  have hs : count253 q = (countLit q [115, 116, 117, 118, 119, 120, 121]) + (countLit q [122, 123, 124, 125, 126, 127, 128]) := List.countP_append (p := literal q) (l₁ := [115, 116, 117, 118, 119, 120, 121]) (l₂ := [122, 123, 124, 125, 126, 127, 128])
  have hm := merge_left (literal (valuationOf q) (239)) (literal (valuationOf q) (253)) (countLit q [115, 116, 117, 118, 119, 120, 121]) (countLit q [122, 123, 124, 125, 126, 127, 128]) (count253 q) 1 (meaning239 q) (meaning253 q) hs
  change valuationOf q 239 = false ∨ valuationOf q 253 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause523 (q : Snake 81) (h : Conditions q) : valuation q 239 = false ∨ valuation q 253 = true := counterClause523 (baseVal q)

theorem counterClause524 (q : Nat → Bool) : valuationOf q 239 = false ∨ valuationOf q 251 = false ∨ valuationOf q 254 = true := by
  have hs : count253 q = (countLit q [115, 116, 117, 118, 119, 120, 121]) + (countLit q [122, 123, 124, 125, 126, 127, 128]) := List.countP_append (p := literal q) (l₁ := [115, 116, 117, 118, 119, 120, 121]) (l₂ := [122, 123, 124, 125, 126, 127, 128])
  have hm := merge_two (literal (valuationOf q) (239)) (literal (valuationOf q) (251)) (literal (valuationOf q) (254)) (countLit q [115, 116, 117, 118, 119, 120, 121]) (countLit q [122, 123, 124, 125, 126, 127, 128]) (count253 q) 1 1 (meaning239 q) (meaning251 q) (meaning254 q) hs
  change valuationOf q 239 = false ∨ valuationOf q 251 = false ∨ valuationOf q 254 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause524 (q : Snake 81) (h : Conditions q) : valuation q 239 = false ∨ valuation q 251 = false ∨ valuation q 254 = true := counterClause524 (baseVal q)

theorem counterClause525 (q : Nat → Bool) : valuationOf q 240 = false ∨ valuationOf q 254 = true := by
  have hs : count253 q = (countLit q [115, 116, 117, 118, 119, 120, 121]) + (countLit q [122, 123, 124, 125, 126, 127, 128]) := List.countP_append (p := literal q) (l₁ := [115, 116, 117, 118, 119, 120, 121]) (l₂ := [122, 123, 124, 125, 126, 127, 128])
  have hm := merge_left (literal (valuationOf q) (240)) (literal (valuationOf q) (254)) (countLit q [115, 116, 117, 118, 119, 120, 121]) (countLit q [122, 123, 124, 125, 126, 127, 128]) (count253 q) 2 (meaning240 q) (meaning254 q) hs
  change valuationOf q 240 = false ∨ valuationOf q 254 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause525 (q : Snake 81) (h : Conditions q) : valuation q 240 = false ∨ valuation q 254 = true := counterClause525 (baseVal q)

theorem counterClause526 (q : Nat → Bool) : valuationOf q 130 = false ∨ valuationOf q 255 = true := by
  have hs : count255 q = (countLit q [130]) + (countLit q [131]) := List.countP_append (p := literal q) (l₁ := [130]) (l₂ := [131])
  have hm := merge_left (literal (valuationOf q) (130)) (literal (valuationOf q) (255)) (countLit q [130]) (countLit q [131]) (count255 q) 1 (meaning130 q) (meaning255 q) hs
  change valuationOf q 130 = false ∨ valuationOf q 255 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause526 (q : Snake 81) (h : Conditions q) : valuation q 130 = false ∨ valuation q 255 = true := counterClause526 (baseVal q)

theorem counterClause527 (q : Nat → Bool) : valuationOf q 255 = false ∨ valuationOf q 257 = true := by
  have hs : count257 q = (countLit q [129]) + (countLit q [130, 131]) := List.countP_append (p := literal q) (l₁ := [129]) (l₂ := [130, 131])
  have hm := merge_right (literal (valuationOf q) (255)) (literal (valuationOf q) (257)) (countLit q [129]) (countLit q [130, 131]) (count257 q) 1 (meaning255 q) (meaning257 q) hs
  change valuationOf q 255 = false ∨ valuationOf q 257 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause527 (q : Snake 81) (h : Conditions q) : valuation q 255 = false ∨ valuation q 257 = true := counterClause527 (baseVal q)

theorem counterClause528 (q : Nat → Bool) : valuationOf q 133 = false ∨ valuationOf q 259 = true := by
  have hs : count259 q = (countLit q [132]) + (countLit q [133]) := List.countP_append (p := literal q) (l₁ := [132]) (l₂ := [133])
  have hm := merge_right (literal (valuationOf q) (133)) (literal (valuationOf q) (259)) (countLit q [132]) (countLit q [133]) (count259 q) 1 (meaning133 q) (meaning259 q) hs
  change valuationOf q 133 = false ∨ valuationOf q 259 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause528 (q : Snake 81) (h : Conditions q) : valuation q 133 = false ∨ valuation q 259 = true := counterClause528 (baseVal q)

theorem counterClause529 (q : Nat → Bool) : valuationOf q 259 = false ∨ valuationOf q 263 = true := by
  have hs : count263 q = (countLit q [132, 133]) + (countLit q [134, 135]) := List.countP_append (p := literal q) (l₁ := [132, 133]) (l₂ := [134, 135])
  have hm := merge_left (literal (valuationOf q) (259)) (literal (valuationOf q) (263)) (countLit q [132, 133]) (countLit q [134, 135]) (count263 q) 1 (meaning259 q) (meaning263 q) hs
  change valuationOf q 259 = false ∨ valuationOf q 263 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause529 (q : Snake 81) (h : Conditions q) : valuation q 259 = false ∨ valuation q 263 = true := counterClause529 (baseVal q)

theorem counterClause530 (q : Nat → Bool) : valuationOf q 263 = false ∨ valuationOf q 265 = true := by
  have hs : count265 q = (countLit q [129, 130, 131]) + (countLit q [132, 133, 134, 135]) := List.countP_append (p := literal q) (l₁ := [129, 130, 131]) (l₂ := [132, 133, 134, 135])
  have hm := merge_right (literal (valuationOf q) (263)) (literal (valuationOf q) (265)) (countLit q [129, 130, 131]) (countLit q [132, 133, 134, 135]) (count265 q) 1 (meaning263 q) (meaning265 q) hs
  change valuationOf q 263 = false ∨ valuationOf q 265 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause530 (q : Snake 81) (h : Conditions q) : valuation q 263 = false ∨ valuation q 265 = true := counterClause530 (baseVal q)

theorem counterClause531 (q : Nat → Bool) : valuationOf q 257 = false ∨ valuationOf q 265 = true := by
  have hs : count265 q = (countLit q [129, 130, 131]) + (countLit q [132, 133, 134, 135]) := List.countP_append (p := literal q) (l₁ := [129, 130, 131]) (l₂ := [132, 133, 134, 135])
  have hm := merge_left (literal (valuationOf q) (257)) (literal (valuationOf q) (265)) (countLit q [129, 130, 131]) (countLit q [132, 133, 134, 135]) (count265 q) 1 (meaning257 q) (meaning265 q) hs
  change valuationOf q 257 = false ∨ valuationOf q 265 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause531 (q : Snake 81) (h : Conditions q) : valuation q 257 = false ∨ valuation q 265 = true := counterClause531 (baseVal q)

theorem counterClause532 (q : Nat → Bool) : valuationOf q 137 = false ∨ valuationOf q 267 = true := by
  have hs : count267 q = (countLit q [137]) + (countLit q [138]) := List.countP_append (p := literal q) (l₁ := [137]) (l₂ := [138])
  have hm := merge_left (literal (valuationOf q) (137)) (literal (valuationOf q) (267)) (countLit q [137]) (countLit q [138]) (count267 q) 1 (meaning137 q) (meaning267 q) hs
  change valuationOf q 137 = false ∨ valuationOf q 267 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause532 (q : Snake 81) (h : Conditions q) : valuation q 137 = false ∨ valuation q 267 = true := counterClause532 (baseVal q)

theorem counterClause533 (q : Nat → Bool) : valuationOf q 267 = false ∨ valuationOf q 269 = true := by
  have hs : count269 q = (countLit q [136]) + (countLit q [137, 138]) := List.countP_append (p := literal q) (l₁ := [136]) (l₂ := [137, 138])
  have hm := merge_right (literal (valuationOf q) (267)) (literal (valuationOf q) (269)) (countLit q [136]) (countLit q [137, 138]) (count269 q) 1 (meaning267 q) (meaning269 q) hs
  change valuationOf q 267 = false ∨ valuationOf q 269 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause533 (q : Snake 81) (h : Conditions q) : valuation q 267 = false ∨ valuation q 269 = true := counterClause533 (baseVal q)

theorem counterClause534 (q : Nat → Bool) : valuationOf q 136 = false ∨ valuationOf q 269 = true := by
  have hs : count269 q = (countLit q [136]) + (countLit q [137, 138]) := List.countP_append (p := literal q) (l₁ := [136]) (l₂ := [137, 138])
  have hm := merge_left (literal (valuationOf q) (136)) (literal (valuationOf q) (269)) (countLit q [136]) (countLit q [137, 138]) (count269 q) 1 (meaning136 q) (meaning269 q) hs
  change valuationOf q 136 = false ∨ valuationOf q 269 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause534 (q : Snake 81) (h : Conditions q) : valuation q 136 = false ∨ valuation q 269 = true := counterClause534 (baseVal q)

theorem counterClause535 (q : Nat → Bool) : valuationOf q 139 = false ∨ valuationOf q 271 = true := by
  have hs : count271 q = (countLit q [139]) + (countLit q [140]) := List.countP_append (p := literal q) (l₁ := [139]) (l₂ := [140])
  have hm := merge_left (literal (valuationOf q) (139)) (literal (valuationOf q) (271)) (countLit q [139]) (countLit q [140]) (count271 q) 1 (meaning139 q) (meaning271 q) hs
  change valuationOf q 139 = false ∨ valuationOf q 271 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause535 (q : Snake 81) (h : Conditions q) : valuation q 139 = false ∨ valuation q 271 = true := counterClause535 (baseVal q)

theorem counterClause536 (q : Nat → Bool) : valuationOf q 141 = false ∨ valuationOf q 273 = true := by
  have hs : count273 q = (countLit q [141]) + (countLit q [142]) := List.countP_append (p := literal q) (l₁ := [141]) (l₂ := [142])
  have hm := merge_left (literal (valuationOf q) (141)) (literal (valuationOf q) (273)) (countLit q [141]) (countLit q [142]) (count273 q) 1 (meaning141 q) (meaning273 q) hs
  change valuationOf q 141 = false ∨ valuationOf q 273 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause536 (q : Snake 81) (h : Conditions q) : valuation q 141 = false ∨ valuation q 273 = true := counterClause536 (baseVal q)

theorem counterClause537 (q : Nat → Bool) : valuationOf q 273 = false ∨ valuationOf q 275 = true := by
  have hs : count275 q = (countLit q [139, 140]) + (countLit q [141, 142]) := List.countP_append (p := literal q) (l₁ := [139, 140]) (l₂ := [141, 142])
  have hm := merge_right (literal (valuationOf q) (273)) (literal (valuationOf q) (275)) (countLit q [139, 140]) (countLit q [141, 142]) (count275 q) 1 (meaning273 q) (meaning275 q) hs
  change valuationOf q 273 = false ∨ valuationOf q 275 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause537 (q : Snake 81) (h : Conditions q) : valuation q 273 = false ∨ valuation q 275 = true := counterClause537 (baseVal q)

theorem counterClause538 (q : Nat → Bool) : valuationOf q 271 = false ∨ valuationOf q 275 = true := by
  have hs : count275 q = (countLit q [139, 140]) + (countLit q [141, 142]) := List.countP_append (p := literal q) (l₁ := [139, 140]) (l₂ := [141, 142])
  have hm := merge_left (literal (valuationOf q) (271)) (literal (valuationOf q) (275)) (countLit q [139, 140]) (countLit q [141, 142]) (count275 q) 1 (meaning271 q) (meaning275 q) hs
  change valuationOf q 271 = false ∨ valuationOf q 275 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause538 (q : Snake 81) (h : Conditions q) : valuation q 271 = false ∨ valuation q 275 = true := counterClause538 (baseVal q)

theorem counterClause539 (q : Nat → Bool) : valuationOf q 275 = false ∨ valuationOf q 277 = true := by
  have hs : count277 q = (countLit q [136, 137, 138]) + (countLit q [139, 140, 141, 142]) := List.countP_append (p := literal q) (l₁ := [136, 137, 138]) (l₂ := [139, 140, 141, 142])
  have hm := merge_right (literal (valuationOf q) (275)) (literal (valuationOf q) (277)) (countLit q [136, 137, 138]) (countLit q [139, 140, 141, 142]) (count277 q) 1 (meaning275 q) (meaning277 q) hs
  change valuationOf q 275 = false ∨ valuationOf q 277 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause539 (q : Snake 81) (h : Conditions q) : valuation q 275 = false ∨ valuation q 277 = true := counterClause539 (baseVal q)

theorem counterClause540 (q : Nat → Bool) : valuationOf q 269 = false ∨ valuationOf q 277 = true := by
  have hs : count277 q = (countLit q [136, 137, 138]) + (countLit q [139, 140, 141, 142]) := List.countP_append (p := literal q) (l₁ := [136, 137, 138]) (l₂ := [139, 140, 141, 142])
  have hm := merge_left (literal (valuationOf q) (269)) (literal (valuationOf q) (277)) (countLit q [136, 137, 138]) (countLit q [139, 140, 141, 142]) (count277 q) 1 (meaning269 q) (meaning277 q) hs
  change valuationOf q 269 = false ∨ valuationOf q 277 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause540 (q : Snake 81) (h : Conditions q) : valuation q 269 = false ∨ valuation q 277 = true := counterClause540 (baseVal q)

theorem counterClause541 (q : Nat → Bool) : valuationOf q 277 = false ∨ valuationOf q 279 = true := by
  have hs : count279 q = (countLit q [129, 130, 131, 132, 133, 134, 135]) + (countLit q [136, 137, 138, 139, 140, 141, 142]) := List.countP_append (p := literal q) (l₁ := [129, 130, 131, 132, 133, 134, 135]) (l₂ := [136, 137, 138, 139, 140, 141, 142])
  have hm := merge_right (literal (valuationOf q) (277)) (literal (valuationOf q) (279)) (countLit q [129, 130, 131, 132, 133, 134, 135]) (countLit q [136, 137, 138, 139, 140, 141, 142]) (count279 q) 1 (meaning277 q) (meaning279 q) hs
  change valuationOf q 277 = false ∨ valuationOf q 279 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause541 (q : Snake 81) (h : Conditions q) : valuation q 277 = false ∨ valuation q 279 = true := counterClause541 (baseVal q)

theorem counterClause542 (q : Nat → Bool) : valuationOf q 265 = false ∨ valuationOf q 279 = true := by
  have hs : count279 q = (countLit q [129, 130, 131, 132, 133, 134, 135]) + (countLit q [136, 137, 138, 139, 140, 141, 142]) := List.countP_append (p := literal q) (l₁ := [129, 130, 131, 132, 133, 134, 135]) (l₂ := [136, 137, 138, 139, 140, 141, 142])
  have hm := merge_left (literal (valuationOf q) (265)) (literal (valuationOf q) (279)) (countLit q [129, 130, 131, 132, 133, 134, 135]) (countLit q [136, 137, 138, 139, 140, 141, 142]) (count279 q) 1 (meaning265 q) (meaning279 q) hs
  change valuationOf q 265 = false ∨ valuationOf q 279 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause542 (q : Snake 81) (h : Conditions q) : valuation q 265 = false ∨ valuation q 279 = true := counterClause542 (baseVal q)

theorem counterClause543 (q : Nat → Bool) : valuationOf q 279 = false ∨ valuationOf q 281 = true := by
  have hs : count281 q = (countLit q [115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128]) + (countLit q [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) := List.countP_append (p := literal q) (l₁ := [115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128]) (l₂ := [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142])
  have hm := merge_right (literal (valuationOf q) (279)) (literal (valuationOf q) (281)) (countLit q [115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128]) (countLit q [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) (count281 q) 1 (meaning279 q) (meaning281 q) hs
  change valuationOf q 279 = false ∨ valuationOf q 281 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause543 (q : Snake 81) (h : Conditions q) : valuation q 279 = false ∨ valuation q 281 = true := counterClause543 (baseVal q)

theorem counterClause544 (q : Nat → Bool) : valuationOf q 253 = false ∨ valuationOf q 281 = true := by
  have hs : count281 q = (countLit q [115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128]) + (countLit q [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) := List.countP_append (p := literal q) (l₁ := [115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128]) (l₂ := [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142])
  have hm := merge_left (literal (valuationOf q) (253)) (literal (valuationOf q) (281)) (countLit q [115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128]) (countLit q [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) (count281 q) 1 (meaning253 q) (meaning281 q) hs
  change valuationOf q 253 = false ∨ valuationOf q 281 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause544 (q : Snake 81) (h : Conditions q) : valuation q 253 = false ∨ valuation q 281 = true := counterClause544 (baseVal q)

theorem block16 (q : Snake 81) (h : Conditions q) : B112E168.Block16 (valuation q) :=
  ⟨clause513 q h, clause514 q h, clause515 q h, clause516 q h, clause517 q h, clause518 q h, clause519 q h, clause520 q h, clause521 q h, clause522 q h, clause523 q h, clause524 q h, clause525 q h, clause526 q h, clause527 q h, clause528 q h, clause529 q h, clause530 q h, clause531 q h, clause532 q h, clause533 q h, clause534 q h, clause535 q h, clause536 q h, clause537 q h, clause538 q h, clause539 q h, clause540 q h, clause541 q h, clause542 q h, clause543 q h, clause544 q h⟩

end
end Snake9.Regrowth.E112168
