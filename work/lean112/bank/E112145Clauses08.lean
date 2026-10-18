import E112145Semantics
import B112E145Inputs
namespace Snake9.Regrowth.E112145
noncomputable section
local instance blockDec8 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause257 (q : Nat → Bool) : valuationOf q 233 = false ∨ valuationOf q 239 = true := by
  have hs : count239 q = (countLit q [117, 118, 119]) + (countLit q [120, 121, 122]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119]) (l₂ := [120, 121, 122])
  have hm := merge_left (literal (valuationOf q) (233)) (literal (valuationOf q) (239)) (countLit q [117, 118, 119]) (countLit q [120, 121, 122]) (count239 q) 1 (meaning233 q) (meaning239 q) hs
  change valuationOf q 233 = false ∨ valuationOf q 239 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause257 (q : Snake 81) (h : Conditions q) : valuation q 233 = false ∨ valuation q 239 = true := counterClause257 (baseVal q)

theorem counterClause258 (q : Nat → Bool) : valuationOf q 233 = false ∨ valuationOf q 237 = false ∨ valuationOf q 240 = true := by
  have hs : count239 q = (countLit q [117, 118, 119]) + (countLit q [120, 121, 122]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119]) (l₂ := [120, 121, 122])
  have hm := merge_two (literal (valuationOf q) (233)) (literal (valuationOf q) (237)) (literal (valuationOf q) (240)) (countLit q [117, 118, 119]) (countLit q [120, 121, 122]) (count239 q) 1 1 (meaning233 q) (meaning237 q) (meaning240 q) hs
  change valuationOf q 233 = false ∨ valuationOf q 237 = false ∨ valuationOf q 240 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause258 (q : Snake 81) (h : Conditions q) : valuation q 233 = false ∨ valuation q 237 = false ∨ valuation q 240 = true := counterClause258 (baseVal q)

theorem counterClause259 (q : Nat → Bool) : valuationOf q 125 = false ∨ valuationOf q 241 = true := by
  have hs : count241 q = (countLit q [125]) + (countLit q [126]) := List.countP_append (p := literal q) (l₁ := [125]) (l₂ := [126])
  have hm := merge_left (literal (valuationOf q) (125)) (literal (valuationOf q) (241)) (countLit q [125]) (countLit q [126]) (count241 q) 1 (meaning125 q) (meaning241 q) hs
  change valuationOf q 125 = false ∨ valuationOf q 241 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause259 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 241 = true := counterClause259 (baseVal q)

theorem counterClause260 (q : Nat → Bool) : valuationOf q 241 = false ∨ valuationOf q 243 = true := by
  have hs : count243 q = (countLit q [124]) + (countLit q [125, 126]) := List.countP_append (p := literal q) (l₁ := [124]) (l₂ := [125, 126])
  have hm := merge_right (literal (valuationOf q) (241)) (literal (valuationOf q) (243)) (countLit q [124]) (countLit q [125, 126]) (count243 q) 1 (meaning241 q) (meaning243 q) hs
  change valuationOf q 241 = false ∨ valuationOf q 243 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause260 (q : Snake 81) (h : Conditions q) : valuation q 241 = false ∨ valuation q 243 = true := counterClause260 (baseVal q)

theorem counterClause261 (q : Nat → Bool) : valuationOf q 128 = false ∨ valuationOf q 245 = true := by
  have hs : count245 q = (countLit q [127]) + (countLit q [128]) := List.countP_append (p := literal q) (l₁ := [127]) (l₂ := [128])
  have hm := merge_right (literal (valuationOf q) (128)) (literal (valuationOf q) (245)) (countLit q [127]) (countLit q [128]) (count245 q) 1 (meaning128 q) (meaning245 q) hs
  change valuationOf q 128 = false ∨ valuationOf q 245 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause261 (q : Snake 81) (h : Conditions q) : valuation q 128 = false ∨ valuation q 245 = true := counterClause261 (baseVal q)

theorem counterClause262 (q : Nat → Bool) : valuationOf q 127 = false ∨ valuationOf q 245 = true := by
  have hs : count245 q = (countLit q [127]) + (countLit q [128]) := List.countP_append (p := literal q) (l₁ := [127]) (l₂ := [128])
  have hm := merge_left (literal (valuationOf q) (127)) (literal (valuationOf q) (245)) (countLit q [127]) (countLit q [128]) (count245 q) 1 (meaning127 q) (meaning245 q) hs
  change valuationOf q 127 = false ∨ valuationOf q 245 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause262 (q : Snake 81) (h : Conditions q) : valuation q 127 = false ∨ valuation q 245 = true := counterClause262 (baseVal q)

theorem counterClause263 (q : Nat → Bool) : valuationOf q 129 = false ∨ valuationOf q 247 = true := by
  have hs : count247 q = (countLit q [129]) + (countLit q [130]) := List.countP_append (p := literal q) (l₁ := [129]) (l₂ := [130])
  have hm := merge_left (literal (valuationOf q) (129)) (literal (valuationOf q) (247)) (countLit q [129]) (countLit q [130]) (count247 q) 1 (meaning129 q) (meaning247 q) hs
  change valuationOf q 129 = false ∨ valuationOf q 247 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause263 (q : Snake 81) (h : Conditions q) : valuation q 129 = false ∨ valuation q 247 = true := counterClause263 (baseVal q)

theorem counterClause264 (q : Nat → Bool) : valuationOf q 247 = false ∨ valuationOf q 249 = true := by
  have hs : count249 q = (countLit q [127, 128]) + (countLit q [129, 130]) := List.countP_append (p := literal q) (l₁ := [127, 128]) (l₂ := [129, 130])
  have hm := merge_right (literal (valuationOf q) (247)) (literal (valuationOf q) (249)) (countLit q [127, 128]) (countLit q [129, 130]) (count249 q) 1 (meaning247 q) (meaning249 q) hs
  change valuationOf q 247 = false ∨ valuationOf q 249 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause264 (q : Snake 81) (h : Conditions q) : valuation q 247 = false ∨ valuation q 249 = true := counterClause264 (baseVal q)

theorem counterClause265 (q : Nat → Bool) : valuationOf q 245 = false ∨ valuationOf q 249 = true := by
  have hs : count249 q = (countLit q [127, 128]) + (countLit q [129, 130]) := List.countP_append (p := literal q) (l₁ := [127, 128]) (l₂ := [129, 130])
  have hm := merge_left (literal (valuationOf q) (245)) (literal (valuationOf q) (249)) (countLit q [127, 128]) (countLit q [129, 130]) (count249 q) 1 (meaning245 q) (meaning249 q) hs
  change valuationOf q 245 = false ∨ valuationOf q 249 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause265 (q : Snake 81) (h : Conditions q) : valuation q 245 = false ∨ valuation q 249 = true := counterClause265 (baseVal q)

theorem counterClause266 (q : Nat → Bool) : valuationOf q 249 = false ∨ valuationOf q 251 = true := by
  have hs : count251 q = (countLit q [124, 125, 126]) + (countLit q [127, 128, 129, 130]) := List.countP_append (p := literal q) (l₁ := [124, 125, 126]) (l₂ := [127, 128, 129, 130])
  have hm := merge_right (literal (valuationOf q) (249)) (literal (valuationOf q) (251)) (countLit q [124, 125, 126]) (countLit q [127, 128, 129, 130]) (count251 q) 1 (meaning249 q) (meaning251 q) hs
  change valuationOf q 249 = false ∨ valuationOf q 251 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause266 (q : Snake 81) (h : Conditions q) : valuation q 249 = false ∨ valuation q 251 = true := counterClause266 (baseVal q)

theorem counterClause267 (q : Nat → Bool) : valuationOf q 243 = false ∨ valuationOf q 251 = true := by
  have hs : count251 q = (countLit q [124, 125, 126]) + (countLit q [127, 128, 129, 130]) := List.countP_append (p := literal q) (l₁ := [124, 125, 126]) (l₂ := [127, 128, 129, 130])
  have hm := merge_left (literal (valuationOf q) (243)) (literal (valuationOf q) (251)) (countLit q [124, 125, 126]) (countLit q [127, 128, 129, 130]) (count251 q) 1 (meaning243 q) (meaning251 q) hs
  change valuationOf q 243 = false ∨ valuationOf q 251 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause267 (q : Snake 81) (h : Conditions q) : valuation q 243 = false ∨ valuation q 251 = true := counterClause267 (baseVal q)

theorem counterClause268 (q : Nat → Bool) : valuationOf q 243 = false ∨ valuationOf q 249 = false ∨ valuationOf q 252 = true := by
  have hs : count251 q = (countLit q [124, 125, 126]) + (countLit q [127, 128, 129, 130]) := List.countP_append (p := literal q) (l₁ := [124, 125, 126]) (l₂ := [127, 128, 129, 130])
  have hm := merge_two (literal (valuationOf q) (243)) (literal (valuationOf q) (249)) (literal (valuationOf q) (252)) (countLit q [124, 125, 126]) (countLit q [127, 128, 129, 130]) (count251 q) 1 1 (meaning243 q) (meaning249 q) (meaning252 q) hs
  change valuationOf q 243 = false ∨ valuationOf q 249 = false ∨ valuationOf q 252 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause268 (q : Snake 81) (h : Conditions q) : valuation q 243 = false ∨ valuation q 249 = false ∨ valuation q 252 = true := counterClause268 (baseVal q)

theorem counterClause269 (q : Nat → Bool) : valuationOf q 251 = false ∨ valuationOf q 253 = true := by
  have hs : count253 q = (countLit q [117, 118, 119, 120, 121, 122]) + (countLit q [124, 125, 126, 127, 128, 129, 130]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119, 120, 121, 122]) (l₂ := [124, 125, 126, 127, 128, 129, 130])
  have hm := merge_right (literal (valuationOf q) (251)) (literal (valuationOf q) (253)) (countLit q [117, 118, 119, 120, 121, 122]) (countLit q [124, 125, 126, 127, 128, 129, 130]) (count253 q) 1 (meaning251 q) (meaning253 q) hs
  change valuationOf q 251 = false ∨ valuationOf q 253 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause269 (q : Snake 81) (h : Conditions q) : valuation q 251 = false ∨ valuation q 253 = true := counterClause269 (baseVal q)

theorem counterClause270 (q : Nat → Bool) : valuationOf q 252 = false ∨ valuationOf q 254 = true := by
  have hs : count253 q = (countLit q [117, 118, 119, 120, 121, 122]) + (countLit q [124, 125, 126, 127, 128, 129, 130]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119, 120, 121, 122]) (l₂ := [124, 125, 126, 127, 128, 129, 130])
  have hm := merge_right (literal (valuationOf q) (252)) (literal (valuationOf q) (254)) (countLit q [117, 118, 119, 120, 121, 122]) (countLit q [124, 125, 126, 127, 128, 129, 130]) (count253 q) 2 (meaning252 q) (meaning254 q) hs
  change valuationOf q 252 = false ∨ valuationOf q 254 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause270 (q : Snake 81) (h : Conditions q) : valuation q 252 = false ∨ valuation q 254 = true := counterClause270 (baseVal q)

theorem counterClause271 (q : Nat → Bool) : valuationOf q 239 = false ∨ valuationOf q 253 = true := by
  have hs : count253 q = (countLit q [117, 118, 119, 120, 121, 122]) + (countLit q [124, 125, 126, 127, 128, 129, 130]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119, 120, 121, 122]) (l₂ := [124, 125, 126, 127, 128, 129, 130])
  have hm := merge_left (literal (valuationOf q) (239)) (literal (valuationOf q) (253)) (countLit q [117, 118, 119, 120, 121, 122]) (countLit q [124, 125, 126, 127, 128, 129, 130]) (count253 q) 1 (meaning239 q) (meaning253 q) hs
  change valuationOf q 239 = false ∨ valuationOf q 253 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause271 (q : Snake 81) (h : Conditions q) : valuation q 239 = false ∨ valuation q 253 = true := counterClause271 (baseVal q)

theorem counterClause272 (q : Nat → Bool) : valuationOf q 239 = false ∨ valuationOf q 251 = false ∨ valuationOf q 254 = true := by
  have hs : count253 q = (countLit q [117, 118, 119, 120, 121, 122]) + (countLit q [124, 125, 126, 127, 128, 129, 130]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119, 120, 121, 122]) (l₂ := [124, 125, 126, 127, 128, 129, 130])
  have hm := merge_two (literal (valuationOf q) (239)) (literal (valuationOf q) (251)) (literal (valuationOf q) (254)) (countLit q [117, 118, 119, 120, 121, 122]) (countLit q [124, 125, 126, 127, 128, 129, 130]) (count253 q) 1 1 (meaning239 q) (meaning251 q) (meaning254 q) hs
  change valuationOf q 239 = false ∨ valuationOf q 251 = false ∨ valuationOf q 254 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause272 (q : Snake 81) (h : Conditions q) : valuation q 239 = false ∨ valuation q 251 = false ∨ valuation q 254 = true := counterClause272 (baseVal q)

theorem counterClause273 (q : Nat → Bool) : valuationOf q 240 = false ∨ valuationOf q 254 = true := by
  have hs : count253 q = (countLit q [117, 118, 119, 120, 121, 122]) + (countLit q [124, 125, 126, 127, 128, 129, 130]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119, 120, 121, 122]) (l₂ := [124, 125, 126, 127, 128, 129, 130])
  have hm := merge_left (literal (valuationOf q) (240)) (literal (valuationOf q) (254)) (countLit q [117, 118, 119, 120, 121, 122]) (countLit q [124, 125, 126, 127, 128, 129, 130]) (count253 q) 2 (meaning240 q) (meaning254 q) hs
  change valuationOf q 240 = false ∨ valuationOf q 254 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause273 (q : Snake 81) (h : Conditions q) : valuation q 240 = false ∨ valuation q 254 = true := counterClause273 (baseVal q)

theorem counterClause274 (q : Nat → Bool) : valuationOf q 253 = false ∨ valuationOf q 255 = true := by
  have hs : count255 q = (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116]) + (countLit q [117, 118, 119, 120, 121, 122, 124, 125, 126, 127, 128, 129, 130]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116]) (l₂ := [117, 118, 119, 120, 121, 122, 124, 125, 126, 127, 128, 129, 130])
  have hm := merge_right (literal (valuationOf q) (253)) (literal (valuationOf q) (255)) (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116]) (countLit q [117, 118, 119, 120, 121, 122, 124, 125, 126, 127, 128, 129, 130]) (count255 q) 1 (meaning253 q) (meaning255 q) hs
  change valuationOf q 253 = false ∨ valuationOf q 255 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause274 (q : Snake 81) (h : Conditions q) : valuation q 253 = false ∨ valuation q 255 = true := counterClause274 (baseVal q)

theorem counterClause275 (q : Nat → Bool) : valuationOf q 254 = false ∨ valuationOf q 256 = true := by
  have hs : count255 q = (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116]) + (countLit q [117, 118, 119, 120, 121, 122, 124, 125, 126, 127, 128, 129, 130]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116]) (l₂ := [117, 118, 119, 120, 121, 122, 124, 125, 126, 127, 128, 129, 130])
  have hm := merge_right (literal (valuationOf q) (254)) (literal (valuationOf q) (256)) (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116]) (countLit q [117, 118, 119, 120, 121, 122, 124, 125, 126, 127, 128, 129, 130]) (count255 q) 2 (meaning254 q) (meaning256 q) hs
  change valuationOf q 254 = false ∨ valuationOf q 256 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause275 (q : Snake 81) (h : Conditions q) : valuation q 254 = false ∨ valuation q 256 = true := counterClause275 (baseVal q)

theorem counterClause276 (q : Nat → Bool) : valuationOf q 229 = false ∨ valuationOf q 255 = true := by
  have hs : count255 q = (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116]) + (countLit q [117, 118, 119, 120, 121, 122, 124, 125, 126, 127, 128, 129, 130]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116]) (l₂ := [117, 118, 119, 120, 121, 122, 124, 125, 126, 127, 128, 129, 130])
  have hm := merge_left (literal (valuationOf q) (229)) (literal (valuationOf q) (255)) (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116]) (countLit q [117, 118, 119, 120, 121, 122, 124, 125, 126, 127, 128, 129, 130]) (count255 q) 1 (meaning229 q) (meaning255 q) hs
  change valuationOf q 229 = false ∨ valuationOf q 255 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause276 (q : Snake 81) (h : Conditions q) : valuation q 229 = false ∨ valuation q 255 = true := counterClause276 (baseVal q)

theorem counterClause277 (q : Nat → Bool) : valuationOf q 229 = false ∨ valuationOf q 253 = false ∨ valuationOf q 256 = true := by
  have hs : count255 q = (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116]) + (countLit q [117, 118, 119, 120, 121, 122, 124, 125, 126, 127, 128, 129, 130]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116]) (l₂ := [117, 118, 119, 120, 121, 122, 124, 125, 126, 127, 128, 129, 130])
  have hm := merge_two (literal (valuationOf q) (229)) (literal (valuationOf q) (253)) (literal (valuationOf q) (256)) (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116]) (countLit q [117, 118, 119, 120, 121, 122, 124, 125, 126, 127, 128, 129, 130]) (count255 q) 1 1 (meaning229 q) (meaning253 q) (meaning256 q) hs
  change valuationOf q 229 = false ∨ valuationOf q 253 = false ∨ valuationOf q 256 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause277 (q : Snake 81) (h : Conditions q) : valuation q 229 = false ∨ valuation q 253 = false ∨ valuation q 256 = true := counterClause277 (baseVal q)

theorem counterClause278 (q : Nat → Bool) : valuationOf q 230 = false ∨ valuationOf q 256 = true := by
  have hs : count255 q = (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116]) + (countLit q [117, 118, 119, 120, 121, 122, 124, 125, 126, 127, 128, 129, 130]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116]) (l₂ := [117, 118, 119, 120, 121, 122, 124, 125, 126, 127, 128, 129, 130])
  have hm := merge_left (literal (valuationOf q) (230)) (literal (valuationOf q) (256)) (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116]) (countLit q [117, 118, 119, 120, 121, 122, 124, 125, 126, 127, 128, 129, 130]) (count255 q) 2 (meaning230 q) (meaning256 q) hs
  change valuationOf q 230 = false ∨ valuationOf q 256 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause278 (q : Snake 81) (h : Conditions q) : valuation q 230 = false ∨ valuation q 256 = true := counterClause278 (baseVal q)

theorem counterClause279 (q : Nat → Bool) : valuationOf q 133 = false ∨ valuationOf q 257 = true := by
  have hs : count257 q = (countLit q [132]) + (countLit q [133]) := List.countP_append (p := literal q) (l₁ := [132]) (l₂ := [133])
  have hm := merge_right (literal (valuationOf q) (133)) (literal (valuationOf q) (257)) (countLit q [132]) (countLit q [133]) (count257 q) 1 (meaning133 q) (meaning257 q) hs
  change valuationOf q 133 = false ∨ valuationOf q 257 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause279 (q : Snake 81) (h : Conditions q) : valuation q 133 = false ∨ valuation q 257 = true := counterClause279 (baseVal q)

theorem counterClause280 (q : Nat → Bool) : valuationOf q 257 = false ∨ valuationOf q 259 = true := by
  have hs : count259 q = (countLit q [131]) + (countLit q [132, 133]) := List.countP_append (p := literal q) (l₁ := [131]) (l₂ := [132, 133])
  have hm := merge_right (literal (valuationOf q) (257)) (literal (valuationOf q) (259)) (countLit q [131]) (countLit q [132, 133]) (count259 q) 1 (meaning257 q) (meaning259 q) hs
  change valuationOf q 257 = false ∨ valuationOf q 259 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause280 (q : Snake 81) (h : Conditions q) : valuation q 257 = false ∨ valuation q 259 = true := counterClause280 (baseVal q)

theorem counterClause281 (q : Nat → Bool) : valuationOf q 136 = false ∨ valuationOf q 261 = true := by
  have hs : count261 q = (countLit q [135]) + (countLit q [136]) := List.countP_append (p := literal q) (l₁ := [135]) (l₂ := [136])
  have hm := merge_right (literal (valuationOf q) (136)) (literal (valuationOf q) (261)) (countLit q [135]) (countLit q [136]) (count261 q) 1 (meaning136 q) (meaning261 q) hs
  change valuationOf q 136 = false ∨ valuationOf q 261 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause281 (q : Snake 81) (h : Conditions q) : valuation q 136 = false ∨ valuation q 261 = true := counterClause281 (baseVal q)

theorem counterClause282 (q : Nat → Bool) : valuationOf q 135 = false ∨ valuationOf q 261 = true := by
  have hs : count261 q = (countLit q [135]) + (countLit q [136]) := List.countP_append (p := literal q) (l₁ := [135]) (l₂ := [136])
  have hm := merge_left (literal (valuationOf q) (135)) (literal (valuationOf q) (261)) (countLit q [135]) (countLit q [136]) (count261 q) 1 (meaning135 q) (meaning261 q) hs
  change valuationOf q 135 = false ∨ valuationOf q 261 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause282 (q : Snake 81) (h : Conditions q) : valuation q 135 = false ∨ valuation q 261 = true := counterClause282 (baseVal q)

theorem counterClause283 (q : Nat → Bool) : valuationOf q 135 = false ∨ valuationOf q 136 = false ∨ valuationOf q 262 = true := by
  have hs : count261 q = (countLit q [135]) + (countLit q [136]) := List.countP_append (p := literal q) (l₁ := [135]) (l₂ := [136])
  have hm := merge_two (literal (valuationOf q) (135)) (literal (valuationOf q) (136)) (literal (valuationOf q) (262)) (countLit q [135]) (countLit q [136]) (count261 q) 1 1 (meaning135 q) (meaning136 q) (meaning262 q) hs
  change valuationOf q 135 = false ∨ valuationOf q 136 = false ∨ valuationOf q 262 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause283 (q : Snake 81) (h : Conditions q) : valuation q 135 = false ∨ valuation q 136 = false ∨ valuation q 262 = true := counterClause283 (baseVal q)

theorem counterClause284 (q : Nat → Bool) : valuationOf q 261 = false ∨ valuationOf q 263 = true := by
  have hs : count263 q = (countLit q [134]) + (countLit q [135, 136]) := List.countP_append (p := literal q) (l₁ := [134]) (l₂ := [135, 136])
  have hm := merge_right (literal (valuationOf q) (261)) (literal (valuationOf q) (263)) (countLit q [134]) (countLit q [135, 136]) (count263 q) 1 (meaning261 q) (meaning263 q) hs
  change valuationOf q 261 = false ∨ valuationOf q 263 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause284 (q : Snake 81) (h : Conditions q) : valuation q 261 = false ∨ valuation q 263 = true := counterClause284 (baseVal q)

theorem counterClause285 (q : Nat → Bool) : valuationOf q 262 = false ∨ valuationOf q 264 = true := by
  have hs : count263 q = (countLit q [134]) + (countLit q [135, 136]) := List.countP_append (p := literal q) (l₁ := [134]) (l₂ := [135, 136])
  have hm := merge_right (literal (valuationOf q) (262)) (literal (valuationOf q) (264)) (countLit q [134]) (countLit q [135, 136]) (count263 q) 2 (meaning262 q) (meaning264 q) hs
  change valuationOf q 262 = false ∨ valuationOf q 264 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause285 (q : Snake 81) (h : Conditions q) : valuation q 262 = false ∨ valuation q 264 = true := counterClause285 (baseVal q)

theorem counterClause286 (q : Nat → Bool) : valuationOf q 134 = false ∨ valuationOf q 263 = true := by
  have hs : count263 q = (countLit q [134]) + (countLit q [135, 136]) := List.countP_append (p := literal q) (l₁ := [134]) (l₂ := [135, 136])
  have hm := merge_left (literal (valuationOf q) (134)) (literal (valuationOf q) (263)) (countLit q [134]) (countLit q [135, 136]) (count263 q) 1 (meaning134 q) (meaning263 q) hs
  change valuationOf q 134 = false ∨ valuationOf q 263 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause286 (q : Snake 81) (h : Conditions q) : valuation q 134 = false ∨ valuation q 263 = true := counterClause286 (baseVal q)

theorem counterClause287 (q : Nat → Bool) : valuationOf q 263 = false ∨ valuationOf q 265 = true := by
  have hs : count265 q = (countLit q [131, 132, 133]) + (countLit q [134, 135, 136]) := List.countP_append (p := literal q) (l₁ := [131, 132, 133]) (l₂ := [134, 135, 136])
  have hm := merge_right (literal (valuationOf q) (263)) (literal (valuationOf q) (265)) (countLit q [131, 132, 133]) (countLit q [134, 135, 136]) (count265 q) 1 (meaning263 q) (meaning265 q) hs
  change valuationOf q 263 = false ∨ valuationOf q 265 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause287 (q : Snake 81) (h : Conditions q) : valuation q 263 = false ∨ valuation q 265 = true := counterClause287 (baseVal q)

theorem counterClause288 (q : Nat → Bool) : valuationOf q 264 = false ∨ valuationOf q 266 = true := by
  have hs : count265 q = (countLit q [131, 132, 133]) + (countLit q [134, 135, 136]) := List.countP_append (p := literal q) (l₁ := [131, 132, 133]) (l₂ := [134, 135, 136])
  have hm := merge_right (literal (valuationOf q) (264)) (literal (valuationOf q) (266)) (countLit q [131, 132, 133]) (countLit q [134, 135, 136]) (count265 q) 2 (meaning264 q) (meaning266 q) hs
  change valuationOf q 264 = false ∨ valuationOf q 266 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause288 (q : Snake 81) (h : Conditions q) : valuation q 264 = false ∨ valuation q 266 = true := counterClause288 (baseVal q)

theorem block8 (q : Snake 81) (h : Conditions q) : B112E145.Block8 (valuation q) :=
  ⟨clause257 q h, clause258 q h, clause259 q h, clause260 q h, clause261 q h, clause262 q h, clause263 q h, clause264 q h, clause265 q h, clause266 q h, clause267 q h, clause268 q h, clause269 q h, clause270 q h, clause271 q h, clause272 q h, clause273 q h, clause274 q h, clause275 q h, clause276 q h, clause277 q h, clause278 q h, clause279 q h, clause280 q h, clause281 q h, clause282 q h, clause283 q h, clause284 q h, clause285 q h, clause286 q h, clause287 q h, clause288 q h⟩

end
end Snake9.Regrowth.E112145
