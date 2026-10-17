import E112171Semantics
import B112E171Inputs
namespace Snake9.Regrowth.E112171
noncomputable section
local instance blockDec14 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause449 (q : Nat → Bool) : valuationOf q 119 = false ∨ valuationOf q 233 = true := by
  have hs : count233 q = (countLit q [118]) + (countLit q [119]) := List.countP_append (p := literal q) (l₁ := [118]) (l₂ := [119])
  have hm := merge_right (literal (valuationOf q) (119)) (literal (valuationOf q) (233)) (countLit q [118]) (countLit q [119]) (count233 q) 1 (meaning119 q) (meaning233 q) hs
  change valuationOf q 119 = false ∨ valuationOf q 233 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause449 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 233 = true := counterClause449 (baseVal q)

theorem counterClause450 (q : Nat → Bool) : valuationOf q 118 = false ∨ valuationOf q 233 = true := by
  have hs : count233 q = (countLit q [118]) + (countLit q [119]) := List.countP_append (p := literal q) (l₁ := [118]) (l₂ := [119])
  have hm := merge_left (literal (valuationOf q) (118)) (literal (valuationOf q) (233)) (countLit q [118]) (countLit q [119]) (count233 q) 1 (meaning118 q) (meaning233 q) hs
  change valuationOf q 118 = false ∨ valuationOf q 233 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause450 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 233 = true := counterClause450 (baseVal q)

theorem counterClause451 (q : Nat → Bool) : valuationOf q 118 = false ∨ valuationOf q 119 = false ∨ valuationOf q 234 = true := by
  have hs : count233 q = (countLit q [118]) + (countLit q [119]) := List.countP_append (p := literal q) (l₁ := [118]) (l₂ := [119])
  have hm := merge_two (literal (valuationOf q) (118)) (literal (valuationOf q) (119)) (literal (valuationOf q) (234)) (countLit q [118]) (countLit q [119]) (count233 q) 1 1 (meaning118 q) (meaning119 q) (meaning234 q) hs
  change valuationOf q 118 = false ∨ valuationOf q 119 = false ∨ valuationOf q 234 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause451 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 119 = false ∨ valuation q 234 = true := counterClause451 (baseVal q)

theorem counterClause452 (q : Nat → Bool) : valuationOf q 233 = false ∨ valuationOf q 237 = true := by
  have hs : count237 q = (countLit q [118, 119]) + (countLit q [120, 121]) := List.countP_append (p := literal q) (l₁ := [118, 119]) (l₂ := [120, 121])
  have hm := merge_left (literal (valuationOf q) (233)) (literal (valuationOf q) (237)) (countLit q [118, 119]) (countLit q [120, 121]) (count237 q) 1 (meaning233 q) (meaning237 q) hs
  change valuationOf q 233 = false ∨ valuationOf q 237 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause452 (q : Snake 81) (h : Conditions q) : valuation q 233 = false ∨ valuation q 237 = true := counterClause452 (baseVal q)

theorem counterClause453 (q : Nat → Bool) : valuationOf q 234 = false ∨ valuationOf q 238 = true := by
  have hs : count237 q = (countLit q [118, 119]) + (countLit q [120, 121]) := List.countP_append (p := literal q) (l₁ := [118, 119]) (l₂ := [120, 121])
  have hm := merge_left (literal (valuationOf q) (234)) (literal (valuationOf q) (238)) (countLit q [118, 119]) (countLit q [120, 121]) (count237 q) 2 (meaning234 q) (meaning238 q) hs
  change valuationOf q 234 = false ∨ valuationOf q 238 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause453 (q : Snake 81) (h : Conditions q) : valuation q 234 = false ∨ valuation q 238 = true := counterClause453 (baseVal q)

theorem counterClause454 (q : Nat → Bool) : valuationOf q 237 = false ∨ valuationOf q 239 = true := by
  have hs : count239 q = (countLit q [115, 116, 117]) + (countLit q [118, 119, 120, 121]) := List.countP_append (p := literal q) (l₁ := [115, 116, 117]) (l₂ := [118, 119, 120, 121])
  have hm := merge_right (literal (valuationOf q) (237)) (literal (valuationOf q) (239)) (countLit q [115, 116, 117]) (countLit q [118, 119, 120, 121]) (count239 q) 1 (meaning237 q) (meaning239 q) hs
  change valuationOf q 237 = false ∨ valuationOf q 239 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause454 (q : Snake 81) (h : Conditions q) : valuation q 237 = false ∨ valuation q 239 = true := counterClause454 (baseVal q)

theorem counterClause455 (q : Nat → Bool) : valuationOf q 238 = false ∨ valuationOf q 240 = true := by
  have hs : count239 q = (countLit q [115, 116, 117]) + (countLit q [118, 119, 120, 121]) := List.countP_append (p := literal q) (l₁ := [115, 116, 117]) (l₂ := [118, 119, 120, 121])
  have hm := merge_right (literal (valuationOf q) (238)) (literal (valuationOf q) (240)) (countLit q [115, 116, 117]) (countLit q [118, 119, 120, 121]) (count239 q) 2 (meaning238 q) (meaning240 q) hs
  change valuationOf q 238 = false ∨ valuationOf q 240 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause455 (q : Snake 81) (h : Conditions q) : valuation q 238 = false ∨ valuation q 240 = true := counterClause455 (baseVal q)

theorem counterClause456 (q : Nat → Bool) : valuationOf q 231 = false ∨ valuationOf q 239 = true := by
  have hs : count239 q = (countLit q [115, 116, 117]) + (countLit q [118, 119, 120, 121]) := List.countP_append (p := literal q) (l₁ := [115, 116, 117]) (l₂ := [118, 119, 120, 121])
  have hm := merge_left (literal (valuationOf q) (231)) (literal (valuationOf q) (239)) (countLit q [115, 116, 117]) (countLit q [118, 119, 120, 121]) (count239 q) 1 (meaning231 q) (meaning239 q) hs
  change valuationOf q 231 = false ∨ valuationOf q 239 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause456 (q : Snake 81) (h : Conditions q) : valuation q 231 = false ∨ valuation q 239 = true := counterClause456 (baseVal q)

theorem counterClause457 (q : Nat → Bool) : valuationOf q 231 = false ∨ valuationOf q 237 = false ∨ valuationOf q 240 = true := by
  have hs : count239 q = (countLit q [115, 116, 117]) + (countLit q [118, 119, 120, 121]) := List.countP_append (p := literal q) (l₁ := [115, 116, 117]) (l₂ := [118, 119, 120, 121])
  have hm := merge_two (literal (valuationOf q) (231)) (literal (valuationOf q) (237)) (literal (valuationOf q) (240)) (countLit q [115, 116, 117]) (countLit q [118, 119, 120, 121]) (count239 q) 1 1 (meaning231 q) (meaning237 q) (meaning240 q) hs
  change valuationOf q 231 = false ∨ valuationOf q 237 = false ∨ valuationOf q 240 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause457 (q : Snake 81) (h : Conditions q) : valuation q 231 = false ∨ valuation q 237 = false ∨ valuation q 240 = true := counterClause457 (baseVal q)

theorem counterClause458 (q : Nat → Bool) : valuationOf q 125 = false ∨ valuationOf q 241 = true := by
  have hs : count241 q = (countLit q [123]) + (countLit q [125]) := List.countP_append (p := literal q) (l₁ := [123]) (l₂ := [125])
  have hm := merge_right (literal (valuationOf q) (125)) (literal (valuationOf q) (241)) (countLit q [123]) (countLit q [125]) (count241 q) 1 (meaning125 q) (meaning241 q) hs
  change valuationOf q 125 = false ∨ valuationOf q 241 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause458 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 241 = true := counterClause458 (baseVal q)

theorem counterClause459 (q : Nat → Bool) : valuationOf q 123 = false ∨ valuationOf q 241 = true := by
  have hs : count241 q = (countLit q [123]) + (countLit q [125]) := List.countP_append (p := literal q) (l₁ := [123]) (l₂ := [125])
  have hm := merge_left (literal (valuationOf q) (123)) (literal (valuationOf q) (241)) (countLit q [123]) (countLit q [125]) (count241 q) 1 (meaning123 q) (meaning241 q) hs
  change valuationOf q 123 = false ∨ valuationOf q 241 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause459 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 241 = true := counterClause459 (baseVal q)

theorem counterClause460 (q : Nat → Bool) : valuationOf q 241 = false ∨ valuationOf q 243 = true := by
  have hs : count243 q = (countLit q [122]) + (countLit q [123, 125]) := List.countP_append (p := literal q) (l₁ := [122]) (l₂ := [123, 125])
  have hm := merge_right (literal (valuationOf q) (241)) (literal (valuationOf q) (243)) (countLit q [122]) (countLit q [123, 125]) (count243 q) 1 (meaning241 q) (meaning243 q) hs
  change valuationOf q 241 = false ∨ valuationOf q 243 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause460 (q : Snake 81) (h : Conditions q) : valuation q 241 = false ∨ valuation q 243 = true := counterClause460 (baseVal q)

theorem counterClause461 (q : Nat → Bool) : valuationOf q 122 = false ∨ valuationOf q 243 = true := by
  have hs : count243 q = (countLit q [122]) + (countLit q [123, 125]) := List.countP_append (p := literal q) (l₁ := [122]) (l₂ := [123, 125])
  have hm := merge_left (literal (valuationOf q) (122)) (literal (valuationOf q) (243)) (countLit q [122]) (countLit q [123, 125]) (count243 q) 1 (meaning122 q) (meaning243 q) hs
  change valuationOf q 122 = false ∨ valuationOf q 243 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause461 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 243 = true := counterClause461 (baseVal q)

theorem counterClause462 (q : Nat → Bool) : valuationOf q 128 = false ∨ valuationOf q 247 = true := by
  have hs : count247 q = (countLit q [128]) + (countLit q [129]) := List.countP_append (p := literal q) (l₁ := [128]) (l₂ := [129])
  have hm := merge_left (literal (valuationOf q) (128)) (literal (valuationOf q) (247)) (countLit q [128]) (countLit q [129]) (count247 q) 1 (meaning128 q) (meaning247 q) hs
  change valuationOf q 128 = false ∨ valuationOf q 247 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause462 (q : Snake 81) (h : Conditions q) : valuation q 128 = false ∨ valuation q 247 = true := counterClause462 (baseVal q)

theorem counterClause463 (q : Nat → Bool) : valuationOf q 247 = false ∨ valuationOf q 249 = true := by
  have hs : count249 q = (countLit q [126, 127]) + (countLit q [128, 129]) := List.countP_append (p := literal q) (l₁ := [126, 127]) (l₂ := [128, 129])
  have hm := merge_right (literal (valuationOf q) (247)) (literal (valuationOf q) (249)) (countLit q [126, 127]) (countLit q [128, 129]) (count249 q) 1 (meaning247 q) (meaning249 q) hs
  change valuationOf q 247 = false ∨ valuationOf q 249 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause463 (q : Snake 81) (h : Conditions q) : valuation q 247 = false ∨ valuation q 249 = true := counterClause463 (baseVal q)

theorem counterClause464 (q : Nat → Bool) : valuationOf q 249 = false ∨ valuationOf q 251 = true := by
  have hs : count251 q = (countLit q [122, 123, 125]) + (countLit q [126, 127, 128, 129]) := List.countP_append (p := literal q) (l₁ := [122, 123, 125]) (l₂ := [126, 127, 128, 129])
  have hm := merge_right (literal (valuationOf q) (249)) (literal (valuationOf q) (251)) (countLit q [122, 123, 125]) (countLit q [126, 127, 128, 129]) (count251 q) 1 (meaning249 q) (meaning251 q) hs
  change valuationOf q 249 = false ∨ valuationOf q 251 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause464 (q : Snake 81) (h : Conditions q) : valuation q 249 = false ∨ valuation q 251 = true := counterClause464 (baseVal q)

theorem counterClause465 (q : Nat → Bool) : valuationOf q 243 = false ∨ valuationOf q 251 = true := by
  have hs : count251 q = (countLit q [122, 123, 125]) + (countLit q [126, 127, 128, 129]) := List.countP_append (p := literal q) (l₁ := [122, 123, 125]) (l₂ := [126, 127, 128, 129])
  have hm := merge_left (literal (valuationOf q) (243)) (literal (valuationOf q) (251)) (countLit q [122, 123, 125]) (countLit q [126, 127, 128, 129]) (count251 q) 1 (meaning243 q) (meaning251 q) hs
  change valuationOf q 243 = false ∨ valuationOf q 251 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause465 (q : Snake 81) (h : Conditions q) : valuation q 243 = false ∨ valuation q 251 = true := counterClause465 (baseVal q)

theorem counterClause466 (q : Nat → Bool) : valuationOf q 251 = false ∨ valuationOf q 253 = true := by
  have hs : count253 q = (countLit q [115, 116, 117, 118, 119, 120, 121]) + (countLit q [122, 123, 125, 126, 127, 128, 129]) := List.countP_append (p := literal q) (l₁ := [115, 116, 117, 118, 119, 120, 121]) (l₂ := [122, 123, 125, 126, 127, 128, 129])
  have hm := merge_right (literal (valuationOf q) (251)) (literal (valuationOf q) (253)) (countLit q [115, 116, 117, 118, 119, 120, 121]) (countLit q [122, 123, 125, 126, 127, 128, 129]) (count253 q) 1 (meaning251 q) (meaning253 q) hs
  change valuationOf q 251 = false ∨ valuationOf q 253 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause466 (q : Snake 81) (h : Conditions q) : valuation q 251 = false ∨ valuation q 253 = true := counterClause466 (baseVal q)

theorem counterClause467 (q : Nat → Bool) : valuationOf q 239 = false ∨ valuationOf q 253 = true := by
  have hs : count253 q = (countLit q [115, 116, 117, 118, 119, 120, 121]) + (countLit q [122, 123, 125, 126, 127, 128, 129]) := List.countP_append (p := literal q) (l₁ := [115, 116, 117, 118, 119, 120, 121]) (l₂ := [122, 123, 125, 126, 127, 128, 129])
  have hm := merge_left (literal (valuationOf q) (239)) (literal (valuationOf q) (253)) (countLit q [115, 116, 117, 118, 119, 120, 121]) (countLit q [122, 123, 125, 126, 127, 128, 129]) (count253 q) 1 (meaning239 q) (meaning253 q) hs
  change valuationOf q 239 = false ∨ valuationOf q 253 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause467 (q : Snake 81) (h : Conditions q) : valuation q 239 = false ∨ valuation q 253 = true := counterClause467 (baseVal q)

theorem counterClause468 (q : Nat → Bool) : valuationOf q 239 = false ∨ valuationOf q 251 = false ∨ valuationOf q 254 = true := by
  have hs : count253 q = (countLit q [115, 116, 117, 118, 119, 120, 121]) + (countLit q [122, 123, 125, 126, 127, 128, 129]) := List.countP_append (p := literal q) (l₁ := [115, 116, 117, 118, 119, 120, 121]) (l₂ := [122, 123, 125, 126, 127, 128, 129])
  have hm := merge_two (literal (valuationOf q) (239)) (literal (valuationOf q) (251)) (literal (valuationOf q) (254)) (countLit q [115, 116, 117, 118, 119, 120, 121]) (countLit q [122, 123, 125, 126, 127, 128, 129]) (count253 q) 1 1 (meaning239 q) (meaning251 q) (meaning254 q) hs
  change valuationOf q 239 = false ∨ valuationOf q 251 = false ∨ valuationOf q 254 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause468 (q : Snake 81) (h : Conditions q) : valuation q 239 = false ∨ valuation q 251 = false ∨ valuation q 254 = true := counterClause468 (baseVal q)

theorem counterClause469 (q : Nat → Bool) : valuationOf q 240 = false ∨ valuationOf q 254 = true := by
  have hs : count253 q = (countLit q [115, 116, 117, 118, 119, 120, 121]) + (countLit q [122, 123, 125, 126, 127, 128, 129]) := List.countP_append (p := literal q) (l₁ := [115, 116, 117, 118, 119, 120, 121]) (l₂ := [122, 123, 125, 126, 127, 128, 129])
  have hm := merge_left (literal (valuationOf q) (240)) (literal (valuationOf q) (254)) (countLit q [115, 116, 117, 118, 119, 120, 121]) (countLit q [122, 123, 125, 126, 127, 128, 129]) (count253 q) 2 (meaning240 q) (meaning254 q) hs
  change valuationOf q 240 = false ∨ valuationOf q 254 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause469 (q : Snake 81) (h : Conditions q) : valuation q 240 = false ∨ valuation q 254 = true := counterClause469 (baseVal q)

theorem counterClause470 (q : Nat → Bool) : valuationOf q 132 = false ∨ valuationOf q 255 = true := by
  have hs : count255 q = (countLit q [131]) + (countLit q [132]) := List.countP_append (p := literal q) (l₁ := [131]) (l₂ := [132])
  have hm := merge_right (literal (valuationOf q) (132)) (literal (valuationOf q) (255)) (countLit q [131]) (countLit q [132]) (count255 q) 1 (meaning132 q) (meaning255 q) hs
  change valuationOf q 132 = false ∨ valuationOf q 255 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause470 (q : Snake 81) (h : Conditions q) : valuation q 132 = false ∨ valuation q 255 = true := counterClause470 (baseVal q)

theorem counterClause471 (q : Nat → Bool) : valuationOf q 131 = false ∨ valuationOf q 255 = true := by
  have hs : count255 q = (countLit q [131]) + (countLit q [132]) := List.countP_append (p := literal q) (l₁ := [131]) (l₂ := [132])
  have hm := merge_left (literal (valuationOf q) (131)) (literal (valuationOf q) (255)) (countLit q [131]) (countLit q [132]) (count255 q) 1 (meaning131 q) (meaning255 q) hs
  change valuationOf q 131 = false ∨ valuationOf q 255 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause471 (q : Snake 81) (h : Conditions q) : valuation q 131 = false ∨ valuation q 255 = true := counterClause471 (baseVal q)

theorem counterClause472 (q : Nat → Bool) : valuationOf q 255 = false ∨ valuationOf q 257 = true := by
  have hs : count257 q = (countLit q [130]) + (countLit q [131, 132]) := List.countP_append (p := literal q) (l₁ := [130]) (l₂ := [131, 132])
  have hm := merge_right (literal (valuationOf q) (255)) (literal (valuationOf q) (257)) (countLit q [130]) (countLit q [131, 132]) (count257 q) 1 (meaning255 q) (meaning257 q) hs
  change valuationOf q 255 = false ∨ valuationOf q 257 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause472 (q : Snake 81) (h : Conditions q) : valuation q 255 = false ∨ valuation q 257 = true := counterClause472 (baseVal q)

theorem counterClause473 (q : Nat → Bool) : valuationOf q 133 = false ∨ valuationOf q 259 = true := by
  have hs : count259 q = (countLit q [133]) + (countLit q [134]) := List.countP_append (p := literal q) (l₁ := [133]) (l₂ := [134])
  have hm := merge_left (literal (valuationOf q) (133)) (literal (valuationOf q) (259)) (countLit q [133]) (countLit q [134]) (count259 q) 1 (meaning133 q) (meaning259 q) hs
  change valuationOf q 133 = false ∨ valuationOf q 259 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause473 (q : Snake 81) (h : Conditions q) : valuation q 133 = false ∨ valuation q 259 = true := counterClause473 (baseVal q)

theorem counterClause474 (q : Nat → Bool) : valuationOf q 135 = false ∨ valuationOf q 261 = true := by
  have hs : count261 q = (countLit q [135]) + (countLit q [136]) := List.countP_append (p := literal q) (l₁ := [135]) (l₂ := [136])
  have hm := merge_left (literal (valuationOf q) (135)) (literal (valuationOf q) (261)) (countLit q [135]) (countLit q [136]) (count261 q) 1 (meaning135 q) (meaning261 q) hs
  change valuationOf q 135 = false ∨ valuationOf q 261 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause474 (q : Snake 81) (h : Conditions q) : valuation q 135 = false ∨ valuation q 261 = true := counterClause474 (baseVal q)

theorem counterClause475 (q : Nat → Bool) : valuationOf q 261 = false ∨ valuationOf q 263 = true := by
  have hs : count263 q = (countLit q [133, 134]) + (countLit q [135, 136]) := List.countP_append (p := literal q) (l₁ := [133, 134]) (l₂ := [135, 136])
  have hm := merge_right (literal (valuationOf q) (261)) (literal (valuationOf q) (263)) (countLit q [133, 134]) (countLit q [135, 136]) (count263 q) 1 (meaning261 q) (meaning263 q) hs
  change valuationOf q 261 = false ∨ valuationOf q 263 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause475 (q : Snake 81) (h : Conditions q) : valuation q 261 = false ∨ valuation q 263 = true := counterClause475 (baseVal q)

theorem counterClause476 (q : Nat → Bool) : valuationOf q 259 = false ∨ valuationOf q 263 = true := by
  have hs : count263 q = (countLit q [133, 134]) + (countLit q [135, 136]) := List.countP_append (p := literal q) (l₁ := [133, 134]) (l₂ := [135, 136])
  have hm := merge_left (literal (valuationOf q) (259)) (literal (valuationOf q) (263)) (countLit q [133, 134]) (countLit q [135, 136]) (count263 q) 1 (meaning259 q) (meaning263 q) hs
  change valuationOf q 259 = false ∨ valuationOf q 263 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause476 (q : Snake 81) (h : Conditions q) : valuation q 259 = false ∨ valuation q 263 = true := counterClause476 (baseVal q)

theorem counterClause477 (q : Nat → Bool) : valuationOf q 263 = false ∨ valuationOf q 265 = true := by
  have hs : count265 q = (countLit q [130, 131, 132]) + (countLit q [133, 134, 135, 136]) := List.countP_append (p := literal q) (l₁ := [130, 131, 132]) (l₂ := [133, 134, 135, 136])
  have hm := merge_right (literal (valuationOf q) (263)) (literal (valuationOf q) (265)) (countLit q [130, 131, 132]) (countLit q [133, 134, 135, 136]) (count265 q) 1 (meaning263 q) (meaning265 q) hs
  change valuationOf q 263 = false ∨ valuationOf q 265 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause477 (q : Snake 81) (h : Conditions q) : valuation q 263 = false ∨ valuation q 265 = true := counterClause477 (baseVal q)

theorem counterClause478 (q : Nat → Bool) : valuationOf q 257 = false ∨ valuationOf q 265 = true := by
  have hs : count265 q = (countLit q [130, 131, 132]) + (countLit q [133, 134, 135, 136]) := List.countP_append (p := literal q) (l₁ := [130, 131, 132]) (l₂ := [133, 134, 135, 136])
  have hm := merge_left (literal (valuationOf q) (257)) (literal (valuationOf q) (265)) (countLit q [130, 131, 132]) (countLit q [133, 134, 135, 136]) (count265 q) 1 (meaning257 q) (meaning265 q) hs
  change valuationOf q 257 = false ∨ valuationOf q 265 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause478 (q : Snake 81) (h : Conditions q) : valuation q 257 = false ∨ valuation q 265 = true := counterClause478 (baseVal q)

theorem counterClause479 (q : Nat → Bool) : valuationOf q 257 = false ∨ valuationOf q 263 = false ∨ valuationOf q 266 = true := by
  have hs : count265 q = (countLit q [130, 131, 132]) + (countLit q [133, 134, 135, 136]) := List.countP_append (p := literal q) (l₁ := [130, 131, 132]) (l₂ := [133, 134, 135, 136])
  have hm := merge_two (literal (valuationOf q) (257)) (literal (valuationOf q) (263)) (literal (valuationOf q) (266)) (countLit q [130, 131, 132]) (countLit q [133, 134, 135, 136]) (count265 q) 1 1 (meaning257 q) (meaning263 q) (meaning266 q) hs
  change valuationOf q 257 = false ∨ valuationOf q 263 = false ∨ valuationOf q 266 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause479 (q : Snake 81) (h : Conditions q) : valuation q 257 = false ∨ valuation q 263 = false ∨ valuation q 266 = true := counterClause479 (baseVal q)

theorem counterClause480 (q : Nat → Bool) : valuationOf q 137 = false ∨ valuationOf q 269 = true := by
  have hs : count269 q = (countLit q [137]) + (countLit q [138, 139]) := List.countP_append (p := literal q) (l₁ := [137]) (l₂ := [138, 139])
  have hm := merge_left (literal (valuationOf q) (137)) (literal (valuationOf q) (269)) (countLit q [137]) (countLit q [138, 139]) (count269 q) 1 (meaning137 q) (meaning269 q) hs
  change valuationOf q 137 = false ∨ valuationOf q 269 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause480 (q : Snake 81) (h : Conditions q) : valuation q 137 = false ∨ valuation q 269 = true := counterClause480 (baseVal q)

theorem block14 (q : Snake 81) (h : Conditions q) : B112E171.Block14 (valuation q) :=
  ⟨clause449 q h, clause450 q h, clause451 q h, clause452 q h, clause453 q h, clause454 q h, clause455 q h, clause456 q h, clause457 q h, clause458 q h, clause459 q h, clause460 q h, clause461 q h, clause462 q h, clause463 q h, clause464 q h, clause465 q h, clause466 q h, clause467 q h, clause468 q h, clause469 q h, clause470 q h, clause471 q h, clause472 q h, clause473 q h, clause474 q h, clause475 q h, clause476 q h, clause477 q h, clause478 q h, clause479 q h, clause480 q h⟩

end
end Snake9.Regrowth.E112171
