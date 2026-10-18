import E112161Semantics
import B112E161Inputs
namespace Snake9.Regrowth.E112161
noncomputable section
local instance blockDec15 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause481 (q : Nat → Bool) : valuationOf q 227 = false ∨ valuationOf q 229 = true := by
  have hs : count229 q = (countLit q [115]) + (countLit q [116, 117]) := List.countP_append (p := literal q) (l₁ := [115]) (l₂ := [116, 117])
  have hm := merge_right (literal (valuationOf q) (227)) (literal (valuationOf q) (229)) (countLit q [115]) (countLit q [116, 117]) (count229 q) 1 (meaning227 q) (meaning229 q) hs
  change valuationOf q 227 = false ∨ valuationOf q 229 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause481 (q : Snake 81) (h : Conditions q) : valuation q 227 = false ∨ valuation q 229 = true := counterClause481 (baseVal q)

theorem counterClause482 (q : Nat → Bool) : valuationOf q 229 = false ∨ valuationOf q 231 = true := by
  have hs : count231 q = (countLit q [112, 113, 114]) + (countLit q [115, 116, 117]) := List.countP_append (p := literal q) (l₁ := [112, 113, 114]) (l₂ := [115, 116, 117])
  have hm := merge_right (literal (valuationOf q) (229)) (literal (valuationOf q) (231)) (countLit q [112, 113, 114]) (countLit q [115, 116, 117]) (count231 q) 1 (meaning229 q) (meaning231 q) hs
  change valuationOf q 229 = false ∨ valuationOf q 231 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause482 (q : Snake 81) (h : Conditions q) : valuation q 229 = false ∨ valuation q 231 = true := counterClause482 (baseVal q)

theorem counterClause483 (q : Nat → Bool) : valuationOf q 225 = false ∨ valuationOf q 231 = true := by
  have hs : count231 q = (countLit q [112, 113, 114]) + (countLit q [115, 116, 117]) := List.countP_append (p := literal q) (l₁ := [112, 113, 114]) (l₂ := [115, 116, 117])
  have hm := merge_left (literal (valuationOf q) (225)) (literal (valuationOf q) (231)) (countLit q [112, 113, 114]) (countLit q [115, 116, 117]) (count231 q) 1 (meaning225 q) (meaning231 q) hs
  change valuationOf q 225 = false ∨ valuationOf q 231 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause483 (q : Snake 81) (h : Conditions q) : valuation q 225 = false ∨ valuation q 231 = true := counterClause483 (baseVal q)

theorem counterClause484 (q : Nat → Bool) : valuationOf q 225 = false ∨ valuationOf q 229 = false ∨ valuationOf q 232 = true := by
  have hs : count231 q = (countLit q [112, 113, 114]) + (countLit q [115, 116, 117]) := List.countP_append (p := literal q) (l₁ := [112, 113, 114]) (l₂ := [115, 116, 117])
  have hm := merge_two (literal (valuationOf q) (225)) (literal (valuationOf q) (229)) (literal (valuationOf q) (232)) (countLit q [112, 113, 114]) (countLit q [115, 116, 117]) (count231 q) 1 1 (meaning225 q) (meaning229 q) (meaning232 q) hs
  change valuationOf q 225 = false ∨ valuationOf q 229 = false ∨ valuationOf q 232 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause484 (q : Snake 81) (h : Conditions q) : valuation q 225 = false ∨ valuation q 229 = false ∨ valuation q 232 = true := counterClause484 (baseVal q)

theorem counterClause485 (q : Nat → Bool) : valuationOf q 121 = false ∨ valuationOf q 233 = true := by
  have hs : count233 q = (countLit q [120]) + (countLit q [121]) := List.countP_append (p := literal q) (l₁ := [120]) (l₂ := [121])
  have hm := merge_right (literal (valuationOf q) (121)) (literal (valuationOf q) (233)) (countLit q [120]) (countLit q [121]) (count233 q) 1 (meaning121 q) (meaning233 q) hs
  change valuationOf q 121 = false ∨ valuationOf q 233 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause485 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 233 = true := counterClause485 (baseVal q)

theorem counterClause486 (q : Nat → Bool) : valuationOf q 233 = false ∨ valuationOf q 235 = true := by
  have hs : count235 q = (countLit q [119]) + (countLit q [120, 121]) := List.countP_append (p := literal q) (l₁ := [119]) (l₂ := [120, 121])
  have hm := merge_right (literal (valuationOf q) (233)) (literal (valuationOf q) (235)) (countLit q [119]) (countLit q [120, 121]) (count235 q) 1 (meaning233 q) (meaning235 q) hs
  change valuationOf q 233 = false ∨ valuationOf q 235 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause486 (q : Snake 81) (h : Conditions q) : valuation q 233 = false ∨ valuation q 235 = true := counterClause486 (baseVal q)

theorem counterClause487 (q : Nat → Bool) : valuationOf q 119 = false ∨ valuationOf q 235 = true := by
  have hs : count235 q = (countLit q [119]) + (countLit q [120, 121]) := List.countP_append (p := literal q) (l₁ := [119]) (l₂ := [120, 121])
  have hm := merge_left (literal (valuationOf q) (119)) (literal (valuationOf q) (235)) (countLit q [119]) (countLit q [120, 121]) (count235 q) 1 (meaning119 q) (meaning235 q) hs
  change valuationOf q 119 = false ∨ valuationOf q 235 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause487 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 235 = true := counterClause487 (baseVal q)

theorem counterClause488 (q : Nat → Bool) : valuationOf q 123 = false ∨ valuationOf q 237 = true := by
  have hs : count237 q = (countLit q [122]) + (countLit q [123]) := List.countP_append (p := literal q) (l₁ := [122]) (l₂ := [123])
  have hm := merge_right (literal (valuationOf q) (123)) (literal (valuationOf q) (237)) (countLit q [122]) (countLit q [123]) (count237 q) 1 (meaning123 q) (meaning237 q) hs
  change valuationOf q 123 = false ∨ valuationOf q 237 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause488 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 237 = true := counterClause488 (baseVal q)

theorem counterClause489 (q : Nat → Bool) : valuationOf q 125 = false ∨ valuationOf q 239 = true := by
  have hs : count239 q = (countLit q [124]) + (countLit q [125]) := List.countP_append (p := literal q) (l₁ := [124]) (l₂ := [125])
  have hm := merge_right (literal (valuationOf q) (125)) (literal (valuationOf q) (239)) (countLit q [124]) (countLit q [125]) (count239 q) 1 (meaning125 q) (meaning239 q) hs
  change valuationOf q 125 = false ∨ valuationOf q 239 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause489 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 239 = true := counterClause489 (baseVal q)

theorem counterClause490 (q : Nat → Bool) : valuationOf q 239 = false ∨ valuationOf q 241 = true := by
  have hs : count241 q = (countLit q [122, 123]) + (countLit q [124, 125]) := List.countP_append (p := literal q) (l₁ := [122, 123]) (l₂ := [124, 125])
  have hm := merge_right (literal (valuationOf q) (239)) (literal (valuationOf q) (241)) (countLit q [122, 123]) (countLit q [124, 125]) (count241 q) 1 (meaning239 q) (meaning241 q) hs
  change valuationOf q 239 = false ∨ valuationOf q 241 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause490 (q : Snake 81) (h : Conditions q) : valuation q 239 = false ∨ valuation q 241 = true := counterClause490 (baseVal q)

theorem counterClause491 (q : Nat → Bool) : valuationOf q 237 = false ∨ valuationOf q 241 = true := by
  have hs : count241 q = (countLit q [122, 123]) + (countLit q [124, 125]) := List.countP_append (p := literal q) (l₁ := [122, 123]) (l₂ := [124, 125])
  have hm := merge_left (literal (valuationOf q) (237)) (literal (valuationOf q) (241)) (countLit q [122, 123]) (countLit q [124, 125]) (count241 q) 1 (meaning237 q) (meaning241 q) hs
  change valuationOf q 237 = false ∨ valuationOf q 241 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause491 (q : Snake 81) (h : Conditions q) : valuation q 237 = false ∨ valuation q 241 = true := counterClause491 (baseVal q)

theorem counterClause492 (q : Nat → Bool) : valuationOf q 241 = false ∨ valuationOf q 243 = true := by
  have hs : count243 q = (countLit q [119, 120, 121]) + (countLit q [122, 123, 124, 125]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121]) (l₂ := [122, 123, 124, 125])
  have hm := merge_right (literal (valuationOf q) (241)) (literal (valuationOf q) (243)) (countLit q [119, 120, 121]) (countLit q [122, 123, 124, 125]) (count243 q) 1 (meaning241 q) (meaning243 q) hs
  change valuationOf q 241 = false ∨ valuationOf q 243 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause492 (q : Snake 81) (h : Conditions q) : valuation q 241 = false ∨ valuation q 243 = true := counterClause492 (baseVal q)

theorem counterClause493 (q : Nat → Bool) : valuationOf q 235 = false ∨ valuationOf q 243 = true := by
  have hs : count243 q = (countLit q [119, 120, 121]) + (countLit q [122, 123, 124, 125]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121]) (l₂ := [122, 123, 124, 125])
  have hm := merge_left (literal (valuationOf q) (235)) (literal (valuationOf q) (243)) (countLit q [119, 120, 121]) (countLit q [122, 123, 124, 125]) (count243 q) 1 (meaning235 q) (meaning243 q) hs
  change valuationOf q 235 = false ∨ valuationOf q 243 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause493 (q : Snake 81) (h : Conditions q) : valuation q 235 = false ∨ valuation q 243 = true := counterClause493 (baseVal q)

theorem counterClause494 (q : Nat → Bool) : valuationOf q 243 = false ∨ valuationOf q 245 = true := by
  have hs : count245 q = (countLit q [112, 113, 114, 115, 116, 117]) + (countLit q [119, 120, 121, 122, 123, 124, 125]) := List.countP_append (p := literal q) (l₁ := [112, 113, 114, 115, 116, 117]) (l₂ := [119, 120, 121, 122, 123, 124, 125])
  have hm := merge_right (literal (valuationOf q) (243)) (literal (valuationOf q) (245)) (countLit q [112, 113, 114, 115, 116, 117]) (countLit q [119, 120, 121, 122, 123, 124, 125]) (count245 q) 1 (meaning243 q) (meaning245 q) hs
  change valuationOf q 243 = false ∨ valuationOf q 245 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause494 (q : Snake 81) (h : Conditions q) : valuation q 243 = false ∨ valuation q 245 = true := counterClause494 (baseVal q)

theorem counterClause495 (q : Nat → Bool) : valuationOf q 231 = false ∨ valuationOf q 245 = true := by
  have hs : count245 q = (countLit q [112, 113, 114, 115, 116, 117]) + (countLit q [119, 120, 121, 122, 123, 124, 125]) := List.countP_append (p := literal q) (l₁ := [112, 113, 114, 115, 116, 117]) (l₂ := [119, 120, 121, 122, 123, 124, 125])
  have hm := merge_left (literal (valuationOf q) (231)) (literal (valuationOf q) (245)) (countLit q [112, 113, 114, 115, 116, 117]) (countLit q [119, 120, 121, 122, 123, 124, 125]) (count245 q) 1 (meaning231 q) (meaning245 q) hs
  change valuationOf q 231 = false ∨ valuationOf q 245 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause495 (q : Snake 81) (h : Conditions q) : valuation q 231 = false ∨ valuation q 245 = true := counterClause495 (baseVal q)

theorem counterClause496 (q : Nat → Bool) : valuationOf q 231 = false ∨ valuationOf q 243 = false ∨ valuationOf q 246 = true := by
  have hs : count245 q = (countLit q [112, 113, 114, 115, 116, 117]) + (countLit q [119, 120, 121, 122, 123, 124, 125]) := List.countP_append (p := literal q) (l₁ := [112, 113, 114, 115, 116, 117]) (l₂ := [119, 120, 121, 122, 123, 124, 125])
  have hm := merge_two (literal (valuationOf q) (231)) (literal (valuationOf q) (243)) (literal (valuationOf q) (246)) (countLit q [112, 113, 114, 115, 116, 117]) (countLit q [119, 120, 121, 122, 123, 124, 125]) (count245 q) 1 1 (meaning231 q) (meaning243 q) (meaning246 q) hs
  change valuationOf q 231 = false ∨ valuationOf q 243 = false ∨ valuationOf q 246 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause496 (q : Snake 81) (h : Conditions q) : valuation q 231 = false ∨ valuation q 243 = false ∨ valuation q 246 = true := counterClause496 (baseVal q)

theorem counterClause497 (q : Nat → Bool) : valuationOf q 232 = false ∨ valuationOf q 246 = true := by
  have hs : count245 q = (countLit q [112, 113, 114, 115, 116, 117]) + (countLit q [119, 120, 121, 122, 123, 124, 125]) := List.countP_append (p := literal q) (l₁ := [112, 113, 114, 115, 116, 117]) (l₂ := [119, 120, 121, 122, 123, 124, 125])
  have hm := merge_left (literal (valuationOf q) (232)) (literal (valuationOf q) (246)) (countLit q [112, 113, 114, 115, 116, 117]) (countLit q [119, 120, 121, 122, 123, 124, 125]) (count245 q) 2 (meaning232 q) (meaning246 q) hs
  change valuationOf q 232 = false ∨ valuationOf q 246 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause497 (q : Snake 81) (h : Conditions q) : valuation q 232 = false ∨ valuation q 246 = true := counterClause497 (baseVal q)

theorem counterClause498 (q : Nat → Bool) : valuationOf q 128 = false ∨ valuationOf q 247 = true := by
  have hs : count247 q = (countLit q [127]) + (countLit q [128]) := List.countP_append (p := literal q) (l₁ := [127]) (l₂ := [128])
  have hm := merge_right (literal (valuationOf q) (128)) (literal (valuationOf q) (247)) (countLit q [127]) (countLit q [128]) (count247 q) 1 (meaning128 q) (meaning247 q) hs
  change valuationOf q 128 = false ∨ valuationOf q 247 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause498 (q : Snake 81) (h : Conditions q) : valuation q 128 = false ∨ valuation q 247 = true := counterClause498 (baseVal q)

theorem counterClause499 (q : Nat → Bool) : valuationOf q 127 = false ∨ valuationOf q 247 = true := by
  have hs : count247 q = (countLit q [127]) + (countLit q [128]) := List.countP_append (p := literal q) (l₁ := [127]) (l₂ := [128])
  have hm := merge_left (literal (valuationOf q) (127)) (literal (valuationOf q) (247)) (countLit q [127]) (countLit q [128]) (count247 q) 1 (meaning127 q) (meaning247 q) hs
  change valuationOf q 127 = false ∨ valuationOf q 247 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause499 (q : Snake 81) (h : Conditions q) : valuation q 127 = false ∨ valuation q 247 = true := counterClause499 (baseVal q)

theorem counterClause500 (q : Nat → Bool) : valuationOf q 127 = false ∨ valuationOf q 128 = false ∨ valuationOf q 248 = true := by
  have hs : count247 q = (countLit q [127]) + (countLit q [128]) := List.countP_append (p := literal q) (l₁ := [127]) (l₂ := [128])
  have hm := merge_two (literal (valuationOf q) (127)) (literal (valuationOf q) (128)) (literal (valuationOf q) (248)) (countLit q [127]) (countLit q [128]) (count247 q) 1 1 (meaning127 q) (meaning128 q) (meaning248 q) hs
  change valuationOf q 127 = false ∨ valuationOf q 128 = false ∨ valuationOf q 248 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause500 (q : Snake 81) (h : Conditions q) : valuation q 127 = false ∨ valuation q 128 = false ∨ valuation q 248 = true := counterClause500 (baseVal q)

theorem counterClause501 (q : Nat → Bool) : valuationOf q 247 = false ∨ valuationOf q 249 = true := by
  have hs : count249 q = (countLit q [126]) + (countLit q [127, 128]) := List.countP_append (p := literal q) (l₁ := [126]) (l₂ := [127, 128])
  have hm := merge_right (literal (valuationOf q) (247)) (literal (valuationOf q) (249)) (countLit q [126]) (countLit q [127, 128]) (count249 q) 1 (meaning247 q) (meaning249 q) hs
  change valuationOf q 247 = false ∨ valuationOf q 249 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause501 (q : Snake 81) (h : Conditions q) : valuation q 247 = false ∨ valuation q 249 = true := counterClause501 (baseVal q)

theorem counterClause502 (q : Nat → Bool) : valuationOf q 248 = false ∨ valuationOf q 250 = true := by
  have hs : count249 q = (countLit q [126]) + (countLit q [127, 128]) := List.countP_append (p := literal q) (l₁ := [126]) (l₂ := [127, 128])
  have hm := merge_right (literal (valuationOf q) (248)) (literal (valuationOf q) (250)) (countLit q [126]) (countLit q [127, 128]) (count249 q) 2 (meaning248 q) (meaning250 q) hs
  change valuationOf q 248 = false ∨ valuationOf q 250 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause502 (q : Snake 81) (h : Conditions q) : valuation q 248 = false ∨ valuation q 250 = true := counterClause502 (baseVal q)

theorem counterClause503 (q : Nat → Bool) : valuationOf q 130 = false ∨ valuationOf q 251 = true := by
  have hs : count251 q = (countLit q [129]) + (countLit q [130]) := List.countP_append (p := literal q) (l₁ := [129]) (l₂ := [130])
  have hm := merge_right (literal (valuationOf q) (130)) (literal (valuationOf q) (251)) (countLit q [129]) (countLit q [130]) (count251 q) 1 (meaning130 q) (meaning251 q) hs
  change valuationOf q 130 = false ∨ valuationOf q 251 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause503 (q : Snake 81) (h : Conditions q) : valuation q 130 = false ∨ valuation q 251 = true := counterClause503 (baseVal q)

theorem counterClause504 (q : Nat → Bool) : valuationOf q 132 = false ∨ valuationOf q 253 = true := by
  have hs : count253 q = (countLit q [131]) + (countLit q [132]) := List.countP_append (p := literal q) (l₁ := [131]) (l₂ := [132])
  have hm := merge_right (literal (valuationOf q) (132)) (literal (valuationOf q) (253)) (countLit q [131]) (countLit q [132]) (count253 q) 1 (meaning132 q) (meaning253 q) hs
  change valuationOf q 132 = false ∨ valuationOf q 253 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause504 (q : Snake 81) (h : Conditions q) : valuation q 132 = false ∨ valuation q 253 = true := counterClause504 (baseVal q)

theorem counterClause505 (q : Nat → Bool) : valuationOf q 253 = false ∨ valuationOf q 255 = true := by
  have hs : count255 q = (countLit q [129, 130]) + (countLit q [131, 132]) := List.countP_append (p := literal q) (l₁ := [129, 130]) (l₂ := [131, 132])
  have hm := merge_right (literal (valuationOf q) (253)) (literal (valuationOf q) (255)) (countLit q [129, 130]) (countLit q [131, 132]) (count255 q) 1 (meaning253 q) (meaning255 q) hs
  change valuationOf q 253 = false ∨ valuationOf q 255 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause505 (q : Snake 81) (h : Conditions q) : valuation q 253 = false ∨ valuation q 255 = true := counterClause505 (baseVal q)

theorem counterClause506 (q : Nat → Bool) : valuationOf q 251 = false ∨ valuationOf q 255 = true := by
  have hs : count255 q = (countLit q [129, 130]) + (countLit q [131, 132]) := List.countP_append (p := literal q) (l₁ := [129, 130]) (l₂ := [131, 132])
  have hm := merge_left (literal (valuationOf q) (251)) (literal (valuationOf q) (255)) (countLit q [129, 130]) (countLit q [131, 132]) (count255 q) 1 (meaning251 q) (meaning255 q) hs
  change valuationOf q 251 = false ∨ valuationOf q 255 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause506 (q : Snake 81) (h : Conditions q) : valuation q 251 = false ∨ valuation q 255 = true := counterClause506 (baseVal q)

theorem counterClause507 (q : Nat → Bool) : valuationOf q 251 = false ∨ valuationOf q 253 = false ∨ valuationOf q 256 = true := by
  have hs : count255 q = (countLit q [129, 130]) + (countLit q [131, 132]) := List.countP_append (p := literal q) (l₁ := [129, 130]) (l₂ := [131, 132])
  have hm := merge_two (literal (valuationOf q) (251)) (literal (valuationOf q) (253)) (literal (valuationOf q) (256)) (countLit q [129, 130]) (countLit q [131, 132]) (count255 q) 1 1 (meaning251 q) (meaning253 q) (meaning256 q) hs
  change valuationOf q 251 = false ∨ valuationOf q 253 = false ∨ valuationOf q 256 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause507 (q : Snake 81) (h : Conditions q) : valuation q 251 = false ∨ valuation q 253 = false ∨ valuation q 256 = true := counterClause507 (baseVal q)

theorem counterClause508 (q : Nat → Bool) : valuationOf q 255 = false ∨ valuationOf q 257 = true := by
  have hs : count257 q = (countLit q [126, 127, 128]) + (countLit q [129, 130, 131, 132]) := List.countP_append (p := literal q) (l₁ := [126, 127, 128]) (l₂ := [129, 130, 131, 132])
  have hm := merge_right (literal (valuationOf q) (255)) (literal (valuationOf q) (257)) (countLit q [126, 127, 128]) (countLit q [129, 130, 131, 132]) (count257 q) 1 (meaning255 q) (meaning257 q) hs
  change valuationOf q 255 = false ∨ valuationOf q 257 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause508 (q : Snake 81) (h : Conditions q) : valuation q 255 = false ∨ valuation q 257 = true := counterClause508 (baseVal q)

theorem counterClause509 (q : Nat → Bool) : valuationOf q 256 = false ∨ valuationOf q 258 = true := by
  have hs : count257 q = (countLit q [126, 127, 128]) + (countLit q [129, 130, 131, 132]) := List.countP_append (p := literal q) (l₁ := [126, 127, 128]) (l₂ := [129, 130, 131, 132])
  have hm := merge_right (literal (valuationOf q) (256)) (literal (valuationOf q) (258)) (countLit q [126, 127, 128]) (countLit q [129, 130, 131, 132]) (count257 q) 2 (meaning256 q) (meaning258 q) hs
  change valuationOf q 256 = false ∨ valuationOf q 258 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause509 (q : Snake 81) (h : Conditions q) : valuation q 256 = false ∨ valuation q 258 = true := counterClause509 (baseVal q)

theorem counterClause510 (q : Nat → Bool) : valuationOf q 249 = false ∨ valuationOf q 257 = true := by
  have hs : count257 q = (countLit q [126, 127, 128]) + (countLit q [129, 130, 131, 132]) := List.countP_append (p := literal q) (l₁ := [126, 127, 128]) (l₂ := [129, 130, 131, 132])
  have hm := merge_left (literal (valuationOf q) (249)) (literal (valuationOf q) (257)) (countLit q [126, 127, 128]) (countLit q [129, 130, 131, 132]) (count257 q) 1 (meaning249 q) (meaning257 q) hs
  change valuationOf q 249 = false ∨ valuationOf q 257 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause510 (q : Snake 81) (h : Conditions q) : valuation q 249 = false ∨ valuation q 257 = true := counterClause510 (baseVal q)

theorem counterClause511 (q : Nat → Bool) : valuationOf q 249 = false ∨ valuationOf q 255 = false ∨ valuationOf q 258 = true := by
  have hs : count257 q = (countLit q [126, 127, 128]) + (countLit q [129, 130, 131, 132]) := List.countP_append (p := literal q) (l₁ := [126, 127, 128]) (l₂ := [129, 130, 131, 132])
  have hm := merge_two (literal (valuationOf q) (249)) (literal (valuationOf q) (255)) (literal (valuationOf q) (258)) (countLit q [126, 127, 128]) (countLit q [129, 130, 131, 132]) (count257 q) 1 1 (meaning249 q) (meaning255 q) (meaning258 q) hs
  change valuationOf q 249 = false ∨ valuationOf q 255 = false ∨ valuationOf q 258 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause511 (q : Snake 81) (h : Conditions q) : valuation q 249 = false ∨ valuation q 255 = false ∨ valuation q 258 = true := counterClause511 (baseVal q)

theorem counterClause512 (q : Nat → Bool) : valuationOf q 250 = false ∨ valuationOf q 258 = true := by
  have hs : count257 q = (countLit q [126, 127, 128]) + (countLit q [129, 130, 131, 132]) := List.countP_append (p := literal q) (l₁ := [126, 127, 128]) (l₂ := [129, 130, 131, 132])
  have hm := merge_left (literal (valuationOf q) (250)) (literal (valuationOf q) (258)) (countLit q [126, 127, 128]) (countLit q [129, 130, 131, 132]) (count257 q) 2 (meaning250 q) (meaning258 q) hs
  change valuationOf q 250 = false ∨ valuationOf q 258 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause512 (q : Snake 81) (h : Conditions q) : valuation q 250 = false ∨ valuation q 258 = true := counterClause512 (baseVal q)

theorem block15 (q : Snake 81) (h : Conditions q) : B112E161.Block15 (valuation q) :=
  ⟨clause481 q h, clause482 q h, clause483 q h, clause484 q h, clause485 q h, clause486 q h, clause487 q h, clause488 q h, clause489 q h, clause490 q h, clause491 q h, clause492 q h, clause493 q h, clause494 q h, clause495 q h, clause496 q h, clause497 q h, clause498 q h, clause499 q h, clause500 q h, clause501 q h, clause502 q h, clause503 q h, clause504 q h, clause505 q h, clause506 q h, clause507 q h, clause508 q h, clause509 q h, clause510 q h, clause511 q h, clause512 q h⟩

end
end Snake9.Regrowth.E112161
