import E112169Semantics
import B112E169Inputs
namespace Snake9.Regrowth.E112169
noncomputable section
local instance blockDec15 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause481 (q : Nat → Bool) : valuationOf q 237 = false ∨ valuationOf q 241 = true := by
  have hs : count241 q = (countLit q [120, 121]) + (countLit q [122, 123]) := List.countP_append (p := literal q) (l₁ := [120, 121]) (l₂ := [122, 123])
  have hm := merge_left (literal (valuationOf q) (237)) (literal (valuationOf q) (241)) (countLit q [120, 121]) (countLit q [122, 123]) (count241 q) 1 (meaning237 q) (meaning241 q) hs
  change valuationOf q 237 = false ∨ valuationOf q 241 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause481 (q : Snake 81) (h : Conditions q) : valuation q 237 = false ∨ valuation q 241 = true := counterClause481 (baseVal q)

theorem counterClause482 (q : Nat → Bool) : valuationOf q 238 = false ∨ valuationOf q 242 = true := by
  have hs : count241 q = (countLit q [120, 121]) + (countLit q [122, 123]) := List.countP_append (p := literal q) (l₁ := [120, 121]) (l₂ := [122, 123])
  have hm := merge_left (literal (valuationOf q) (238)) (literal (valuationOf q) (242)) (countLit q [120, 121]) (countLit q [122, 123]) (count241 q) 2 (meaning238 q) (meaning242 q) hs
  change valuationOf q 238 = false ∨ valuationOf q 242 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause482 (q : Snake 81) (h : Conditions q) : valuation q 238 = false ∨ valuation q 242 = true := counterClause482 (baseVal q)

theorem counterClause483 (q : Nat → Bool) : valuationOf q 241 = false ∨ valuationOf q 243 = true := by
  have hs : count243 q = (countLit q [117, 118, 119]) + (countLit q [120, 121, 122, 123]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119]) (l₂ := [120, 121, 122, 123])
  have hm := merge_right (literal (valuationOf q) (241)) (literal (valuationOf q) (243)) (countLit q [117, 118, 119]) (countLit q [120, 121, 122, 123]) (count243 q) 1 (meaning241 q) (meaning243 q) hs
  change valuationOf q 241 = false ∨ valuationOf q 243 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause483 (q : Snake 81) (h : Conditions q) : valuation q 241 = false ∨ valuation q 243 = true := counterClause483 (baseVal q)

theorem counterClause484 (q : Nat → Bool) : valuationOf q 242 = false ∨ valuationOf q 244 = true := by
  have hs : count243 q = (countLit q [117, 118, 119]) + (countLit q [120, 121, 122, 123]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119]) (l₂ := [120, 121, 122, 123])
  have hm := merge_right (literal (valuationOf q) (242)) (literal (valuationOf q) (244)) (countLit q [117, 118, 119]) (countLit q [120, 121, 122, 123]) (count243 q) 2 (meaning242 q) (meaning244 q) hs
  change valuationOf q 242 = false ∨ valuationOf q 244 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause484 (q : Snake 81) (h : Conditions q) : valuation q 242 = false ∨ valuation q 244 = true := counterClause484 (baseVal q)

theorem counterClause485 (q : Nat → Bool) : valuationOf q 235 = false ∨ valuationOf q 243 = true := by
  have hs : count243 q = (countLit q [117, 118, 119]) + (countLit q [120, 121, 122, 123]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119]) (l₂ := [120, 121, 122, 123])
  have hm := merge_left (literal (valuationOf q) (235)) (literal (valuationOf q) (243)) (countLit q [117, 118, 119]) (countLit q [120, 121, 122, 123]) (count243 q) 1 (meaning235 q) (meaning243 q) hs
  change valuationOf q 235 = false ∨ valuationOf q 243 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause485 (q : Snake 81) (h : Conditions q) : valuation q 235 = false ∨ valuation q 243 = true := counterClause485 (baseVal q)

theorem counterClause486 (q : Nat → Bool) : valuationOf q 235 = false ∨ valuationOf q 241 = false ∨ valuationOf q 244 = true := by
  have hs : count243 q = (countLit q [117, 118, 119]) + (countLit q [120, 121, 122, 123]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119]) (l₂ := [120, 121, 122, 123])
  have hm := merge_two (literal (valuationOf q) (235)) (literal (valuationOf q) (241)) (literal (valuationOf q) (244)) (countLit q [117, 118, 119]) (countLit q [120, 121, 122, 123]) (count243 q) 1 1 (meaning235 q) (meaning241 q) (meaning244 q) hs
  change valuationOf q 235 = false ∨ valuationOf q 241 = false ∨ valuationOf q 244 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause486 (q : Snake 81) (h : Conditions q) : valuation q 235 = false ∨ valuation q 241 = false ∨ valuation q 244 = true := counterClause486 (baseVal q)

theorem counterClause487 (q : Nat → Bool) : valuationOf q 125 = false ∨ valuationOf q 245 = true := by
  have hs : count245 q = (countLit q [125]) + (countLit q [127]) := List.countP_append (p := literal q) (l₁ := [125]) (l₂ := [127])
  have hm := merge_left (literal (valuationOf q) (125)) (literal (valuationOf q) (245)) (countLit q [125]) (countLit q [127]) (count245 q) 1 (meaning125 q) (meaning245 q) hs
  change valuationOf q 125 = false ∨ valuationOf q 245 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause487 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 245 = true := counterClause487 (baseVal q)

theorem counterClause488 (q : Nat → Bool) : valuationOf q 245 = false ∨ valuationOf q 247 = true := by
  have hs : count247 q = (countLit q [124]) + (countLit q [125, 127]) := List.countP_append (p := literal q) (l₁ := [124]) (l₂ := [125, 127])
  have hm := merge_right (literal (valuationOf q) (245)) (literal (valuationOf q) (247)) (countLit q [124]) (countLit q [125, 127]) (count247 q) 1 (meaning245 q) (meaning247 q) hs
  change valuationOf q 245 = false ∨ valuationOf q 247 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause488 (q : Snake 81) (h : Conditions q) : valuation q 245 = false ∨ valuation q 247 = true := counterClause488 (baseVal q)

theorem counterClause489 (q : Nat → Bool) : valuationOf q 124 = false ∨ valuationOf q 247 = true := by
  have hs : count247 q = (countLit q [124]) + (countLit q [125, 127]) := List.countP_append (p := literal q) (l₁ := [124]) (l₂ := [125, 127])
  have hm := merge_left (literal (valuationOf q) (124)) (literal (valuationOf q) (247)) (countLit q [124]) (countLit q [125, 127]) (count247 q) 1 (meaning124 q) (meaning247 q) hs
  change valuationOf q 124 = false ∨ valuationOf q 247 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause489 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 247 = true := counterClause489 (baseVal q)

theorem counterClause490 (q : Nat → Bool) : valuationOf q 124 = false ∨ valuationOf q 245 = false ∨ valuationOf q 248 = true := by
  have hs : count247 q = (countLit q [124]) + (countLit q [125, 127]) := List.countP_append (p := literal q) (l₁ := [124]) (l₂ := [125, 127])
  have hm := merge_two (literal (valuationOf q) (124)) (literal (valuationOf q) (245)) (literal (valuationOf q) (248)) (countLit q [124]) (countLit q [125, 127]) (count247 q) 1 1 (meaning124 q) (meaning245 q) (meaning248 q) hs
  change valuationOf q 124 = false ∨ valuationOf q 245 = false ∨ valuationOf q 248 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause490 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 245 = false ∨ valuation q 248 = true := counterClause490 (baseVal q)

theorem counterClause491 (q : Nat → Bool) : valuationOf q 128 = false ∨ valuationOf q 249 = true := by
  have hs : count249 q = (countLit q [128]) + (countLit q [129]) := List.countP_append (p := literal q) (l₁ := [128]) (l₂ := [129])
  have hm := merge_left (literal (valuationOf q) (128)) (literal (valuationOf q) (249)) (countLit q [128]) (countLit q [129]) (count249 q) 1 (meaning128 q) (meaning249 q) hs
  change valuationOf q 128 = false ∨ valuationOf q 249 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause491 (q : Snake 81) (h : Conditions q) : valuation q 128 = false ∨ valuation q 249 = true := counterClause491 (baseVal q)

theorem counterClause492 (q : Nat → Bool) : valuationOf q 249 = false ∨ valuationOf q 253 = true := by
  have hs : count253 q = (countLit q [128, 129]) + (countLit q [130, 131]) := List.countP_append (p := literal q) (l₁ := [128, 129]) (l₂ := [130, 131])
  have hm := merge_left (literal (valuationOf q) (249)) (literal (valuationOf q) (253)) (countLit q [128, 129]) (countLit q [130, 131]) (count253 q) 1 (meaning249 q) (meaning253 q) hs
  change valuationOf q 249 = false ∨ valuationOf q 253 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause492 (q : Snake 81) (h : Conditions q) : valuation q 249 = false ∨ valuation q 253 = true := counterClause492 (baseVal q)

theorem counterClause493 (q : Nat → Bool) : valuationOf q 253 = false ∨ valuationOf q 255 = true := by
  have hs : count255 q = (countLit q [124, 125, 127]) + (countLit q [128, 129, 130, 131]) := List.countP_append (p := literal q) (l₁ := [124, 125, 127]) (l₂ := [128, 129, 130, 131])
  have hm := merge_right (literal (valuationOf q) (253)) (literal (valuationOf q) (255)) (countLit q [124, 125, 127]) (countLit q [128, 129, 130, 131]) (count255 q) 1 (meaning253 q) (meaning255 q) hs
  change valuationOf q 253 = false ∨ valuationOf q 255 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause493 (q : Snake 81) (h : Conditions q) : valuation q 253 = false ∨ valuation q 255 = true := counterClause493 (baseVal q)

theorem counterClause494 (q : Nat → Bool) : valuationOf q 247 = false ∨ valuationOf q 255 = true := by
  have hs : count255 q = (countLit q [124, 125, 127]) + (countLit q [128, 129, 130, 131]) := List.countP_append (p := literal q) (l₁ := [124, 125, 127]) (l₂ := [128, 129, 130, 131])
  have hm := merge_left (literal (valuationOf q) (247)) (literal (valuationOf q) (255)) (countLit q [124, 125, 127]) (countLit q [128, 129, 130, 131]) (count255 q) 1 (meaning247 q) (meaning255 q) hs
  change valuationOf q 247 = false ∨ valuationOf q 255 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause494 (q : Snake 81) (h : Conditions q) : valuation q 247 = false ∨ valuation q 255 = true := counterClause494 (baseVal q)

theorem counterClause495 (q : Nat → Bool) : valuationOf q 247 = false ∨ valuationOf q 253 = false ∨ valuationOf q 256 = true := by
  have hs : count255 q = (countLit q [124, 125, 127]) + (countLit q [128, 129, 130, 131]) := List.countP_append (p := literal q) (l₁ := [124, 125, 127]) (l₂ := [128, 129, 130, 131])
  have hm := merge_two (literal (valuationOf q) (247)) (literal (valuationOf q) (253)) (literal (valuationOf q) (256)) (countLit q [124, 125, 127]) (countLit q [128, 129, 130, 131]) (count255 q) 1 1 (meaning247 q) (meaning253 q) (meaning256 q) hs
  change valuationOf q 247 = false ∨ valuationOf q 253 = false ∨ valuationOf q 256 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause495 (q : Snake 81) (h : Conditions q) : valuation q 247 = false ∨ valuation q 253 = false ∨ valuation q 256 = true := counterClause495 (baseVal q)

theorem counterClause496 (q : Nat → Bool) : valuationOf q 248 = false ∨ valuationOf q 256 = true := by
  have hs : count255 q = (countLit q [124, 125, 127]) + (countLit q [128, 129, 130, 131]) := List.countP_append (p := literal q) (l₁ := [124, 125, 127]) (l₂ := [128, 129, 130, 131])
  have hm := merge_left (literal (valuationOf q) (248)) (literal (valuationOf q) (256)) (countLit q [124, 125, 127]) (countLit q [128, 129, 130, 131]) (count255 q) 2 (meaning248 q) (meaning256 q) hs
  change valuationOf q 248 = false ∨ valuationOf q 256 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause496 (q : Snake 81) (h : Conditions q) : valuation q 248 = false ∨ valuation q 256 = true := counterClause496 (baseVal q)

theorem counterClause497 (q : Nat → Bool) : valuationOf q 255 = false ∨ valuationOf q 257 = true := by
  have hs : count257 q = (countLit q [117, 118, 119, 120, 121, 122, 123]) + (countLit q [124, 125, 127, 128, 129, 130, 131]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119, 120, 121, 122, 123]) (l₂ := [124, 125, 127, 128, 129, 130, 131])
  have hm := merge_right (literal (valuationOf q) (255)) (literal (valuationOf q) (257)) (countLit q [117, 118, 119, 120, 121, 122, 123]) (countLit q [124, 125, 127, 128, 129, 130, 131]) (count257 q) 1 (meaning255 q) (meaning257 q) hs
  change valuationOf q 255 = false ∨ valuationOf q 257 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause497 (q : Snake 81) (h : Conditions q) : valuation q 255 = false ∨ valuation q 257 = true := counterClause497 (baseVal q)

theorem counterClause498 (q : Nat → Bool) : valuationOf q 256 = false ∨ valuationOf q 258 = true := by
  have hs : count257 q = (countLit q [117, 118, 119, 120, 121, 122, 123]) + (countLit q [124, 125, 127, 128, 129, 130, 131]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119, 120, 121, 122, 123]) (l₂ := [124, 125, 127, 128, 129, 130, 131])
  have hm := merge_right (literal (valuationOf q) (256)) (literal (valuationOf q) (258)) (countLit q [117, 118, 119, 120, 121, 122, 123]) (countLit q [124, 125, 127, 128, 129, 130, 131]) (count257 q) 2 (meaning256 q) (meaning258 q) hs
  change valuationOf q 256 = false ∨ valuationOf q 258 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause498 (q : Snake 81) (h : Conditions q) : valuation q 256 = false ∨ valuation q 258 = true := counterClause498 (baseVal q)

theorem counterClause499 (q : Nat → Bool) : valuationOf q 243 = false ∨ valuationOf q 257 = true := by
  have hs : count257 q = (countLit q [117, 118, 119, 120, 121, 122, 123]) + (countLit q [124, 125, 127, 128, 129, 130, 131]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119, 120, 121, 122, 123]) (l₂ := [124, 125, 127, 128, 129, 130, 131])
  have hm := merge_left (literal (valuationOf q) (243)) (literal (valuationOf q) (257)) (countLit q [117, 118, 119, 120, 121, 122, 123]) (countLit q [124, 125, 127, 128, 129, 130, 131]) (count257 q) 1 (meaning243 q) (meaning257 q) hs
  change valuationOf q 243 = false ∨ valuationOf q 257 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause499 (q : Snake 81) (h : Conditions q) : valuation q 243 = false ∨ valuation q 257 = true := counterClause499 (baseVal q)

theorem counterClause500 (q : Nat → Bool) : valuationOf q 243 = false ∨ valuationOf q 255 = false ∨ valuationOf q 258 = true := by
  have hs : count257 q = (countLit q [117, 118, 119, 120, 121, 122, 123]) + (countLit q [124, 125, 127, 128, 129, 130, 131]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119, 120, 121, 122, 123]) (l₂ := [124, 125, 127, 128, 129, 130, 131])
  have hm := merge_two (literal (valuationOf q) (243)) (literal (valuationOf q) (255)) (literal (valuationOf q) (258)) (countLit q [117, 118, 119, 120, 121, 122, 123]) (countLit q [124, 125, 127, 128, 129, 130, 131]) (count257 q) 1 1 (meaning243 q) (meaning255 q) (meaning258 q) hs
  change valuationOf q 243 = false ∨ valuationOf q 255 = false ∨ valuationOf q 258 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause500 (q : Snake 81) (h : Conditions q) : valuation q 243 = false ∨ valuation q 255 = false ∨ valuation q 258 = true := counterClause500 (baseVal q)

theorem counterClause501 (q : Nat → Bool) : valuationOf q 244 = false ∨ valuationOf q 258 = true := by
  have hs : count257 q = (countLit q [117, 118, 119, 120, 121, 122, 123]) + (countLit q [124, 125, 127, 128, 129, 130, 131]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119, 120, 121, 122, 123]) (l₂ := [124, 125, 127, 128, 129, 130, 131])
  have hm := merge_left (literal (valuationOf q) (244)) (literal (valuationOf q) (258)) (countLit q [117, 118, 119, 120, 121, 122, 123]) (countLit q [124, 125, 127, 128, 129, 130, 131]) (count257 q) 2 (meaning244 q) (meaning258 q) hs
  change valuationOf q 244 = false ∨ valuationOf q 258 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause501 (q : Snake 81) (h : Conditions q) : valuation q 244 = false ∨ valuation q 258 = true := counterClause501 (baseVal q)

theorem counterClause502 (q : Nat → Bool) : valuationOf q 134 = false ∨ valuationOf q 259 = true := by
  have hs : count259 q = (countLit q [133]) + (countLit q [134]) := List.countP_append (p := literal q) (l₁ := [133]) (l₂ := [134])
  have hm := merge_right (literal (valuationOf q) (134)) (literal (valuationOf q) (259)) (countLit q [133]) (countLit q [134]) (count259 q) 1 (meaning134 q) (meaning259 q) hs
  change valuationOf q 134 = false ∨ valuationOf q 259 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause502 (q : Snake 81) (h : Conditions q) : valuation q 134 = false ∨ valuation q 259 = true := counterClause502 (baseVal q)

theorem counterClause503 (q : Nat → Bool) : valuationOf q 133 = false ∨ valuationOf q 259 = true := by
  have hs : count259 q = (countLit q [133]) + (countLit q [134]) := List.countP_append (p := literal q) (l₁ := [133]) (l₂ := [134])
  have hm := merge_left (literal (valuationOf q) (133)) (literal (valuationOf q) (259)) (countLit q [133]) (countLit q [134]) (count259 q) 1 (meaning133 q) (meaning259 q) hs
  change valuationOf q 133 = false ∨ valuationOf q 259 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause503 (q : Snake 81) (h : Conditions q) : valuation q 133 = false ∨ valuation q 259 = true := counterClause503 (baseVal q)

theorem counterClause504 (q : Nat → Bool) : valuationOf q 133 = false ∨ valuationOf q 134 = false ∨ valuationOf q 260 = true := by
  have hs : count259 q = (countLit q [133]) + (countLit q [134]) := List.countP_append (p := literal q) (l₁ := [133]) (l₂ := [134])
  have hm := merge_two (literal (valuationOf q) (133)) (literal (valuationOf q) (134)) (literal (valuationOf q) (260)) (countLit q [133]) (countLit q [134]) (count259 q) 1 1 (meaning133 q) (meaning134 q) (meaning260 q) hs
  change valuationOf q 133 = false ∨ valuationOf q 134 = false ∨ valuationOf q 260 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause504 (q : Snake 81) (h : Conditions q) : valuation q 133 = false ∨ valuation q 134 = false ∨ valuation q 260 = true := counterClause504 (baseVal q)

theorem counterClause505 (q : Nat → Bool) : valuationOf q 259 = false ∨ valuationOf q 261 = true := by
  have hs : count261 q = (countLit q [132]) + (countLit q [133, 134]) := List.countP_append (p := literal q) (l₁ := [132]) (l₂ := [133, 134])
  have hm := merge_right (literal (valuationOf q) (259)) (literal (valuationOf q) (261)) (countLit q [132]) (countLit q [133, 134]) (count261 q) 1 (meaning259 q) (meaning261 q) hs
  change valuationOf q 259 = false ∨ valuationOf q 261 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause505 (q : Snake 81) (h : Conditions q) : valuation q 259 = false ∨ valuation q 261 = true := counterClause505 (baseVal q)

theorem counterClause506 (q : Nat → Bool) : valuationOf q 260 = false ∨ valuationOf q 262 = true := by
  have hs : count261 q = (countLit q [132]) + (countLit q [133, 134]) := List.countP_append (p := literal q) (l₁ := [132]) (l₂ := [133, 134])
  have hm := merge_right (literal (valuationOf q) (260)) (literal (valuationOf q) (262)) (countLit q [132]) (countLit q [133, 134]) (count261 q) 2 (meaning260 q) (meaning262 q) hs
  change valuationOf q 260 = false ∨ valuationOf q 262 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause506 (q : Snake 81) (h : Conditions q) : valuation q 260 = false ∨ valuation q 262 = true := counterClause506 (baseVal q)

theorem counterClause507 (q : Nat → Bool) : valuationOf q 135 = false ∨ valuationOf q 263 = true := by
  have hs : count263 q = (countLit q [135]) + (countLit q [136]) := List.countP_append (p := literal q) (l₁ := [135]) (l₂ := [136])
  have hm := merge_left (literal (valuationOf q) (135)) (literal (valuationOf q) (263)) (countLit q [135]) (countLit q [136]) (count263 q) 1 (meaning135 q) (meaning263 q) hs
  change valuationOf q 135 = false ∨ valuationOf q 263 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause507 (q : Snake 81) (h : Conditions q) : valuation q 135 = false ∨ valuation q 263 = true := counterClause507 (baseVal q)

theorem counterClause508 (q : Nat → Bool) : valuationOf q 137 = false ∨ valuationOf q 265 = true := by
  have hs : count265 q = (countLit q [137]) + (countLit q [138]) := List.countP_append (p := literal q) (l₁ := [137]) (l₂ := [138])
  have hm := merge_left (literal (valuationOf q) (137)) (literal (valuationOf q) (265)) (countLit q [137]) (countLit q [138]) (count265 q) 1 (meaning137 q) (meaning265 q) hs
  change valuationOf q 137 = false ∨ valuationOf q 265 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause508 (q : Snake 81) (h : Conditions q) : valuation q 137 = false ∨ valuation q 265 = true := counterClause508 (baseVal q)

theorem counterClause509 (q : Nat → Bool) : valuationOf q 265 = false ∨ valuationOf q 267 = true := by
  have hs : count267 q = (countLit q [135, 136]) + (countLit q [137, 138]) := List.countP_append (p := literal q) (l₁ := [135, 136]) (l₂ := [137, 138])
  have hm := merge_right (literal (valuationOf q) (265)) (literal (valuationOf q) (267)) (countLit q [135, 136]) (countLit q [137, 138]) (count267 q) 1 (meaning265 q) (meaning267 q) hs
  change valuationOf q 265 = false ∨ valuationOf q 267 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause509 (q : Snake 81) (h : Conditions q) : valuation q 265 = false ∨ valuation q 267 = true := counterClause509 (baseVal q)

theorem counterClause510 (q : Nat → Bool) : valuationOf q 263 = false ∨ valuationOf q 267 = true := by
  have hs : count267 q = (countLit q [135, 136]) + (countLit q [137, 138]) := List.countP_append (p := literal q) (l₁ := [135, 136]) (l₂ := [137, 138])
  have hm := merge_left (literal (valuationOf q) (263)) (literal (valuationOf q) (267)) (countLit q [135, 136]) (countLit q [137, 138]) (count267 q) 1 (meaning263 q) (meaning267 q) hs
  change valuationOf q 263 = false ∨ valuationOf q 267 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause510 (q : Snake 81) (h : Conditions q) : valuation q 263 = false ∨ valuation q 267 = true := counterClause510 (baseVal q)

theorem counterClause511 (q : Nat → Bool) : valuationOf q 267 = false ∨ valuationOf q 269 = true := by
  have hs : count269 q = (countLit q [132, 133, 134]) + (countLit q [135, 136, 137, 138]) := List.countP_append (p := literal q) (l₁ := [132, 133, 134]) (l₂ := [135, 136, 137, 138])
  have hm := merge_right (literal (valuationOf q) (267)) (literal (valuationOf q) (269)) (countLit q [132, 133, 134]) (countLit q [135, 136, 137, 138]) (count269 q) 1 (meaning267 q) (meaning269 q) hs
  change valuationOf q 267 = false ∨ valuationOf q 269 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause511 (q : Snake 81) (h : Conditions q) : valuation q 267 = false ∨ valuation q 269 = true := counterClause511 (baseVal q)

theorem counterClause512 (q : Nat → Bool) : valuationOf q 261 = false ∨ valuationOf q 269 = true := by
  have hs : count269 q = (countLit q [132, 133, 134]) + (countLit q [135, 136, 137, 138]) := List.countP_append (p := literal q) (l₁ := [132, 133, 134]) (l₂ := [135, 136, 137, 138])
  have hm := merge_left (literal (valuationOf q) (261)) (literal (valuationOf q) (269)) (countLit q [132, 133, 134]) (countLit q [135, 136, 137, 138]) (count269 q) 1 (meaning261 q) (meaning269 q) hs
  change valuationOf q 261 = false ∨ valuationOf q 269 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause512 (q : Snake 81) (h : Conditions q) : valuation q 261 = false ∨ valuation q 269 = true := counterClause512 (baseVal q)

theorem block15 (q : Snake 81) (h : Conditions q) : B112E169.Block15 (valuation q) :=
  ⟨clause481 q h, clause482 q h, clause483 q h, clause484 q h, clause485 q h, clause486 q h, clause487 q h, clause488 q h, clause489 q h, clause490 q h, clause491 q h, clause492 q h, clause493 q h, clause494 q h, clause495 q h, clause496 q h, clause497 q h, clause498 q h, clause499 q h, clause500 q h, clause501 q h, clause502 q h, clause503 q h, clause504 q h, clause505 q h, clause506 q h, clause507 q h, clause508 q h, clause509 q h, clause510 q h, clause511 q h, clause512 q h⟩

end
end Snake9.Regrowth.E112169
