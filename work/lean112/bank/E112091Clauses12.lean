import E112091Semantics
import B112E091Inputs
namespace Snake9.Regrowth.E112091
noncomputable section
local instance blockDec12 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause385 (q : Nat → Bool) : valuationOf q 129 = false ∨ valuationOf q 251 = true := by
  have hs : count251 q = (countLit q [129]) + (countLit q [130]) := List.countP_append (p := literal q) (l₁ := [129]) (l₂ := [130])
  have hm := merge_left (literal (valuationOf q) (129)) (literal (valuationOf q) (251)) (countLit q [129]) (countLit q [130]) (count251 q) 1 (meaning129 q) (meaning251 q) hs
  change valuationOf q 129 = false ∨ valuationOf q 251 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause385 (q : Snake 81) (h : Conditions q) : valuation q 129 = false ∨ valuation q 251 = true := counterClause385 (baseVal q)

theorem counterClause386 (q : Nat → Bool) : valuationOf q 131 = false ∨ valuationOf q 253 = true := by
  have hs : count253 q = (countLit q [131]) + (countLit q [132]) := List.countP_append (p := literal q) (l₁ := [131]) (l₂ := [132])
  have hm := merge_left (literal (valuationOf q) (131)) (literal (valuationOf q) (253)) (countLit q [131]) (countLit q [132]) (count253 q) 1 (meaning131 q) (meaning253 q) hs
  change valuationOf q 131 = false ∨ valuationOf q 253 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause386 (q : Snake 81) (h : Conditions q) : valuation q 131 = false ∨ valuation q 253 = true := counterClause386 (baseVal q)

theorem counterClause387 (q : Nat → Bool) : valuationOf q 253 = false ∨ valuationOf q 255 = true := by
  have hs : count255 q = (countLit q [129, 130]) + (countLit q [131, 132]) := List.countP_append (p := literal q) (l₁ := [129, 130]) (l₂ := [131, 132])
  have hm := merge_right (literal (valuationOf q) (253)) (literal (valuationOf q) (255)) (countLit q [129, 130]) (countLit q [131, 132]) (count255 q) 1 (meaning253 q) (meaning255 q) hs
  change valuationOf q 253 = false ∨ valuationOf q 255 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause387 (q : Snake 81) (h : Conditions q) : valuation q 253 = false ∨ valuation q 255 = true := counterClause387 (baseVal q)

theorem counterClause388 (q : Nat → Bool) : valuationOf q 251 = false ∨ valuationOf q 255 = true := by
  have hs : count255 q = (countLit q [129, 130]) + (countLit q [131, 132]) := List.countP_append (p := literal q) (l₁ := [129, 130]) (l₂ := [131, 132])
  have hm := merge_left (literal (valuationOf q) (251)) (literal (valuationOf q) (255)) (countLit q [129, 130]) (countLit q [131, 132]) (count255 q) 1 (meaning251 q) (meaning255 q) hs
  change valuationOf q 251 = false ∨ valuationOf q 255 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause388 (q : Snake 81) (h : Conditions q) : valuation q 251 = false ∨ valuation q 255 = true := counterClause388 (baseVal q)

theorem counterClause389 (q : Nat → Bool) : valuationOf q 255 = false ∨ valuationOf q 257 = true := by
  have hs : count257 q = (countLit q [126, 127, 128]) + (countLit q [129, 130, 131, 132]) := List.countP_append (p := literal q) (l₁ := [126, 127, 128]) (l₂ := [129, 130, 131, 132])
  have hm := merge_right (literal (valuationOf q) (255)) (literal (valuationOf q) (257)) (countLit q [126, 127, 128]) (countLit q [129, 130, 131, 132]) (count257 q) 1 (meaning255 q) (meaning257 q) hs
  change valuationOf q 255 = false ∨ valuationOf q 257 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause389 (q : Snake 81) (h : Conditions q) : valuation q 255 = false ∨ valuation q 257 = true := counterClause389 (baseVal q)

theorem counterClause390 (q : Nat → Bool) : valuationOf q 249 = false ∨ valuationOf q 257 = true := by
  have hs : count257 q = (countLit q [126, 127, 128]) + (countLit q [129, 130, 131, 132]) := List.countP_append (p := literal q) (l₁ := [126, 127, 128]) (l₂ := [129, 130, 131, 132])
  have hm := merge_left (literal (valuationOf q) (249)) (literal (valuationOf q) (257)) (countLit q [126, 127, 128]) (countLit q [129, 130, 131, 132]) (count257 q) 1 (meaning249 q) (meaning257 q) hs
  change valuationOf q 249 = false ∨ valuationOf q 257 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause390 (q : Snake 81) (h : Conditions q) : valuation q 249 = false ∨ valuation q 257 = true := counterClause390 (baseVal q)

theorem counterClause391 (q : Nat → Bool) : valuationOf q 249 = false ∨ valuationOf q 255 = false ∨ valuationOf q 258 = true := by
  have hs : count257 q = (countLit q [126, 127, 128]) + (countLit q [129, 130, 131, 132]) := List.countP_append (p := literal q) (l₁ := [126, 127, 128]) (l₂ := [129, 130, 131, 132])
  have hm := merge_two (literal (valuationOf q) (249)) (literal (valuationOf q) (255)) (literal (valuationOf q) (258)) (countLit q [126, 127, 128]) (countLit q [129, 130, 131, 132]) (count257 q) 1 1 (meaning249 q) (meaning255 q) (meaning258 q) hs
  change valuationOf q 249 = false ∨ valuationOf q 255 = false ∨ valuationOf q 258 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause391 (q : Snake 81) (h : Conditions q) : valuation q 249 = false ∨ valuation q 255 = false ∨ valuation q 258 = true := counterClause391 (baseVal q)

theorem counterClause392 (q : Nat → Bool) : valuationOf q 257 = false ∨ valuationOf q 259 = true := by
  have hs : count259 q = (countLit q [120, 121, 122, 123, 124, 125]) + (countLit q [126, 127, 128, 129, 130, 131, 132]) := List.countP_append (p := literal q) (l₁ := [120, 121, 122, 123, 124, 125]) (l₂ := [126, 127, 128, 129, 130, 131, 132])
  have hm := merge_right (literal (valuationOf q) (257)) (literal (valuationOf q) (259)) (countLit q [120, 121, 122, 123, 124, 125]) (countLit q [126, 127, 128, 129, 130, 131, 132]) (count259 q) 1 (meaning257 q) (meaning259 q) hs
  change valuationOf q 257 = false ∨ valuationOf q 259 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause392 (q : Snake 81) (h : Conditions q) : valuation q 257 = false ∨ valuation q 259 = true := counterClause392 (baseVal q)

theorem counterClause393 (q : Nat → Bool) : valuationOf q 258 = false ∨ valuationOf q 260 = true := by
  have hs : count259 q = (countLit q [120, 121, 122, 123, 124, 125]) + (countLit q [126, 127, 128, 129, 130, 131, 132]) := List.countP_append (p := literal q) (l₁ := [120, 121, 122, 123, 124, 125]) (l₂ := [126, 127, 128, 129, 130, 131, 132])
  have hm := merge_right (literal (valuationOf q) (258)) (literal (valuationOf q) (260)) (countLit q [120, 121, 122, 123, 124, 125]) (countLit q [126, 127, 128, 129, 130, 131, 132]) (count259 q) 2 (meaning258 q) (meaning260 q) hs
  change valuationOf q 258 = false ∨ valuationOf q 260 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause393 (q : Snake 81) (h : Conditions q) : valuation q 258 = false ∨ valuation q 260 = true := counterClause393 (baseVal q)

theorem counterClause394 (q : Nat → Bool) : valuationOf q 245 = false ∨ valuationOf q 259 = true := by
  have hs : count259 q = (countLit q [120, 121, 122, 123, 124, 125]) + (countLit q [126, 127, 128, 129, 130, 131, 132]) := List.countP_append (p := literal q) (l₁ := [120, 121, 122, 123, 124, 125]) (l₂ := [126, 127, 128, 129, 130, 131, 132])
  have hm := merge_left (literal (valuationOf q) (245)) (literal (valuationOf q) (259)) (countLit q [120, 121, 122, 123, 124, 125]) (countLit q [126, 127, 128, 129, 130, 131, 132]) (count259 q) 1 (meaning245 q) (meaning259 q) hs
  change valuationOf q 245 = false ∨ valuationOf q 259 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause394 (q : Snake 81) (h : Conditions q) : valuation q 245 = false ∨ valuation q 259 = true := counterClause394 (baseVal q)

theorem counterClause395 (q : Nat → Bool) : valuationOf q 245 = false ∨ valuationOf q 257 = false ∨ valuationOf q 260 = true := by
  have hs : count259 q = (countLit q [120, 121, 122, 123, 124, 125]) + (countLit q [126, 127, 128, 129, 130, 131, 132]) := List.countP_append (p := literal q) (l₁ := [120, 121, 122, 123, 124, 125]) (l₂ := [126, 127, 128, 129, 130, 131, 132])
  have hm := merge_two (literal (valuationOf q) (245)) (literal (valuationOf q) (257)) (literal (valuationOf q) (260)) (countLit q [120, 121, 122, 123, 124, 125]) (countLit q [126, 127, 128, 129, 130, 131, 132]) (count259 q) 1 1 (meaning245 q) (meaning257 q) (meaning260 q) hs
  change valuationOf q 245 = false ∨ valuationOf q 257 = false ∨ valuationOf q 260 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause395 (q : Snake 81) (h : Conditions q) : valuation q 245 = false ∨ valuation q 257 = false ∨ valuation q 260 = true := counterClause395 (baseVal q)

theorem counterClause396 (q : Nat → Bool) : valuationOf q 246 = false ∨ valuationOf q 260 = true := by
  have hs : count259 q = (countLit q [120, 121, 122, 123, 124, 125]) + (countLit q [126, 127, 128, 129, 130, 131, 132]) := List.countP_append (p := literal q) (l₁ := [120, 121, 122, 123, 124, 125]) (l₂ := [126, 127, 128, 129, 130, 131, 132])
  have hm := merge_left (literal (valuationOf q) (246)) (literal (valuationOf q) (260)) (countLit q [120, 121, 122, 123, 124, 125]) (countLit q [126, 127, 128, 129, 130, 131, 132]) (count259 q) 2 (meaning246 q) (meaning260 q) hs
  change valuationOf q 246 = false ∨ valuationOf q 260 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause396 (q : Snake 81) (h : Conditions q) : valuation q 246 = false ∨ valuation q 260 = true := counterClause396 (baseVal q)

theorem counterClause397 (q : Nat → Bool) : valuationOf q 259 = false ∨ valuationOf q 261 = true := by
  have hs : count261 q = (countLit q [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119]) + (countLit q [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) := List.countP_append (p := literal q) (l₁ := [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119]) (l₂ := [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132])
  have hm := merge_right (literal (valuationOf q) (259)) (literal (valuationOf q) (261)) (countLit q [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119]) (countLit q [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) (count261 q) 1 (meaning259 q) (meaning261 q) hs
  change valuationOf q 259 = false ∨ valuationOf q 261 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause397 (q : Snake 81) (h : Conditions q) : valuation q 259 = false ∨ valuation q 261 = true := counterClause397 (baseVal q)

theorem counterClause398 (q : Nat → Bool) : valuationOf q 260 = false ∨ valuationOf q 262 = true := by
  have hs : count261 q = (countLit q [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119]) + (countLit q [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) := List.countP_append (p := literal q) (l₁ := [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119]) (l₂ := [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132])
  have hm := merge_right (literal (valuationOf q) (260)) (literal (valuationOf q) (262)) (countLit q [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119]) (countLit q [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) (count261 q) 2 (meaning260 q) (meaning262 q) hs
  change valuationOf q 260 = false ∨ valuationOf q 262 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause398 (q : Snake 81) (h : Conditions q) : valuation q 260 = false ∨ valuation q 262 = true := counterClause398 (baseVal q)

theorem counterClause399 (q : Nat → Bool) : valuationOf q 235 = false ∨ valuationOf q 261 = true := by
  have hs : count261 q = (countLit q [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119]) + (countLit q [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) := List.countP_append (p := literal q) (l₁ := [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119]) (l₂ := [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132])
  have hm := merge_left (literal (valuationOf q) (235)) (literal (valuationOf q) (261)) (countLit q [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119]) (countLit q [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) (count261 q) 1 (meaning235 q) (meaning261 q) hs
  change valuationOf q 235 = false ∨ valuationOf q 261 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause399 (q : Snake 81) (h : Conditions q) : valuation q 235 = false ∨ valuation q 261 = true := counterClause399 (baseVal q)

theorem counterClause400 (q : Nat → Bool) : valuationOf q 235 = false ∨ valuationOf q 259 = false ∨ valuationOf q 262 = true := by
  have hs : count261 q = (countLit q [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119]) + (countLit q [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) := List.countP_append (p := literal q) (l₁ := [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119]) (l₂ := [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132])
  have hm := merge_two (literal (valuationOf q) (235)) (literal (valuationOf q) (259)) (literal (valuationOf q) (262)) (countLit q [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119]) (countLit q [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) (count261 q) 1 1 (meaning235 q) (meaning259 q) (meaning262 q) hs
  change valuationOf q 235 = false ∨ valuationOf q 259 = false ∨ valuationOf q 262 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause400 (q : Snake 81) (h : Conditions q) : valuation q 235 = false ∨ valuation q 259 = false ∨ valuation q 262 = true := counterClause400 (baseVal q)

theorem counterClause401 (q : Nat → Bool) : valuationOf q 236 = false ∨ valuationOf q 262 = true := by
  have hs : count261 q = (countLit q [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119]) + (countLit q [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) := List.countP_append (p := literal q) (l₁ := [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119]) (l₂ := [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132])
  have hm := merge_left (literal (valuationOf q) (236)) (literal (valuationOf q) (262)) (countLit q [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119]) (countLit q [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) (count261 q) 2 (meaning236 q) (meaning262 q) hs
  change valuationOf q 236 = false ∨ valuationOf q 262 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause401 (q : Snake 81) (h : Conditions q) : valuation q 236 = false ∨ valuation q 262 = true := counterClause401 (baseVal q)

theorem counterClause402 (q : Nat → Bool) : valuationOf q 135 = false ∨ valuationOf q 263 = true := by
  have hs : count263 q = (countLit q [134]) + (countLit q [135]) := List.countP_append (p := literal q) (l₁ := [134]) (l₂ := [135])
  have hm := merge_right (literal (valuationOf q) (135)) (literal (valuationOf q) (263)) (countLit q [134]) (countLit q [135]) (count263 q) 1 (meaning135 q) (meaning263 q) hs
  change valuationOf q 135 = false ∨ valuationOf q 263 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause402 (q : Snake 81) (h : Conditions q) : valuation q 135 = false ∨ valuation q 263 = true := counterClause402 (baseVal q)

theorem counterClause403 (q : Nat → Bool) : valuationOf q 263 = false ∨ valuationOf q 265 = true := by
  have hs : count265 q = (countLit q [133]) + (countLit q [134, 135]) := List.countP_append (p := literal q) (l₁ := [133]) (l₂ := [134, 135])
  have hm := merge_right (literal (valuationOf q) (263)) (literal (valuationOf q) (265)) (countLit q [133]) (countLit q [134, 135]) (count265 q) 1 (meaning263 q) (meaning265 q) hs
  change valuationOf q 263 = false ∨ valuationOf q 265 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause403 (q : Snake 81) (h : Conditions q) : valuation q 263 = false ∨ valuation q 265 = true := counterClause403 (baseVal q)

theorem counterClause404 (q : Nat → Bool) : valuationOf q 133 = false ∨ valuationOf q 265 = true := by
  have hs : count265 q = (countLit q [133]) + (countLit q [134, 135]) := List.countP_append (p := literal q) (l₁ := [133]) (l₂ := [134, 135])
  have hm := merge_left (literal (valuationOf q) (133)) (literal (valuationOf q) (265)) (countLit q [133]) (countLit q [134, 135]) (count265 q) 1 (meaning133 q) (meaning265 q) hs
  change valuationOf q 133 = false ∨ valuationOf q 265 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause404 (q : Snake 81) (h : Conditions q) : valuation q 133 = false ∨ valuation q 265 = true := counterClause404 (baseVal q)

theorem counterClause405 (q : Nat → Bool) : valuationOf q 133 = false ∨ valuationOf q 263 = false ∨ valuationOf q 266 = true := by
  have hs : count265 q = (countLit q [133]) + (countLit q [134, 135]) := List.countP_append (p := literal q) (l₁ := [133]) (l₂ := [134, 135])
  have hm := merge_two (literal (valuationOf q) (133)) (literal (valuationOf q) (263)) (literal (valuationOf q) (266)) (countLit q [133]) (countLit q [134, 135]) (count265 q) 1 1 (meaning133 q) (meaning263 q) (meaning266 q) hs
  change valuationOf q 133 = false ∨ valuationOf q 263 = false ∨ valuationOf q 266 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause405 (q : Snake 81) (h : Conditions q) : valuation q 133 = false ∨ valuation q 263 = false ∨ valuation q 266 = true := counterClause405 (baseVal q)

theorem counterClause406 (q : Nat → Bool) : valuationOf q 138 = false ∨ valuationOf q 267 = true := by
  have hs : count267 q = (countLit q [137]) + (countLit q [138]) := List.countP_append (p := literal q) (l₁ := [137]) (l₂ := [138])
  have hm := merge_right (literal (valuationOf q) (138)) (literal (valuationOf q) (267)) (countLit q [137]) (countLit q [138]) (count267 q) 1 (meaning138 q) (meaning267 q) hs
  change valuationOf q 138 = false ∨ valuationOf q 267 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause406 (q : Snake 81) (h : Conditions q) : valuation q 138 = false ∨ valuation q 267 = true := counterClause406 (baseVal q)

theorem counterClause407 (q : Nat → Bool) : valuationOf q 267 = false ∨ valuationOf q 269 = true := by
  have hs : count269 q = (countLit q [136]) + (countLit q [137, 138]) := List.countP_append (p := literal q) (l₁ := [136]) (l₂ := [137, 138])
  have hm := merge_right (literal (valuationOf q) (267)) (literal (valuationOf q) (269)) (countLit q [136]) (countLit q [137, 138]) (count269 q) 1 (meaning267 q) (meaning269 q) hs
  change valuationOf q 267 = false ∨ valuationOf q 269 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause407 (q : Snake 81) (h : Conditions q) : valuation q 267 = false ∨ valuation q 269 = true := counterClause407 (baseVal q)

theorem counterClause408 (q : Nat → Bool) : valuationOf q 269 = false ∨ valuationOf q 271 = true := by
  have hs : count271 q = (countLit q [133, 134, 135]) + (countLit q [136, 137, 138]) := List.countP_append (p := literal q) (l₁ := [133, 134, 135]) (l₂ := [136, 137, 138])
  have hm := merge_right (literal (valuationOf q) (269)) (literal (valuationOf q) (271)) (countLit q [133, 134, 135]) (countLit q [136, 137, 138]) (count271 q) 1 (meaning269 q) (meaning271 q) hs
  change valuationOf q 269 = false ∨ valuationOf q 271 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause408 (q : Snake 81) (h : Conditions q) : valuation q 269 = false ∨ valuation q 271 = true := counterClause408 (baseVal q)

theorem counterClause409 (q : Nat → Bool) : valuationOf q 265 = false ∨ valuationOf q 271 = true := by
  have hs : count271 q = (countLit q [133, 134, 135]) + (countLit q [136, 137, 138]) := List.countP_append (p := literal q) (l₁ := [133, 134, 135]) (l₂ := [136, 137, 138])
  have hm := merge_left (literal (valuationOf q) (265)) (literal (valuationOf q) (271)) (countLit q [133, 134, 135]) (countLit q [136, 137, 138]) (count271 q) 1 (meaning265 q) (meaning271 q) hs
  change valuationOf q 265 = false ∨ valuationOf q 271 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause409 (q : Snake 81) (h : Conditions q) : valuation q 265 = false ∨ valuation q 271 = true := counterClause409 (baseVal q)

theorem counterClause410 (q : Nat → Bool) : valuationOf q 265 = false ∨ valuationOf q 269 = false ∨ valuationOf q 272 = true := by
  have hs : count271 q = (countLit q [133, 134, 135]) + (countLit q [136, 137, 138]) := List.countP_append (p := literal q) (l₁ := [133, 134, 135]) (l₂ := [136, 137, 138])
  have hm := merge_two (literal (valuationOf q) (265)) (literal (valuationOf q) (269)) (literal (valuationOf q) (272)) (countLit q [133, 134, 135]) (countLit q [136, 137, 138]) (count271 q) 1 1 (meaning265 q) (meaning269 q) (meaning272 q) hs
  change valuationOf q 265 = false ∨ valuationOf q 269 = false ∨ valuationOf q 272 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause410 (q : Snake 81) (h : Conditions q) : valuation q 265 = false ∨ valuation q 269 = false ∨ valuation q 272 = true := counterClause410 (baseVal q)

theorem counterClause411 (q : Nat → Bool) : valuationOf q 266 = false ∨ valuationOf q 272 = true := by
  have hs : count271 q = (countLit q [133, 134, 135]) + (countLit q [136, 137, 138]) := List.countP_append (p := literal q) (l₁ := [133, 134, 135]) (l₂ := [136, 137, 138])
  have hm := merge_left (literal (valuationOf q) (266)) (literal (valuationOf q) (272)) (countLit q [133, 134, 135]) (countLit q [136, 137, 138]) (count271 q) 2 (meaning266 q) (meaning272 q) hs
  change valuationOf q 266 = false ∨ valuationOf q 272 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause411 (q : Snake 81) (h : Conditions q) : valuation q 266 = false ∨ valuation q 272 = true := counterClause411 (baseVal q)

theorem counterClause412 (q : Nat → Bool) : valuationOf q 141 = false ∨ valuationOf q 273 = true := by
  have hs : count273 q = (countLit q [140]) + (countLit q [141]) := List.countP_append (p := literal q) (l₁ := [140]) (l₂ := [141])
  have hm := merge_right (literal (valuationOf q) (141)) (literal (valuationOf q) (273)) (countLit q [140]) (countLit q [141]) (count273 q) 1 (meaning141 q) (meaning273 q) hs
  change valuationOf q 141 = false ∨ valuationOf q 273 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause412 (q : Snake 81) (h : Conditions q) : valuation q 141 = false ∨ valuation q 273 = true := counterClause412 (baseVal q)

theorem counterClause413 (q : Nat → Bool) : valuationOf q 273 = false ∨ valuationOf q 275 = true := by
  have hs : count275 q = (countLit q [139]) + (countLit q [140, 141]) := List.countP_append (p := literal q) (l₁ := [139]) (l₂ := [140, 141])
  have hm := merge_right (literal (valuationOf q) (273)) (literal (valuationOf q) (275)) (countLit q [139]) (countLit q [140, 141]) (count275 q) 1 (meaning273 q) (meaning275 q) hs
  change valuationOf q 273 = false ∨ valuationOf q 275 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause413 (q : Snake 81) (h : Conditions q) : valuation q 273 = false ∨ valuation q 275 = true := counterClause413 (baseVal q)

theorem counterClause414 (q : Nat → Bool) : valuationOf q 143 = false ∨ valuationOf q 277 = true := by
  have hs : count277 q = (countLit q [142]) + (countLit q [143]) := List.countP_append (p := literal q) (l₁ := [142]) (l₂ := [143])
  have hm := merge_right (literal (valuationOf q) (143)) (literal (valuationOf q) (277)) (countLit q [142]) (countLit q [143]) (count277 q) 1 (meaning143 q) (meaning277 q) hs
  change valuationOf q 143 = false ∨ valuationOf q 277 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause414 (q : Snake 81) (h : Conditions q) : valuation q 143 = false ∨ valuation q 277 = true := counterClause414 (baseVal q)

theorem counterClause415 (q : Nat → Bool) : valuationOf q 277 = false ∨ valuationOf q 281 = true := by
  have hs : count281 q = (countLit q [142, 143]) + (countLit q [144, 145]) := List.countP_append (p := literal q) (l₁ := [142, 143]) (l₂ := [144, 145])
  have hm := merge_left (literal (valuationOf q) (277)) (literal (valuationOf q) (281)) (countLit q [142, 143]) (countLit q [144, 145]) (count281 q) 1 (meaning277 q) (meaning281 q) hs
  change valuationOf q 277 = false ∨ valuationOf q 281 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause415 (q : Snake 81) (h : Conditions q) : valuation q 277 = false ∨ valuation q 281 = true := counterClause415 (baseVal q)

theorem counterClause416 (q : Nat → Bool) : valuationOf q 281 = false ∨ valuationOf q 283 = true := by
  have hs : count283 q = (countLit q [139, 140, 141]) + (countLit q [142, 143, 144, 145]) := List.countP_append (p := literal q) (l₁ := [139, 140, 141]) (l₂ := [142, 143, 144, 145])
  have hm := merge_right (literal (valuationOf q) (281)) (literal (valuationOf q) (283)) (countLit q [139, 140, 141]) (countLit q [142, 143, 144, 145]) (count283 q) 1 (meaning281 q) (meaning283 q) hs
  change valuationOf q 281 = false ∨ valuationOf q 283 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause416 (q : Snake 81) (h : Conditions q) : valuation q 281 = false ∨ valuation q 283 = true := counterClause416 (baseVal q)

theorem block12 (q : Snake 81) (h : Conditions q) : B112E091.Block12 (valuation q) :=
  ⟨clause385 q h, clause386 q h, clause387 q h, clause388 q h, clause389 q h, clause390 q h, clause391 q h, clause392 q h, clause393 q h, clause394 q h, clause395 q h, clause396 q h, clause397 q h, clause398 q h, clause399 q h, clause400 q h, clause401 q h, clause402 q h, clause403 q h, clause404 q h, clause405 q h, clause406 q h, clause407 q h, clause408 q h, clause409 q h, clause410 q h, clause411 q h, clause412 q h, clause413 q h, clause414 q h, clause415 q h, clause416 q h⟩

end
end Snake9.Regrowth.E112091
