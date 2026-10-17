import E112175Semantics
import B112E175Inputs
namespace Snake9.Regrowth.E112175
noncomputable section
local instance blockDec9 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause289 (q : Nat → Bool) : valuationOf q 126 = false ∨ valuationOf q 245 = true := by
  have hs : count245 q = (countLit q [126]) + (countLit q [127]) := List.countP_append (p := literal q) (l₁ := [126]) (l₂ := [127])
  have hm := merge_left (literal (valuationOf q) (126)) (literal (valuationOf q) (245)) (countLit q [126]) (countLit q [127]) (count245 q) 1 (meaning126 q) (meaning245 q) hs
  change valuationOf q 126 = false ∨ valuationOf q 245 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause289 (q : Snake 81) (h : Conditions q) : valuation q 126 = false ∨ valuation q 245 = true := counterClause289 (baseVal q)

theorem counterClause290 (q : Nat → Bool) : valuationOf q 129 = false ∨ valuationOf q 247 = true := by
  have hs : count247 q = (countLit q [128]) + (countLit q [129]) := List.countP_append (p := literal q) (l₁ := [128]) (l₂ := [129])
  have hm := merge_right (literal (valuationOf q) (129)) (literal (valuationOf q) (247)) (countLit q [128]) (countLit q [129]) (count247 q) 1 (meaning129 q) (meaning247 q) hs
  change valuationOf q 129 = false ∨ valuationOf q 247 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause290 (q : Snake 81) (h : Conditions q) : valuation q 129 = false ∨ valuation q 247 = true := counterClause290 (baseVal q)

theorem counterClause291 (q : Nat → Bool) : valuationOf q 247 = false ∨ valuationOf q 249 = true := by
  have hs : count249 q = (countLit q [126, 127]) + (countLit q [128, 129]) := List.countP_append (p := literal q) (l₁ := [126, 127]) (l₂ := [128, 129])
  have hm := merge_right (literal (valuationOf q) (247)) (literal (valuationOf q) (249)) (countLit q [126, 127]) (countLit q [128, 129]) (count249 q) 1 (meaning247 q) (meaning249 q) hs
  change valuationOf q 247 = false ∨ valuationOf q 249 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause291 (q : Snake 81) (h : Conditions q) : valuation q 247 = false ∨ valuation q 249 = true := counterClause291 (baseVal q)

theorem counterClause292 (q : Nat → Bool) : valuationOf q 245 = false ∨ valuationOf q 249 = true := by
  have hs : count249 q = (countLit q [126, 127]) + (countLit q [128, 129]) := List.countP_append (p := literal q) (l₁ := [126, 127]) (l₂ := [128, 129])
  have hm := merge_left (literal (valuationOf q) (245)) (literal (valuationOf q) (249)) (countLit q [126, 127]) (countLit q [128, 129]) (count249 q) 1 (meaning245 q) (meaning249 q) hs
  change valuationOf q 245 = false ∨ valuationOf q 249 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause292 (q : Snake 81) (h : Conditions q) : valuation q 245 = false ∨ valuation q 249 = true := counterClause292 (baseVal q)

theorem counterClause293 (q : Nat → Bool) : valuationOf q 245 = false ∨ valuationOf q 247 = false ∨ valuationOf q 250 = true := by
  have hs : count249 q = (countLit q [126, 127]) + (countLit q [128, 129]) := List.countP_append (p := literal q) (l₁ := [126, 127]) (l₂ := [128, 129])
  have hm := merge_two (literal (valuationOf q) (245)) (literal (valuationOf q) (247)) (literal (valuationOf q) (250)) (countLit q [126, 127]) (countLit q [128, 129]) (count249 q) 1 1 (meaning245 q) (meaning247 q) (meaning250 q) hs
  change valuationOf q 245 = false ∨ valuationOf q 247 = false ∨ valuationOf q 250 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause293 (q : Snake 81) (h : Conditions q) : valuation q 245 = false ∨ valuation q 247 = false ∨ valuation q 250 = true := counterClause293 (baseVal q)

theorem counterClause294 (q : Nat → Bool) : valuationOf q 249 = false ∨ valuationOf q 251 = true := by
  have hs : count251 q = (countLit q [123, 124, 125]) + (countLit q [126, 127, 128, 129]) := List.countP_append (p := literal q) (l₁ := [123, 124, 125]) (l₂ := [126, 127, 128, 129])
  have hm := merge_right (literal (valuationOf q) (249)) (literal (valuationOf q) (251)) (countLit q [123, 124, 125]) (countLit q [126, 127, 128, 129]) (count251 q) 1 (meaning249 q) (meaning251 q) hs
  change valuationOf q 249 = false ∨ valuationOf q 251 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause294 (q : Snake 81) (h : Conditions q) : valuation q 249 = false ∨ valuation q 251 = true := counterClause294 (baseVal q)

theorem counterClause295 (q : Nat → Bool) : valuationOf q 250 = false ∨ valuationOf q 252 = true := by
  have hs : count251 q = (countLit q [123, 124, 125]) + (countLit q [126, 127, 128, 129]) := List.countP_append (p := literal q) (l₁ := [123, 124, 125]) (l₂ := [126, 127, 128, 129])
  have hm := merge_right (literal (valuationOf q) (250)) (literal (valuationOf q) (252)) (countLit q [123, 124, 125]) (countLit q [126, 127, 128, 129]) (count251 q) 2 (meaning250 q) (meaning252 q) hs
  change valuationOf q 250 = false ∨ valuationOf q 252 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause295 (q : Snake 81) (h : Conditions q) : valuation q 250 = false ∨ valuation q 252 = true := counterClause295 (baseVal q)

theorem counterClause296 (q : Nat → Bool) : valuationOf q 243 = false ∨ valuationOf q 251 = true := by
  have hs : count251 q = (countLit q [123, 124, 125]) + (countLit q [126, 127, 128, 129]) := List.countP_append (p := literal q) (l₁ := [123, 124, 125]) (l₂ := [126, 127, 128, 129])
  have hm := merge_left (literal (valuationOf q) (243)) (literal (valuationOf q) (251)) (countLit q [123, 124, 125]) (countLit q [126, 127, 128, 129]) (count251 q) 1 (meaning243 q) (meaning251 q) hs
  change valuationOf q 243 = false ∨ valuationOf q 251 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause296 (q : Snake 81) (h : Conditions q) : valuation q 243 = false ∨ valuation q 251 = true := counterClause296 (baseVal q)

theorem counterClause297 (q : Nat → Bool) : valuationOf q 251 = false ∨ valuationOf q 253 = true := by
  have hs : count253 q = (countLit q [117, 118, 119, 120, 121, 122]) + (countLit q [123, 124, 125, 126, 127, 128, 129]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119, 120, 121, 122]) (l₂ := [123, 124, 125, 126, 127, 128, 129])
  have hm := merge_right (literal (valuationOf q) (251)) (literal (valuationOf q) (253)) (countLit q [117, 118, 119, 120, 121, 122]) (countLit q [123, 124, 125, 126, 127, 128, 129]) (count253 q) 1 (meaning251 q) (meaning253 q) hs
  change valuationOf q 251 = false ∨ valuationOf q 253 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause297 (q : Snake 81) (h : Conditions q) : valuation q 251 = false ∨ valuation q 253 = true := counterClause297 (baseVal q)

theorem counterClause298 (q : Nat → Bool) : valuationOf q 252 = false ∨ valuationOf q 254 = true := by
  have hs : count253 q = (countLit q [117, 118, 119, 120, 121, 122]) + (countLit q [123, 124, 125, 126, 127, 128, 129]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119, 120, 121, 122]) (l₂ := [123, 124, 125, 126, 127, 128, 129])
  have hm := merge_right (literal (valuationOf q) (252)) (literal (valuationOf q) (254)) (countLit q [117, 118, 119, 120, 121, 122]) (countLit q [123, 124, 125, 126, 127, 128, 129]) (count253 q) 2 (meaning252 q) (meaning254 q) hs
  change valuationOf q 252 = false ∨ valuationOf q 254 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause298 (q : Snake 81) (h : Conditions q) : valuation q 252 = false ∨ valuation q 254 = true := counterClause298 (baseVal q)

theorem counterClause299 (q : Nat → Bool) : valuationOf q 239 = false ∨ valuationOf q 253 = true := by
  have hs : count253 q = (countLit q [117, 118, 119, 120, 121, 122]) + (countLit q [123, 124, 125, 126, 127, 128, 129]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119, 120, 121, 122]) (l₂ := [123, 124, 125, 126, 127, 128, 129])
  have hm := merge_left (literal (valuationOf q) (239)) (literal (valuationOf q) (253)) (countLit q [117, 118, 119, 120, 121, 122]) (countLit q [123, 124, 125, 126, 127, 128, 129]) (count253 q) 1 (meaning239 q) (meaning253 q) hs
  change valuationOf q 239 = false ∨ valuationOf q 253 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause299 (q : Snake 81) (h : Conditions q) : valuation q 239 = false ∨ valuation q 253 = true := counterClause299 (baseVal q)

theorem counterClause300 (q : Nat → Bool) : valuationOf q 239 = false ∨ valuationOf q 251 = false ∨ valuationOf q 254 = true := by
  have hs : count253 q = (countLit q [117, 118, 119, 120, 121, 122]) + (countLit q [123, 124, 125, 126, 127, 128, 129]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119, 120, 121, 122]) (l₂ := [123, 124, 125, 126, 127, 128, 129])
  have hm := merge_two (literal (valuationOf q) (239)) (literal (valuationOf q) (251)) (literal (valuationOf q) (254)) (countLit q [117, 118, 119, 120, 121, 122]) (countLit q [123, 124, 125, 126, 127, 128, 129]) (count253 q) 1 1 (meaning239 q) (meaning251 q) (meaning254 q) hs
  change valuationOf q 239 = false ∨ valuationOf q 251 = false ∨ valuationOf q 254 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause300 (q : Snake 81) (h : Conditions q) : valuation q 239 = false ∨ valuation q 251 = false ∨ valuation q 254 = true := counterClause300 (baseVal q)

theorem counterClause301 (q : Nat → Bool) : valuationOf q 253 = false ∨ valuationOf q 255 = true := by
  have hs : count255 q = (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116]) + (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116]) (l₂ := [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129])
  have hm := merge_right (literal (valuationOf q) (253)) (literal (valuationOf q) (255)) (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116]) (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129]) (count255 q) 1 (meaning253 q) (meaning255 q) hs
  change valuationOf q 253 = false ∨ valuationOf q 255 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause301 (q : Snake 81) (h : Conditions q) : valuation q 253 = false ∨ valuation q 255 = true := counterClause301 (baseVal q)

theorem counterClause302 (q : Nat → Bool) : valuationOf q 254 = false ∨ valuationOf q 256 = true := by
  have hs : count255 q = (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116]) + (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116]) (l₂ := [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129])
  have hm := merge_right (literal (valuationOf q) (254)) (literal (valuationOf q) (256)) (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116]) (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129]) (count255 q) 2 (meaning254 q) (meaning256 q) hs
  change valuationOf q 254 = false ∨ valuationOf q 256 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause302 (q : Snake 81) (h : Conditions q) : valuation q 254 = false ∨ valuation q 256 = true := counterClause302 (baseVal q)

theorem counterClause303 (q : Nat → Bool) : valuationOf q 229 = false ∨ valuationOf q 255 = true := by
  have hs : count255 q = (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116]) + (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116]) (l₂ := [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129])
  have hm := merge_left (literal (valuationOf q) (229)) (literal (valuationOf q) (255)) (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116]) (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129]) (count255 q) 1 (meaning229 q) (meaning255 q) hs
  change valuationOf q 229 = false ∨ valuationOf q 255 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause303 (q : Snake 81) (h : Conditions q) : valuation q 229 = false ∨ valuation q 255 = true := counterClause303 (baseVal q)

theorem counterClause304 (q : Nat → Bool) : valuationOf q 229 = false ∨ valuationOf q 253 = false ∨ valuationOf q 256 = true := by
  have hs : count255 q = (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116]) + (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116]) (l₂ := [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129])
  have hm := merge_two (literal (valuationOf q) (229)) (literal (valuationOf q) (253)) (literal (valuationOf q) (256)) (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116]) (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129]) (count255 q) 1 1 (meaning229 q) (meaning253 q) (meaning256 q) hs
  change valuationOf q 229 = false ∨ valuationOf q 253 = false ∨ valuationOf q 256 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause304 (q : Snake 81) (h : Conditions q) : valuation q 229 = false ∨ valuation q 253 = false ∨ valuation q 256 = true := counterClause304 (baseVal q)

theorem counterClause305 (q : Nat → Bool) : valuationOf q 230 = false ∨ valuationOf q 256 = true := by
  have hs : count255 q = (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116]) + (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116]) (l₂ := [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129])
  have hm := merge_left (literal (valuationOf q) (230)) (literal (valuationOf q) (256)) (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116]) (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129]) (count255 q) 2 (meaning230 q) (meaning256 q) hs
  change valuationOf q 230 = false ∨ valuationOf q 256 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause305 (q : Snake 81) (h : Conditions q) : valuation q 230 = false ∨ valuation q 256 = true := counterClause305 (baseVal q)

theorem counterClause306 (q : Nat → Bool) : valuationOf q 131 = false ∨ valuationOf q 257 = true := by
  have hs : count257 q = (countLit q [131]) + (countLit q [132]) := List.countP_append (p := literal q) (l₁ := [131]) (l₂ := [132])
  have hm := merge_left (literal (valuationOf q) (131)) (literal (valuationOf q) (257)) (countLit q [131]) (countLit q [132]) (count257 q) 1 (meaning131 q) (meaning257 q) hs
  change valuationOf q 131 = false ∨ valuationOf q 257 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause306 (q : Snake 81) (h : Conditions q) : valuation q 131 = false ∨ valuation q 257 = true := counterClause306 (baseVal q)

theorem counterClause307 (q : Nat → Bool) : valuationOf q 257 = false ∨ valuationOf q 259 = true := by
  have hs : count259 q = (countLit q [130]) + (countLit q [131, 132]) := List.countP_append (p := literal q) (l₁ := [130]) (l₂ := [131, 132])
  have hm := merge_right (literal (valuationOf q) (257)) (literal (valuationOf q) (259)) (countLit q [130]) (countLit q [131, 132]) (count259 q) 1 (meaning257 q) (meaning259 q) hs
  change valuationOf q 257 = false ∨ valuationOf q 259 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause307 (q : Snake 81) (h : Conditions q) : valuation q 257 = false ∨ valuation q 259 = true := counterClause307 (baseVal q)

theorem counterClause308 (q : Nat → Bool) : valuationOf q 134 = false ∨ valuationOf q 261 = true := by
  have hs : count261 q = (countLit q [134]) + (countLit q [135]) := List.countP_append (p := literal q) (l₁ := [134]) (l₂ := [135])
  have hm := merge_left (literal (valuationOf q) (134)) (literal (valuationOf q) (261)) (countLit q [134]) (countLit q [135]) (count261 q) 1 (meaning134 q) (meaning261 q) hs
  change valuationOf q 134 = false ∨ valuationOf q 261 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause308 (q : Snake 81) (h : Conditions q) : valuation q 134 = false ∨ valuation q 261 = true := counterClause308 (baseVal q)

theorem counterClause309 (q : Nat → Bool) : valuationOf q 261 = false ∨ valuationOf q 263 = true := by
  have hs : count263 q = (countLit q [133]) + (countLit q [134, 135]) := List.countP_append (p := literal q) (l₁ := [133]) (l₂ := [134, 135])
  have hm := merge_right (literal (valuationOf q) (261)) (literal (valuationOf q) (263)) (countLit q [133]) (countLit q [134, 135]) (count263 q) 1 (meaning261 q) (meaning263 q) hs
  change valuationOf q 261 = false ∨ valuationOf q 263 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause309 (q : Snake 81) (h : Conditions q) : valuation q 261 = false ∨ valuation q 263 = true := counterClause309 (baseVal q)

theorem counterClause310 (q : Nat → Bool) : valuationOf q 263 = false ∨ valuationOf q 265 = true := by
  have hs : count265 q = (countLit q [130, 131, 132]) + (countLit q [133, 134, 135]) := List.countP_append (p := literal q) (l₁ := [130, 131, 132]) (l₂ := [133, 134, 135])
  have hm := merge_right (literal (valuationOf q) (263)) (literal (valuationOf q) (265)) (countLit q [130, 131, 132]) (countLit q [133, 134, 135]) (count265 q) 1 (meaning263 q) (meaning265 q) hs
  change valuationOf q 263 = false ∨ valuationOf q 265 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause310 (q : Snake 81) (h : Conditions q) : valuation q 263 = false ∨ valuation q 265 = true := counterClause310 (baseVal q)

theorem counterClause311 (q : Nat → Bool) : valuationOf q 259 = false ∨ valuationOf q 265 = true := by
  have hs : count265 q = (countLit q [130, 131, 132]) + (countLit q [133, 134, 135]) := List.countP_append (p := literal q) (l₁ := [130, 131, 132]) (l₂ := [133, 134, 135])
  have hm := merge_left (literal (valuationOf q) (259)) (literal (valuationOf q) (265)) (countLit q [130, 131, 132]) (countLit q [133, 134, 135]) (count265 q) 1 (meaning259 q) (meaning265 q) hs
  change valuationOf q 259 = false ∨ valuationOf q 265 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause311 (q : Snake 81) (h : Conditions q) : valuation q 259 = false ∨ valuation q 265 = true := counterClause311 (baseVal q)

theorem counterClause312 (q : Nat → Bool) : valuationOf q 137 = false ∨ valuationOf q 267 = true := by
  have hs : count267 q = (countLit q [137]) + (countLit q [138]) := List.countP_append (p := literal q) (l₁ := [137]) (l₂ := [138])
  have hm := merge_left (literal (valuationOf q) (137)) (literal (valuationOf q) (267)) (countLit q [137]) (countLit q [138]) (count267 q) 1 (meaning137 q) (meaning267 q) hs
  change valuationOf q 137 = false ∨ valuationOf q 267 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause312 (q : Snake 81) (h : Conditions q) : valuation q 137 = false ∨ valuation q 267 = true := counterClause312 (baseVal q)

theorem counterClause313 (q : Nat → Bool) : valuationOf q 267 = false ∨ valuationOf q 269 = true := by
  have hs : count269 q = (countLit q [136]) + (countLit q [137, 138]) := List.countP_append (p := literal q) (l₁ := [136]) (l₂ := [137, 138])
  have hm := merge_right (literal (valuationOf q) (267)) (literal (valuationOf q) (269)) (countLit q [136]) (countLit q [137, 138]) (count269 q) 1 (meaning267 q) (meaning269 q) hs
  change valuationOf q 267 = false ∨ valuationOf q 269 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause313 (q : Snake 81) (h : Conditions q) : valuation q 267 = false ∨ valuation q 269 = true := counterClause313 (baseVal q)

theorem counterClause314 (q : Nat → Bool) : valuationOf q 140 = false ∨ valuationOf q 271 = true := by
  have hs : count271 q = (countLit q [139]) + (countLit q [140]) := List.countP_append (p := literal q) (l₁ := [139]) (l₂ := [140])
  have hm := merge_right (literal (valuationOf q) (140)) (literal (valuationOf q) (271)) (countLit q [139]) (countLit q [140]) (count271 q) 1 (meaning140 q) (meaning271 q) hs
  change valuationOf q 140 = false ∨ valuationOf q 271 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause314 (q : Snake 81) (h : Conditions q) : valuation q 140 = false ∨ valuation q 271 = true := counterClause314 (baseVal q)

theorem counterClause315 (q : Nat → Bool) : valuationOf q 139 = false ∨ valuationOf q 271 = true := by
  have hs : count271 q = (countLit q [139]) + (countLit q [140]) := List.countP_append (p := literal q) (l₁ := [139]) (l₂ := [140])
  have hm := merge_left (literal (valuationOf q) (139)) (literal (valuationOf q) (271)) (countLit q [139]) (countLit q [140]) (count271 q) 1 (meaning139 q) (meaning271 q) hs
  change valuationOf q 139 = false ∨ valuationOf q 271 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause315 (q : Snake 81) (h : Conditions q) : valuation q 139 = false ∨ valuation q 271 = true := counterClause315 (baseVal q)

theorem counterClause316 (q : Nat → Bool) : valuationOf q 139 = false ∨ valuationOf q 140 = false ∨ valuationOf q 272 = true := by
  have hs : count271 q = (countLit q [139]) + (countLit q [140]) := List.countP_append (p := literal q) (l₁ := [139]) (l₂ := [140])
  have hm := merge_two (literal (valuationOf q) (139)) (literal (valuationOf q) (140)) (literal (valuationOf q) (272)) (countLit q [139]) (countLit q [140]) (count271 q) 1 1 (meaning139 q) (meaning140 q) (meaning272 q) hs
  change valuationOf q 139 = false ∨ valuationOf q 140 = false ∨ valuationOf q 272 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause316 (q : Snake 81) (h : Conditions q) : valuation q 139 = false ∨ valuation q 140 = false ∨ valuation q 272 = true := counterClause316 (baseVal q)

theorem counterClause317 (q : Nat → Bool) : valuationOf q 142 = false ∨ valuationOf q 273 = true := by
  have hs : count273 q = (countLit q [141]) + (countLit q [142]) := List.countP_append (p := literal q) (l₁ := [141]) (l₂ := [142])
  have hm := merge_right (literal (valuationOf q) (142)) (literal (valuationOf q) (273)) (countLit q [141]) (countLit q [142]) (count273 q) 1 (meaning142 q) (meaning273 q) hs
  change valuationOf q 142 = false ∨ valuationOf q 273 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause317 (q : Snake 81) (h : Conditions q) : valuation q 142 = false ∨ valuation q 273 = true := counterClause317 (baseVal q)

theorem counterClause318 (q : Nat → Bool) : valuationOf q 273 = false ∨ valuationOf q 275 = true := by
  have hs : count275 q = (countLit q [139, 140]) + (countLit q [141, 142]) := List.countP_append (p := literal q) (l₁ := [139, 140]) (l₂ := [141, 142])
  have hm := merge_right (literal (valuationOf q) (273)) (literal (valuationOf q) (275)) (countLit q [139, 140]) (countLit q [141, 142]) (count275 q) 1 (meaning273 q) (meaning275 q) hs
  change valuationOf q 273 = false ∨ valuationOf q 275 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause318 (q : Snake 81) (h : Conditions q) : valuation q 273 = false ∨ valuation q 275 = true := counterClause318 (baseVal q)

theorem counterClause319 (q : Nat → Bool) : valuationOf q 271 = false ∨ valuationOf q 275 = true := by
  have hs : count275 q = (countLit q [139, 140]) + (countLit q [141, 142]) := List.countP_append (p := literal q) (l₁ := [139, 140]) (l₂ := [141, 142])
  have hm := merge_left (literal (valuationOf q) (271)) (literal (valuationOf q) (275)) (countLit q [139, 140]) (countLit q [141, 142]) (count275 q) 1 (meaning271 q) (meaning275 q) hs
  change valuationOf q 271 = false ∨ valuationOf q 275 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause319 (q : Snake 81) (h : Conditions q) : valuation q 271 = false ∨ valuation q 275 = true := counterClause319 (baseVal q)

theorem counterClause320 (q : Nat → Bool) : valuationOf q 271 = false ∨ valuationOf q 273 = false ∨ valuationOf q 276 = true := by
  have hs : count275 q = (countLit q [139, 140]) + (countLit q [141, 142]) := List.countP_append (p := literal q) (l₁ := [139, 140]) (l₂ := [141, 142])
  have hm := merge_two (literal (valuationOf q) (271)) (literal (valuationOf q) (273)) (literal (valuationOf q) (276)) (countLit q [139, 140]) (countLit q [141, 142]) (count275 q) 1 1 (meaning271 q) (meaning273 q) (meaning276 q) hs
  change valuationOf q 271 = false ∨ valuationOf q 273 = false ∨ valuationOf q 276 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause320 (q : Snake 81) (h : Conditions q) : valuation q 271 = false ∨ valuation q 273 = false ∨ valuation q 276 = true := counterClause320 (baseVal q)

theorem block9 (q : Snake 81) (h : Conditions q) : B112E175.Block9 (valuation q) :=
  ⟨clause289 q h, clause290 q h, clause291 q h, clause292 q h, clause293 q h, clause294 q h, clause295 q h, clause296 q h, clause297 q h, clause298 q h, clause299 q h, clause300 q h, clause301 q h, clause302 q h, clause303 q h, clause304 q h, clause305 q h, clause306 q h, clause307 q h, clause308 q h, clause309 q h, clause310 q h, clause311 q h, clause312 q h, clause313 q h, clause314 q h, clause315 q h, clause316 q h, clause317 q h, clause318 q h, clause319 q h, clause320 q h⟩

end
end Snake9.Regrowth.E112175
