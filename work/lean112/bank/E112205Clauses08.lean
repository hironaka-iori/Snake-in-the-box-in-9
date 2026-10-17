import E112205Semantics
import B112E205Inputs
namespace Snake9.Regrowth.E112205
noncomputable section
local instance blockDec8 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause257 (q : Nat → Bool) : valuationOf q 353 = false ∨ valuationOf q 357 = true := by
  have hs : count357 q = (countLit q [180, 181]) + (countLit q [182, 183]) := List.countP_append (p := literal q) (l₁ := [180, 181]) (l₂ := [182, 183])
  have hm := merge_left (literal (valuationOf q) (353)) (literal (valuationOf q) (357)) (countLit q [180, 181]) (countLit q [182, 183]) (count357 q) 1 (meaning353 q) (meaning357 q) hs
  change valuationOf q 353 = false ∨ valuationOf q 357 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause257 (q : Snake 81) (h : Conditions q) : valuation q 353 = false ∨ valuation q 357 = true := counterClause257 (baseVal q)

theorem counterClause258 (q : Nat → Bool) : valuationOf q 357 = false ∨ valuationOf q 359 = true := by
  have hs : count359 q = (countLit q [177, 178, 179]) + (countLit q [180, 181, 182, 183]) := List.countP_append (p := literal q) (l₁ := [177, 178, 179]) (l₂ := [180, 181, 182, 183])
  have hm := merge_right (literal (valuationOf q) (357)) (literal (valuationOf q) (359)) (countLit q [177, 178, 179]) (countLit q [180, 181, 182, 183]) (count359 q) 1 (meaning357 q) (meaning359 q) hs
  change valuationOf q 357 = false ∨ valuationOf q 359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause258 (q : Snake 81) (h : Conditions q) : valuation q 357 = false ∨ valuation q 359 = true := counterClause258 (baseVal q)

theorem counterClause259 (q : Nat → Bool) : valuationOf q 351 = false ∨ valuationOf q 359 = true := by
  have hs : count359 q = (countLit q [177, 178, 179]) + (countLit q [180, 181, 182, 183]) := List.countP_append (p := literal q) (l₁ := [177, 178, 179]) (l₂ := [180, 181, 182, 183])
  have hm := merge_left (literal (valuationOf q) (351)) (literal (valuationOf q) (359)) (countLit q [177, 178, 179]) (countLit q [180, 181, 182, 183]) (count359 q) 1 (meaning351 q) (meaning359 q) hs
  change valuationOf q 351 = false ∨ valuationOf q 359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause259 (q : Snake 81) (h : Conditions q) : valuation q 351 = false ∨ valuation q 359 = true := counterClause259 (baseVal q)

theorem counterClause260 (q : Nat → Bool) : valuationOf q 351 = false ∨ valuationOf q 357 = false ∨ valuationOf q 360 = true := by
  have hs : count359 q = (countLit q [177, 178, 179]) + (countLit q [180, 181, 182, 183]) := List.countP_append (p := literal q) (l₁ := [177, 178, 179]) (l₂ := [180, 181, 182, 183])
  have hm := merge_two (literal (valuationOf q) (351)) (literal (valuationOf q) (357)) (literal (valuationOf q) (360)) (countLit q [177, 178, 179]) (countLit q [180, 181, 182, 183]) (count359 q) 1 1 (meaning351 q) (meaning357 q) (meaning360 q) hs
  change valuationOf q 351 = false ∨ valuationOf q 357 = false ∨ valuationOf q 360 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause260 (q : Snake 81) (h : Conditions q) : valuation q 351 = false ∨ valuation q 357 = false ∨ valuation q 360 = true := counterClause260 (baseVal q)

theorem counterClause261 (q : Nat → Bool) : valuationOf q 188 = false ∨ valuationOf q 365 = true := by
  have hs : count365 q = (countLit q [187]) + (countLit q [188]) := List.countP_append (p := literal q) (l₁ := [187]) (l₂ := [188])
  have hm := merge_right (literal (valuationOf q) (188)) (literal (valuationOf q) (365)) (countLit q [187]) (countLit q [188]) (count365 q) 1 (meaning188 q) (meaning365 q) hs
  change valuationOf q 188 = false ∨ valuationOf q 365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause261 (q : Snake 81) (h : Conditions q) : valuation q 188 = false ∨ valuation q 365 = true := counterClause261 (baseVal q)

theorem counterClause262 (q : Nat → Bool) : valuationOf q 189 = false ∨ valuationOf q 367 = true := by
  have hs : count367 q = (countLit q [189]) + (countLit q [190]) := List.countP_append (p := literal q) (l₁ := [189]) (l₂ := [190])
  have hm := merge_left (literal (valuationOf q) (189)) (literal (valuationOf q) (367)) (countLit q [189]) (countLit q [190]) (count367 q) 1 (meaning189 q) (meaning367 q) hs
  change valuationOf q 189 = false ∨ valuationOf q 367 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause262 (q : Snake 81) (h : Conditions q) : valuation q 189 = false ∨ valuation q 367 = true := counterClause262 (baseVal q)

theorem counterClause263 (q : Nat → Bool) : valuationOf q 367 = false ∨ valuationOf q 369 = true := by
  have hs : count369 q = (countLit q [187, 188]) + (countLit q [189, 190]) := List.countP_append (p := literal q) (l₁ := [187, 188]) (l₂ := [189, 190])
  have hm := merge_right (literal (valuationOf q) (367)) (literal (valuationOf q) (369)) (countLit q [187, 188]) (countLit q [189, 190]) (count369 q) 1 (meaning367 q) (meaning369 q) hs
  change valuationOf q 367 = false ∨ valuationOf q 369 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause263 (q : Snake 81) (h : Conditions q) : valuation q 367 = false ∨ valuation q 369 = true := counterClause263 (baseVal q)

theorem counterClause264 (q : Nat → Bool) : valuationOf q 365 = false ∨ valuationOf q 369 = true := by
  have hs : count369 q = (countLit q [187, 188]) + (countLit q [189, 190]) := List.countP_append (p := literal q) (l₁ := [187, 188]) (l₂ := [189, 190])
  have hm := merge_left (literal (valuationOf q) (365)) (literal (valuationOf q) (369)) (countLit q [187, 188]) (countLit q [189, 190]) (count369 q) 1 (meaning365 q) (meaning369 q) hs
  change valuationOf q 365 = false ∨ valuationOf q 369 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause264 (q : Snake 81) (h : Conditions q) : valuation q 365 = false ∨ valuation q 369 = true := counterClause264 (baseVal q)

theorem counterClause265 (q : Nat → Bool) : valuationOf q 369 = false ∨ valuationOf q 371 = true := by
  have hs : count371 q = (countLit q [184, 185, 186]) + (countLit q [187, 188, 189, 190]) := List.countP_append (p := literal q) (l₁ := [184, 185, 186]) (l₂ := [187, 188, 189, 190])
  have hm := merge_right (literal (valuationOf q) (369)) (literal (valuationOf q) (371)) (countLit q [184, 185, 186]) (countLit q [187, 188, 189, 190]) (count371 q) 1 (meaning369 q) (meaning371 q) hs
  change valuationOf q 369 = false ∨ valuationOf q 371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause265 (q : Snake 81) (h : Conditions q) : valuation q 369 = false ∨ valuation q 371 = true := counterClause265 (baseVal q)

theorem counterClause266 (q : Nat → Bool) : valuationOf q 371 = false ∨ valuationOf q 373 = true := by
  have hs : count373 q = (countLit q [177, 178, 179, 180, 181, 182, 183]) + (countLit q [184, 185, 186, 187, 188, 189, 190]) := List.countP_append (p := literal q) (l₁ := [177, 178, 179, 180, 181, 182, 183]) (l₂ := [184, 185, 186, 187, 188, 189, 190])
  have hm := merge_right (literal (valuationOf q) (371)) (literal (valuationOf q) (373)) (countLit q [177, 178, 179, 180, 181, 182, 183]) (countLit q [184, 185, 186, 187, 188, 189, 190]) (count373 q) 1 (meaning371 q) (meaning373 q) hs
  change valuationOf q 371 = false ∨ valuationOf q 373 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause266 (q : Snake 81) (h : Conditions q) : valuation q 371 = false ∨ valuation q 373 = true := counterClause266 (baseVal q)

theorem counterClause267 (q : Nat → Bool) : valuationOf q 359 = false ∨ valuationOf q 373 = true := by
  have hs : count373 q = (countLit q [177, 178, 179, 180, 181, 182, 183]) + (countLit q [184, 185, 186, 187, 188, 189, 190]) := List.countP_append (p := literal q) (l₁ := [177, 178, 179, 180, 181, 182, 183]) (l₂ := [184, 185, 186, 187, 188, 189, 190])
  have hm := merge_left (literal (valuationOf q) (359)) (literal (valuationOf q) (373)) (countLit q [177, 178, 179, 180, 181, 182, 183]) (countLit q [184, 185, 186, 187, 188, 189, 190]) (count373 q) 1 (meaning359 q) (meaning373 q) hs
  change valuationOf q 359 = false ∨ valuationOf q 373 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause267 (q : Snake 81) (h : Conditions q) : valuation q 359 = false ∨ valuation q 373 = true := counterClause267 (baseVal q)

theorem counterClause268 (q : Nat → Bool) : valuationOf q 360 = false ∨ valuationOf q 374 = true := by
  have hs : count373 q = (countLit q [177, 178, 179, 180, 181, 182, 183]) + (countLit q [184, 185, 186, 187, 188, 189, 190]) := List.countP_append (p := literal q) (l₁ := [177, 178, 179, 180, 181, 182, 183]) (l₂ := [184, 185, 186, 187, 188, 189, 190])
  have hm := merge_left (literal (valuationOf q) (360)) (literal (valuationOf q) (374)) (countLit q [177, 178, 179, 180, 181, 182, 183]) (countLit q [184, 185, 186, 187, 188, 189, 190]) (count373 q) 2 (meaning360 q) (meaning374 q) hs
  change valuationOf q 360 = false ∨ valuationOf q 374 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause268 (q : Snake 81) (h : Conditions q) : valuation q 360 = false ∨ valuation q 374 = true := counterClause268 (baseVal q)

theorem counterClause269 (q : Nat → Bool) : valuationOf q 373 = false ∨ valuationOf q 375 = true := by
  have hs : count375 q = (countLit q [164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) + (countLit q [177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) := List.countP_append (p := literal q) (l₁ := [164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) (l₂ := [177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190])
  have hm := merge_right (literal (valuationOf q) (373)) (literal (valuationOf q) (375)) (countLit q [164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) (countLit q [177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) (count375 q) 1 (meaning373 q) (meaning375 q) hs
  change valuationOf q 373 = false ∨ valuationOf q 375 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause269 (q : Snake 81) (h : Conditions q) : valuation q 373 = false ∨ valuation q 375 = true := counterClause269 (baseVal q)

theorem counterClause270 (q : Nat → Bool) : valuationOf q 374 = false ∨ valuationOf q 376 = true := by
  have hs : count375 q = (countLit q [164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) + (countLit q [177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) := List.countP_append (p := literal q) (l₁ := [164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) (l₂ := [177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190])
  have hm := merge_right (literal (valuationOf q) (374)) (literal (valuationOf q) (376)) (countLit q [164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) (countLit q [177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) (count375 q) 2 (meaning374 q) (meaning376 q) hs
  change valuationOf q 374 = false ∨ valuationOf q 376 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause270 (q : Snake 81) (h : Conditions q) : valuation q 374 = false ∨ valuation q 376 = true := counterClause270 (baseVal q)

theorem counterClause271 (q : Nat → Bool) : valuationOf q 347 = false ∨ valuationOf q 375 = true := by
  have hs : count375 q = (countLit q [164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) + (countLit q [177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) := List.countP_append (p := literal q) (l₁ := [164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) (l₂ := [177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190])
  have hm := merge_left (literal (valuationOf q) (347)) (literal (valuationOf q) (375)) (countLit q [164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) (countLit q [177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) (count375 q) 1 (meaning347 q) (meaning375 q) hs
  change valuationOf q 347 = false ∨ valuationOf q 375 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause271 (q : Snake 81) (h : Conditions q) : valuation q 347 = false ∨ valuation q 375 = true := counterClause271 (baseVal q)

theorem counterClause272 (q : Nat → Bool) : valuationOf q 348 = false ∨ valuationOf q 376 = true := by
  have hs : count375 q = (countLit q [164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) + (countLit q [177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) := List.countP_append (p := literal q) (l₁ := [164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) (l₂ := [177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190])
  have hm := merge_left (literal (valuationOf q) (348)) (literal (valuationOf q) (376)) (countLit q [164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) (countLit q [177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) (count375 q) 2 (meaning348 q) (meaning376 q) hs
  change valuationOf q 348 = false ∨ valuationOf q 376 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause272 (q : Snake 81) (h : Conditions q) : valuation q 348 = false ∨ valuation q 376 = true := counterClause272 (baseVal q)

theorem counterClause273 (q : Nat → Bool) : valuationOf q 191 = false ∨ valuationOf q 379 = true := by
  have hs : count379 q = (countLit q [191]) + (countLit q [192, 193]) := List.countP_append (p := literal q) (l₁ := [191]) (l₂ := [192, 193])
  have hm := merge_left (literal (valuationOf q) (191)) (literal (valuationOf q) (379)) (countLit q [191]) (countLit q [192, 193]) (count379 q) 1 (meaning191 q) (meaning379 q) hs
  change valuationOf q 191 = false ∨ valuationOf q 379 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause273 (q : Snake 81) (h : Conditions q) : valuation q 191 = false ∨ valuation q 379 = true := counterClause273 (baseVal q)

theorem counterClause274 (q : Nat → Bool) : valuationOf q 196 = false ∨ valuationOf q 381 = true := by
  have hs : count381 q = (countLit q [195]) + (countLit q [196]) := List.countP_append (p := literal q) (l₁ := [195]) (l₂ := [196])
  have hm := merge_right (literal (valuationOf q) (196)) (literal (valuationOf q) (381)) (countLit q [195]) (countLit q [196]) (count381 q) 1 (meaning196 q) (meaning381 q) hs
  change valuationOf q 196 = false ∨ valuationOf q 381 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause274 (q : Snake 81) (h : Conditions q) : valuation q 196 = false ∨ valuation q 381 = true := counterClause274 (baseVal q)

theorem counterClause275 (q : Nat → Bool) : valuationOf q 381 = false ∨ valuationOf q 383 = true := by
  have hs : count383 q = (countLit q [194]) + (countLit q [195, 196]) := List.countP_append (p := literal q) (l₁ := [194]) (l₂ := [195, 196])
  have hm := merge_right (literal (valuationOf q) (381)) (literal (valuationOf q) (383)) (countLit q [194]) (countLit q [195, 196]) (count383 q) 1 (meaning381 q) (meaning383 q) hs
  change valuationOf q 381 = false ∨ valuationOf q 383 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause275 (q : Snake 81) (h : Conditions q) : valuation q 381 = false ∨ valuation q 383 = true := counterClause275 (baseVal q)

theorem counterClause276 (q : Nat → Bool) : valuationOf q 194 = false ∨ valuationOf q 383 = true := by
  have hs : count383 q = (countLit q [194]) + (countLit q [195, 196]) := List.countP_append (p := literal q) (l₁ := [194]) (l₂ := [195, 196])
  have hm := merge_left (literal (valuationOf q) (194)) (literal (valuationOf q) (383)) (countLit q [194]) (countLit q [195, 196]) (count383 q) 1 (meaning194 q) (meaning383 q) hs
  change valuationOf q 194 = false ∨ valuationOf q 383 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause276 (q : Snake 81) (h : Conditions q) : valuation q 194 = false ∨ valuation q 383 = true := counterClause276 (baseVal q)

theorem counterClause277 (q : Nat → Bool) : valuationOf q 194 = false ∨ valuationOf q 381 = false ∨ valuationOf q 384 = true := by
  have hs : count383 q = (countLit q [194]) + (countLit q [195, 196]) := List.countP_append (p := literal q) (l₁ := [194]) (l₂ := [195, 196])
  have hm := merge_two (literal (valuationOf q) (194)) (literal (valuationOf q) (381)) (literal (valuationOf q) (384)) (countLit q [194]) (countLit q [195, 196]) (count383 q) 1 1 (meaning194 q) (meaning381 q) (meaning384 q) hs
  change valuationOf q 194 = false ∨ valuationOf q 381 = false ∨ valuationOf q 384 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause277 (q : Snake 81) (h : Conditions q) : valuation q 194 = false ∨ valuation q 381 = false ∨ valuation q 384 = true := counterClause277 (baseVal q)

theorem counterClause278 (q : Nat → Bool) : valuationOf q 383 = false ∨ valuationOf q 385 = true := by
  have hs : count385 q = (countLit q [191, 192, 193]) + (countLit q [194, 195, 196]) := List.countP_append (p := literal q) (l₁ := [191, 192, 193]) (l₂ := [194, 195, 196])
  have hm := merge_right (literal (valuationOf q) (383)) (literal (valuationOf q) (385)) (countLit q [191, 192, 193]) (countLit q [194, 195, 196]) (count385 q) 1 (meaning383 q) (meaning385 q) hs
  change valuationOf q 383 = false ∨ valuationOf q 385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause278 (q : Snake 81) (h : Conditions q) : valuation q 383 = false ∨ valuation q 385 = true := counterClause278 (baseVal q)

theorem counterClause279 (q : Nat → Bool) : valuationOf q 384 = false ∨ valuationOf q 386 = true := by
  have hs : count385 q = (countLit q [191, 192, 193]) + (countLit q [194, 195, 196]) := List.countP_append (p := literal q) (l₁ := [191, 192, 193]) (l₂ := [194, 195, 196])
  have hm := merge_right (literal (valuationOf q) (384)) (literal (valuationOf q) (386)) (countLit q [191, 192, 193]) (countLit q [194, 195, 196]) (count385 q) 2 (meaning384 q) (meaning386 q) hs
  change valuationOf q 384 = false ∨ valuationOf q 386 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause279 (q : Snake 81) (h : Conditions q) : valuation q 384 = false ∨ valuation q 386 = true := counterClause279 (baseVal q)

theorem counterClause280 (q : Nat → Bool) : valuationOf q 379 = false ∨ valuationOf q 385 = true := by
  have hs : count385 q = (countLit q [191, 192, 193]) + (countLit q [194, 195, 196]) := List.countP_append (p := literal q) (l₁ := [191, 192, 193]) (l₂ := [194, 195, 196])
  have hm := merge_left (literal (valuationOf q) (379)) (literal (valuationOf q) (385)) (countLit q [191, 192, 193]) (countLit q [194, 195, 196]) (count385 q) 1 (meaning379 q) (meaning385 q) hs
  change valuationOf q 379 = false ∨ valuationOf q 385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause280 (q : Snake 81) (h : Conditions q) : valuation q 379 = false ∨ valuation q 385 = true := counterClause280 (baseVal q)

theorem counterClause281 (q : Nat → Bool) : valuationOf q 379 = false ∨ valuationOf q 383 = false ∨ valuationOf q 386 = true := by
  have hs : count385 q = (countLit q [191, 192, 193]) + (countLit q [194, 195, 196]) := List.countP_append (p := literal q) (l₁ := [191, 192, 193]) (l₂ := [194, 195, 196])
  have hm := merge_two (literal (valuationOf q) (379)) (literal (valuationOf q) (383)) (literal (valuationOf q) (386)) (countLit q [191, 192, 193]) (countLit q [194, 195, 196]) (count385 q) 1 1 (meaning379 q) (meaning383 q) (meaning386 q) hs
  change valuationOf q 379 = false ∨ valuationOf q 383 = false ∨ valuationOf q 386 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause281 (q : Snake 81) (h : Conditions q) : valuation q 379 = false ∨ valuation q 383 = false ∨ valuation q 386 = true := counterClause281 (baseVal q)

theorem counterClause282 (q : Nat → Bool) : valuationOf q 197 = false ∨ valuationOf q 389 = true := by
  have hs : count389 q = (countLit q [197]) + (countLit q [198, 199]) := List.countP_append (p := literal q) (l₁ := [197]) (l₂ := [198, 199])
  have hm := merge_left (literal (valuationOf q) (197)) (literal (valuationOf q) (389)) (countLit q [197]) (countLit q [198, 199]) (count389 q) 1 (meaning197 q) (meaning389 q) hs
  change valuationOf q 197 = false ∨ valuationOf q 389 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause282 (q : Snake 81) (h : Conditions q) : valuation q 197 = false ∨ valuation q 389 = true := counterClause282 (baseVal q)

theorem counterClause283 (q : Nat → Bool) : valuationOf q 200 = false ∨ valuationOf q 391 = true := by
  have hs : count391 q = (countLit q [200]) + (countLit q [201]) := List.countP_append (p := literal q) (l₁ := [200]) (l₂ := [201])
  have hm := merge_left (literal (valuationOf q) (200)) (literal (valuationOf q) (391)) (countLit q [200]) (countLit q [201]) (count391 q) 1 (meaning200 q) (meaning391 q) hs
  change valuationOf q 200 = false ∨ valuationOf q 391 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause283 (q : Snake 81) (h : Conditions q) : valuation q 200 = false ∨ valuation q 391 = true := counterClause283 (baseVal q)

theorem counterClause284 (q : Nat → Bool) : valuationOf q 203 = false ∨ valuationOf q 393 = true := by
  have hs : count393 q = (countLit q [203]) + (countLit q [204]) := List.countP_append (p := literal q) (l₁ := [203]) (l₂ := [204])
  have hm := merge_left (literal (valuationOf q) (203)) (literal (valuationOf q) (393)) (countLit q [203]) (countLit q [204]) (count393 q) 1 (meaning203 q) (meaning393 q) hs
  change valuationOf q 203 = false ∨ valuationOf q 393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause284 (q : Snake 81) (h : Conditions q) : valuation q 203 = false ∨ valuation q 393 = true := counterClause284 (baseVal q)

theorem counterClause285 (q : Nat → Bool) : valuationOf q 393 = false ∨ valuationOf q 395 = true := by
  have hs : count395 q = (countLit q [200, 201]) + (countLit q [203, 204]) := List.countP_append (p := literal q) (l₁ := [200, 201]) (l₂ := [203, 204])
  have hm := merge_right (literal (valuationOf q) (393)) (literal (valuationOf q) (395)) (countLit q [200, 201]) (countLit q [203, 204]) (count395 q) 1 (meaning393 q) (meaning395 q) hs
  change valuationOf q 393 = false ∨ valuationOf q 395 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause285 (q : Snake 81) (h : Conditions q) : valuation q 393 = false ∨ valuation q 395 = true := counterClause285 (baseVal q)

theorem counterClause286 (q : Nat → Bool) : valuationOf q 391 = false ∨ valuationOf q 395 = true := by
  have hs : count395 q = (countLit q [200, 201]) + (countLit q [203, 204]) := List.countP_append (p := literal q) (l₁ := [200, 201]) (l₂ := [203, 204])
  have hm := merge_left (literal (valuationOf q) (391)) (literal (valuationOf q) (395)) (countLit q [200, 201]) (countLit q [203, 204]) (count395 q) 1 (meaning391 q) (meaning395 q) hs
  change valuationOf q 391 = false ∨ valuationOf q 395 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause286 (q : Snake 81) (h : Conditions q) : valuation q 391 = false ∨ valuation q 395 = true := counterClause286 (baseVal q)

theorem counterClause287 (q : Nat → Bool) : valuationOf q 395 = false ∨ valuationOf q 397 = true := by
  have hs : count397 q = (countLit q [197, 198, 199]) + (countLit q [200, 201, 203, 204]) := List.countP_append (p := literal q) (l₁ := [197, 198, 199]) (l₂ := [200, 201, 203, 204])
  have hm := merge_right (literal (valuationOf q) (395)) (literal (valuationOf q) (397)) (countLit q [197, 198, 199]) (countLit q [200, 201, 203, 204]) (count397 q) 1 (meaning395 q) (meaning397 q) hs
  change valuationOf q 395 = false ∨ valuationOf q 397 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause287 (q : Snake 81) (h : Conditions q) : valuation q 395 = false ∨ valuation q 397 = true := counterClause287 (baseVal q)

theorem counterClause288 (q : Nat → Bool) : valuationOf q 389 = false ∨ valuationOf q 397 = true := by
  have hs : count397 q = (countLit q [197, 198, 199]) + (countLit q [200, 201, 203, 204]) := List.countP_append (p := literal q) (l₁ := [197, 198, 199]) (l₂ := [200, 201, 203, 204])
  have hm := merge_left (literal (valuationOf q) (389)) (literal (valuationOf q) (397)) (countLit q [197, 198, 199]) (countLit q [200, 201, 203, 204]) (count397 q) 1 (meaning389 q) (meaning397 q) hs
  change valuationOf q 389 = false ∨ valuationOf q 397 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause288 (q : Snake 81) (h : Conditions q) : valuation q 389 = false ∨ valuation q 397 = true := counterClause288 (baseVal q)

theorem block8 (q : Snake 81) (h : Conditions q) : B112E205.Block8 (valuation q) :=
  ⟨clause257 q h, clause258 q h, clause259 q h, clause260 q h, clause261 q h, clause262 q h, clause263 q h, clause264 q h, clause265 q h, clause266 q h, clause267 q h, clause268 q h, clause269 q h, clause270 q h, clause271 q h, clause272 q h, clause273 q h, clause274 q h, clause275 q h, clause276 q h, clause277 q h, clause278 q h, clause279 q h, clause280 q h, clause281 q h, clause282 q h, clause283 q h, clause284 q h, clause285 q h, clause286 q h, clause287 q h, clause288 q h⟩

end
end Snake9.Regrowth.E112205
