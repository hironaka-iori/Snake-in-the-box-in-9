import E112091Semantics
import B112E091Inputs
namespace Snake9.Regrowth.E112091
noncomputable section
local instance blockDec16 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause513 (q : Nat → Bool) : valuationOf q 369 = false ∨ valuationOf q 371 = true := by
  have hs : count371 q = (countLit q [189]) + (countLit q [190, 191]) := List.countP_append (p := literal q) (l₁ := [189]) (l₂ := [190, 191])
  have hm := merge_right (literal (valuationOf q) (369)) (literal (valuationOf q) (371)) (countLit q [189]) (countLit q [190, 191]) (count371 q) 1 (meaning369 q) (meaning371 q) hs
  change valuationOf q 369 = false ∨ valuationOf q 371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause513 (q : Snake 81) (h : Conditions q) : valuation q 369 = false ∨ valuation q 371 = true := counterClause513 (baseVal q)

theorem counterClause514 (q : Nat → Bool) : valuationOf q 189 = false ∨ valuationOf q 371 = true := by
  have hs : count371 q = (countLit q [189]) + (countLit q [190, 191]) := List.countP_append (p := literal q) (l₁ := [189]) (l₂ := [190, 191])
  have hm := merge_left (literal (valuationOf q) (189)) (literal (valuationOf q) (371)) (countLit q [189]) (countLit q [190, 191]) (count371 q) 1 (meaning189 q) (meaning371 q) hs
  change valuationOf q 189 = false ∨ valuationOf q 371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause514 (q : Snake 81) (h : Conditions q) : valuation q 189 = false ∨ valuation q 371 = true := counterClause514 (baseVal q)

theorem counterClause515 (q : Nat → Bool) : valuationOf q 189 = false ∨ valuationOf q 369 = false ∨ valuationOf q 372 = true := by
  have hs : count371 q = (countLit q [189]) + (countLit q [190, 191]) := List.countP_append (p := literal q) (l₁ := [189]) (l₂ := [190, 191])
  have hm := merge_two (literal (valuationOf q) (189)) (literal (valuationOf q) (369)) (literal (valuationOf q) (372)) (countLit q [189]) (countLit q [190, 191]) (count371 q) 1 1 (meaning189 q) (meaning369 q) (meaning372 q) hs
  change valuationOf q 189 = false ∨ valuationOf q 369 = false ∨ valuationOf q 372 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause515 (q : Snake 81) (h : Conditions q) : valuation q 189 = false ∨ valuation q 369 = false ∨ valuation q 372 = true := counterClause515 (baseVal q)

theorem counterClause516 (q : Nat → Bool) : valuationOf q 371 = false ∨ valuationOf q 373 = true := by
  have hs : count373 q = (countLit q [186, 187, 188]) + (countLit q [189, 190, 191]) := List.countP_append (p := literal q) (l₁ := [186, 187, 188]) (l₂ := [189, 190, 191])
  have hm := merge_right (literal (valuationOf q) (371)) (literal (valuationOf q) (373)) (countLit q [186, 187, 188]) (countLit q [189, 190, 191]) (count373 q) 1 (meaning371 q) (meaning373 q) hs
  change valuationOf q 371 = false ∨ valuationOf q 373 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause516 (q : Snake 81) (h : Conditions q) : valuation q 371 = false ∨ valuation q 373 = true := counterClause516 (baseVal q)

theorem counterClause517 (q : Nat → Bool) : valuationOf q 372 = false ∨ valuationOf q 374 = true := by
  have hs : count373 q = (countLit q [186, 187, 188]) + (countLit q [189, 190, 191]) := List.countP_append (p := literal q) (l₁ := [186, 187, 188]) (l₂ := [189, 190, 191])
  have hm := merge_right (literal (valuationOf q) (372)) (literal (valuationOf q) (374)) (countLit q [186, 187, 188]) (countLit q [189, 190, 191]) (count373 q) 2 (meaning372 q) (meaning374 q) hs
  change valuationOf q 372 = false ∨ valuationOf q 374 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause517 (q : Snake 81) (h : Conditions q) : valuation q 372 = false ∨ valuation q 374 = true := counterClause517 (baseVal q)

theorem counterClause518 (q : Nat → Bool) : valuationOf q 367 = false ∨ valuationOf q 373 = true := by
  have hs : count373 q = (countLit q [186, 187, 188]) + (countLit q [189, 190, 191]) := List.countP_append (p := literal q) (l₁ := [186, 187, 188]) (l₂ := [189, 190, 191])
  have hm := merge_left (literal (valuationOf q) (367)) (literal (valuationOf q) (373)) (countLit q [186, 187, 188]) (countLit q [189, 190, 191]) (count373 q) 1 (meaning367 q) (meaning373 q) hs
  change valuationOf q 367 = false ∨ valuationOf q 373 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause518 (q : Snake 81) (h : Conditions q) : valuation q 367 = false ∨ valuation q 373 = true := counterClause518 (baseVal q)

theorem counterClause519 (q : Nat → Bool) : valuationOf q 367 = false ∨ valuationOf q 371 = false ∨ valuationOf q 374 = true := by
  have hs : count373 q = (countLit q [186, 187, 188]) + (countLit q [189, 190, 191]) := List.countP_append (p := literal q) (l₁ := [186, 187, 188]) (l₂ := [189, 190, 191])
  have hm := merge_two (literal (valuationOf q) (367)) (literal (valuationOf q) (371)) (literal (valuationOf q) (374)) (countLit q [186, 187, 188]) (countLit q [189, 190, 191]) (count373 q) 1 1 (meaning367 q) (meaning371 q) (meaning374 q) hs
  change valuationOf q 367 = false ∨ valuationOf q 371 = false ∨ valuationOf q 374 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause519 (q : Snake 81) (h : Conditions q) : valuation q 367 = false ∨ valuation q 371 = false ∨ valuation q 374 = true := counterClause519 (baseVal q)

theorem counterClause520 (q : Nat → Bool) : valuationOf q 193 = false ∨ valuationOf q 375 = true := by
  have hs : count375 q = (countLit q [193]) + (countLit q [194]) := List.countP_append (p := literal q) (l₁ := [193]) (l₂ := [194])
  have hm := merge_left (literal (valuationOf q) (193)) (literal (valuationOf q) (375)) (countLit q [193]) (countLit q [194]) (count375 q) 1 (meaning193 q) (meaning375 q) hs
  change valuationOf q 193 = false ∨ valuationOf q 375 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause520 (q : Snake 81) (h : Conditions q) : valuation q 193 = false ∨ valuation q 375 = true := counterClause520 (baseVal q)

theorem counterClause521 (q : Nat → Bool) : valuationOf q 375 = false ∨ valuationOf q 377 = true := by
  have hs : count377 q = (countLit q [192]) + (countLit q [193, 194]) := List.countP_append (p := literal q) (l₁ := [192]) (l₂ := [193, 194])
  have hm := merge_right (literal (valuationOf q) (375)) (literal (valuationOf q) (377)) (countLit q [192]) (countLit q [193, 194]) (count377 q) 1 (meaning375 q) (meaning377 q) hs
  change valuationOf q 375 = false ∨ valuationOf q 377 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause521 (q : Snake 81) (h : Conditions q) : valuation q 375 = false ∨ valuation q 377 = true := counterClause521 (baseVal q)

theorem counterClause522 (q : Nat → Bool) : valuationOf q 195 = false ∨ valuationOf q 379 = true := by
  have hs : count379 q = (countLit q [195]) + (countLit q [196]) := List.countP_append (p := literal q) (l₁ := [195]) (l₂ := [196])
  have hm := merge_left (literal (valuationOf q) (195)) (literal (valuationOf q) (379)) (countLit q [195]) (countLit q [196]) (count379 q) 1 (meaning195 q) (meaning379 q) hs
  change valuationOf q 195 = false ∨ valuationOf q 379 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause522 (q : Snake 81) (h : Conditions q) : valuation q 195 = false ∨ valuation q 379 = true := counterClause522 (baseVal q)

theorem counterClause523 (q : Nat → Bool) : valuationOf q 197 = false ∨ valuationOf q 381 = true := by
  have hs : count381 q = (countLit q [197]) + (countLit q [198]) := List.countP_append (p := literal q) (l₁ := [197]) (l₂ := [198])
  have hm := merge_left (literal (valuationOf q) (197)) (literal (valuationOf q) (381)) (countLit q [197]) (countLit q [198]) (count381 q) 1 (meaning197 q) (meaning381 q) hs
  change valuationOf q 197 = false ∨ valuationOf q 381 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause523 (q : Snake 81) (h : Conditions q) : valuation q 197 = false ∨ valuation q 381 = true := counterClause523 (baseVal q)

theorem counterClause524 (q : Nat → Bool) : valuationOf q 381 = false ∨ valuationOf q 383 = true := by
  have hs : count383 q = (countLit q [195, 196]) + (countLit q [197, 198]) := List.countP_append (p := literal q) (l₁ := [195, 196]) (l₂ := [197, 198])
  have hm := merge_right (literal (valuationOf q) (381)) (literal (valuationOf q) (383)) (countLit q [195, 196]) (countLit q [197, 198]) (count383 q) 1 (meaning381 q) (meaning383 q) hs
  change valuationOf q 381 = false ∨ valuationOf q 383 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause524 (q : Snake 81) (h : Conditions q) : valuation q 381 = false ∨ valuation q 383 = true := counterClause524 (baseVal q)

theorem counterClause525 (q : Nat → Bool) : valuationOf q 379 = false ∨ valuationOf q 383 = true := by
  have hs : count383 q = (countLit q [195, 196]) + (countLit q [197, 198]) := List.countP_append (p := literal q) (l₁ := [195, 196]) (l₂ := [197, 198])
  have hm := merge_left (literal (valuationOf q) (379)) (literal (valuationOf q) (383)) (countLit q [195, 196]) (countLit q [197, 198]) (count383 q) 1 (meaning379 q) (meaning383 q) hs
  change valuationOf q 379 = false ∨ valuationOf q 383 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause525 (q : Snake 81) (h : Conditions q) : valuation q 379 = false ∨ valuation q 383 = true := counterClause525 (baseVal q)

theorem counterClause526 (q : Nat → Bool) : valuationOf q 383 = false ∨ valuationOf q 385 = true := by
  have hs : count385 q = (countLit q [192, 193, 194]) + (countLit q [195, 196, 197, 198]) := List.countP_append (p := literal q) (l₁ := [192, 193, 194]) (l₂ := [195, 196, 197, 198])
  have hm := merge_right (literal (valuationOf q) (383)) (literal (valuationOf q) (385)) (countLit q [192, 193, 194]) (countLit q [195, 196, 197, 198]) (count385 q) 1 (meaning383 q) (meaning385 q) hs
  change valuationOf q 383 = false ∨ valuationOf q 385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause526 (q : Snake 81) (h : Conditions q) : valuation q 383 = false ∨ valuation q 385 = true := counterClause526 (baseVal q)

theorem counterClause527 (q : Nat → Bool) : valuationOf q 377 = false ∨ valuationOf q 385 = true := by
  have hs : count385 q = (countLit q [192, 193, 194]) + (countLit q [195, 196, 197, 198]) := List.countP_append (p := literal q) (l₁ := [192, 193, 194]) (l₂ := [195, 196, 197, 198])
  have hm := merge_left (literal (valuationOf q) (377)) (literal (valuationOf q) (385)) (countLit q [192, 193, 194]) (countLit q [195, 196, 197, 198]) (count385 q) 1 (meaning377 q) (meaning385 q) hs
  change valuationOf q 377 = false ∨ valuationOf q 385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause527 (q : Snake 81) (h : Conditions q) : valuation q 377 = false ∨ valuation q 385 = true := counterClause527 (baseVal q)

theorem counterClause528 (q : Nat → Bool) : valuationOf q 385 = false ∨ valuationOf q 387 = true := by
  have hs : count387 q = (countLit q [186, 187, 188, 189, 190, 191]) + (countLit q [192, 193, 194, 195, 196, 197, 198]) := List.countP_append (p := literal q) (l₁ := [186, 187, 188, 189, 190, 191]) (l₂ := [192, 193, 194, 195, 196, 197, 198])
  have hm := merge_right (literal (valuationOf q) (385)) (literal (valuationOf q) (387)) (countLit q [186, 187, 188, 189, 190, 191]) (countLit q [192, 193, 194, 195, 196, 197, 198]) (count387 q) 1 (meaning385 q) (meaning387 q) hs
  change valuationOf q 385 = false ∨ valuationOf q 387 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause528 (q : Snake 81) (h : Conditions q) : valuation q 385 = false ∨ valuation q 387 = true := counterClause528 (baseVal q)

theorem counterClause529 (q : Nat → Bool) : valuationOf q 373 = false ∨ valuationOf q 387 = true := by
  have hs : count387 q = (countLit q [186, 187, 188, 189, 190, 191]) + (countLit q [192, 193, 194, 195, 196, 197, 198]) := List.countP_append (p := literal q) (l₁ := [186, 187, 188, 189, 190, 191]) (l₂ := [192, 193, 194, 195, 196, 197, 198])
  have hm := merge_left (literal (valuationOf q) (373)) (literal (valuationOf q) (387)) (countLit q [186, 187, 188, 189, 190, 191]) (countLit q [192, 193, 194, 195, 196, 197, 198]) (count387 q) 1 (meaning373 q) (meaning387 q) hs
  change valuationOf q 373 = false ∨ valuationOf q 387 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause529 (q : Snake 81) (h : Conditions q) : valuation q 373 = false ∨ valuation q 387 = true := counterClause529 (baseVal q)

theorem counterClause530 (q : Nat → Bool) : valuationOf q 373 = false ∨ valuationOf q 385 = false ∨ valuationOf q 388 = true := by
  have hs : count387 q = (countLit q [186, 187, 188, 189, 190, 191]) + (countLit q [192, 193, 194, 195, 196, 197, 198]) := List.countP_append (p := literal q) (l₁ := [186, 187, 188, 189, 190, 191]) (l₂ := [192, 193, 194, 195, 196, 197, 198])
  have hm := merge_two (literal (valuationOf q) (373)) (literal (valuationOf q) (385)) (literal (valuationOf q) (388)) (countLit q [186, 187, 188, 189, 190, 191]) (countLit q [192, 193, 194, 195, 196, 197, 198]) (count387 q) 1 1 (meaning373 q) (meaning385 q) (meaning388 q) hs
  change valuationOf q 373 = false ∨ valuationOf q 385 = false ∨ valuationOf q 388 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause530 (q : Snake 81) (h : Conditions q) : valuation q 373 = false ∨ valuation q 385 = false ∨ valuation q 388 = true := counterClause530 (baseVal q)

theorem counterClause531 (q : Nat → Bool) : valuationOf q 374 = false ∨ valuationOf q 388 = true := by
  have hs : count387 q = (countLit q [186, 187, 188, 189, 190, 191]) + (countLit q [192, 193, 194, 195, 196, 197, 198]) := List.countP_append (p := literal q) (l₁ := [186, 187, 188, 189, 190, 191]) (l₂ := [192, 193, 194, 195, 196, 197, 198])
  have hm := merge_left (literal (valuationOf q) (374)) (literal (valuationOf q) (388)) (countLit q [186, 187, 188, 189, 190, 191]) (countLit q [192, 193, 194, 195, 196, 197, 198]) (count387 q) 2 (meaning374 q) (meaning388 q) hs
  change valuationOf q 374 = false ∨ valuationOf q 388 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause531 (q : Snake 81) (h : Conditions q) : valuation q 374 = false ∨ valuation q 388 = true := counterClause531 (baseVal q)

theorem counterClause532 (q : Nat → Bool) : valuationOf q 199 = false ∨ valuationOf q 391 = true := by
  have hs : count391 q = (countLit q [199]) + (countLit q [200, 201]) := List.countP_append (p := literal q) (l₁ := [199]) (l₂ := [200, 201])
  have hm := merge_left (literal (valuationOf q) (199)) (literal (valuationOf q) (391)) (countLit q [199]) (countLit q [200, 201]) (count391 q) 1 (meaning199 q) (meaning391 q) hs
  change valuationOf q 199 = false ∨ valuationOf q 391 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause532 (q : Snake 81) (h : Conditions q) : valuation q 199 = false ∨ valuation q 391 = true := counterClause532 (baseVal q)

theorem counterClause533 (q : Nat → Bool) : valuationOf q 202 = false ∨ valuationOf q 393 = true := by
  have hs : count393 q = (countLit q [202]) + (countLit q [203]) := List.countP_append (p := literal q) (l₁ := [202]) (l₂ := [203])
  have hm := merge_left (literal (valuationOf q) (202)) (literal (valuationOf q) (393)) (countLit q [202]) (countLit q [203]) (count393 q) 1 (meaning202 q) (meaning393 q) hs
  change valuationOf q 202 = false ∨ valuationOf q 393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause533 (q : Snake 81) (h : Conditions q) : valuation q 202 = false ∨ valuation q 393 = true := counterClause533 (baseVal q)

theorem counterClause534 (q : Nat → Bool) : valuationOf q 204 = false ∨ valuationOf q 395 = true := by
  have hs : count395 q = (countLit q [204]) + (countLit q [205]) := List.countP_append (p := literal q) (l₁ := [204]) (l₂ := [205])
  have hm := merge_left (literal (valuationOf q) (204)) (literal (valuationOf q) (395)) (countLit q [204]) (countLit q [205]) (count395 q) 1 (meaning204 q) (meaning395 q) hs
  change valuationOf q 204 = false ∨ valuationOf q 395 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause534 (q : Snake 81) (h : Conditions q) : valuation q 204 = false ∨ valuation q 395 = true := counterClause534 (baseVal q)

theorem counterClause535 (q : Nat → Bool) : valuationOf q 395 = false ∨ valuationOf q 397 = true := by
  have hs : count397 q = (countLit q [202, 203]) + (countLit q [204, 205]) := List.countP_append (p := literal q) (l₁ := [202, 203]) (l₂ := [204, 205])
  have hm := merge_right (literal (valuationOf q) (395)) (literal (valuationOf q) (397)) (countLit q [202, 203]) (countLit q [204, 205]) (count397 q) 1 (meaning395 q) (meaning397 q) hs
  change valuationOf q 395 = false ∨ valuationOf q 397 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause535 (q : Snake 81) (h : Conditions q) : valuation q 395 = false ∨ valuation q 397 = true := counterClause535 (baseVal q)

theorem counterClause536 (q : Nat → Bool) : valuationOf q 393 = false ∨ valuationOf q 397 = true := by
  have hs : count397 q = (countLit q [202, 203]) + (countLit q [204, 205]) := List.countP_append (p := literal q) (l₁ := [202, 203]) (l₂ := [204, 205])
  have hm := merge_left (literal (valuationOf q) (393)) (literal (valuationOf q) (397)) (countLit q [202, 203]) (countLit q [204, 205]) (count397 q) 1 (meaning393 q) (meaning397 q) hs
  change valuationOf q 393 = false ∨ valuationOf q 397 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause536 (q : Snake 81) (h : Conditions q) : valuation q 393 = false ∨ valuation q 397 = true := counterClause536 (baseVal q)

theorem counterClause537 (q : Nat → Bool) : valuationOf q 397 = false ∨ valuationOf q 399 = true := by
  have hs : count399 q = (countLit q [199, 200, 201]) + (countLit q [202, 203, 204, 205]) := List.countP_append (p := literal q) (l₁ := [199, 200, 201]) (l₂ := [202, 203, 204, 205])
  have hm := merge_right (literal (valuationOf q) (397)) (literal (valuationOf q) (399)) (countLit q [199, 200, 201]) (countLit q [202, 203, 204, 205]) (count399 q) 1 (meaning397 q) (meaning399 q) hs
  change valuationOf q 397 = false ∨ valuationOf q 399 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause537 (q : Snake 81) (h : Conditions q) : valuation q 397 = false ∨ valuation q 399 = true := counterClause537 (baseVal q)

theorem counterClause538 (q : Nat → Bool) : valuationOf q 391 = false ∨ valuationOf q 399 = true := by
  have hs : count399 q = (countLit q [199, 200, 201]) + (countLit q [202, 203, 204, 205]) := List.countP_append (p := literal q) (l₁ := [199, 200, 201]) (l₂ := [202, 203, 204, 205])
  have hm := merge_left (literal (valuationOf q) (391)) (literal (valuationOf q) (399)) (countLit q [199, 200, 201]) (countLit q [202, 203, 204, 205]) (count399 q) 1 (meaning391 q) (meaning399 q) hs
  change valuationOf q 391 = false ∨ valuationOf q 399 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause538 (q : Snake 81) (h : Conditions q) : valuation q 391 = false ∨ valuation q 399 = true := counterClause538 (baseVal q)

theorem counterClause539 (q : Nat → Bool) : valuationOf q 391 = false ∨ valuationOf q 397 = false ∨ valuationOf q 400 = true := by
  have hs : count399 q = (countLit q [199, 200, 201]) + (countLit q [202, 203, 204, 205]) := List.countP_append (p := literal q) (l₁ := [199, 200, 201]) (l₂ := [202, 203, 204, 205])
  have hm := merge_two (literal (valuationOf q) (391)) (literal (valuationOf q) (397)) (literal (valuationOf q) (400)) (countLit q [199, 200, 201]) (countLit q [202, 203, 204, 205]) (count399 q) 1 1 (meaning391 q) (meaning397 q) (meaning400 q) hs
  change valuationOf q 391 = false ∨ valuationOf q 397 = false ∨ valuationOf q 400 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause539 (q : Snake 81) (h : Conditions q) : valuation q 391 = false ∨ valuation q 397 = false ∨ valuation q 400 = true := counterClause539 (baseVal q)

theorem counterClause540 (q : Nat → Bool) : valuationOf q 208 = false ∨ valuationOf q 401 = true := by
  have hs : count401 q = (countLit q [207]) + (countLit q [208]) := List.countP_append (p := literal q) (l₁ := [207]) (l₂ := [208])
  have hm := merge_right (literal (valuationOf q) (208)) (literal (valuationOf q) (401)) (countLit q [207]) (countLit q [208]) (count401 q) 1 (meaning208 q) (meaning401 q) hs
  change valuationOf q 208 = false ∨ valuationOf q 401 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause540 (q : Snake 81) (h : Conditions q) : valuation q 208 = false ∨ valuation q 401 = true := counterClause540 (baseVal q)

theorem counterClause541 (q : Nat → Bool) : valuationOf q 401 = false ∨ valuationOf q 403 = true := by
  have hs : count403 q = (countLit q [206]) + (countLit q [207, 208]) := List.countP_append (p := literal q) (l₁ := [206]) (l₂ := [207, 208])
  have hm := merge_right (literal (valuationOf q) (401)) (literal (valuationOf q) (403)) (countLit q [206]) (countLit q [207, 208]) (count403 q) 1 (meaning401 q) (meaning403 q) hs
  change valuationOf q 401 = false ∨ valuationOf q 403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause541 (q : Snake 81) (h : Conditions q) : valuation q 401 = false ∨ valuation q 403 = true := counterClause541 (baseVal q)

theorem counterClause542 (q : Nat → Bool) : valuationOf q 206 = false ∨ valuationOf q 403 = true := by
  have hs : count403 q = (countLit q [206]) + (countLit q [207, 208]) := List.countP_append (p := literal q) (l₁ := [206]) (l₂ := [207, 208])
  have hm := merge_left (literal (valuationOf q) (206)) (literal (valuationOf q) (403)) (countLit q [206]) (countLit q [207, 208]) (count403 q) 1 (meaning206 q) (meaning403 q) hs
  change valuationOf q 206 = false ∨ valuationOf q 403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause542 (q : Snake 81) (h : Conditions q) : valuation q 206 = false ∨ valuation q 403 = true := counterClause542 (baseVal q)

theorem counterClause543 (q : Nat → Bool) : valuationOf q 206 = false ∨ valuationOf q 401 = false ∨ valuationOf q 404 = true := by
  have hs : count403 q = (countLit q [206]) + (countLit q [207, 208]) := List.countP_append (p := literal q) (l₁ := [206]) (l₂ := [207, 208])
  have hm := merge_two (literal (valuationOf q) (206)) (literal (valuationOf q) (401)) (literal (valuationOf q) (404)) (countLit q [206]) (countLit q [207, 208]) (count403 q) 1 1 (meaning206 q) (meaning401 q) (meaning404 q) hs
  change valuationOf q 206 = false ∨ valuationOf q 401 = false ∨ valuationOf q 404 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause543 (q : Snake 81) (h : Conditions q) : valuation q 206 = false ∨ valuation q 401 = false ∨ valuation q 404 = true := counterClause543 (baseVal q)

theorem counterClause544 (q : Nat → Bool) : valuationOf q 209 = false ∨ valuationOf q 405 = true := by
  have hs : count405 q = (countLit q [209]) + (countLit q [210]) := List.countP_append (p := literal q) (l₁ := [209]) (l₂ := [210])
  have hm := merge_left (literal (valuationOf q) (209)) (literal (valuationOf q) (405)) (countLit q [209]) (countLit q [210]) (count405 q) 1 (meaning209 q) (meaning405 q) hs
  change valuationOf q 209 = false ∨ valuationOf q 405 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause544 (q : Snake 81) (h : Conditions q) : valuation q 209 = false ∨ valuation q 405 = true := counterClause544 (baseVal q)

theorem block16 (q : Snake 81) (h : Conditions q) : B112E091.Block16 (valuation q) :=
  ⟨clause513 q h, clause514 q h, clause515 q h, clause516 q h, clause517 q h, clause518 q h, clause519 q h, clause520 q h, clause521 q h, clause522 q h, clause523 q h, clause524 q h, clause525 q h, clause526 q h, clause527 q h, clause528 q h, clause529 q h, clause530 q h, clause531 q h, clause532 q h, clause533 q h, clause534 q h, clause535 q h, clause536 q h, clause537 q h, clause538 q h, clause539 q h, clause540 q h, clause541 q h, clause542 q h, clause543 q h, clause544 q h⟩

end
end Snake9.Regrowth.E112091
