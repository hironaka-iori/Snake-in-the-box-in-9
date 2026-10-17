import E112145Semantics
import B112E145Inputs
namespace Snake9.Regrowth.E112145
noncomputable section
local instance blockDec12 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause385 (q : Nat → Bool) : valuationOf q 194 = false ∨ valuationOf q 375 = true := by
  have hs : count375 q = (countLit q [194]) + (countLit q [195]) := List.countP_append (p := literal q) (l₁ := [194]) (l₂ := [195])
  have hm := merge_left (literal (valuationOf q) (194)) (literal (valuationOf q) (375)) (countLit q [194]) (countLit q [195]) (count375 q) 1 (meaning194 q) (meaning375 q) hs
  change valuationOf q 194 = false ∨ valuationOf q 375 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause385 (q : Snake 81) (h : Conditions q) : valuation q 194 = false ∨ valuation q 375 = true := counterClause385 (baseVal q)

theorem counterClause386 (q : Nat → Bool) : valuationOf q 375 = false ∨ valuationOf q 377 = true := by
  have hs : count377 q = (countLit q [192, 193]) + (countLit q [194, 195]) := List.countP_append (p := literal q) (l₁ := [192, 193]) (l₂ := [194, 195])
  have hm := merge_right (literal (valuationOf q) (375)) (literal (valuationOf q) (377)) (countLit q [192, 193]) (countLit q [194, 195]) (count377 q) 1 (meaning375 q) (meaning377 q) hs
  change valuationOf q 375 = false ∨ valuationOf q 377 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause386 (q : Snake 81) (h : Conditions q) : valuation q 375 = false ∨ valuation q 377 = true := counterClause386 (baseVal q)

theorem counterClause387 (q : Nat → Bool) : valuationOf q 377 = false ∨ valuationOf q 379 = true := by
  have hs : count379 q = (countLit q [189, 190, 191]) + (countLit q [192, 193, 194, 195]) := List.countP_append (p := literal q) (l₁ := [189, 190, 191]) (l₂ := [192, 193, 194, 195])
  have hm := merge_right (literal (valuationOf q) (377)) (literal (valuationOf q) (379)) (countLit q [189, 190, 191]) (countLit q [192, 193, 194, 195]) (count379 q) 1 (meaning377 q) (meaning379 q) hs
  change valuationOf q 377 = false ∨ valuationOf q 379 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause387 (q : Snake 81) (h : Conditions q) : valuation q 377 = false ∨ valuation q 379 = true := counterClause387 (baseVal q)

theorem counterClause388 (q : Nat → Bool) : valuationOf q 371 = false ∨ valuationOf q 379 = true := by
  have hs : count379 q = (countLit q [189, 190, 191]) + (countLit q [192, 193, 194, 195]) := List.countP_append (p := literal q) (l₁ := [189, 190, 191]) (l₂ := [192, 193, 194, 195])
  have hm := merge_left (literal (valuationOf q) (371)) (literal (valuationOf q) (379)) (countLit q [189, 190, 191]) (countLit q [192, 193, 194, 195]) (count379 q) 1 (meaning371 q) (meaning379 q) hs
  change valuationOf q 371 = false ∨ valuationOf q 379 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause388 (q : Snake 81) (h : Conditions q) : valuation q 371 = false ∨ valuation q 379 = true := counterClause388 (baseVal q)

theorem counterClause389 (q : Nat → Bool) : valuationOf q 372 = false ∨ valuationOf q 380 = true := by
  have hs : count379 q = (countLit q [189, 190, 191]) + (countLit q [192, 193, 194, 195]) := List.countP_append (p := literal q) (l₁ := [189, 190, 191]) (l₂ := [192, 193, 194, 195])
  have hm := merge_left (literal (valuationOf q) (372)) (literal (valuationOf q) (380)) (countLit q [189, 190, 191]) (countLit q [192, 193, 194, 195]) (count379 q) 2 (meaning372 q) (meaning380 q) hs
  change valuationOf q 372 = false ∨ valuationOf q 380 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause389 (q : Snake 81) (h : Conditions q) : valuation q 372 = false ∨ valuation q 380 = true := counterClause389 (baseVal q)

theorem counterClause390 (q : Nat → Bool) : valuationOf q 379 = false ∨ valuationOf q 381 = true := by
  have hs : count381 q = (countLit q [183, 184, 185, 186, 187, 188]) + (countLit q [189, 190, 191, 192, 193, 194, 195]) := List.countP_append (p := literal q) (l₁ := [183, 184, 185, 186, 187, 188]) (l₂ := [189, 190, 191, 192, 193, 194, 195])
  have hm := merge_right (literal (valuationOf q) (379)) (literal (valuationOf q) (381)) (countLit q [183, 184, 185, 186, 187, 188]) (countLit q [189, 190, 191, 192, 193, 194, 195]) (count381 q) 1 (meaning379 q) (meaning381 q) hs
  change valuationOf q 379 = false ∨ valuationOf q 381 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause390 (q : Snake 81) (h : Conditions q) : valuation q 379 = false ∨ valuation q 381 = true := counterClause390 (baseVal q)

theorem counterClause391 (q : Nat → Bool) : valuationOf q 380 = false ∨ valuationOf q 382 = true := by
  have hs : count381 q = (countLit q [183, 184, 185, 186, 187, 188]) + (countLit q [189, 190, 191, 192, 193, 194, 195]) := List.countP_append (p := literal q) (l₁ := [183, 184, 185, 186, 187, 188]) (l₂ := [189, 190, 191, 192, 193, 194, 195])
  have hm := merge_right (literal (valuationOf q) (380)) (literal (valuationOf q) (382)) (countLit q [183, 184, 185, 186, 187, 188]) (countLit q [189, 190, 191, 192, 193, 194, 195]) (count381 q) 2 (meaning380 q) (meaning382 q) hs
  change valuationOf q 380 = false ∨ valuationOf q 382 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause391 (q : Snake 81) (h : Conditions q) : valuation q 380 = false ∨ valuation q 382 = true := counterClause391 (baseVal q)

theorem counterClause392 (q : Nat → Bool) : valuationOf q 367 = false ∨ valuationOf q 381 = true := by
  have hs : count381 q = (countLit q [183, 184, 185, 186, 187, 188]) + (countLit q [189, 190, 191, 192, 193, 194, 195]) := List.countP_append (p := literal q) (l₁ := [183, 184, 185, 186, 187, 188]) (l₂ := [189, 190, 191, 192, 193, 194, 195])
  have hm := merge_left (literal (valuationOf q) (367)) (literal (valuationOf q) (381)) (countLit q [183, 184, 185, 186, 187, 188]) (countLit q [189, 190, 191, 192, 193, 194, 195]) (count381 q) 1 (meaning367 q) (meaning381 q) hs
  change valuationOf q 367 = false ∨ valuationOf q 381 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause392 (q : Snake 81) (h : Conditions q) : valuation q 367 = false ∨ valuation q 381 = true := counterClause392 (baseVal q)

theorem counterClause393 (q : Nat → Bool) : valuationOf q 197 = false ∨ valuationOf q 383 = true := by
  have hs : count383 q = (countLit q [197]) + (countLit q [198]) := List.countP_append (p := literal q) (l₁ := [197]) (l₂ := [198])
  have hm := merge_left (literal (valuationOf q) (197)) (literal (valuationOf q) (383)) (countLit q [197]) (countLit q [198]) (count383 q) 1 (meaning197 q) (meaning383 q) hs
  change valuationOf q 197 = false ∨ valuationOf q 383 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause393 (q : Snake 81) (h : Conditions q) : valuation q 197 = false ∨ valuation q 383 = true := counterClause393 (baseVal q)

theorem counterClause394 (q : Nat → Bool) : valuationOf q 383 = false ∨ valuationOf q 385 = true := by
  have hs : count385 q = (countLit q [196]) + (countLit q [197, 198]) := List.countP_append (p := literal q) (l₁ := [196]) (l₂ := [197, 198])
  have hm := merge_right (literal (valuationOf q) (383)) (literal (valuationOf q) (385)) (countLit q [196]) (countLit q [197, 198]) (count385 q) 1 (meaning383 q) (meaning385 q) hs
  change valuationOf q 383 = false ∨ valuationOf q 385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause394 (q : Snake 81) (h : Conditions q) : valuation q 383 = false ∨ valuation q 385 = true := counterClause394 (baseVal q)

theorem counterClause395 (q : Nat → Bool) : valuationOf q 196 = false ∨ valuationOf q 385 = true := by
  have hs : count385 q = (countLit q [196]) + (countLit q [197, 198]) := List.countP_append (p := literal q) (l₁ := [196]) (l₂ := [197, 198])
  have hm := merge_left (literal (valuationOf q) (196)) (literal (valuationOf q) (385)) (countLit q [196]) (countLit q [197, 198]) (count385 q) 1 (meaning196 q) (meaning385 q) hs
  change valuationOf q 196 = false ∨ valuationOf q 385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause395 (q : Snake 81) (h : Conditions q) : valuation q 196 = false ∨ valuation q 385 = true := counterClause395 (baseVal q)

theorem counterClause396 (q : Nat → Bool) : valuationOf q 199 = false ∨ valuationOf q 389 = true := by
  have hs : count389 q = (countLit q [199]) + (countLit q [200, 201]) := List.countP_append (p := literal q) (l₁ := [199]) (l₂ := [200, 201])
  have hm := merge_left (literal (valuationOf q) (199)) (literal (valuationOf q) (389)) (countLit q [199]) (countLit q [200, 201]) (count389 q) 1 (meaning199 q) (meaning389 q) hs
  change valuationOf q 199 = false ∨ valuationOf q 389 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause396 (q : Snake 81) (h : Conditions q) : valuation q 199 = false ∨ valuation q 389 = true := counterClause396 (baseVal q)

theorem counterClause397 (q : Nat → Bool) : valuationOf q 389 = false ∨ valuationOf q 391 = true := by
  have hs : count391 q = (countLit q [196, 197, 198]) + (countLit q [199, 200, 201]) := List.countP_append (p := literal q) (l₁ := [196, 197, 198]) (l₂ := [199, 200, 201])
  have hm := merge_right (literal (valuationOf q) (389)) (literal (valuationOf q) (391)) (countLit q [196, 197, 198]) (countLit q [199, 200, 201]) (count391 q) 1 (meaning389 q) (meaning391 q) hs
  change valuationOf q 389 = false ∨ valuationOf q 391 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause397 (q : Snake 81) (h : Conditions q) : valuation q 389 = false ∨ valuation q 391 = true := counterClause397 (baseVal q)

theorem counterClause398 (q : Nat → Bool) : valuationOf q 385 = false ∨ valuationOf q 391 = true := by
  have hs : count391 q = (countLit q [196, 197, 198]) + (countLit q [199, 200, 201]) := List.countP_append (p := literal q) (l₁ := [196, 197, 198]) (l₂ := [199, 200, 201])
  have hm := merge_left (literal (valuationOf q) (385)) (literal (valuationOf q) (391)) (countLit q [196, 197, 198]) (countLit q [199, 200, 201]) (count391 q) 1 (meaning385 q) (meaning391 q) hs
  change valuationOf q 385 = false ∨ valuationOf q 391 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause398 (q : Snake 81) (h : Conditions q) : valuation q 385 = false ∨ valuation q 391 = true := counterClause398 (baseVal q)

theorem counterClause399 (q : Nat → Bool) : valuationOf q 204 = false ∨ valuationOf q 393 = true := by
  have hs : count393 q = (countLit q [203]) + (countLit q [204]) := List.countP_append (p := literal q) (l₁ := [203]) (l₂ := [204])
  have hm := merge_right (literal (valuationOf q) (204)) (literal (valuationOf q) (393)) (countLit q [203]) (countLit q [204]) (count393 q) 1 (meaning204 q) (meaning393 q) hs
  change valuationOf q 204 = false ∨ valuationOf q 393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause399 (q : Snake 81) (h : Conditions q) : valuation q 204 = false ∨ valuation q 393 = true := counterClause399 (baseVal q)

theorem counterClause400 (q : Nat → Bool) : valuationOf q 203 = false ∨ valuationOf q 393 = true := by
  have hs : count393 q = (countLit q [203]) + (countLit q [204]) := List.countP_append (p := literal q) (l₁ := [203]) (l₂ := [204])
  have hm := merge_left (literal (valuationOf q) (203)) (literal (valuationOf q) (393)) (countLit q [203]) (countLit q [204]) (count393 q) 1 (meaning203 q) (meaning393 q) hs
  change valuationOf q 203 = false ∨ valuationOf q 393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause400 (q : Snake 81) (h : Conditions q) : valuation q 203 = false ∨ valuation q 393 = true := counterClause400 (baseVal q)

theorem counterClause401 (q : Nat → Bool) : valuationOf q 393 = false ∨ valuationOf q 395 = true := by
  have hs : count395 q = (countLit q [202]) + (countLit q [203, 204]) := List.countP_append (p := literal q) (l₁ := [202]) (l₂ := [203, 204])
  have hm := merge_right (literal (valuationOf q) (393)) (literal (valuationOf q) (395)) (countLit q [202]) (countLit q [203, 204]) (count395 q) 1 (meaning393 q) (meaning395 q) hs
  change valuationOf q 393 = false ∨ valuationOf q 395 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause401 (q : Snake 81) (h : Conditions q) : valuation q 393 = false ∨ valuation q 395 = true := counterClause401 (baseVal q)

theorem counterClause402 (q : Nat → Bool) : valuationOf q 206 = false ∨ valuationOf q 397 = true := by
  have hs : count397 q = (countLit q [205]) + (countLit q [206]) := List.countP_append (p := literal q) (l₁ := [205]) (l₂ := [206])
  have hm := merge_right (literal (valuationOf q) (206)) (literal (valuationOf q) (397)) (countLit q [205]) (countLit q [206]) (count397 q) 1 (meaning206 q) (meaning397 q) hs
  change valuationOf q 206 = false ∨ valuationOf q 397 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause402 (q : Snake 81) (h : Conditions q) : valuation q 206 = false ∨ valuation q 397 = true := counterClause402 (baseVal q)

theorem counterClause403 (q : Nat → Bool) : valuationOf q 205 = false ∨ valuationOf q 397 = true := by
  have hs : count397 q = (countLit q [205]) + (countLit q [206]) := List.countP_append (p := literal q) (l₁ := [205]) (l₂ := [206])
  have hm := merge_left (literal (valuationOf q) (205)) (literal (valuationOf q) (397)) (countLit q [205]) (countLit q [206]) (count397 q) 1 (meaning205 q) (meaning397 q) hs
  change valuationOf q 205 = false ∨ valuationOf q 397 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause403 (q : Snake 81) (h : Conditions q) : valuation q 205 = false ∨ valuation q 397 = true := counterClause403 (baseVal q)

theorem counterClause404 (q : Nat → Bool) : valuationOf q 205 = false ∨ valuationOf q 206 = false ∨ valuationOf q 398 = true := by
  have hs : count397 q = (countLit q [205]) + (countLit q [206]) := List.countP_append (p := literal q) (l₁ := [205]) (l₂ := [206])
  have hm := merge_two (literal (valuationOf q) (205)) (literal (valuationOf q) (206)) (literal (valuationOf q) (398)) (countLit q [205]) (countLit q [206]) (count397 q) 1 1 (meaning205 q) (meaning206 q) (meaning398 q) hs
  change valuationOf q 205 = false ∨ valuationOf q 206 = false ∨ valuationOf q 398 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause404 (q : Snake 81) (h : Conditions q) : valuation q 205 = false ∨ valuation q 206 = false ∨ valuation q 398 = true := counterClause404 (baseVal q)

theorem counterClause405 (q : Nat → Bool) : valuationOf q 397 = false ∨ valuationOf q 401 = true := by
  have hs : count401 q = (countLit q [205, 206]) + (countLit q [207, 208]) := List.countP_append (p := literal q) (l₁ := [205, 206]) (l₂ := [207, 208])
  have hm := merge_left (literal (valuationOf q) (397)) (literal (valuationOf q) (401)) (countLit q [205, 206]) (countLit q [207, 208]) (count401 q) 1 (meaning397 q) (meaning401 q) hs
  change valuationOf q 397 = false ∨ valuationOf q 401 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause405 (q : Snake 81) (h : Conditions q) : valuation q 397 = false ∨ valuation q 401 = true := counterClause405 (baseVal q)

theorem counterClause406 (q : Nat → Bool) : valuationOf q 398 = false ∨ valuationOf q 402 = true := by
  have hs : count401 q = (countLit q [205, 206]) + (countLit q [207, 208]) := List.countP_append (p := literal q) (l₁ := [205, 206]) (l₂ := [207, 208])
  have hm := merge_left (literal (valuationOf q) (398)) (literal (valuationOf q) (402)) (countLit q [205, 206]) (countLit q [207, 208]) (count401 q) 2 (meaning398 q) (meaning402 q) hs
  change valuationOf q 398 = false ∨ valuationOf q 402 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause406 (q : Snake 81) (h : Conditions q) : valuation q 398 = false ∨ valuation q 402 = true := counterClause406 (baseVal q)

theorem counterClause407 (q : Nat → Bool) : valuationOf q 401 = false ∨ valuationOf q 403 = true := by
  have hs : count403 q = (countLit q [202, 203, 204]) + (countLit q [205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [202, 203, 204]) (l₂ := [205, 206, 207, 208])
  have hm := merge_right (literal (valuationOf q) (401)) (literal (valuationOf q) (403)) (countLit q [202, 203, 204]) (countLit q [205, 206, 207, 208]) (count403 q) 1 (meaning401 q) (meaning403 q) hs
  change valuationOf q 401 = false ∨ valuationOf q 403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause407 (q : Snake 81) (h : Conditions q) : valuation q 401 = false ∨ valuation q 403 = true := counterClause407 (baseVal q)

theorem counterClause408 (q : Nat → Bool) : valuationOf q 402 = false ∨ valuationOf q 404 = true := by
  have hs : count403 q = (countLit q [202, 203, 204]) + (countLit q [205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [202, 203, 204]) (l₂ := [205, 206, 207, 208])
  have hm := merge_right (literal (valuationOf q) (402)) (literal (valuationOf q) (404)) (countLit q [202, 203, 204]) (countLit q [205, 206, 207, 208]) (count403 q) 2 (meaning402 q) (meaning404 q) hs
  change valuationOf q 402 = false ∨ valuationOf q 404 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause408 (q : Snake 81) (h : Conditions q) : valuation q 402 = false ∨ valuation q 404 = true := counterClause408 (baseVal q)

theorem counterClause409 (q : Nat → Bool) : valuationOf q 395 = false ∨ valuationOf q 403 = true := by
  have hs : count403 q = (countLit q [202, 203, 204]) + (countLit q [205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [202, 203, 204]) (l₂ := [205, 206, 207, 208])
  have hm := merge_left (literal (valuationOf q) (395)) (literal (valuationOf q) (403)) (countLit q [202, 203, 204]) (countLit q [205, 206, 207, 208]) (count403 q) 1 (meaning395 q) (meaning403 q) hs
  change valuationOf q 395 = false ∨ valuationOf q 403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause409 (q : Snake 81) (h : Conditions q) : valuation q 395 = false ∨ valuation q 403 = true := counterClause409 (baseVal q)

theorem counterClause410 (q : Nat → Bool) : valuationOf q 403 = false ∨ valuationOf q 405 = true := by
  have hs : count405 q = (countLit q [196, 197, 198, 199, 200, 201]) + (countLit q [202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [196, 197, 198, 199, 200, 201]) (l₂ := [202, 203, 204, 205, 206, 207, 208])
  have hm := merge_right (literal (valuationOf q) (403)) (literal (valuationOf q) (405)) (countLit q [196, 197, 198, 199, 200, 201]) (countLit q [202, 203, 204, 205, 206, 207, 208]) (count405 q) 1 (meaning403 q) (meaning405 q) hs
  change valuationOf q 403 = false ∨ valuationOf q 405 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause410 (q : Snake 81) (h : Conditions q) : valuation q 403 = false ∨ valuation q 405 = true := counterClause410 (baseVal q)

theorem counterClause411 (q : Nat → Bool) : valuationOf q 404 = false ∨ valuationOf q 406 = true := by
  have hs : count405 q = (countLit q [196, 197, 198, 199, 200, 201]) + (countLit q [202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [196, 197, 198, 199, 200, 201]) (l₂ := [202, 203, 204, 205, 206, 207, 208])
  have hm := merge_right (literal (valuationOf q) (404)) (literal (valuationOf q) (406)) (countLit q [196, 197, 198, 199, 200, 201]) (countLit q [202, 203, 204, 205, 206, 207, 208]) (count405 q) 2 (meaning404 q) (meaning406 q) hs
  change valuationOf q 404 = false ∨ valuationOf q 406 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause411 (q : Snake 81) (h : Conditions q) : valuation q 404 = false ∨ valuation q 406 = true := counterClause411 (baseVal q)

theorem counterClause412 (q : Nat → Bool) : valuationOf q 391 = false ∨ valuationOf q 405 = true := by
  have hs : count405 q = (countLit q [196, 197, 198, 199, 200, 201]) + (countLit q [202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [196, 197, 198, 199, 200, 201]) (l₂ := [202, 203, 204, 205, 206, 207, 208])
  have hm := merge_left (literal (valuationOf q) (391)) (literal (valuationOf q) (405)) (countLit q [196, 197, 198, 199, 200, 201]) (countLit q [202, 203, 204, 205, 206, 207, 208]) (count405 q) 1 (meaning391 q) (meaning405 q) hs
  change valuationOf q 391 = false ∨ valuationOf q 405 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause412 (q : Snake 81) (h : Conditions q) : valuation q 391 = false ∨ valuation q 405 = true := counterClause412 (baseVal q)

theorem counterClause413 (q : Nat → Bool) : valuationOf q 405 = false ∨ valuationOf q 407 = true := by
  have hs : count407 q = (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195]) + (countLit q [196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195]) (l₂ := [196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208])
  have hm := merge_right (literal (valuationOf q) (405)) (literal (valuationOf q) (407)) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195]) (countLit q [196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (count407 q) 1 (meaning405 q) (meaning407 q) hs
  change valuationOf q 405 = false ∨ valuationOf q 407 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause413 (q : Snake 81) (h : Conditions q) : valuation q 405 = false ∨ valuation q 407 = true := counterClause413 (baseVal q)

theorem counterClause414 (q : Nat → Bool) : valuationOf q 406 = false ∨ valuationOf q 408 = true := by
  have hs : count407 q = (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195]) + (countLit q [196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195]) (l₂ := [196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208])
  have hm := merge_right (literal (valuationOf q) (406)) (literal (valuationOf q) (408)) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195]) (countLit q [196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (count407 q) 2 (meaning406 q) (meaning408 q) hs
  change valuationOf q 406 = false ∨ valuationOf q 408 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause414 (q : Snake 81) (h : Conditions q) : valuation q 406 = false ∨ valuation q 408 = true := counterClause414 (baseVal q)

theorem counterClause415 (q : Nat → Bool) : valuationOf q 381 = false ∨ valuationOf q 407 = true := by
  have hs : count407 q = (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195]) + (countLit q [196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195]) (l₂ := [196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208])
  have hm := merge_left (literal (valuationOf q) (381)) (literal (valuationOf q) (407)) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195]) (countLit q [196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (count407 q) 1 (meaning381 q) (meaning407 q) hs
  change valuationOf q 381 = false ∨ valuationOf q 407 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause415 (q : Snake 81) (h : Conditions q) : valuation q 381 = false ∨ valuation q 407 = true := counterClause415 (baseVal q)

theorem counterClause416 (q : Nat → Bool) : valuationOf q 382 = false ∨ valuationOf q 408 = true := by
  have hs : count407 q = (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195]) + (countLit q [196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195]) (l₂ := [196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208])
  have hm := merge_left (literal (valuationOf q) (382)) (literal (valuationOf q) (408)) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195]) (countLit q [196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (count407 q) 2 (meaning382 q) (meaning408 q) hs
  change valuationOf q 382 = false ∨ valuationOf q 408 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause416 (q : Snake 81) (h : Conditions q) : valuation q 382 = false ∨ valuation q 408 = true := counterClause416 (baseVal q)

theorem block12 (q : Snake 81) (h : Conditions q) : B112E145.Block12 (valuation q) :=
  ⟨clause385 q h, clause386 q h, clause387 q h, clause388 q h, clause389 q h, clause390 q h, clause391 q h, clause392 q h, clause393 q h, clause394 q h, clause395 q h, clause396 q h, clause397 q h, clause398 q h, clause399 q h, clause400 q h, clause401 q h, clause402 q h, clause403 q h, clause404 q h, clause405 q h, clause406 q h, clause407 q h, clause408 q h, clause409 q h, clause410 q h, clause411 q h, clause412 q h, clause413 q h, clause414 q h, clause415 q h, clause416 q h⟩

end
end Snake9.Regrowth.E112145
