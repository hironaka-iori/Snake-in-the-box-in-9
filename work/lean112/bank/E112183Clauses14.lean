import E112183Semantics
import B112E183Inputs
namespace Snake9.Regrowth.E112183
noncomputable section
local instance blockDec14 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause449 (q : Nat → Bool) : valuationOf q 194 = false ∨ valuationOf q 379 = true := by
  have hs : count379 q = (countLit q [194]) + (countLit q [195]) := List.countP_append (p := literal q) (l₁ := [194]) (l₂ := [195])
  have hm := merge_left (literal (valuationOf q) (194)) (literal (valuationOf q) (379)) (countLit q [194]) (countLit q [195]) (count379 q) 1 (meaning194 q) (meaning379 q) hs
  change valuationOf q 194 = false ∨ valuationOf q 379 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause449 (q : Snake 81) (h : Conditions q) : valuation q 194 = false ∨ valuation q 379 = true := counterClause449 (baseVal q)

theorem counterClause450 (q : Nat → Bool) : valuationOf q 379 = false ∨ valuationOf q 381 = true := by
  have hs : count381 q = (countLit q [193]) + (countLit q [194, 195]) := List.countP_append (p := literal q) (l₁ := [193]) (l₂ := [194, 195])
  have hm := merge_right (literal (valuationOf q) (379)) (literal (valuationOf q) (381)) (countLit q [193]) (countLit q [194, 195]) (count381 q) 1 (meaning379 q) (meaning381 q) hs
  change valuationOf q 379 = false ∨ valuationOf q 381 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause450 (q : Snake 81) (h : Conditions q) : valuation q 379 = false ∨ valuation q 381 = true := counterClause450 (baseVal q)

theorem counterClause451 (q : Nat → Bool) : valuationOf q 198 = false ∨ valuationOf q 385 = true := by
  have hs : count385 q = (countLit q [198]) + (countLit q [199]) := List.countP_append (p := literal q) (l₁ := [198]) (l₂ := [199])
  have hm := merge_left (literal (valuationOf q) (198)) (literal (valuationOf q) (385)) (countLit q [198]) (countLit q [199]) (count385 q) 1 (meaning198 q) (meaning385 q) hs
  change valuationOf q 198 = false ∨ valuationOf q 385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause451 (q : Snake 81) (h : Conditions q) : valuation q 198 = false ∨ valuation q 385 = true := counterClause451 (baseVal q)

theorem counterClause452 (q : Nat → Bool) : valuationOf q 385 = false ∨ valuationOf q 387 = true := by
  have hs : count387 q = (countLit q [196, 197]) + (countLit q [198, 199]) := List.countP_append (p := literal q) (l₁ := [196, 197]) (l₂ := [198, 199])
  have hm := merge_right (literal (valuationOf q) (385)) (literal (valuationOf q) (387)) (countLit q [196, 197]) (countLit q [198, 199]) (count387 q) 1 (meaning385 q) (meaning387 q) hs
  change valuationOf q 385 = false ∨ valuationOf q 387 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause452 (q : Snake 81) (h : Conditions q) : valuation q 385 = false ∨ valuation q 387 = true := counterClause452 (baseVal q)

theorem counterClause453 (q : Nat → Bool) : valuationOf q 387 = false ∨ valuationOf q 389 = true := by
  have hs : count389 q = (countLit q [193, 194, 195]) + (countLit q [196, 197, 198, 199]) := List.countP_append (p := literal q) (l₁ := [193, 194, 195]) (l₂ := [196, 197, 198, 199])
  have hm := merge_right (literal (valuationOf q) (387)) (literal (valuationOf q) (389)) (countLit q [193, 194, 195]) (countLit q [196, 197, 198, 199]) (count389 q) 1 (meaning387 q) (meaning389 q) hs
  change valuationOf q 387 = false ∨ valuationOf q 389 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause453 (q : Snake 81) (h : Conditions q) : valuation q 387 = false ∨ valuation q 389 = true := counterClause453 (baseVal q)

theorem counterClause454 (q : Nat → Bool) : valuationOf q 381 = false ∨ valuationOf q 389 = true := by
  have hs : count389 q = (countLit q [193, 194, 195]) + (countLit q [196, 197, 198, 199]) := List.countP_append (p := literal q) (l₁ := [193, 194, 195]) (l₂ := [196, 197, 198, 199])
  have hm := merge_left (literal (valuationOf q) (381)) (literal (valuationOf q) (389)) (countLit q [193, 194, 195]) (countLit q [196, 197, 198, 199]) (count389 q) 1 (meaning381 q) (meaning389 q) hs
  change valuationOf q 381 = false ∨ valuationOf q 389 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause454 (q : Snake 81) (h : Conditions q) : valuation q 381 = false ∨ valuation q 389 = true := counterClause454 (baseVal q)

theorem counterClause455 (q : Nat → Bool) : valuationOf q 381 = false ∨ valuationOf q 387 = false ∨ valuationOf q 390 = true := by
  have hs : count389 q = (countLit q [193, 194, 195]) + (countLit q [196, 197, 198, 199]) := List.countP_append (p := literal q) (l₁ := [193, 194, 195]) (l₂ := [196, 197, 198, 199])
  have hm := merge_two (literal (valuationOf q) (381)) (literal (valuationOf q) (387)) (literal (valuationOf q) (390)) (countLit q [193, 194, 195]) (countLit q [196, 197, 198, 199]) (count389 q) 1 1 (meaning381 q) (meaning387 q) (meaning390 q) hs
  change valuationOf q 381 = false ∨ valuationOf q 387 = false ∨ valuationOf q 390 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause455 (q : Snake 81) (h : Conditions q) : valuation q 381 = false ∨ valuation q 387 = false ∨ valuation q 390 = true := counterClause455 (baseVal q)

theorem counterClause456 (q : Nat → Bool) : valuationOf q 202 = false ∨ valuationOf q 391 = true := by
  have hs : count391 q = (countLit q [201]) + (countLit q [202]) := List.countP_append (p := literal q) (l₁ := [201]) (l₂ := [202])
  have hm := merge_right (literal (valuationOf q) (202)) (literal (valuationOf q) (391)) (countLit q [201]) (countLit q [202]) (count391 q) 1 (meaning202 q) (meaning391 q) hs
  change valuationOf q 202 = false ∨ valuationOf q 391 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause456 (q : Snake 81) (h : Conditions q) : valuation q 202 = false ∨ valuation q 391 = true := counterClause456 (baseVal q)

theorem counterClause457 (q : Nat → Bool) : valuationOf q 201 = false ∨ valuationOf q 391 = true := by
  have hs : count391 q = (countLit q [201]) + (countLit q [202]) := List.countP_append (p := literal q) (l₁ := [201]) (l₂ := [202])
  have hm := merge_left (literal (valuationOf q) (201)) (literal (valuationOf q) (391)) (countLit q [201]) (countLit q [202]) (count391 q) 1 (meaning201 q) (meaning391 q) hs
  change valuationOf q 201 = false ∨ valuationOf q 391 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause457 (q : Snake 81) (h : Conditions q) : valuation q 201 = false ∨ valuation q 391 = true := counterClause457 (baseVal q)

theorem counterClause458 (q : Nat → Bool) : valuationOf q 201 = false ∨ valuationOf q 202 = false ∨ valuationOf q 392 = true := by
  have hs : count391 q = (countLit q [201]) + (countLit q [202]) := List.countP_append (p := literal q) (l₁ := [201]) (l₂ := [202])
  have hm := merge_two (literal (valuationOf q) (201)) (literal (valuationOf q) (202)) (literal (valuationOf q) (392)) (countLit q [201]) (countLit q [202]) (count391 q) 1 1 (meaning201 q) (meaning202 q) (meaning392 q) hs
  change valuationOf q 201 = false ∨ valuationOf q 202 = false ∨ valuationOf q 392 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause458 (q : Snake 81) (h : Conditions q) : valuation q 201 = false ∨ valuation q 202 = false ∨ valuation q 392 = true := counterClause458 (baseVal q)

theorem counterClause459 (q : Nat → Bool) : valuationOf q 391 = false ∨ valuationOf q 393 = true := by
  have hs : count393 q = (countLit q [200]) + (countLit q [201, 202]) := List.countP_append (p := literal q) (l₁ := [200]) (l₂ := [201, 202])
  have hm := merge_right (literal (valuationOf q) (391)) (literal (valuationOf q) (393)) (countLit q [200]) (countLit q [201, 202]) (count393 q) 1 (meaning391 q) (meaning393 q) hs
  change valuationOf q 391 = false ∨ valuationOf q 393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause459 (q : Snake 81) (h : Conditions q) : valuation q 391 = false ∨ valuation q 393 = true := counterClause459 (baseVal q)

theorem counterClause460 (q : Nat → Bool) : valuationOf q 392 = false ∨ valuationOf q 394 = true := by
  have hs : count393 q = (countLit q [200]) + (countLit q [201, 202]) := List.countP_append (p := literal q) (l₁ := [200]) (l₂ := [201, 202])
  have hm := merge_right (literal (valuationOf q) (392)) (literal (valuationOf q) (394)) (countLit q [200]) (countLit q [201, 202]) (count393 q) 2 (meaning392 q) (meaning394 q) hs
  change valuationOf q 392 = false ∨ valuationOf q 394 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause460 (q : Snake 81) (h : Conditions q) : valuation q 392 = false ∨ valuation q 394 = true := counterClause460 (baseVal q)

theorem counterClause461 (q : Nat → Bool) : valuationOf q 200 = false ∨ valuationOf q 393 = true := by
  have hs : count393 q = (countLit q [200]) + (countLit q [201, 202]) := List.countP_append (p := literal q) (l₁ := [200]) (l₂ := [201, 202])
  have hm := merge_left (literal (valuationOf q) (200)) (literal (valuationOf q) (393)) (countLit q [200]) (countLit q [201, 202]) (count393 q) 1 (meaning200 q) (meaning393 q) hs
  change valuationOf q 200 = false ∨ valuationOf q 393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause461 (q : Snake 81) (h : Conditions q) : valuation q 200 = false ∨ valuation q 393 = true := counterClause461 (baseVal q)

theorem counterClause462 (q : Nat → Bool) : valuationOf q 200 = false ∨ valuationOf q 391 = false ∨ valuationOf q 394 = true := by
  have hs : count393 q = (countLit q [200]) + (countLit q [201, 202]) := List.countP_append (p := literal q) (l₁ := [200]) (l₂ := [201, 202])
  have hm := merge_two (literal (valuationOf q) (200)) (literal (valuationOf q) (391)) (literal (valuationOf q) (394)) (countLit q [200]) (countLit q [201, 202]) (count393 q) 1 1 (meaning200 q) (meaning391 q) (meaning394 q) hs
  change valuationOf q 200 = false ∨ valuationOf q 391 = false ∨ valuationOf q 394 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause462 (q : Snake 81) (h : Conditions q) : valuation q 200 = false ∨ valuation q 391 = false ∨ valuation q 394 = true := counterClause462 (baseVal q)

theorem counterClause463 (q : Nat → Bool) : valuationOf q 206 = false ∨ valuationOf q 397 = true := by
  have hs : count397 q = (countLit q [205]) + (countLit q [206]) := List.countP_append (p := literal q) (l₁ := [205]) (l₂ := [206])
  have hm := merge_right (literal (valuationOf q) (206)) (literal (valuationOf q) (397)) (countLit q [205]) (countLit q [206]) (count397 q) 1 (meaning206 q) (meaning397 q) hs
  change valuationOf q 206 = false ∨ valuationOf q 397 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause463 (q : Snake 81) (h : Conditions q) : valuation q 206 = false ∨ valuation q 397 = true := counterClause463 (baseVal q)

theorem counterClause464 (q : Nat → Bool) : valuationOf q 397 = false ∨ valuationOf q 399 = true := by
  have hs : count399 q = (countLit q [203, 204]) + (countLit q [205, 206]) := List.countP_append (p := literal q) (l₁ := [203, 204]) (l₂ := [205, 206])
  have hm := merge_right (literal (valuationOf q) (397)) (literal (valuationOf q) (399)) (countLit q [203, 204]) (countLit q [205, 206]) (count399 q) 1 (meaning397 q) (meaning399 q) hs
  change valuationOf q 397 = false ∨ valuationOf q 399 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause464 (q : Snake 81) (h : Conditions q) : valuation q 397 = false ∨ valuation q 399 = true := counterClause464 (baseVal q)

theorem counterClause465 (q : Nat → Bool) : valuationOf q 399 = false ∨ valuationOf q 401 = true := by
  have hs : count401 q = (countLit q [200, 201, 202]) + (countLit q [203, 204, 205, 206]) := List.countP_append (p := literal q) (l₁ := [200, 201, 202]) (l₂ := [203, 204, 205, 206])
  have hm := merge_right (literal (valuationOf q) (399)) (literal (valuationOf q) (401)) (countLit q [200, 201, 202]) (countLit q [203, 204, 205, 206]) (count401 q) 1 (meaning399 q) (meaning401 q) hs
  change valuationOf q 399 = false ∨ valuationOf q 401 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause465 (q : Snake 81) (h : Conditions q) : valuation q 399 = false ∨ valuation q 401 = true := counterClause465 (baseVal q)

theorem counterClause466 (q : Nat → Bool) : valuationOf q 393 = false ∨ valuationOf q 401 = true := by
  have hs : count401 q = (countLit q [200, 201, 202]) + (countLit q [203, 204, 205, 206]) := List.countP_append (p := literal q) (l₁ := [200, 201, 202]) (l₂ := [203, 204, 205, 206])
  have hm := merge_left (literal (valuationOf q) (393)) (literal (valuationOf q) (401)) (countLit q [200, 201, 202]) (countLit q [203, 204, 205, 206]) (count401 q) 1 (meaning393 q) (meaning401 q) hs
  change valuationOf q 393 = false ∨ valuationOf q 401 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause466 (q : Snake 81) (h : Conditions q) : valuation q 393 = false ∨ valuation q 401 = true := counterClause466 (baseVal q)

theorem counterClause467 (q : Nat → Bool) : valuationOf q 394 = false ∨ valuationOf q 402 = true := by
  have hs : count401 q = (countLit q [200, 201, 202]) + (countLit q [203, 204, 205, 206]) := List.countP_append (p := literal q) (l₁ := [200, 201, 202]) (l₂ := [203, 204, 205, 206])
  have hm := merge_left (literal (valuationOf q) (394)) (literal (valuationOf q) (402)) (countLit q [200, 201, 202]) (countLit q [203, 204, 205, 206]) (count401 q) 2 (meaning394 q) (meaning402 q) hs
  change valuationOf q 394 = false ∨ valuationOf q 402 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause467 (q : Snake 81) (h : Conditions q) : valuation q 394 = false ∨ valuation q 402 = true := counterClause467 (baseVal q)

theorem counterClause468 (q : Nat → Bool) : valuationOf q 401 = false ∨ valuationOf q 403 = true := by
  have hs : count403 q = (countLit q [193, 194, 195, 196, 197, 198, 199]) + (countLit q [200, 201, 202, 203, 204, 205, 206]) := List.countP_append (p := literal q) (l₁ := [193, 194, 195, 196, 197, 198, 199]) (l₂ := [200, 201, 202, 203, 204, 205, 206])
  have hm := merge_right (literal (valuationOf q) (401)) (literal (valuationOf q) (403)) (countLit q [193, 194, 195, 196, 197, 198, 199]) (countLit q [200, 201, 202, 203, 204, 205, 206]) (count403 q) 1 (meaning401 q) (meaning403 q) hs
  change valuationOf q 401 = false ∨ valuationOf q 403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause468 (q : Snake 81) (h : Conditions q) : valuation q 401 = false ∨ valuation q 403 = true := counterClause468 (baseVal q)

theorem counterClause469 (q : Nat → Bool) : valuationOf q 402 = false ∨ valuationOf q 404 = true := by
  have hs : count403 q = (countLit q [193, 194, 195, 196, 197, 198, 199]) + (countLit q [200, 201, 202, 203, 204, 205, 206]) := List.countP_append (p := literal q) (l₁ := [193, 194, 195, 196, 197, 198, 199]) (l₂ := [200, 201, 202, 203, 204, 205, 206])
  have hm := merge_right (literal (valuationOf q) (402)) (literal (valuationOf q) (404)) (countLit q [193, 194, 195, 196, 197, 198, 199]) (countLit q [200, 201, 202, 203, 204, 205, 206]) (count403 q) 2 (meaning402 q) (meaning404 q) hs
  change valuationOf q 402 = false ∨ valuationOf q 404 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause469 (q : Snake 81) (h : Conditions q) : valuation q 402 = false ∨ valuation q 404 = true := counterClause469 (baseVal q)

theorem counterClause470 (q : Nat → Bool) : valuationOf q 389 = false ∨ valuationOf q 403 = true := by
  have hs : count403 q = (countLit q [193, 194, 195, 196, 197, 198, 199]) + (countLit q [200, 201, 202, 203, 204, 205, 206]) := List.countP_append (p := literal q) (l₁ := [193, 194, 195, 196, 197, 198, 199]) (l₂ := [200, 201, 202, 203, 204, 205, 206])
  have hm := merge_left (literal (valuationOf q) (389)) (literal (valuationOf q) (403)) (countLit q [193, 194, 195, 196, 197, 198, 199]) (countLit q [200, 201, 202, 203, 204, 205, 206]) (count403 q) 1 (meaning389 q) (meaning403 q) hs
  change valuationOf q 389 = false ∨ valuationOf q 403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause470 (q : Snake 81) (h : Conditions q) : valuation q 389 = false ∨ valuation q 403 = true := counterClause470 (baseVal q)

theorem counterClause471 (q : Nat → Bool) : valuationOf q 389 = false ∨ valuationOf q 401 = false ∨ valuationOf q 404 = true := by
  have hs : count403 q = (countLit q [193, 194, 195, 196, 197, 198, 199]) + (countLit q [200, 201, 202, 203, 204, 205, 206]) := List.countP_append (p := literal q) (l₁ := [193, 194, 195, 196, 197, 198, 199]) (l₂ := [200, 201, 202, 203, 204, 205, 206])
  have hm := merge_two (literal (valuationOf q) (389)) (literal (valuationOf q) (401)) (literal (valuationOf q) (404)) (countLit q [193, 194, 195, 196, 197, 198, 199]) (countLit q [200, 201, 202, 203, 204, 205, 206]) (count403 q) 1 1 (meaning389 q) (meaning401 q) (meaning404 q) hs
  change valuationOf q 389 = false ∨ valuationOf q 401 = false ∨ valuationOf q 404 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause471 (q : Snake 81) (h : Conditions q) : valuation q 389 = false ∨ valuation q 401 = false ∨ valuation q 404 = true := counterClause471 (baseVal q)

theorem counterClause472 (q : Nat → Bool) : valuationOf q 390 = false ∨ valuationOf q 404 = true := by
  have hs : count403 q = (countLit q [193, 194, 195, 196, 197, 198, 199]) + (countLit q [200, 201, 202, 203, 204, 205, 206]) := List.countP_append (p := literal q) (l₁ := [193, 194, 195, 196, 197, 198, 199]) (l₂ := [200, 201, 202, 203, 204, 205, 206])
  have hm := merge_left (literal (valuationOf q) (390)) (literal (valuationOf q) (404)) (countLit q [193, 194, 195, 196, 197, 198, 199]) (countLit q [200, 201, 202, 203, 204, 205, 206]) (count403 q) 2 (meaning390 q) (meaning404 q) hs
  change valuationOf q 390 = false ∨ valuationOf q 404 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause472 (q : Snake 81) (h : Conditions q) : valuation q 390 = false ∨ valuation q 404 = true := counterClause472 (baseVal q)

theorem counterClause473 (q : Nat → Bool) : valuationOf q 209 = false ∨ valuationOf q 405 = true := by
  have hs : count405 q = (countLit q [208]) + (countLit q [209]) := List.countP_append (p := literal q) (l₁ := [208]) (l₂ := [209])
  have hm := merge_right (literal (valuationOf q) (209)) (literal (valuationOf q) (405)) (countLit q [208]) (countLit q [209]) (count405 q) 1 (meaning209 q) (meaning405 q) hs
  change valuationOf q 209 = false ∨ valuationOf q 405 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause473 (q : Snake 81) (h : Conditions q) : valuation q 209 = false ∨ valuation q 405 = true := counterClause473 (baseVal q)

theorem counterClause474 (q : Nat → Bool) : valuationOf q 208 = false ∨ valuationOf q 405 = true := by
  have hs : count405 q = (countLit q [208]) + (countLit q [209]) := List.countP_append (p := literal q) (l₁ := [208]) (l₂ := [209])
  have hm := merge_left (literal (valuationOf q) (208)) (literal (valuationOf q) (405)) (countLit q [208]) (countLit q [209]) (count405 q) 1 (meaning208 q) (meaning405 q) hs
  change valuationOf q 208 = false ∨ valuationOf q 405 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause474 (q : Snake 81) (h : Conditions q) : valuation q 208 = false ∨ valuation q 405 = true := counterClause474 (baseVal q)

theorem counterClause475 (q : Nat → Bool) : valuationOf q 405 = false ∨ valuationOf q 407 = true := by
  have hs : count407 q = (countLit q [207]) + (countLit q [208, 209]) := List.countP_append (p := literal q) (l₁ := [207]) (l₂ := [208, 209])
  have hm := merge_right (literal (valuationOf q) (405)) (literal (valuationOf q) (407)) (countLit q [207]) (countLit q [208, 209]) (count407 q) 1 (meaning405 q) (meaning407 q) hs
  change valuationOf q 405 = false ∨ valuationOf q 407 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause475 (q : Snake 81) (h : Conditions q) : valuation q 405 = false ∨ valuation q 407 = true := counterClause475 (baseVal q)

theorem counterClause476 (q : Nat → Bool) : valuationOf q 211 = false ∨ valuationOf q 409 = true := by
  have hs : count409 q = (countLit q [210]) + (countLit q [211]) := List.countP_append (p := literal q) (l₁ := [210]) (l₂ := [211])
  have hm := merge_right (literal (valuationOf q) (211)) (literal (valuationOf q) (409)) (countLit q [210]) (countLit q [211]) (count409 q) 1 (meaning211 q) (meaning409 q) hs
  change valuationOf q 211 = false ∨ valuationOf q 409 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause476 (q : Snake 81) (h : Conditions q) : valuation q 211 = false ∨ valuation q 409 = true := counterClause476 (baseVal q)

theorem counterClause477 (q : Nat → Bool) : valuationOf q 409 = false ∨ valuationOf q 413 = true := by
  have hs : count413 q = (countLit q [210, 211]) + (countLit q [212, 213]) := List.countP_append (p := literal q) (l₁ := [210, 211]) (l₂ := [212, 213])
  have hm := merge_left (literal (valuationOf q) (409)) (literal (valuationOf q) (413)) (countLit q [210, 211]) (countLit q [212, 213]) (count413 q) 1 (meaning409 q) (meaning413 q) hs
  change valuationOf q 409 = false ∨ valuationOf q 413 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause477 (q : Snake 81) (h : Conditions q) : valuation q 409 = false ∨ valuation q 413 = true := counterClause477 (baseVal q)

theorem counterClause478 (q : Nat → Bool) : valuationOf q 413 = false ∨ valuationOf q 415 = true := by
  have hs : count415 q = (countLit q [207, 208, 209]) + (countLit q [210, 211, 212, 213]) := List.countP_append (p := literal q) (l₁ := [207, 208, 209]) (l₂ := [210, 211, 212, 213])
  have hm := merge_right (literal (valuationOf q) (413)) (literal (valuationOf q) (415)) (countLit q [207, 208, 209]) (countLit q [210, 211, 212, 213]) (count415 q) 1 (meaning413 q) (meaning415 q) hs
  change valuationOf q 413 = false ∨ valuationOf q 415 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause478 (q : Snake 81) (h : Conditions q) : valuation q 413 = false ∨ valuation q 415 = true := counterClause478 (baseVal q)

theorem counterClause479 (q : Nat → Bool) : valuationOf q 407 = false ∨ valuationOf q 415 = true := by
  have hs : count415 q = (countLit q [207, 208, 209]) + (countLit q [210, 211, 212, 213]) := List.countP_append (p := literal q) (l₁ := [207, 208, 209]) (l₂ := [210, 211, 212, 213])
  have hm := merge_left (literal (valuationOf q) (407)) (literal (valuationOf q) (415)) (countLit q [207, 208, 209]) (countLit q [210, 211, 212, 213]) (count415 q) 1 (meaning407 q) (meaning415 q) hs
  change valuationOf q 407 = false ∨ valuationOf q 415 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause479 (q : Snake 81) (h : Conditions q) : valuation q 407 = false ∨ valuation q 415 = true := counterClause479 (baseVal q)

theorem counterClause480 (q : Nat → Bool) : valuationOf q 216 = false ∨ valuationOf q 417 = true := by
  have hs : count417 q = (countLit q [215]) + (countLit q [216]) := List.countP_append (p := literal q) (l₁ := [215]) (l₂ := [216])
  have hm := merge_right (literal (valuationOf q) (216)) (literal (valuationOf q) (417)) (countLit q [215]) (countLit q [216]) (count417 q) 1 (meaning216 q) (meaning417 q) hs
  change valuationOf q 216 = false ∨ valuationOf q 417 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause480 (q : Snake 81) (h : Conditions q) : valuation q 216 = false ∨ valuation q 417 = true := counterClause480 (baseVal q)

theorem block14 (q : Snake 81) (h : Conditions q) : B112E183.Block14 (valuation q) :=
  ⟨clause449 q h, clause450 q h, clause451 q h, clause452 q h, clause453 q h, clause454 q h, clause455 q h, clause456 q h, clause457 q h, clause458 q h, clause459 q h, clause460 q h, clause461 q h, clause462 q h, clause463 q h, clause464 q h, clause465 q h, clause466 q h, clause467 q h, clause468 q h, clause469 q h, clause470 q h, clause471 q h, clause472 q h, clause473 q h, clause474 q h, clause475 q h, clause476 q h, clause477 q h, clause478 q h, clause479 q h, clause480 q h⟩

end
end Snake9.Regrowth.E112183
