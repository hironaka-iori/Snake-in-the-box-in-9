import E112161Semantics
import B112E161Inputs
namespace Snake9.Regrowth.E112161
noncomputable section
local instance blockDec20 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause641 (q : Nat → Bool) : valuationOf q 380 = false ∨ valuationOf q 382 = true := by
  have hs : count381 q = (countLit q [168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180]) + (countLit q [181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) := List.countP_append (p := literal q) (l₁ := [168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180]) (l₂ := [181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194])
  have hm := merge_right (literal (valuationOf q) (380)) (literal (valuationOf q) (382)) (countLit q [168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180]) (countLit q [181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) (count381 q) 2 (meaning380 q) (meaning382 q) hs
  change valuationOf q 380 = false ∨ valuationOf q 382 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause641 (q : Snake 81) (h : Conditions q) : valuation q 380 = false ∨ valuation q 382 = true := counterClause641 (baseVal q)

theorem counterClause642 (q : Nat → Bool) : valuationOf q 353 = false ∨ valuationOf q 381 = true := by
  have hs : count381 q = (countLit q [168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180]) + (countLit q [181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) := List.countP_append (p := literal q) (l₁ := [168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180]) (l₂ := [181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194])
  have hm := merge_left (literal (valuationOf q) (353)) (literal (valuationOf q) (381)) (countLit q [168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180]) (countLit q [181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) (count381 q) 1 (meaning353 q) (meaning381 q) hs
  change valuationOf q 353 = false ∨ valuationOf q 381 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause642 (q : Snake 81) (h : Conditions q) : valuation q 353 = false ∨ valuation q 381 = true := counterClause642 (baseVal q)

theorem counterClause643 (q : Nat → Bool) : valuationOf q 353 = false ∨ valuationOf q 379 = false ∨ valuationOf q 382 = true := by
  have hs : count381 q = (countLit q [168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180]) + (countLit q [181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) := List.countP_append (p := literal q) (l₁ := [168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180]) (l₂ := [181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194])
  have hm := merge_two (literal (valuationOf q) (353)) (literal (valuationOf q) (379)) (literal (valuationOf q) (382)) (countLit q [168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180]) (countLit q [181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) (count381 q) 1 1 (meaning353 q) (meaning379 q) (meaning382 q) hs
  change valuationOf q 353 = false ∨ valuationOf q 379 = false ∨ valuationOf q 382 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause643 (q : Snake 81) (h : Conditions q) : valuation q 353 = false ∨ valuation q 379 = false ∨ valuation q 382 = true := counterClause643 (baseVal q)

theorem counterClause644 (q : Nat → Bool) : valuationOf q 354 = false ∨ valuationOf q 382 = true := by
  have hs : count381 q = (countLit q [168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180]) + (countLit q [181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) := List.countP_append (p := literal q) (l₁ := [168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180]) (l₂ := [181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194])
  have hm := merge_left (literal (valuationOf q) (354)) (literal (valuationOf q) (382)) (countLit q [168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180]) (countLit q [181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) (count381 q) 2 (meaning354 q) (meaning382 q) hs
  change valuationOf q 354 = false ∨ valuationOf q 382 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause644 (q : Snake 81) (h : Conditions q) : valuation q 354 = false ∨ valuation q 382 = true := counterClause644 (baseVal q)

theorem counterClause645 (q : Nat → Bool) : valuationOf q 196 = false ∨ valuationOf q 383 = true := by
  have hs : count383 q = (countLit q [196]) + (countLit q [197]) := List.countP_append (p := literal q) (l₁ := [196]) (l₂ := [197])
  have hm := merge_left (literal (valuationOf q) (196)) (literal (valuationOf q) (383)) (countLit q [196]) (countLit q [197]) (count383 q) 1 (meaning196 q) (meaning383 q) hs
  change valuationOf q 196 = false ∨ valuationOf q 383 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause645 (q : Snake 81) (h : Conditions q) : valuation q 196 = false ∨ valuation q 383 = true := counterClause645 (baseVal q)

theorem counterClause646 (q : Nat → Bool) : valuationOf q 383 = false ∨ valuationOf q 385 = true := by
  have hs : count385 q = (countLit q [195]) + (countLit q [196, 197]) := List.countP_append (p := literal q) (l₁ := [195]) (l₂ := [196, 197])
  have hm := merge_right (literal (valuationOf q) (383)) (literal (valuationOf q) (385)) (countLit q [195]) (countLit q [196, 197]) (count385 q) 1 (meaning383 q) (meaning385 q) hs
  change valuationOf q 383 = false ∨ valuationOf q 385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause646 (q : Snake 81) (h : Conditions q) : valuation q 383 = false ∨ valuation q 385 = true := counterClause646 (baseVal q)

theorem counterClause647 (q : Nat → Bool) : valuationOf q 199 = false ∨ valuationOf q 387 = true := by
  have hs : count387 q = (countLit q [198]) + (countLit q [199]) := List.countP_append (p := literal q) (l₁ := [198]) (l₂ := [199])
  have hm := merge_right (literal (valuationOf q) (199)) (literal (valuationOf q) (387)) (countLit q [198]) (countLit q [199]) (count387 q) 1 (meaning199 q) (meaning387 q) hs
  change valuationOf q 199 = false ∨ valuationOf q 387 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause647 (q : Snake 81) (h : Conditions q) : valuation q 199 = false ∨ valuation q 387 = true := counterClause647 (baseVal q)

theorem counterClause648 (q : Nat → Bool) : valuationOf q 198 = false ∨ valuationOf q 387 = true := by
  have hs : count387 q = (countLit q [198]) + (countLit q [199]) := List.countP_append (p := literal q) (l₁ := [198]) (l₂ := [199])
  have hm := merge_left (literal (valuationOf q) (198)) (literal (valuationOf q) (387)) (countLit q [198]) (countLit q [199]) (count387 q) 1 (meaning198 q) (meaning387 q) hs
  change valuationOf q 198 = false ∨ valuationOf q 387 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause648 (q : Snake 81) (h : Conditions q) : valuation q 198 = false ∨ valuation q 387 = true := counterClause648 (baseVal q)

theorem counterClause649 (q : Nat → Bool) : valuationOf q 198 = false ∨ valuationOf q 199 = false ∨ valuationOf q 388 = true := by
  have hs : count387 q = (countLit q [198]) + (countLit q [199]) := List.countP_append (p := literal q) (l₁ := [198]) (l₂ := [199])
  have hm := merge_two (literal (valuationOf q) (198)) (literal (valuationOf q) (199)) (literal (valuationOf q) (388)) (countLit q [198]) (countLit q [199]) (count387 q) 1 1 (meaning198 q) (meaning199 q) (meaning388 q) hs
  change valuationOf q 198 = false ∨ valuationOf q 199 = false ∨ valuationOf q 388 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause649 (q : Snake 81) (h : Conditions q) : valuation q 198 = false ∨ valuation q 199 = false ∨ valuation q 388 = true := counterClause649 (baseVal q)

theorem counterClause650 (q : Nat → Bool) : valuationOf q 201 = false ∨ valuationOf q 389 = true := by
  have hs : count389 q = (countLit q [200]) + (countLit q [201]) := List.countP_append (p := literal q) (l₁ := [200]) (l₂ := [201])
  have hm := merge_right (literal (valuationOf q) (201)) (literal (valuationOf q) (389)) (countLit q [200]) (countLit q [201]) (count389 q) 1 (meaning201 q) (meaning389 q) hs
  change valuationOf q 201 = false ∨ valuationOf q 389 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause650 (q : Snake 81) (h : Conditions q) : valuation q 201 = false ∨ valuation q 389 = true := counterClause650 (baseVal q)

theorem counterClause651 (q : Nat → Bool) : valuationOf q 389 = false ∨ valuationOf q 391 = true := by
  have hs : count391 q = (countLit q [198, 199]) + (countLit q [200, 201]) := List.countP_append (p := literal q) (l₁ := [198, 199]) (l₂ := [200, 201])
  have hm := merge_right (literal (valuationOf q) (389)) (literal (valuationOf q) (391)) (countLit q [198, 199]) (countLit q [200, 201]) (count391 q) 1 (meaning389 q) (meaning391 q) hs
  change valuationOf q 389 = false ∨ valuationOf q 391 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause651 (q : Snake 81) (h : Conditions q) : valuation q 389 = false ∨ valuation q 391 = true := counterClause651 (baseVal q)

theorem counterClause652 (q : Nat → Bool) : valuationOf q 387 = false ∨ valuationOf q 391 = true := by
  have hs : count391 q = (countLit q [198, 199]) + (countLit q [200, 201]) := List.countP_append (p := literal q) (l₁ := [198, 199]) (l₂ := [200, 201])
  have hm := merge_left (literal (valuationOf q) (387)) (literal (valuationOf q) (391)) (countLit q [198, 199]) (countLit q [200, 201]) (count391 q) 1 (meaning387 q) (meaning391 q) hs
  change valuationOf q 387 = false ∨ valuationOf q 391 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause652 (q : Snake 81) (h : Conditions q) : valuation q 387 = false ∨ valuation q 391 = true := counterClause652 (baseVal q)

theorem counterClause653 (q : Nat → Bool) : valuationOf q 387 = false ∨ valuationOf q 389 = false ∨ valuationOf q 392 = true := by
  have hs : count391 q = (countLit q [198, 199]) + (countLit q [200, 201]) := List.countP_append (p := literal q) (l₁ := [198, 199]) (l₂ := [200, 201])
  have hm := merge_two (literal (valuationOf q) (387)) (literal (valuationOf q) (389)) (literal (valuationOf q) (392)) (countLit q [198, 199]) (countLit q [200, 201]) (count391 q) 1 1 (meaning387 q) (meaning389 q) (meaning392 q) hs
  change valuationOf q 387 = false ∨ valuationOf q 389 = false ∨ valuationOf q 392 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause653 (q : Snake 81) (h : Conditions q) : valuation q 387 = false ∨ valuation q 389 = false ∨ valuation q 392 = true := counterClause653 (baseVal q)

theorem counterClause654 (q : Nat → Bool) : valuationOf q 388 = false ∨ valuationOf q 392 = true := by
  have hs : count391 q = (countLit q [198, 199]) + (countLit q [200, 201]) := List.countP_append (p := literal q) (l₁ := [198, 199]) (l₂ := [200, 201])
  have hm := merge_left (literal (valuationOf q) (388)) (literal (valuationOf q) (392)) (countLit q [198, 199]) (countLit q [200, 201]) (count391 q) 2 (meaning388 q) (meaning392 q) hs
  change valuationOf q 388 = false ∨ valuationOf q 392 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause654 (q : Snake 81) (h : Conditions q) : valuation q 388 = false ∨ valuation q 392 = true := counterClause654 (baseVal q)

theorem counterClause655 (q : Nat → Bool) : valuationOf q 391 = false ∨ valuationOf q 393 = true := by
  have hs : count393 q = (countLit q [195, 196, 197]) + (countLit q [198, 199, 200, 201]) := List.countP_append (p := literal q) (l₁ := [195, 196, 197]) (l₂ := [198, 199, 200, 201])
  have hm := merge_right (literal (valuationOf q) (391)) (literal (valuationOf q) (393)) (countLit q [195, 196, 197]) (countLit q [198, 199, 200, 201]) (count393 q) 1 (meaning391 q) (meaning393 q) hs
  change valuationOf q 391 = false ∨ valuationOf q 393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause655 (q : Snake 81) (h : Conditions q) : valuation q 391 = false ∨ valuation q 393 = true := counterClause655 (baseVal q)

theorem counterClause656 (q : Nat → Bool) : valuationOf q 392 = false ∨ valuationOf q 394 = true := by
  have hs : count393 q = (countLit q [195, 196, 197]) + (countLit q [198, 199, 200, 201]) := List.countP_append (p := literal q) (l₁ := [195, 196, 197]) (l₂ := [198, 199, 200, 201])
  have hm := merge_right (literal (valuationOf q) (392)) (literal (valuationOf q) (394)) (countLit q [195, 196, 197]) (countLit q [198, 199, 200, 201]) (count393 q) 2 (meaning392 q) (meaning394 q) hs
  change valuationOf q 392 = false ∨ valuationOf q 394 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause656 (q : Snake 81) (h : Conditions q) : valuation q 392 = false ∨ valuation q 394 = true := counterClause656 (baseVal q)

theorem counterClause657 (q : Nat → Bool) : valuationOf q 385 = false ∨ valuationOf q 393 = true := by
  have hs : count393 q = (countLit q [195, 196, 197]) + (countLit q [198, 199, 200, 201]) := List.countP_append (p := literal q) (l₁ := [195, 196, 197]) (l₂ := [198, 199, 200, 201])
  have hm := merge_left (literal (valuationOf q) (385)) (literal (valuationOf q) (393)) (countLit q [195, 196, 197]) (countLit q [198, 199, 200, 201]) (count393 q) 1 (meaning385 q) (meaning393 q) hs
  change valuationOf q 385 = false ∨ valuationOf q 393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause657 (q : Snake 81) (h : Conditions q) : valuation q 385 = false ∨ valuation q 393 = true := counterClause657 (baseVal q)

theorem counterClause658 (q : Nat → Bool) : valuationOf q 204 = false ∨ valuationOf q 395 = true := by
  have hs : count395 q = (countLit q [203]) + (countLit q [204]) := List.countP_append (p := literal q) (l₁ := [203]) (l₂ := [204])
  have hm := merge_right (literal (valuationOf q) (204)) (literal (valuationOf q) (395)) (countLit q [203]) (countLit q [204]) (count395 q) 1 (meaning204 q) (meaning395 q) hs
  change valuationOf q 204 = false ∨ valuationOf q 395 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause658 (q : Snake 81) (h : Conditions q) : valuation q 204 = false ∨ valuation q 395 = true := counterClause658 (baseVal q)

theorem counterClause659 (q : Nat → Bool) : valuationOf q 395 = false ∨ valuationOf q 397 = true := by
  have hs : count397 q = (countLit q [202]) + (countLit q [203, 204]) := List.countP_append (p := literal q) (l₁ := [202]) (l₂ := [203, 204])
  have hm := merge_right (literal (valuationOf q) (395)) (literal (valuationOf q) (397)) (countLit q [202]) (countLit q [203, 204]) (count397 q) 1 (meaning395 q) (meaning397 q) hs
  change valuationOf q 395 = false ∨ valuationOf q 397 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause659 (q : Snake 81) (h : Conditions q) : valuation q 395 = false ∨ valuation q 397 = true := counterClause659 (baseVal q)

theorem counterClause660 (q : Nat → Bool) : valuationOf q 206 = false ∨ valuationOf q 399 = true := by
  have hs : count399 q = (countLit q [205]) + (countLit q [206]) := List.countP_append (p := literal q) (l₁ := [205]) (l₂ := [206])
  have hm := merge_right (literal (valuationOf q) (206)) (literal (valuationOf q) (399)) (countLit q [205]) (countLit q [206]) (count399 q) 1 (meaning206 q) (meaning399 q) hs
  change valuationOf q 206 = false ∨ valuationOf q 399 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause660 (q : Snake 81) (h : Conditions q) : valuation q 206 = false ∨ valuation q 399 = true := counterClause660 (baseVal q)

theorem counterClause661 (q : Nat → Bool) : valuationOf q 208 = false ∨ valuationOf q 401 = true := by
  have hs : count401 q = (countLit q [207]) + (countLit q [208]) := List.countP_append (p := literal q) (l₁ := [207]) (l₂ := [208])
  have hm := merge_right (literal (valuationOf q) (208)) (literal (valuationOf q) (401)) (countLit q [207]) (countLit q [208]) (count401 q) 1 (meaning208 q) (meaning401 q) hs
  change valuationOf q 208 = false ∨ valuationOf q 401 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause661 (q : Snake 81) (h : Conditions q) : valuation q 208 = false ∨ valuation q 401 = true := counterClause661 (baseVal q)

theorem counterClause662 (q : Nat → Bool) : valuationOf q 401 = false ∨ valuationOf q 403 = true := by
  have hs : count403 q = (countLit q [205, 206]) + (countLit q [207, 208]) := List.countP_append (p := literal q) (l₁ := [205, 206]) (l₂ := [207, 208])
  have hm := merge_right (literal (valuationOf q) (401)) (literal (valuationOf q) (403)) (countLit q [205, 206]) (countLit q [207, 208]) (count403 q) 1 (meaning401 q) (meaning403 q) hs
  change valuationOf q 401 = false ∨ valuationOf q 403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause662 (q : Snake 81) (h : Conditions q) : valuation q 401 = false ∨ valuation q 403 = true := counterClause662 (baseVal q)

theorem counterClause663 (q : Nat → Bool) : valuationOf q 399 = false ∨ valuationOf q 403 = true := by
  have hs : count403 q = (countLit q [205, 206]) + (countLit q [207, 208]) := List.countP_append (p := literal q) (l₁ := [205, 206]) (l₂ := [207, 208])
  have hm := merge_left (literal (valuationOf q) (399)) (literal (valuationOf q) (403)) (countLit q [205, 206]) (countLit q [207, 208]) (count403 q) 1 (meaning399 q) (meaning403 q) hs
  change valuationOf q 399 = false ∨ valuationOf q 403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause663 (q : Snake 81) (h : Conditions q) : valuation q 399 = false ∨ valuation q 403 = true := counterClause663 (baseVal q)

theorem counterClause664 (q : Nat → Bool) : valuationOf q 403 = false ∨ valuationOf q 405 = true := by
  have hs : count405 q = (countLit q [202, 203, 204]) + (countLit q [205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [202, 203, 204]) (l₂ := [205, 206, 207, 208])
  have hm := merge_right (literal (valuationOf q) (403)) (literal (valuationOf q) (405)) (countLit q [202, 203, 204]) (countLit q [205, 206, 207, 208]) (count405 q) 1 (meaning403 q) (meaning405 q) hs
  change valuationOf q 403 = false ∨ valuationOf q 405 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause664 (q : Snake 81) (h : Conditions q) : valuation q 403 = false ∨ valuation q 405 = true := counterClause664 (baseVal q)

theorem counterClause665 (q : Nat → Bool) : valuationOf q 397 = false ∨ valuationOf q 405 = true := by
  have hs : count405 q = (countLit q [202, 203, 204]) + (countLit q [205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [202, 203, 204]) (l₂ := [205, 206, 207, 208])
  have hm := merge_left (literal (valuationOf q) (397)) (literal (valuationOf q) (405)) (countLit q [202, 203, 204]) (countLit q [205, 206, 207, 208]) (count405 q) 1 (meaning397 q) (meaning405 q) hs
  change valuationOf q 397 = false ∨ valuationOf q 405 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause665 (q : Snake 81) (h : Conditions q) : valuation q 397 = false ∨ valuation q 405 = true := counterClause665 (baseVal q)

theorem counterClause666 (q : Nat → Bool) : valuationOf q 405 = false ∨ valuationOf q 407 = true := by
  have hs : count407 q = (countLit q [195, 196, 197, 198, 199, 200, 201]) + (countLit q [202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [195, 196, 197, 198, 199, 200, 201]) (l₂ := [202, 203, 204, 205, 206, 207, 208])
  have hm := merge_right (literal (valuationOf q) (405)) (literal (valuationOf q) (407)) (countLit q [195, 196, 197, 198, 199, 200, 201]) (countLit q [202, 203, 204, 205, 206, 207, 208]) (count407 q) 1 (meaning405 q) (meaning407 q) hs
  change valuationOf q 405 = false ∨ valuationOf q 407 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause666 (q : Snake 81) (h : Conditions q) : valuation q 405 = false ∨ valuation q 407 = true := counterClause666 (baseVal q)

theorem counterClause667 (q : Nat → Bool) : valuationOf q 393 = false ∨ valuationOf q 407 = true := by
  have hs : count407 q = (countLit q [195, 196, 197, 198, 199, 200, 201]) + (countLit q [202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [195, 196, 197, 198, 199, 200, 201]) (l₂ := [202, 203, 204, 205, 206, 207, 208])
  have hm := merge_left (literal (valuationOf q) (393)) (literal (valuationOf q) (407)) (countLit q [195, 196, 197, 198, 199, 200, 201]) (countLit q [202, 203, 204, 205, 206, 207, 208]) (count407 q) 1 (meaning393 q) (meaning407 q) hs
  change valuationOf q 393 = false ∨ valuationOf q 407 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause667 (q : Snake 81) (h : Conditions q) : valuation q 393 = false ∨ valuation q 407 = true := counterClause667 (baseVal q)

theorem counterClause668 (q : Nat → Bool) : valuationOf q 393 = false ∨ valuationOf q 405 = false ∨ valuationOf q 408 = true := by
  have hs : count407 q = (countLit q [195, 196, 197, 198, 199, 200, 201]) + (countLit q [202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [195, 196, 197, 198, 199, 200, 201]) (l₂ := [202, 203, 204, 205, 206, 207, 208])
  have hm := merge_two (literal (valuationOf q) (393)) (literal (valuationOf q) (405)) (literal (valuationOf q) (408)) (countLit q [195, 196, 197, 198, 199, 200, 201]) (countLit q [202, 203, 204, 205, 206, 207, 208]) (count407 q) 1 1 (meaning393 q) (meaning405 q) (meaning408 q) hs
  change valuationOf q 393 = false ∨ valuationOf q 405 = false ∨ valuationOf q 408 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause668 (q : Snake 81) (h : Conditions q) : valuation q 393 = false ∨ valuation q 405 = false ∨ valuation q 408 = true := counterClause668 (baseVal q)

theorem counterClause669 (q : Nat → Bool) : valuationOf q 394 = false ∨ valuationOf q 408 = true := by
  have hs : count407 q = (countLit q [195, 196, 197, 198, 199, 200, 201]) + (countLit q [202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [195, 196, 197, 198, 199, 200, 201]) (l₂ := [202, 203, 204, 205, 206, 207, 208])
  have hm := merge_left (literal (valuationOf q) (394)) (literal (valuationOf q) (408)) (countLit q [195, 196, 197, 198, 199, 200, 201]) (countLit q [202, 203, 204, 205, 206, 207, 208]) (count407 q) 2 (meaning394 q) (meaning408 q) hs
  change valuationOf q 394 = false ∨ valuationOf q 408 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause669 (q : Snake 81) (h : Conditions q) : valuation q 394 = false ∨ valuation q 408 = true := counterClause669 (baseVal q)

theorem counterClause670 (q : Nat → Bool) : valuationOf q 209 = false ∨ valuationOf q 411 = true := by
  have hs : count411 q = (countLit q [209]) + (countLit q [210, 211]) := List.countP_append (p := literal q) (l₁ := [209]) (l₂ := [210, 211])
  have hm := merge_left (literal (valuationOf q) (209)) (literal (valuationOf q) (411)) (countLit q [209]) (countLit q [210, 211]) (count411 q) 1 (meaning209 q) (meaning411 q) hs
  change valuationOf q 209 = false ∨ valuationOf q 411 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause670 (q : Snake 81) (h : Conditions q) : valuation q 209 = false ∨ valuation q 411 = true := counterClause670 (baseVal q)

theorem counterClause671 (q : Nat → Bool) : valuationOf q 212 = false ∨ valuationOf q 413 = true := by
  have hs : count413 q = (countLit q [212]) + (countLit q [213]) := List.countP_append (p := literal q) (l₁ := [212]) (l₂ := [213])
  have hm := merge_left (literal (valuationOf q) (212)) (literal (valuationOf q) (413)) (countLit q [212]) (countLit q [213]) (count413 q) 1 (meaning212 q) (meaning413 q) hs
  change valuationOf q 212 = false ∨ valuationOf q 413 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause671 (q : Snake 81) (h : Conditions q) : valuation q 212 = false ∨ valuation q 413 = true := counterClause671 (baseVal q)

theorem counterClause672 (q : Nat → Bool) : valuationOf q 215 = false ∨ valuationOf q 415 = true := by
  have hs : count415 q = (countLit q [214]) + (countLit q [215]) := List.countP_append (p := literal q) (l₁ := [214]) (l₂ := [215])
  have hm := merge_right (literal (valuationOf q) (215)) (literal (valuationOf q) (415)) (countLit q [214]) (countLit q [215]) (count415 q) 1 (meaning215 q) (meaning415 q) hs
  change valuationOf q 215 = false ∨ valuationOf q 415 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause672 (q : Snake 81) (h : Conditions q) : valuation q 215 = false ∨ valuation q 415 = true := counterClause672 (baseVal q)

theorem block20 (q : Snake 81) (h : Conditions q) : B112E161.Block20 (valuation q) :=
  ⟨clause641 q h, clause642 q h, clause643 q h, clause644 q h, clause645 q h, clause646 q h, clause647 q h, clause648 q h, clause649 q h, clause650 q h, clause651 q h, clause652 q h, clause653 q h, clause654 q h, clause655 q h, clause656 q h, clause657 q h, clause658 q h, clause659 q h, clause660 q h, clause661 q h, clause662 q h, clause663 q h, clause664 q h, clause665 q h, clause666 q h, clause667 q h, clause668 q h, clause669 q h, clause670 q h, clause671 q h, clause672 q h⟩

end
end Snake9.Regrowth.E112161
