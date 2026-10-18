import E112203Semantics
import B112E203Inputs
namespace Snake9.Regrowth.E112203
noncomputable section
local instance blockDec21 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause673 (q : Nat → Bool) : valuationOf q 191 = false ∨ valuationOf q 375 = true := by
  have hs : count375 q = (countLit q [191]) + (countLit q [192]) := List.countP_append (p := literal q) (l₁ := [191]) (l₂ := [192])
  have hm := merge_left (literal (valuationOf q) (191)) (literal (valuationOf q) (375)) (countLit q [191]) (countLit q [192]) (count375 q) 1 (meaning191 q) (meaning375 q) hs
  change valuationOf q 191 = false ∨ valuationOf q 375 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause673 (q : Snake 81) (h : Conditions q) : valuation q 191 = false ∨ valuation q 375 = true := counterClause673 (baseVal q)

theorem counterClause674 (q : Nat → Bool) : valuationOf q 191 = false ∨ valuationOf q 192 = false ∨ valuationOf q 376 = true := by
  have hs : count375 q = (countLit q [191]) + (countLit q [192]) := List.countP_append (p := literal q) (l₁ := [191]) (l₂ := [192])
  have hm := merge_two (literal (valuationOf q) (191)) (literal (valuationOf q) (192)) (literal (valuationOf q) (376)) (countLit q [191]) (countLit q [192]) (count375 q) 1 1 (meaning191 q) (meaning192 q) (meaning376 q) hs
  change valuationOf q 191 = false ∨ valuationOf q 192 = false ∨ valuationOf q 376 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause674 (q : Snake 81) (h : Conditions q) : valuation q 191 = false ∨ valuation q 192 = false ∨ valuation q 376 = true := counterClause674 (baseVal q)

theorem counterClause675 (q : Nat → Bool) : valuationOf q 375 = false ∨ valuationOf q 377 = true := by
  have hs : count377 q = (countLit q [190]) + (countLit q [191, 192]) := List.countP_append (p := literal q) (l₁ := [190]) (l₂ := [191, 192])
  have hm := merge_right (literal (valuationOf q) (375)) (literal (valuationOf q) (377)) (countLit q [190]) (countLit q [191, 192]) (count377 q) 1 (meaning375 q) (meaning377 q) hs
  change valuationOf q 375 = false ∨ valuationOf q 377 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause675 (q : Snake 81) (h : Conditions q) : valuation q 375 = false ∨ valuation q 377 = true := counterClause675 (baseVal q)

theorem counterClause676 (q : Nat → Bool) : valuationOf q 376 = false ∨ valuationOf q 378 = true := by
  have hs : count377 q = (countLit q [190]) + (countLit q [191, 192]) := List.countP_append (p := literal q) (l₁ := [190]) (l₂ := [191, 192])
  have hm := merge_right (literal (valuationOf q) (376)) (literal (valuationOf q) (378)) (countLit q [190]) (countLit q [191, 192]) (count377 q) 2 (meaning376 q) (meaning378 q) hs
  change valuationOf q 376 = false ∨ valuationOf q 378 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause676 (q : Snake 81) (h : Conditions q) : valuation q 376 = false ∨ valuation q 378 = true := counterClause676 (baseVal q)

theorem counterClause677 (q : Nat → Bool) : valuationOf q 196 = false ∨ valuationOf q 381 = true := by
  have hs : count381 q = (countLit q [195]) + (countLit q [196]) := List.countP_append (p := literal q) (l₁ := [195]) (l₂ := [196])
  have hm := merge_right (literal (valuationOf q) (196)) (literal (valuationOf q) (381)) (countLit q [195]) (countLit q [196]) (count381 q) 1 (meaning196 q) (meaning381 q) hs
  change valuationOf q 196 = false ∨ valuationOf q 381 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause677 (q : Snake 81) (h : Conditions q) : valuation q 196 = false ∨ valuation q 381 = true := counterClause677 (baseVal q)

theorem counterClause678 (q : Nat → Bool) : valuationOf q 381 = false ∨ valuationOf q 383 = true := by
  have hs : count383 q = (countLit q [193, 194]) + (countLit q [195, 196]) := List.countP_append (p := literal q) (l₁ := [193, 194]) (l₂ := [195, 196])
  have hm := merge_right (literal (valuationOf q) (381)) (literal (valuationOf q) (383)) (countLit q [193, 194]) (countLit q [195, 196]) (count383 q) 1 (meaning381 q) (meaning383 q) hs
  change valuationOf q 381 = false ∨ valuationOf q 383 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause678 (q : Snake 81) (h : Conditions q) : valuation q 381 = false ∨ valuation q 383 = true := counterClause678 (baseVal q)

theorem counterClause679 (q : Nat → Bool) : valuationOf q 383 = false ∨ valuationOf q 385 = true := by
  have hs : count385 q = (countLit q [190, 191, 192]) + (countLit q [193, 194, 195, 196]) := List.countP_append (p := literal q) (l₁ := [190, 191, 192]) (l₂ := [193, 194, 195, 196])
  have hm := merge_right (literal (valuationOf q) (383)) (literal (valuationOf q) (385)) (countLit q [190, 191, 192]) (countLit q [193, 194, 195, 196]) (count385 q) 1 (meaning383 q) (meaning385 q) hs
  change valuationOf q 383 = false ∨ valuationOf q 385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause679 (q : Snake 81) (h : Conditions q) : valuation q 383 = false ∨ valuation q 385 = true := counterClause679 (baseVal q)

theorem counterClause680 (q : Nat → Bool) : valuationOf q 377 = false ∨ valuationOf q 385 = true := by
  have hs : count385 q = (countLit q [190, 191, 192]) + (countLit q [193, 194, 195, 196]) := List.countP_append (p := literal q) (l₁ := [190, 191, 192]) (l₂ := [193, 194, 195, 196])
  have hm := merge_left (literal (valuationOf q) (377)) (literal (valuationOf q) (385)) (countLit q [190, 191, 192]) (countLit q [193, 194, 195, 196]) (count385 q) 1 (meaning377 q) (meaning385 q) hs
  change valuationOf q 377 = false ∨ valuationOf q 385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause680 (q : Snake 81) (h : Conditions q) : valuation q 377 = false ∨ valuation q 385 = true := counterClause680 (baseVal q)

theorem counterClause681 (q : Nat → Bool) : valuationOf q 378 = false ∨ valuationOf q 386 = true := by
  have hs : count385 q = (countLit q [190, 191, 192]) + (countLit q [193, 194, 195, 196]) := List.countP_append (p := literal q) (l₁ := [190, 191, 192]) (l₂ := [193, 194, 195, 196])
  have hm := merge_left (literal (valuationOf q) (378)) (literal (valuationOf q) (386)) (countLit q [190, 191, 192]) (countLit q [193, 194, 195, 196]) (count385 q) 2 (meaning378 q) (meaning386 q) hs
  change valuationOf q 378 = false ∨ valuationOf q 386 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause681 (q : Snake 81) (h : Conditions q) : valuation q 378 = false ∨ valuation q 386 = true := counterClause681 (baseVal q)

theorem counterClause682 (q : Nat → Bool) : valuationOf q 200 = false ∨ valuationOf q 389 = true := by
  have hs : count389 q = (countLit q [199]) + (countLit q [200]) := List.countP_append (p := literal q) (l₁ := [199]) (l₂ := [200])
  have hm := merge_right (literal (valuationOf q) (200)) (literal (valuationOf q) (389)) (countLit q [199]) (countLit q [200]) (count389 q) 1 (meaning200 q) (meaning389 q) hs
  change valuationOf q 200 = false ∨ valuationOf q 389 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause682 (q : Snake 81) (h : Conditions q) : valuation q 200 = false ∨ valuation q 389 = true := counterClause682 (baseVal q)

theorem counterClause683 (q : Nat → Bool) : valuationOf q 199 = false ∨ valuationOf q 389 = true := by
  have hs : count389 q = (countLit q [199]) + (countLit q [200]) := List.countP_append (p := literal q) (l₁ := [199]) (l₂ := [200])
  have hm := merge_left (literal (valuationOf q) (199)) (literal (valuationOf q) (389)) (countLit q [199]) (countLit q [200]) (count389 q) 1 (meaning199 q) (meaning389 q) hs
  change valuationOf q 199 = false ∨ valuationOf q 389 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause683 (q : Snake 81) (h : Conditions q) : valuation q 199 = false ∨ valuation q 389 = true := counterClause683 (baseVal q)

theorem counterClause684 (q : Nat → Bool) : valuationOf q 389 = false ∨ valuationOf q 391 = true := by
  have hs : count391 q = (countLit q [197, 198]) + (countLit q [199, 200]) := List.countP_append (p := literal q) (l₁ := [197, 198]) (l₂ := [199, 200])
  have hm := merge_right (literal (valuationOf q) (389)) (literal (valuationOf q) (391)) (countLit q [197, 198]) (countLit q [199, 200]) (count391 q) 1 (meaning389 q) (meaning391 q) hs
  change valuationOf q 389 = false ∨ valuationOf q 391 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause684 (q : Snake 81) (h : Conditions q) : valuation q 389 = false ∨ valuation q 391 = true := counterClause684 (baseVal q)

theorem counterClause685 (q : Nat → Bool) : valuationOf q 391 = false ∨ valuationOf q 399 = true := by
  have hs : count399 q = (countLit q [197, 198, 199, 200]) + (countLit q [201, 202, 203, 204]) := List.countP_append (p := literal q) (l₁ := [197, 198, 199, 200]) (l₂ := [201, 202, 203, 204])
  have hm := merge_left (literal (valuationOf q) (391)) (literal (valuationOf q) (399)) (countLit q [197, 198, 199, 200]) (countLit q [201, 202, 203, 204]) (count399 q) 1 (meaning391 q) (meaning399 q) hs
  change valuationOf q 391 = false ∨ valuationOf q 399 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause685 (q : Snake 81) (h : Conditions q) : valuation q 391 = false ∨ valuation q 399 = true := counterClause685 (baseVal q)

theorem counterClause686 (q : Nat → Bool) : valuationOf q 399 = false ∨ valuationOf q 401 = true := by
  have hs : count401 q = (countLit q [190, 191, 192, 193, 194, 195, 196]) + (countLit q [197, 198, 199, 200, 201, 202, 203, 204]) := List.countP_append (p := literal q) (l₁ := [190, 191, 192, 193, 194, 195, 196]) (l₂ := [197, 198, 199, 200, 201, 202, 203, 204])
  have hm := merge_right (literal (valuationOf q) (399)) (literal (valuationOf q) (401)) (countLit q [190, 191, 192, 193, 194, 195, 196]) (countLit q [197, 198, 199, 200, 201, 202, 203, 204]) (count401 q) 1 (meaning399 q) (meaning401 q) hs
  change valuationOf q 399 = false ∨ valuationOf q 401 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause686 (q : Snake 81) (h : Conditions q) : valuation q 399 = false ∨ valuation q 401 = true := counterClause686 (baseVal q)

theorem counterClause687 (q : Nat → Bool) : valuationOf q 385 = false ∨ valuationOf q 401 = true := by
  have hs : count401 q = (countLit q [190, 191, 192, 193, 194, 195, 196]) + (countLit q [197, 198, 199, 200, 201, 202, 203, 204]) := List.countP_append (p := literal q) (l₁ := [190, 191, 192, 193, 194, 195, 196]) (l₂ := [197, 198, 199, 200, 201, 202, 203, 204])
  have hm := merge_left (literal (valuationOf q) (385)) (literal (valuationOf q) (401)) (countLit q [190, 191, 192, 193, 194, 195, 196]) (countLit q [197, 198, 199, 200, 201, 202, 203, 204]) (count401 q) 1 (meaning385 q) (meaning401 q) hs
  change valuationOf q 385 = false ∨ valuationOf q 401 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause687 (q : Snake 81) (h : Conditions q) : valuation q 385 = false ∨ valuation q 401 = true := counterClause687 (baseVal q)

theorem counterClause688 (q : Nat → Bool) : valuationOf q 386 = false ∨ valuationOf q 402 = true := by
  have hs : count401 q = (countLit q [190, 191, 192, 193, 194, 195, 196]) + (countLit q [197, 198, 199, 200, 201, 202, 203, 204]) := List.countP_append (p := literal q) (l₁ := [190, 191, 192, 193, 194, 195, 196]) (l₂ := [197, 198, 199, 200, 201, 202, 203, 204])
  have hm := merge_left (literal (valuationOf q) (386)) (literal (valuationOf q) (402)) (countLit q [190, 191, 192, 193, 194, 195, 196]) (countLit q [197, 198, 199, 200, 201, 202, 203, 204]) (count401 q) 2 (meaning386 q) (meaning402 q) hs
  change valuationOf q 386 = false ∨ valuationOf q 402 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause688 (q : Snake 81) (h : Conditions q) : valuation q 386 = false ∨ valuation q 402 = true := counterClause688 (baseVal q)

theorem counterClause689 (q : Nat → Bool) : valuationOf q 401 = false ∨ valuationOf q 403 = true := by
  have hs : count403 q = (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189]) + (countLit q [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]) := List.countP_append (p := literal q) (l₁ := [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189]) (l₂ := [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204])
  have hm := merge_right (literal (valuationOf q) (401)) (literal (valuationOf q) (403)) (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189]) (countLit q [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]) (count403 q) 1 (meaning401 q) (meaning403 q) hs
  change valuationOf q 401 = false ∨ valuationOf q 403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause689 (q : Snake 81) (h : Conditions q) : valuation q 401 = false ∨ valuation q 403 = true := counterClause689 (baseVal q)

theorem counterClause690 (q : Nat → Bool) : valuationOf q 402 = false ∨ valuationOf q 404 = true := by
  have hs : count403 q = (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189]) + (countLit q [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]) := List.countP_append (p := literal q) (l₁ := [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189]) (l₂ := [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204])
  have hm := merge_right (literal (valuationOf q) (402)) (literal (valuationOf q) (404)) (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189]) (countLit q [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]) (count403 q) 2 (meaning402 q) (meaning404 q) hs
  change valuationOf q 402 = false ∨ valuationOf q 404 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause690 (q : Snake 81) (h : Conditions q) : valuation q 402 = false ∨ valuation q 404 = true := counterClause690 (baseVal q)

theorem counterClause691 (q : Nat → Bool) : valuationOf q 373 = false ∨ valuationOf q 403 = true := by
  have hs : count403 q = (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189]) + (countLit q [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]) := List.countP_append (p := literal q) (l₁ := [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189]) (l₂ := [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204])
  have hm := merge_left (literal (valuationOf q) (373)) (literal (valuationOf q) (403)) (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189]) (countLit q [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]) (count403 q) 1 (meaning373 q) (meaning403 q) hs
  change valuationOf q 373 = false ∨ valuationOf q 403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause691 (q : Snake 81) (h : Conditions q) : valuation q 373 = false ∨ valuation q 403 = true := counterClause691 (baseVal q)

theorem counterClause692 (q : Nat → Bool) : valuationOf q 373 = false ∨ valuationOf q 401 = false ∨ valuationOf q 404 = true := by
  have hs : count403 q = (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189]) + (countLit q [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]) := List.countP_append (p := literal q) (l₁ := [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189]) (l₂ := [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204])
  have hm := merge_two (literal (valuationOf q) (373)) (literal (valuationOf q) (401)) (literal (valuationOf q) (404)) (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189]) (countLit q [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]) (count403 q) 1 1 (meaning373 q) (meaning401 q) (meaning404 q) hs
  change valuationOf q 373 = false ∨ valuationOf q 401 = false ∨ valuationOf q 404 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause692 (q : Snake 81) (h : Conditions q) : valuation q 373 = false ∨ valuation q 401 = false ∨ valuation q 404 = true := counterClause692 (baseVal q)

theorem counterClause693 (q : Nat → Bool) : valuationOf q 374 = false ∨ valuationOf q 404 = true := by
  have hs : count403 q = (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189]) + (countLit q [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]) := List.countP_append (p := literal q) (l₁ := [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189]) (l₂ := [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204])
  have hm := merge_left (literal (valuationOf q) (374)) (literal (valuationOf q) (404)) (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189]) (countLit q [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]) (count403 q) 2 (meaning374 q) (meaning404 q) hs
  change valuationOf q 374 = false ∨ valuationOf q 404 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause693 (q : Snake 81) (h : Conditions q) : valuation q 374 = false ∨ valuation q 404 = true := counterClause693 (baseVal q)

theorem counterClause694 (q : Nat → Bool) : valuationOf q 206 = false ∨ valuationOf q 405 = true := by
  have hs : count405 q = (countLit q [206]) + (countLit q [207]) := List.countP_append (p := literal q) (l₁ := [206]) (l₂ := [207])
  have hm := merge_left (literal (valuationOf q) (206)) (literal (valuationOf q) (405)) (countLit q [206]) (countLit q [207]) (count405 q) 1 (meaning206 q) (meaning405 q) hs
  change valuationOf q 206 = false ∨ valuationOf q 405 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause694 (q : Snake 81) (h : Conditions q) : valuation q 206 = false ∨ valuation q 405 = true := counterClause694 (baseVal q)

theorem counterClause695 (q : Nat → Bool) : valuationOf q 405 = false ∨ valuationOf q 407 = true := by
  have hs : count407 q = (countLit q [205]) + (countLit q [206, 207]) := List.countP_append (p := literal q) (l₁ := [205]) (l₂ := [206, 207])
  have hm := merge_right (literal (valuationOf q) (405)) (literal (valuationOf q) (407)) (countLit q [205]) (countLit q [206, 207]) (count407 q) 1 (meaning405 q) (meaning407 q) hs
  change valuationOf q 405 = false ∨ valuationOf q 407 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause695 (q : Snake 81) (h : Conditions q) : valuation q 405 = false ∨ valuation q 407 = true := counterClause695 (baseVal q)

theorem counterClause696 (q : Nat → Bool) : valuationOf q 407 = false ∨ valuationOf q 415 = true := by
  have hs : count415 q = (countLit q [205, 206, 207]) + (countLit q [208, 209, 210, 211]) := List.countP_append (p := literal q) (l₁ := [205, 206, 207]) (l₂ := [208, 209, 210, 211])
  have hm := merge_left (literal (valuationOf q) (407)) (literal (valuationOf q) (415)) (countLit q [205, 206, 207]) (countLit q [208, 209, 210, 211]) (count415 q) 1 (meaning407 q) (meaning415 q) hs
  change valuationOf q 407 = false ∨ valuationOf q 415 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause696 (q : Snake 81) (h : Conditions q) : valuation q 407 = false ∨ valuation q 415 = true := counterClause696 (baseVal q)

theorem counterClause697 (q : Nat → Bool) : valuationOf q 212 = false ∨ valuationOf q 419 = true := by
  have hs : count419 q = (countLit q [212]) + (countLit q [213, 214]) := List.countP_append (p := literal q) (l₁ := [212]) (l₂ := [213, 214])
  have hm := merge_left (literal (valuationOf q) (212)) (literal (valuationOf q) (419)) (countLit q [212]) (countLit q [213, 214]) (count419 q) 1 (meaning212 q) (meaning419 q) hs
  change valuationOf q 212 = false ∨ valuationOf q 419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause697 (q : Snake 81) (h : Conditions q) : valuation q 212 = false ∨ valuation q 419 = true := counterClause697 (baseVal q)

theorem counterClause698 (q : Nat → Bool) : valuationOf q 218 = false ∨ valuationOf q 423 = true := by
  have hs : count423 q = (countLit q [217]) + (countLit q [218]) := List.countP_append (p := literal q) (l₁ := [217]) (l₂ := [218])
  have hm := merge_right (literal (valuationOf q) (218)) (literal (valuationOf q) (423)) (countLit q [217]) (countLit q [218]) (count423 q) 1 (meaning218 q) (meaning423 q) hs
  change valuationOf q 218 = false ∨ valuationOf q 423 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause698 (q : Snake 81) (h : Conditions q) : valuation q 218 = false ∨ valuation q 423 = true := counterClause698 (baseVal q)

theorem counterClause699 (q : Nat → Bool) : valuationOf q 423 = false ∨ valuationOf q 425 = true := by
  have hs : count425 q = (countLit q [215, 216]) + (countLit q [217, 218]) := List.countP_append (p := literal q) (l₁ := [215, 216]) (l₂ := [217, 218])
  have hm := merge_right (literal (valuationOf q) (423)) (literal (valuationOf q) (425)) (countLit q [215, 216]) (countLit q [217, 218]) (count425 q) 1 (meaning423 q) (meaning425 q) hs
  change valuationOf q 423 = false ∨ valuationOf q 425 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause699 (q : Snake 81) (h : Conditions q) : valuation q 423 = false ∨ valuation q 425 = true := counterClause699 (baseVal q)

theorem counterClause700 (q : Nat → Bool) : valuationOf q 425 = false ∨ valuationOf q 427 = true := by
  have hs : count427 q = (countLit q [212, 213, 214]) + (countLit q [215, 216, 217, 218]) := List.countP_append (p := literal q) (l₁ := [212, 213, 214]) (l₂ := [215, 216, 217, 218])
  have hm := merge_right (literal (valuationOf q) (425)) (literal (valuationOf q) (427)) (countLit q [212, 213, 214]) (countLit q [215, 216, 217, 218]) (count427 q) 1 (meaning425 q) (meaning427 q) hs
  change valuationOf q 425 = false ∨ valuationOf q 427 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause700 (q : Snake 81) (h : Conditions q) : valuation q 425 = false ∨ valuation q 427 = true := counterClause700 (baseVal q)

theorem counterClause701 (q : Nat → Bool) : valuationOf q 419 = false ∨ valuationOf q 427 = true := by
  have hs : count427 q = (countLit q [212, 213, 214]) + (countLit q [215, 216, 217, 218]) := List.countP_append (p := literal q) (l₁ := [212, 213, 214]) (l₂ := [215, 216, 217, 218])
  have hm := merge_left (literal (valuationOf q) (419)) (literal (valuationOf q) (427)) (countLit q [212, 213, 214]) (countLit q [215, 216, 217, 218]) (count427 q) 1 (meaning419 q) (meaning427 q) hs
  change valuationOf q 419 = false ∨ valuationOf q 427 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause701 (q : Snake 81) (h : Conditions q) : valuation q 419 = false ∨ valuation q 427 = true := counterClause701 (baseVal q)

theorem counterClause702 (q : Nat → Bool) : valuationOf q 427 = false ∨ valuationOf q 429 = true := by
  have hs : count429 q = (countLit q [205, 206, 207, 208, 209, 210, 211]) + (countLit q [212, 213, 214, 215, 216, 217, 218]) := List.countP_append (p := literal q) (l₁ := [205, 206, 207, 208, 209, 210, 211]) (l₂ := [212, 213, 214, 215, 216, 217, 218])
  have hm := merge_right (literal (valuationOf q) (427)) (literal (valuationOf q) (429)) (countLit q [205, 206, 207, 208, 209, 210, 211]) (countLit q [212, 213, 214, 215, 216, 217, 218]) (count429 q) 1 (meaning427 q) (meaning429 q) hs
  change valuationOf q 427 = false ∨ valuationOf q 429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause702 (q : Snake 81) (h : Conditions q) : valuation q 427 = false ∨ valuation q 429 = true := counterClause702 (baseVal q)

theorem counterClause703 (q : Nat → Bool) : valuationOf q 415 = false ∨ valuationOf q 429 = true := by
  have hs : count429 q = (countLit q [205, 206, 207, 208, 209, 210, 211]) + (countLit q [212, 213, 214, 215, 216, 217, 218]) := List.countP_append (p := literal q) (l₁ := [205, 206, 207, 208, 209, 210, 211]) (l₂ := [212, 213, 214, 215, 216, 217, 218])
  have hm := merge_left (literal (valuationOf q) (415)) (literal (valuationOf q) (429)) (countLit q [205, 206, 207, 208, 209, 210, 211]) (countLit q [212, 213, 214, 215, 216, 217, 218]) (count429 q) 1 (meaning415 q) (meaning429 q) hs
  change valuationOf q 415 = false ∨ valuationOf q 429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause703 (q : Snake 81) (h : Conditions q) : valuation q 415 = false ∨ valuation q 429 = true := counterClause703 (baseVal q)

theorem counterClause704 (q : Nat → Bool) : valuationOf q 222 = false ∨ valuationOf q 431 = true := by
  have hs : count431 q = (countLit q [220]) + (countLit q [222]) := List.countP_append (p := literal q) (l₁ := [220]) (l₂ := [222])
  have hm := merge_right (literal (valuationOf q) (222)) (literal (valuationOf q) (431)) (countLit q [220]) (countLit q [222]) (count431 q) 1 (meaning222 q) (meaning431 q) hs
  change valuationOf q 222 = false ∨ valuationOf q 431 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause704 (q : Snake 81) (h : Conditions q) : valuation q 222 = false ∨ valuation q 431 = true := counterClause704 (baseVal q)

theorem block21 (q : Snake 81) (h : Conditions q) : B112E203.Block21 (valuation q) :=
  ⟨clause673 q h, clause674 q h, clause675 q h, clause676 q h, clause677 q h, clause678 q h, clause679 q h, clause680 q h, clause681 q h, clause682 q h, clause683 q h, clause684 q h, clause685 q h, clause686 q h, clause687 q h, clause688 q h, clause689 q h, clause690 q h, clause691 q h, clause692 q h, clause693 q h, clause694 q h, clause695 q h, clause696 q h, clause697 q h, clause698 q h, clause699 q h, clause700 q h, clause701 q h, clause702 q h, clause703 q h, clause704 q h⟩

end
end Snake9.Regrowth.E112203
