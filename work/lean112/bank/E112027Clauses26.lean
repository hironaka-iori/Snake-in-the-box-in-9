import E112027Semantics
import B112E027Inputs
namespace Snake9.Regrowth.E112027
noncomputable section
local instance blockDec26 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause833 (q : Nat → Bool) : valuationOf q 199 = false ∨ valuationOf q 389 = true := by
  have hs : count389 q = (countLit q [199]) + (countLit q [200]) := List.countP_append (p := literal q) (l₁ := [199]) (l₂ := [200])
  have hm := merge_left (literal (valuationOf q) (199)) (literal (valuationOf q) (389)) (countLit q [199]) (countLit q [200]) (count389 q) 1 (meaning199 q) (meaning389 q) hs
  change valuationOf q 199 = false ∨ valuationOf q 389 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause833 (q : Snake 81) (h : Conditions q) : valuation q 199 = false ∨ valuation q 389 = true := counterClause833 (baseVal q)

theorem counterClause834 (q : Nat → Bool) : valuationOf q 199 = false ∨ valuationOf q 200 = false ∨ valuationOf q 390 = true := by
  have hs : count389 q = (countLit q [199]) + (countLit q [200]) := List.countP_append (p := literal q) (l₁ := [199]) (l₂ := [200])
  have hm := merge_two (literal (valuationOf q) (199)) (literal (valuationOf q) (200)) (literal (valuationOf q) (390)) (countLit q [199]) (countLit q [200]) (count389 q) 1 1 (meaning199 q) (meaning200 q) (meaning390 q) hs
  change valuationOf q 199 = false ∨ valuationOf q 200 = false ∨ valuationOf q 390 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause834 (q : Snake 81) (h : Conditions q) : valuation q 199 = false ∨ valuation q 200 = false ∨ valuation q 390 = true := counterClause834 (baseVal q)

theorem counterClause835 (q : Nat → Bool) : valuationOf q 389 = false ∨ valuationOf q 393 = true := by
  have hs : count393 q = (countLit q [199, 200]) + (countLit q [201, 202]) := List.countP_append (p := literal q) (l₁ := [199, 200]) (l₂ := [201, 202])
  have hm := merge_left (literal (valuationOf q) (389)) (literal (valuationOf q) (393)) (countLit q [199, 200]) (countLit q [201, 202]) (count393 q) 1 (meaning389 q) (meaning393 q) hs
  change valuationOf q 389 = false ∨ valuationOf q 393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause835 (q : Snake 81) (h : Conditions q) : valuation q 389 = false ∨ valuation q 393 = true := counterClause835 (baseVal q)

theorem counterClause836 (q : Nat → Bool) : valuationOf q 390 = false ∨ valuationOf q 394 = true := by
  have hs : count393 q = (countLit q [199, 200]) + (countLit q [201, 202]) := List.countP_append (p := literal q) (l₁ := [199, 200]) (l₂ := [201, 202])
  have hm := merge_left (literal (valuationOf q) (390)) (literal (valuationOf q) (394)) (countLit q [199, 200]) (countLit q [201, 202]) (count393 q) 2 (meaning390 q) (meaning394 q) hs
  change valuationOf q 390 = false ∨ valuationOf q 394 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause836 (q : Snake 81) (h : Conditions q) : valuation q 390 = false ∨ valuation q 394 = true := counterClause836 (baseVal q)

theorem counterClause837 (q : Nat → Bool) : valuationOf q 203 = false ∨ valuationOf q 395 = true := by
  have hs : count395 q = (countLit q [203]) + (countLit q [204]) := List.countP_append (p := literal q) (l₁ := [203]) (l₂ := [204])
  have hm := merge_left (literal (valuationOf q) (203)) (literal (valuationOf q) (395)) (countLit q [203]) (countLit q [204]) (count395 q) 1 (meaning203 q) (meaning395 q) hs
  change valuationOf q 203 = false ∨ valuationOf q 395 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause837 (q : Snake 81) (h : Conditions q) : valuation q 203 = false ∨ valuation q 395 = true := counterClause837 (baseVal q)

theorem counterClause838 (q : Nat → Bool) : valuationOf q 395 = false ∨ valuationOf q 399 = true := by
  have hs : count399 q = (countLit q [203, 204]) + (countLit q [205, 206]) := List.countP_append (p := literal q) (l₁ := [203, 204]) (l₂ := [205, 206])
  have hm := merge_left (literal (valuationOf q) (395)) (literal (valuationOf q) (399)) (countLit q [203, 204]) (countLit q [205, 206]) (count399 q) 1 (meaning395 q) (meaning399 q) hs
  change valuationOf q 395 = false ∨ valuationOf q 399 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause838 (q : Snake 81) (h : Conditions q) : valuation q 395 = false ∨ valuation q 399 = true := counterClause838 (baseVal q)

theorem counterClause839 (q : Nat → Bool) : valuationOf q 399 = false ∨ valuationOf q 401 = true := by
  have hs : count401 q = (countLit q [199, 200, 201, 202]) + (countLit q [203, 204, 205, 206]) := List.countP_append (p := literal q) (l₁ := [199, 200, 201, 202]) (l₂ := [203, 204, 205, 206])
  have hm := merge_right (literal (valuationOf q) (399)) (literal (valuationOf q) (401)) (countLit q [199, 200, 201, 202]) (countLit q [203, 204, 205, 206]) (count401 q) 1 (meaning399 q) (meaning401 q) hs
  change valuationOf q 399 = false ∨ valuationOf q 401 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause839 (q : Snake 81) (h : Conditions q) : valuation q 399 = false ∨ valuation q 401 = true := counterClause839 (baseVal q)

theorem counterClause840 (q : Nat → Bool) : valuationOf q 393 = false ∨ valuationOf q 401 = true := by
  have hs : count401 q = (countLit q [199, 200, 201, 202]) + (countLit q [203, 204, 205, 206]) := List.countP_append (p := literal q) (l₁ := [199, 200, 201, 202]) (l₂ := [203, 204, 205, 206])
  have hm := merge_left (literal (valuationOf q) (393)) (literal (valuationOf q) (401)) (countLit q [199, 200, 201, 202]) (countLit q [203, 204, 205, 206]) (count401 q) 1 (meaning393 q) (meaning401 q) hs
  change valuationOf q 393 = false ∨ valuationOf q 401 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause840 (q : Snake 81) (h : Conditions q) : valuation q 393 = false ∨ valuation q 401 = true := counterClause840 (baseVal q)

theorem counterClause841 (q : Nat → Bool) : valuationOf q 393 = false ∨ valuationOf q 399 = false ∨ valuationOf q 402 = true := by
  have hs : count401 q = (countLit q [199, 200, 201, 202]) + (countLit q [203, 204, 205, 206]) := List.countP_append (p := literal q) (l₁ := [199, 200, 201, 202]) (l₂ := [203, 204, 205, 206])
  have hm := merge_two (literal (valuationOf q) (393)) (literal (valuationOf q) (399)) (literal (valuationOf q) (402)) (countLit q [199, 200, 201, 202]) (countLit q [203, 204, 205, 206]) (count401 q) 1 1 (meaning393 q) (meaning399 q) (meaning402 q) hs
  change valuationOf q 393 = false ∨ valuationOf q 399 = false ∨ valuationOf q 402 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause841 (q : Snake 81) (h : Conditions q) : valuation q 393 = false ∨ valuation q 399 = false ∨ valuation q 402 = true := counterClause841 (baseVal q)

theorem counterClause842 (q : Nat → Bool) : valuationOf q 394 = false ∨ valuationOf q 402 = true := by
  have hs : count401 q = (countLit q [199, 200, 201, 202]) + (countLit q [203, 204, 205, 206]) := List.countP_append (p := literal q) (l₁ := [199, 200, 201, 202]) (l₂ := [203, 204, 205, 206])
  have hm := merge_left (literal (valuationOf q) (394)) (literal (valuationOf q) (402)) (countLit q [199, 200, 201, 202]) (countLit q [203, 204, 205, 206]) (count401 q) 2 (meaning394 q) (meaning402 q) hs
  change valuationOf q 394 = false ∨ valuationOf q 402 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause842 (q : Snake 81) (h : Conditions q) : valuation q 394 = false ∨ valuation q 402 = true := counterClause842 (baseVal q)

theorem counterClause843 (q : Nat → Bool) : valuationOf q 401 = false ∨ valuationOf q 403 = true := by
  have hs : count403 q = (countLit q [192, 193, 194, 195, 196, 197, 198]) + (countLit q [199, 200, 201, 202, 203, 204, 205, 206]) := List.countP_append (p := literal q) (l₁ := [192, 193, 194, 195, 196, 197, 198]) (l₂ := [199, 200, 201, 202, 203, 204, 205, 206])
  have hm := merge_right (literal (valuationOf q) (401)) (literal (valuationOf q) (403)) (countLit q [192, 193, 194, 195, 196, 197, 198]) (countLit q [199, 200, 201, 202, 203, 204, 205, 206]) (count403 q) 1 (meaning401 q) (meaning403 q) hs
  change valuationOf q 401 = false ∨ valuationOf q 403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause843 (q : Snake 81) (h : Conditions q) : valuation q 401 = false ∨ valuation q 403 = true := counterClause843 (baseVal q)

theorem counterClause844 (q : Nat → Bool) : valuationOf q 402 = false ∨ valuationOf q 404 = true := by
  have hs : count403 q = (countLit q [192, 193, 194, 195, 196, 197, 198]) + (countLit q [199, 200, 201, 202, 203, 204, 205, 206]) := List.countP_append (p := literal q) (l₁ := [192, 193, 194, 195, 196, 197, 198]) (l₂ := [199, 200, 201, 202, 203, 204, 205, 206])
  have hm := merge_right (literal (valuationOf q) (402)) (literal (valuationOf q) (404)) (countLit q [192, 193, 194, 195, 196, 197, 198]) (countLit q [199, 200, 201, 202, 203, 204, 205, 206]) (count403 q) 2 (meaning402 q) (meaning404 q) hs
  change valuationOf q 402 = false ∨ valuationOf q 404 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause844 (q : Snake 81) (h : Conditions q) : valuation q 402 = false ∨ valuation q 404 = true := counterClause844 (baseVal q)

theorem counterClause845 (q : Nat → Bool) : valuationOf q 387 = false ∨ valuationOf q 403 = true := by
  have hs : count403 q = (countLit q [192, 193, 194, 195, 196, 197, 198]) + (countLit q [199, 200, 201, 202, 203, 204, 205, 206]) := List.countP_append (p := literal q) (l₁ := [192, 193, 194, 195, 196, 197, 198]) (l₂ := [199, 200, 201, 202, 203, 204, 205, 206])
  have hm := merge_left (literal (valuationOf q) (387)) (literal (valuationOf q) (403)) (countLit q [192, 193, 194, 195, 196, 197, 198]) (countLit q [199, 200, 201, 202, 203, 204, 205, 206]) (count403 q) 1 (meaning387 q) (meaning403 q) hs
  change valuationOf q 387 = false ∨ valuationOf q 403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause845 (q : Snake 81) (h : Conditions q) : valuation q 387 = false ∨ valuation q 403 = true := counterClause845 (baseVal q)

theorem counterClause846 (q : Nat → Bool) : valuationOf q 387 = false ∨ valuationOf q 401 = false ∨ valuationOf q 404 = true := by
  have hs : count403 q = (countLit q [192, 193, 194, 195, 196, 197, 198]) + (countLit q [199, 200, 201, 202, 203, 204, 205, 206]) := List.countP_append (p := literal q) (l₁ := [192, 193, 194, 195, 196, 197, 198]) (l₂ := [199, 200, 201, 202, 203, 204, 205, 206])
  have hm := merge_two (literal (valuationOf q) (387)) (literal (valuationOf q) (401)) (literal (valuationOf q) (404)) (countLit q [192, 193, 194, 195, 196, 197, 198]) (countLit q [199, 200, 201, 202, 203, 204, 205, 206]) (count403 q) 1 1 (meaning387 q) (meaning401 q) (meaning404 q) hs
  change valuationOf q 387 = false ∨ valuationOf q 401 = false ∨ valuationOf q 404 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause846 (q : Snake 81) (h : Conditions q) : valuation q 387 = false ∨ valuation q 401 = false ∨ valuation q 404 = true := counterClause846 (baseVal q)

theorem counterClause847 (q : Nat → Bool) : valuationOf q 388 = false ∨ valuationOf q 404 = true := by
  have hs : count403 q = (countLit q [192, 193, 194, 195, 196, 197, 198]) + (countLit q [199, 200, 201, 202, 203, 204, 205, 206]) := List.countP_append (p := literal q) (l₁ := [192, 193, 194, 195, 196, 197, 198]) (l₂ := [199, 200, 201, 202, 203, 204, 205, 206])
  have hm := merge_left (literal (valuationOf q) (388)) (literal (valuationOf q) (404)) (countLit q [192, 193, 194, 195, 196, 197, 198]) (countLit q [199, 200, 201, 202, 203, 204, 205, 206]) (count403 q) 2 (meaning388 q) (meaning404 q) hs
  change valuationOf q 388 = false ∨ valuationOf q 404 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause847 (q : Snake 81) (h : Conditions q) : valuation q 388 = false ∨ valuation q 404 = true := counterClause847 (baseVal q)

theorem counterClause848 (q : Nat → Bool) : valuationOf q 403 = false ∨ valuationOf q 405 = true := by
  have hs : count405 q = (countLit q [177, 178, 179, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) + (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) := List.countP_append (p := literal q) (l₁ := [177, 178, 179, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) (l₂ := [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206])
  have hm := merge_right (literal (valuationOf q) (403)) (literal (valuationOf q) (405)) (countLit q [177, 178, 179, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (count405 q) 1 (meaning403 q) (meaning405 q) hs
  change valuationOf q 403 = false ∨ valuationOf q 405 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause848 (q : Snake 81) (h : Conditions q) : valuation q 403 = false ∨ valuation q 405 = true := counterClause848 (baseVal q)

theorem counterClause849 (q : Nat → Bool) : valuationOf q 404 = false ∨ valuationOf q 406 = true := by
  have hs : count405 q = (countLit q [177, 178, 179, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) + (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) := List.countP_append (p := literal q) (l₁ := [177, 178, 179, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) (l₂ := [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206])
  have hm := merge_right (literal (valuationOf q) (404)) (literal (valuationOf q) (406)) (countLit q [177, 178, 179, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (count405 q) 2 (meaning404 q) (meaning406 q) hs
  change valuationOf q 404 = false ∨ valuationOf q 406 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause849 (q : Snake 81) (h : Conditions q) : valuation q 404 = false ∨ valuation q 406 = true := counterClause849 (baseVal q)

theorem counterClause850 (q : Nat → Bool) : valuationOf q 375 = false ∨ valuationOf q 405 = true := by
  have hs : count405 q = (countLit q [177, 178, 179, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) + (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) := List.countP_append (p := literal q) (l₁ := [177, 178, 179, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) (l₂ := [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206])
  have hm := merge_left (literal (valuationOf q) (375)) (literal (valuationOf q) (405)) (countLit q [177, 178, 179, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (count405 q) 1 (meaning375 q) (meaning405 q) hs
  change valuationOf q 375 = false ∨ valuationOf q 405 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause850 (q : Snake 81) (h : Conditions q) : valuation q 375 = false ∨ valuation q 405 = true := counterClause850 (baseVal q)

theorem counterClause851 (q : Nat → Bool) : valuationOf q 375 = false ∨ valuationOf q 403 = false ∨ valuationOf q 406 = true := by
  have hs : count405 q = (countLit q [177, 178, 179, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) + (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) := List.countP_append (p := literal q) (l₁ := [177, 178, 179, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) (l₂ := [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206])
  have hm := merge_two (literal (valuationOf q) (375)) (literal (valuationOf q) (403)) (literal (valuationOf q) (406)) (countLit q [177, 178, 179, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (count405 q) 1 1 (meaning375 q) (meaning403 q) (meaning406 q) hs
  change valuationOf q 375 = false ∨ valuationOf q 403 = false ∨ valuationOf q 406 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause851 (q : Snake 81) (h : Conditions q) : valuation q 375 = false ∨ valuation q 403 = false ∨ valuation q 406 = true := counterClause851 (baseVal q)

theorem counterClause852 (q : Nat → Bool) : valuationOf q 376 = false ∨ valuationOf q 406 = true := by
  have hs : count405 q = (countLit q [177, 178, 179, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) + (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) := List.countP_append (p := literal q) (l₁ := [177, 178, 179, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) (l₂ := [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206])
  have hm := merge_left (literal (valuationOf q) (376)) (literal (valuationOf q) (406)) (countLit q [177, 178, 179, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (count405 q) 2 (meaning376 q) (meaning406 q) hs
  change valuationOf q 376 = false ∨ valuationOf q 406 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause852 (q : Snake 81) (h : Conditions q) : valuation q 376 = false ∨ valuation q 406 = true := counterClause852 (baseVal q)

theorem counterClause853 (q : Nat → Bool) : valuationOf q 208 = false ∨ valuationOf q 407 = true := by
  have hs : count407 q = (countLit q [208]) + (countLit q [209]) := List.countP_append (p := literal q) (l₁ := [208]) (l₂ := [209])
  have hm := merge_left (literal (valuationOf q) (208)) (literal (valuationOf q) (407)) (countLit q [208]) (countLit q [209]) (count407 q) 1 (meaning208 q) (meaning407 q) hs
  change valuationOf q 208 = false ∨ valuationOf q 407 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause853 (q : Snake 81) (h : Conditions q) : valuation q 208 = false ∨ valuation q 407 = true := counterClause853 (baseVal q)

theorem counterClause854 (q : Nat → Bool) : valuationOf q 407 = false ∨ valuationOf q 409 = true := by
  have hs : count409 q = (countLit q [207]) + (countLit q [208, 209]) := List.countP_append (p := literal q) (l₁ := [207]) (l₂ := [208, 209])
  have hm := merge_right (literal (valuationOf q) (407)) (literal (valuationOf q) (409)) (countLit q [207]) (countLit q [208, 209]) (count409 q) 1 (meaning407 q) (meaning409 q) hs
  change valuationOf q 407 = false ∨ valuationOf q 409 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause854 (q : Snake 81) (h : Conditions q) : valuation q 407 = false ∨ valuation q 409 = true := counterClause854 (baseVal q)

theorem counterClause855 (q : Nat → Bool) : valuationOf q 207 = false ∨ valuationOf q 409 = true := by
  have hs : count409 q = (countLit q [207]) + (countLit q [208, 209]) := List.countP_append (p := literal q) (l₁ := [207]) (l₂ := [208, 209])
  have hm := merge_left (literal (valuationOf q) (207)) (literal (valuationOf q) (409)) (countLit q [207]) (countLit q [208, 209]) (count409 q) 1 (meaning207 q) (meaning409 q) hs
  change valuationOf q 207 = false ∨ valuationOf q 409 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause855 (q : Snake 81) (h : Conditions q) : valuation q 207 = false ∨ valuation q 409 = true := counterClause855 (baseVal q)

theorem counterClause856 (q : Nat → Bool) : valuationOf q 210 = false ∨ valuationOf q 411 = true := by
  have hs : count411 q = (countLit q [210]) + (countLit q [211]) := List.countP_append (p := literal q) (l₁ := [210]) (l₂ := [211])
  have hm := merge_left (literal (valuationOf q) (210)) (literal (valuationOf q) (411)) (countLit q [210]) (countLit q [211]) (count411 q) 1 (meaning210 q) (meaning411 q) hs
  change valuationOf q 210 = false ∨ valuationOf q 411 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause856 (q : Snake 81) (h : Conditions q) : valuation q 210 = false ∨ valuation q 411 = true := counterClause856 (baseVal q)

theorem counterClause857 (q : Nat → Bool) : valuationOf q 213 = false ∨ valuationOf q 413 = true := by
  have hs : count413 q = (countLit q [212]) + (countLit q [213]) := List.countP_append (p := literal q) (l₁ := [212]) (l₂ := [213])
  have hm := merge_right (literal (valuationOf q) (213)) (literal (valuationOf q) (413)) (countLit q [212]) (countLit q [213]) (count413 q) 1 (meaning213 q) (meaning413 q) hs
  change valuationOf q 213 = false ∨ valuationOf q 413 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause857 (q : Snake 81) (h : Conditions q) : valuation q 213 = false ∨ valuation q 413 = true := counterClause857 (baseVal q)

theorem counterClause858 (q : Nat → Bool) : valuationOf q 413 = false ∨ valuationOf q 415 = true := by
  have hs : count415 q = (countLit q [210, 211]) + (countLit q [212, 213]) := List.countP_append (p := literal q) (l₁ := [210, 211]) (l₂ := [212, 213])
  have hm := merge_right (literal (valuationOf q) (413)) (literal (valuationOf q) (415)) (countLit q [210, 211]) (countLit q [212, 213]) (count415 q) 1 (meaning413 q) (meaning415 q) hs
  change valuationOf q 413 = false ∨ valuationOf q 415 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause858 (q : Snake 81) (h : Conditions q) : valuation q 413 = false ∨ valuation q 415 = true := counterClause858 (baseVal q)

theorem counterClause859 (q : Nat → Bool) : valuationOf q 411 = false ∨ valuationOf q 415 = true := by
  have hs : count415 q = (countLit q [210, 211]) + (countLit q [212, 213]) := List.countP_append (p := literal q) (l₁ := [210, 211]) (l₂ := [212, 213])
  have hm := merge_left (literal (valuationOf q) (411)) (literal (valuationOf q) (415)) (countLit q [210, 211]) (countLit q [212, 213]) (count415 q) 1 (meaning411 q) (meaning415 q) hs
  change valuationOf q 411 = false ∨ valuationOf q 415 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause859 (q : Snake 81) (h : Conditions q) : valuation q 411 = false ∨ valuation q 415 = true := counterClause859 (baseVal q)

theorem counterClause860 (q : Nat → Bool) : valuationOf q 415 = false ∨ valuationOf q 417 = true := by
  have hs : count417 q = (countLit q [207, 208, 209]) + (countLit q [210, 211, 212, 213]) := List.countP_append (p := literal q) (l₁ := [207, 208, 209]) (l₂ := [210, 211, 212, 213])
  have hm := merge_right (literal (valuationOf q) (415)) (literal (valuationOf q) (417)) (countLit q [207, 208, 209]) (countLit q [210, 211, 212, 213]) (count417 q) 1 (meaning415 q) (meaning417 q) hs
  change valuationOf q 415 = false ∨ valuationOf q 417 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause860 (q : Snake 81) (h : Conditions q) : valuation q 415 = false ∨ valuation q 417 = true := counterClause860 (baseVal q)

theorem counterClause861 (q : Nat → Bool) : valuationOf q 409 = false ∨ valuationOf q 417 = true := by
  have hs : count417 q = (countLit q [207, 208, 209]) + (countLit q [210, 211, 212, 213]) := List.countP_append (p := literal q) (l₁ := [207, 208, 209]) (l₂ := [210, 211, 212, 213])
  have hm := merge_left (literal (valuationOf q) (409)) (literal (valuationOf q) (417)) (countLit q [207, 208, 209]) (countLit q [210, 211, 212, 213]) (count417 q) 1 (meaning409 q) (meaning417 q) hs
  change valuationOf q 409 = false ∨ valuationOf q 417 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause861 (q : Snake 81) (h : Conditions q) : valuation q 409 = false ∨ valuation q 417 = true := counterClause861 (baseVal q)

theorem counterClause862 (q : Nat → Bool) : valuationOf q 409 = false ∨ valuationOf q 415 = false ∨ valuationOf q 418 = true := by
  have hs : count417 q = (countLit q [207, 208, 209]) + (countLit q [210, 211, 212, 213]) := List.countP_append (p := literal q) (l₁ := [207, 208, 209]) (l₂ := [210, 211, 212, 213])
  have hm := merge_two (literal (valuationOf q) (409)) (literal (valuationOf q) (415)) (literal (valuationOf q) (418)) (countLit q [207, 208, 209]) (countLit q [210, 211, 212, 213]) (count417 q) 1 1 (meaning409 q) (meaning415 q) (meaning418 q) hs
  change valuationOf q 409 = false ∨ valuationOf q 415 = false ∨ valuationOf q 418 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause862 (q : Snake 81) (h : Conditions q) : valuation q 409 = false ∨ valuation q 415 = false ∨ valuation q 418 = true := counterClause862 (baseVal q)

theorem counterClause863 (q : Nat → Bool) : valuationOf q 215 = false ∨ valuationOf q 419 = true := by
  have hs : count419 q = (countLit q [214]) + (countLit q [215]) := List.countP_append (p := literal q) (l₁ := [214]) (l₂ := [215])
  have hm := merge_right (literal (valuationOf q) (215)) (literal (valuationOf q) (419)) (countLit q [214]) (countLit q [215]) (count419 q) 1 (meaning215 q) (meaning419 q) hs
  change valuationOf q 215 = false ∨ valuationOf q 419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause863 (q : Snake 81) (h : Conditions q) : valuation q 215 = false ∨ valuation q 419 = true := counterClause863 (baseVal q)

theorem counterClause864 (q : Nat → Bool) : valuationOf q 214 = false ∨ valuationOf q 419 = true := by
  have hs : count419 q = (countLit q [214]) + (countLit q [215]) := List.countP_append (p := literal q) (l₁ := [214]) (l₂ := [215])
  have hm := merge_left (literal (valuationOf q) (214)) (literal (valuationOf q) (419)) (countLit q [214]) (countLit q [215]) (count419 q) 1 (meaning214 q) (meaning419 q) hs
  change valuationOf q 214 = false ∨ valuationOf q 419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause864 (q : Snake 81) (h : Conditions q) : valuation q 214 = false ∨ valuation q 419 = true := counterClause864 (baseVal q)

theorem block26 (q : Snake 81) (h : Conditions q) : B112E027.Block26 (valuation q) :=
  ⟨clause833 q h, clause834 q h, clause835 q h, clause836 q h, clause837 q h, clause838 q h, clause839 q h, clause840 q h, clause841 q h, clause842 q h, clause843 q h, clause844 q h, clause845 q h, clause846 q h, clause847 q h, clause848 q h, clause849 q h, clause850 q h, clause851 q h, clause852 q h, clause853 q h, clause854 q h, clause855 q h, clause856 q h, clause857 q h, clause858 q h, clause859 q h, clause860 q h, clause861 q h, clause862 q h, clause863 q h, clause864 q h⟩

end
end Snake9.Regrowth.E112027
