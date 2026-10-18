import E112158Semantics
import B112E158Inputs
namespace Snake9.Regrowth.E112158
noncomputable section
local instance blockDec26 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause833 (q : Nat → Bool) : valuationOf q 193 = false ∨ valuationOf q 377 = true := by
  have hs : count377 q = (countLit q [192]) + (countLit q [193]) := List.countP_append (p := literal q) (l₁ := [192]) (l₂ := [193])
  have hm := merge_right (literal (valuationOf q) (193)) (literal (valuationOf q) (377)) (countLit q [192]) (countLit q [193]) (count377 q) 1 (meaning193 q) (meaning377 q) hs
  change valuationOf q 193 = false ∨ valuationOf q 377 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause833 (q : Snake 81) (h : Conditions q) : valuation q 193 = false ∨ valuation q 377 = true := counterClause833 (baseVal q)

theorem counterClause834 (q : Nat → Bool) : valuationOf q 377 = false ∨ valuationOf q 379 = true := by
  have hs : count379 q = (countLit q [191]) + (countLit q [192, 193]) := List.countP_append (p := literal q) (l₁ := [191]) (l₂ := [192, 193])
  have hm := merge_right (literal (valuationOf q) (377)) (literal (valuationOf q) (379)) (countLit q [191]) (countLit q [192, 193]) (count379 q) 1 (meaning377 q) (meaning379 q) hs
  change valuationOf q 377 = false ∨ valuationOf q 379 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause834 (q : Snake 81) (h : Conditions q) : valuation q 377 = false ∨ valuation q 379 = true := counterClause834 (baseVal q)

theorem counterClause835 (q : Nat → Bool) : valuationOf q 194 = false ∨ valuationOf q 381 = true := by
  have hs : count381 q = (countLit q [194]) + (countLit q [195]) := List.countP_append (p := literal q) (l₁ := [194]) (l₂ := [195])
  have hm := merge_left (literal (valuationOf q) (194)) (literal (valuationOf q) (381)) (countLit q [194]) (countLit q [195]) (count381 q) 1 (meaning194 q) (meaning381 q) hs
  change valuationOf q 194 = false ∨ valuationOf q 381 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause835 (q : Snake 81) (h : Conditions q) : valuation q 194 = false ∨ valuation q 381 = true := counterClause835 (baseVal q)

theorem counterClause836 (q : Nat → Bool) : valuationOf q 197 = false ∨ valuationOf q 383 = true := by
  have hs : count383 q = (countLit q [197]) + (countLit q [198]) := List.countP_append (p := literal q) (l₁ := [197]) (l₂ := [198])
  have hm := merge_left (literal (valuationOf q) (197)) (literal (valuationOf q) (383)) (countLit q [197]) (countLit q [198]) (count383 q) 1 (meaning197 q) (meaning383 q) hs
  change valuationOf q 197 = false ∨ valuationOf q 383 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause836 (q : Snake 81) (h : Conditions q) : valuation q 197 = false ∨ valuation q 383 = true := counterClause836 (baseVal q)

theorem counterClause837 (q : Nat → Bool) : valuationOf q 383 = false ∨ valuationOf q 385 = true := by
  have hs : count385 q = (countLit q [194, 195]) + (countLit q [197, 198]) := List.countP_append (p := literal q) (l₁ := [194, 195]) (l₂ := [197, 198])
  have hm := merge_right (literal (valuationOf q) (383)) (literal (valuationOf q) (385)) (countLit q [194, 195]) (countLit q [197, 198]) (count385 q) 1 (meaning383 q) (meaning385 q) hs
  change valuationOf q 383 = false ∨ valuationOf q 385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause837 (q : Snake 81) (h : Conditions q) : valuation q 383 = false ∨ valuation q 385 = true := counterClause837 (baseVal q)

theorem counterClause838 (q : Nat → Bool) : valuationOf q 381 = false ∨ valuationOf q 385 = true := by
  have hs : count385 q = (countLit q [194, 195]) + (countLit q [197, 198]) := List.countP_append (p := literal q) (l₁ := [194, 195]) (l₂ := [197, 198])
  have hm := merge_left (literal (valuationOf q) (381)) (literal (valuationOf q) (385)) (countLit q [194, 195]) (countLit q [197, 198]) (count385 q) 1 (meaning381 q) (meaning385 q) hs
  change valuationOf q 381 = false ∨ valuationOf q 385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause838 (q : Snake 81) (h : Conditions q) : valuation q 381 = false ∨ valuation q 385 = true := counterClause838 (baseVal q)

theorem counterClause839 (q : Nat → Bool) : valuationOf q 381 = false ∨ valuationOf q 383 = false ∨ valuationOf q 386 = true := by
  have hs : count385 q = (countLit q [194, 195]) + (countLit q [197, 198]) := List.countP_append (p := literal q) (l₁ := [194, 195]) (l₂ := [197, 198])
  have hm := merge_two (literal (valuationOf q) (381)) (literal (valuationOf q) (383)) (literal (valuationOf q) (386)) (countLit q [194, 195]) (countLit q [197, 198]) (count385 q) 1 1 (meaning381 q) (meaning383 q) (meaning386 q) hs
  change valuationOf q 381 = false ∨ valuationOf q 383 = false ∨ valuationOf q 386 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause839 (q : Snake 81) (h : Conditions q) : valuation q 381 = false ∨ valuation q 383 = false ∨ valuation q 386 = true := counterClause839 (baseVal q)

theorem counterClause840 (q : Nat → Bool) : valuationOf q 385 = false ∨ valuationOf q 387 = true := by
  have hs : count387 q = (countLit q [191, 192, 193]) + (countLit q [194, 195, 197, 198]) := List.countP_append (p := literal q) (l₁ := [191, 192, 193]) (l₂ := [194, 195, 197, 198])
  have hm := merge_right (literal (valuationOf q) (385)) (literal (valuationOf q) (387)) (countLit q [191, 192, 193]) (countLit q [194, 195, 197, 198]) (count387 q) 1 (meaning385 q) (meaning387 q) hs
  change valuationOf q 385 = false ∨ valuationOf q 387 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause840 (q : Snake 81) (h : Conditions q) : valuation q 385 = false ∨ valuation q 387 = true := counterClause840 (baseVal q)

theorem counterClause841 (q : Nat → Bool) : valuationOf q 386 = false ∨ valuationOf q 388 = true := by
  have hs : count387 q = (countLit q [191, 192, 193]) + (countLit q [194, 195, 197, 198]) := List.countP_append (p := literal q) (l₁ := [191, 192, 193]) (l₂ := [194, 195, 197, 198])
  have hm := merge_right (literal (valuationOf q) (386)) (literal (valuationOf q) (388)) (countLit q [191, 192, 193]) (countLit q [194, 195, 197, 198]) (count387 q) 2 (meaning386 q) (meaning388 q) hs
  change valuationOf q 386 = false ∨ valuationOf q 388 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause841 (q : Snake 81) (h : Conditions q) : valuation q 386 = false ∨ valuation q 388 = true := counterClause841 (baseVal q)

theorem counterClause842 (q : Nat → Bool) : valuationOf q 379 = false ∨ valuationOf q 387 = true := by
  have hs : count387 q = (countLit q [191, 192, 193]) + (countLit q [194, 195, 197, 198]) := List.countP_append (p := literal q) (l₁ := [191, 192, 193]) (l₂ := [194, 195, 197, 198])
  have hm := merge_left (literal (valuationOf q) (379)) (literal (valuationOf q) (387)) (countLit q [191, 192, 193]) (countLit q [194, 195, 197, 198]) (count387 q) 1 (meaning379 q) (meaning387 q) hs
  change valuationOf q 379 = false ∨ valuationOf q 387 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause842 (q : Snake 81) (h : Conditions q) : valuation q 379 = false ∨ valuation q 387 = true := counterClause842 (baseVal q)

theorem counterClause843 (q : Nat → Bool) : valuationOf q 379 = false ∨ valuationOf q 385 = false ∨ valuationOf q 388 = true := by
  have hs : count387 q = (countLit q [191, 192, 193]) + (countLit q [194, 195, 197, 198]) := List.countP_append (p := literal q) (l₁ := [191, 192, 193]) (l₂ := [194, 195, 197, 198])
  have hm := merge_two (literal (valuationOf q) (379)) (literal (valuationOf q) (385)) (literal (valuationOf q) (388)) (countLit q [191, 192, 193]) (countLit q [194, 195, 197, 198]) (count387 q) 1 1 (meaning379 q) (meaning385 q) (meaning388 q) hs
  change valuationOf q 379 = false ∨ valuationOf q 385 = false ∨ valuationOf q 388 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause843 (q : Snake 81) (h : Conditions q) : valuation q 379 = false ∨ valuation q 385 = false ∨ valuation q 388 = true := counterClause843 (baseVal q)

theorem counterClause844 (q : Nat → Bool) : valuationOf q 199 = false ∨ valuationOf q 389 = true := by
  have hs : count389 q = (countLit q [199]) + (countLit q [200]) := List.countP_append (p := literal q) (l₁ := [199]) (l₂ := [200])
  have hm := merge_left (literal (valuationOf q) (199)) (literal (valuationOf q) (389)) (countLit q [199]) (countLit q [200]) (count389 q) 1 (meaning199 q) (meaning389 q) hs
  change valuationOf q 199 = false ∨ valuationOf q 389 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause844 (q : Snake 81) (h : Conditions q) : valuation q 199 = false ∨ valuation q 389 = true := counterClause844 (baseVal q)

theorem counterClause845 (q : Nat → Bool) : valuationOf q 201 = false ∨ valuationOf q 391 = true := by
  have hs : count391 q = (countLit q [201]) + (countLit q [202]) := List.countP_append (p := literal q) (l₁ := [201]) (l₂ := [202])
  have hm := merge_left (literal (valuationOf q) (201)) (literal (valuationOf q) (391)) (countLit q [201]) (countLit q [202]) (count391 q) 1 (meaning201 q) (meaning391 q) hs
  change valuationOf q 201 = false ∨ valuationOf q 391 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause845 (q : Snake 81) (h : Conditions q) : valuation q 201 = false ∨ valuation q 391 = true := counterClause845 (baseVal q)

theorem counterClause846 (q : Nat → Bool) : valuationOf q 391 = false ∨ valuationOf q 393 = true := by
  have hs : count393 q = (countLit q [199, 200]) + (countLit q [201, 202]) := List.countP_append (p := literal q) (l₁ := [199, 200]) (l₂ := [201, 202])
  have hm := merge_right (literal (valuationOf q) (391)) (literal (valuationOf q) (393)) (countLit q [199, 200]) (countLit q [201, 202]) (count393 q) 1 (meaning391 q) (meaning393 q) hs
  change valuationOf q 391 = false ∨ valuationOf q 393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause846 (q : Snake 81) (h : Conditions q) : valuation q 391 = false ∨ valuation q 393 = true := counterClause846 (baseVal q)

theorem counterClause847 (q : Nat → Bool) : valuationOf q 389 = false ∨ valuationOf q 393 = true := by
  have hs : count393 q = (countLit q [199, 200]) + (countLit q [201, 202]) := List.countP_append (p := literal q) (l₁ := [199, 200]) (l₂ := [201, 202])
  have hm := merge_left (literal (valuationOf q) (389)) (literal (valuationOf q) (393)) (countLit q [199, 200]) (countLit q [201, 202]) (count393 q) 1 (meaning389 q) (meaning393 q) hs
  change valuationOf q 389 = false ∨ valuationOf q 393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause847 (q : Snake 81) (h : Conditions q) : valuation q 389 = false ∨ valuation q 393 = true := counterClause847 (baseVal q)

theorem counterClause848 (q : Nat → Bool) : valuationOf q 203 = false ∨ valuationOf q 395 = true := by
  have hs : count395 q = (countLit q [203]) + (countLit q [204]) := List.countP_append (p := literal q) (l₁ := [203]) (l₂ := [204])
  have hm := merge_left (literal (valuationOf q) (203)) (literal (valuationOf q) (395)) (countLit q [203]) (countLit q [204]) (count395 q) 1 (meaning203 q) (meaning395 q) hs
  change valuationOf q 203 = false ∨ valuationOf q 395 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause848 (q : Snake 81) (h : Conditions q) : valuation q 203 = false ∨ valuation q 395 = true := counterClause848 (baseVal q)

theorem counterClause849 (q : Nat → Bool) : valuationOf q 206 = false ∨ valuationOf q 397 = true := by
  have hs : count397 q = (countLit q [205]) + (countLit q [206]) := List.countP_append (p := literal q) (l₁ := [205]) (l₂ := [206])
  have hm := merge_right (literal (valuationOf q) (206)) (literal (valuationOf q) (397)) (countLit q [205]) (countLit q [206]) (count397 q) 1 (meaning206 q) (meaning397 q) hs
  change valuationOf q 206 = false ∨ valuationOf q 397 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause849 (q : Snake 81) (h : Conditions q) : valuation q 206 = false ∨ valuation q 397 = true := counterClause849 (baseVal q)

theorem counterClause850 (q : Nat → Bool) : valuationOf q 397 = false ∨ valuationOf q 399 = true := by
  have hs : count399 q = (countLit q [203, 204]) + (countLit q [205, 206]) := List.countP_append (p := literal q) (l₁ := [203, 204]) (l₂ := [205, 206])
  have hm := merge_right (literal (valuationOf q) (397)) (literal (valuationOf q) (399)) (countLit q [203, 204]) (countLit q [205, 206]) (count399 q) 1 (meaning397 q) (meaning399 q) hs
  change valuationOf q 397 = false ∨ valuationOf q 399 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause850 (q : Snake 81) (h : Conditions q) : valuation q 397 = false ∨ valuation q 399 = true := counterClause850 (baseVal q)

theorem counterClause851 (q : Nat → Bool) : valuationOf q 395 = false ∨ valuationOf q 399 = true := by
  have hs : count399 q = (countLit q [203, 204]) + (countLit q [205, 206]) := List.countP_append (p := literal q) (l₁ := [203, 204]) (l₂ := [205, 206])
  have hm := merge_left (literal (valuationOf q) (395)) (literal (valuationOf q) (399)) (countLit q [203, 204]) (countLit q [205, 206]) (count399 q) 1 (meaning395 q) (meaning399 q) hs
  change valuationOf q 395 = false ∨ valuationOf q 399 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause851 (q : Snake 81) (h : Conditions q) : valuation q 395 = false ∨ valuation q 399 = true := counterClause851 (baseVal q)

theorem counterClause852 (q : Nat → Bool) : valuationOf q 399 = false ∨ valuationOf q 401 = true := by
  have hs : count401 q = (countLit q [199, 200, 201, 202]) + (countLit q [203, 204, 205, 206]) := List.countP_append (p := literal q) (l₁ := [199, 200, 201, 202]) (l₂ := [203, 204, 205, 206])
  have hm := merge_right (literal (valuationOf q) (399)) (literal (valuationOf q) (401)) (countLit q [199, 200, 201, 202]) (countLit q [203, 204, 205, 206]) (count401 q) 1 (meaning399 q) (meaning401 q) hs
  change valuationOf q 399 = false ∨ valuationOf q 401 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause852 (q : Snake 81) (h : Conditions q) : valuation q 399 = false ∨ valuation q 401 = true := counterClause852 (baseVal q)

theorem counterClause853 (q : Nat → Bool) : valuationOf q 393 = false ∨ valuationOf q 401 = true := by
  have hs : count401 q = (countLit q [199, 200, 201, 202]) + (countLit q [203, 204, 205, 206]) := List.countP_append (p := literal q) (l₁ := [199, 200, 201, 202]) (l₂ := [203, 204, 205, 206])
  have hm := merge_left (literal (valuationOf q) (393)) (literal (valuationOf q) (401)) (countLit q [199, 200, 201, 202]) (countLit q [203, 204, 205, 206]) (count401 q) 1 (meaning393 q) (meaning401 q) hs
  change valuationOf q 393 = false ∨ valuationOf q 401 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause853 (q : Snake 81) (h : Conditions q) : valuation q 393 = false ∨ valuation q 401 = true := counterClause853 (baseVal q)

theorem counterClause854 (q : Nat → Bool) : valuationOf q 393 = false ∨ valuationOf q 399 = false ∨ valuationOf q 402 = true := by
  have hs : count401 q = (countLit q [199, 200, 201, 202]) + (countLit q [203, 204, 205, 206]) := List.countP_append (p := literal q) (l₁ := [199, 200, 201, 202]) (l₂ := [203, 204, 205, 206])
  have hm := merge_two (literal (valuationOf q) (393)) (literal (valuationOf q) (399)) (literal (valuationOf q) (402)) (countLit q [199, 200, 201, 202]) (countLit q [203, 204, 205, 206]) (count401 q) 1 1 (meaning393 q) (meaning399 q) (meaning402 q) hs
  change valuationOf q 393 = false ∨ valuationOf q 399 = false ∨ valuationOf q 402 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause854 (q : Snake 81) (h : Conditions q) : valuation q 393 = false ∨ valuation q 399 = false ∨ valuation q 402 = true := counterClause854 (baseVal q)

theorem counterClause855 (q : Nat → Bool) : valuationOf q 401 = false ∨ valuationOf q 403 = true := by
  have hs : count403 q = (countLit q [191, 192, 193, 194, 195, 197, 198]) + (countLit q [199, 200, 201, 202, 203, 204, 205, 206]) := List.countP_append (p := literal q) (l₁ := [191, 192, 193, 194, 195, 197, 198]) (l₂ := [199, 200, 201, 202, 203, 204, 205, 206])
  have hm := merge_right (literal (valuationOf q) (401)) (literal (valuationOf q) (403)) (countLit q [191, 192, 193, 194, 195, 197, 198]) (countLit q [199, 200, 201, 202, 203, 204, 205, 206]) (count403 q) 1 (meaning401 q) (meaning403 q) hs
  change valuationOf q 401 = false ∨ valuationOf q 403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause855 (q : Snake 81) (h : Conditions q) : valuation q 401 = false ∨ valuation q 403 = true := counterClause855 (baseVal q)

theorem counterClause856 (q : Nat → Bool) : valuationOf q 402 = false ∨ valuationOf q 404 = true := by
  have hs : count403 q = (countLit q [191, 192, 193, 194, 195, 197, 198]) + (countLit q [199, 200, 201, 202, 203, 204, 205, 206]) := List.countP_append (p := literal q) (l₁ := [191, 192, 193, 194, 195, 197, 198]) (l₂ := [199, 200, 201, 202, 203, 204, 205, 206])
  have hm := merge_right (literal (valuationOf q) (402)) (literal (valuationOf q) (404)) (countLit q [191, 192, 193, 194, 195, 197, 198]) (countLit q [199, 200, 201, 202, 203, 204, 205, 206]) (count403 q) 2 (meaning402 q) (meaning404 q) hs
  change valuationOf q 402 = false ∨ valuationOf q 404 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause856 (q : Snake 81) (h : Conditions q) : valuation q 402 = false ∨ valuation q 404 = true := counterClause856 (baseVal q)

theorem counterClause857 (q : Nat → Bool) : valuationOf q 387 = false ∨ valuationOf q 403 = true := by
  have hs : count403 q = (countLit q [191, 192, 193, 194, 195, 197, 198]) + (countLit q [199, 200, 201, 202, 203, 204, 205, 206]) := List.countP_append (p := literal q) (l₁ := [191, 192, 193, 194, 195, 197, 198]) (l₂ := [199, 200, 201, 202, 203, 204, 205, 206])
  have hm := merge_left (literal (valuationOf q) (387)) (literal (valuationOf q) (403)) (countLit q [191, 192, 193, 194, 195, 197, 198]) (countLit q [199, 200, 201, 202, 203, 204, 205, 206]) (count403 q) 1 (meaning387 q) (meaning403 q) hs
  change valuationOf q 387 = false ∨ valuationOf q 403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause857 (q : Snake 81) (h : Conditions q) : valuation q 387 = false ∨ valuation q 403 = true := counterClause857 (baseVal q)

theorem counterClause858 (q : Nat → Bool) : valuationOf q 387 = false ∨ valuationOf q 401 = false ∨ valuationOf q 404 = true := by
  have hs : count403 q = (countLit q [191, 192, 193, 194, 195, 197, 198]) + (countLit q [199, 200, 201, 202, 203, 204, 205, 206]) := List.countP_append (p := literal q) (l₁ := [191, 192, 193, 194, 195, 197, 198]) (l₂ := [199, 200, 201, 202, 203, 204, 205, 206])
  have hm := merge_two (literal (valuationOf q) (387)) (literal (valuationOf q) (401)) (literal (valuationOf q) (404)) (countLit q [191, 192, 193, 194, 195, 197, 198]) (countLit q [199, 200, 201, 202, 203, 204, 205, 206]) (count403 q) 1 1 (meaning387 q) (meaning401 q) (meaning404 q) hs
  change valuationOf q 387 = false ∨ valuationOf q 401 = false ∨ valuationOf q 404 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause858 (q : Snake 81) (h : Conditions q) : valuation q 387 = false ∨ valuation q 401 = false ∨ valuation q 404 = true := counterClause858 (baseVal q)

theorem counterClause859 (q : Nat → Bool) : valuationOf q 388 = false ∨ valuationOf q 404 = true := by
  have hs : count403 q = (countLit q [191, 192, 193, 194, 195, 197, 198]) + (countLit q [199, 200, 201, 202, 203, 204, 205, 206]) := List.countP_append (p := literal q) (l₁ := [191, 192, 193, 194, 195, 197, 198]) (l₂ := [199, 200, 201, 202, 203, 204, 205, 206])
  have hm := merge_left (literal (valuationOf q) (388)) (literal (valuationOf q) (404)) (countLit q [191, 192, 193, 194, 195, 197, 198]) (countLit q [199, 200, 201, 202, 203, 204, 205, 206]) (count403 q) 2 (meaning388 q) (meaning404 q) hs
  change valuationOf q 388 = false ∨ valuationOf q 404 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause859 (q : Snake 81) (h : Conditions q) : valuation q 388 = false ∨ valuation q 404 = true := counterClause859 (baseVal q)

theorem counterClause860 (q : Nat → Bool) : valuationOf q 403 = false ∨ valuationOf q 405 = true := by
  have hs : count405 q = (countLit q [177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) + (countLit q [191, 192, 193, 194, 195, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) := List.countP_append (p := literal q) (l₁ := [177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) (l₂ := [191, 192, 193, 194, 195, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206])
  have hm := merge_right (literal (valuationOf q) (403)) (literal (valuationOf q) (405)) (countLit q [177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) (countLit q [191, 192, 193, 194, 195, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (count405 q) 1 (meaning403 q) (meaning405 q) hs
  change valuationOf q 403 = false ∨ valuationOf q 405 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause860 (q : Snake 81) (h : Conditions q) : valuation q 403 = false ∨ valuation q 405 = true := counterClause860 (baseVal q)

theorem counterClause861 (q : Nat → Bool) : valuationOf q 404 = false ∨ valuationOf q 406 = true := by
  have hs : count405 q = (countLit q [177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) + (countLit q [191, 192, 193, 194, 195, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) := List.countP_append (p := literal q) (l₁ := [177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) (l₂ := [191, 192, 193, 194, 195, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206])
  have hm := merge_right (literal (valuationOf q) (404)) (literal (valuationOf q) (406)) (countLit q [177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) (countLit q [191, 192, 193, 194, 195, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (count405 q) 2 (meaning404 q) (meaning406 q) hs
  change valuationOf q 404 = false ∨ valuationOf q 406 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause861 (q : Snake 81) (h : Conditions q) : valuation q 404 = false ∨ valuation q 406 = true := counterClause861 (baseVal q)

theorem counterClause862 (q : Nat → Bool) : valuationOf q 375 = false ∨ valuationOf q 405 = true := by
  have hs : count405 q = (countLit q [177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) + (countLit q [191, 192, 193, 194, 195, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) := List.countP_append (p := literal q) (l₁ := [177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) (l₂ := [191, 192, 193, 194, 195, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206])
  have hm := merge_left (literal (valuationOf q) (375)) (literal (valuationOf q) (405)) (countLit q [177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) (countLit q [191, 192, 193, 194, 195, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (count405 q) 1 (meaning375 q) (meaning405 q) hs
  change valuationOf q 375 = false ∨ valuationOf q 405 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause862 (q : Snake 81) (h : Conditions q) : valuation q 375 = false ∨ valuation q 405 = true := counterClause862 (baseVal q)

theorem counterClause863 (q : Nat → Bool) : valuationOf q 375 = false ∨ valuationOf q 403 = false ∨ valuationOf q 406 = true := by
  have hs : count405 q = (countLit q [177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) + (countLit q [191, 192, 193, 194, 195, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) := List.countP_append (p := literal q) (l₁ := [177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) (l₂ := [191, 192, 193, 194, 195, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206])
  have hm := merge_two (literal (valuationOf q) (375)) (literal (valuationOf q) (403)) (literal (valuationOf q) (406)) (countLit q [177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) (countLit q [191, 192, 193, 194, 195, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (count405 q) 1 1 (meaning375 q) (meaning403 q) (meaning406 q) hs
  change valuationOf q 375 = false ∨ valuationOf q 403 = false ∨ valuationOf q 406 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause863 (q : Snake 81) (h : Conditions q) : valuation q 375 = false ∨ valuation q 403 = false ∨ valuation q 406 = true := counterClause863 (baseVal q)

theorem counterClause864 (q : Nat → Bool) : valuationOf q 208 = false ∨ valuationOf q 407 = true := by
  have hs : count407 q = (countLit q [208]) + (countLit q [209]) := List.countP_append (p := literal q) (l₁ := [208]) (l₂ := [209])
  have hm := merge_left (literal (valuationOf q) (208)) (literal (valuationOf q) (407)) (countLit q [208]) (countLit q [209]) (count407 q) 1 (meaning208 q) (meaning407 q) hs
  change valuationOf q 208 = false ∨ valuationOf q 407 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause864 (q : Snake 81) (h : Conditions q) : valuation q 208 = false ∨ valuation q 407 = true := counterClause864 (baseVal q)

theorem block26 (q : Snake 81) (h : Conditions q) : B112E158.Block26 (valuation q) :=
  ⟨clause833 q h, clause834 q h, clause835 q h, clause836 q h, clause837 q h, clause838 q h, clause839 q h, clause840 q h, clause841 q h, clause842 q h, clause843 q h, clause844 q h, clause845 q h, clause846 q h, clause847 q h, clause848 q h, clause849 q h, clause850 q h, clause851 q h, clause852 q h, clause853 q h, clause854 q h, clause855 q h, clause856 q h, clause857 q h, clause858 q h, clause859 q h, clause860 q h, clause861 q h, clause862 q h, clause863 q h, clause864 q h⟩

end
end Snake9.Regrowth.E112158
