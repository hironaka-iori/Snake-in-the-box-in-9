import E112064Semantics
import B112E064Inputs
namespace Snake9.Regrowth.E112064
noncomputable section
local instance blockDec26 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause833 (q : Nat → Bool) : valuationOf q 192 = false ∨ valuationOf q 375 = true := by
  have hs : count375 q = (countLit q [191]) + (countLit q [192]) := List.countP_append (p := literal q) (l₁ := [191]) (l₂ := [192])
  have hm := merge_right (literal (valuationOf q) (192)) (literal (valuationOf q) (375)) (countLit q [191]) (countLit q [192]) (count375 q) 1 (meaning192 q) (meaning375 q) hs
  change valuationOf q 192 = false ∨ valuationOf q 375 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause833 (q : Snake 81) (h : Conditions q) : valuation q 192 = false ∨ valuation q 375 = true := counterClause833 (baseVal q)

theorem counterClause834 (q : Nat → Bool) : valuationOf q 375 = false ∨ valuationOf q 377 = true := by
  have hs : count377 q = (countLit q [190]) + (countLit q [191, 192]) := List.countP_append (p := literal q) (l₁ := [190]) (l₂ := [191, 192])
  have hm := merge_right (literal (valuationOf q) (375)) (literal (valuationOf q) (377)) (countLit q [190]) (countLit q [191, 192]) (count377 q) 1 (meaning375 q) (meaning377 q) hs
  change valuationOf q 375 = false ∨ valuationOf q 377 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause834 (q : Snake 81) (h : Conditions q) : valuation q 375 = false ∨ valuation q 377 = true := counterClause834 (baseVal q)

theorem counterClause835 (q : Nat → Bool) : valuationOf q 190 = false ∨ valuationOf q 377 = true := by
  have hs : count377 q = (countLit q [190]) + (countLit q [191, 192]) := List.countP_append (p := literal q) (l₁ := [190]) (l₂ := [191, 192])
  have hm := merge_left (literal (valuationOf q) (190)) (literal (valuationOf q) (377)) (countLit q [190]) (countLit q [191, 192]) (count377 q) 1 (meaning190 q) (meaning377 q) hs
  change valuationOf q 190 = false ∨ valuationOf q 377 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause835 (q : Snake 81) (h : Conditions q) : valuation q 190 = false ∨ valuation q 377 = true := counterClause835 (baseVal q)

theorem counterClause836 (q : Nat → Bool) : valuationOf q 194 = false ∨ valuationOf q 379 = true := by
  have hs : count379 q = (countLit q [193]) + (countLit q [194]) := List.countP_append (p := literal q) (l₁ := [193]) (l₂ := [194])
  have hm := merge_right (literal (valuationOf q) (194)) (literal (valuationOf q) (379)) (countLit q [193]) (countLit q [194]) (count379 q) 1 (meaning194 q) (meaning379 q) hs
  change valuationOf q 194 = false ∨ valuationOf q 379 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause836 (q : Snake 81) (h : Conditions q) : valuation q 194 = false ∨ valuation q 379 = true := counterClause836 (baseVal q)

theorem counterClause837 (q : Nat → Bool) : valuationOf q 196 = false ∨ valuationOf q 381 = true := by
  have hs : count381 q = (countLit q [195]) + (countLit q [196]) := List.countP_append (p := literal q) (l₁ := [195]) (l₂ := [196])
  have hm := merge_right (literal (valuationOf q) (196)) (literal (valuationOf q) (381)) (countLit q [195]) (countLit q [196]) (count381 q) 1 (meaning196 q) (meaning381 q) hs
  change valuationOf q 196 = false ∨ valuationOf q 381 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause837 (q : Snake 81) (h : Conditions q) : valuation q 196 = false ∨ valuation q 381 = true := counterClause837 (baseVal q)

theorem counterClause838 (q : Nat → Bool) : valuationOf q 381 = false ∨ valuationOf q 383 = true := by
  have hs : count383 q = (countLit q [193, 194]) + (countLit q [195, 196]) := List.countP_append (p := literal q) (l₁ := [193, 194]) (l₂ := [195, 196])
  have hm := merge_right (literal (valuationOf q) (381)) (literal (valuationOf q) (383)) (countLit q [193, 194]) (countLit q [195, 196]) (count383 q) 1 (meaning381 q) (meaning383 q) hs
  change valuationOf q 381 = false ∨ valuationOf q 383 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause838 (q : Snake 81) (h : Conditions q) : valuation q 381 = false ∨ valuation q 383 = true := counterClause838 (baseVal q)

theorem counterClause839 (q : Nat → Bool) : valuationOf q 379 = false ∨ valuationOf q 383 = true := by
  have hs : count383 q = (countLit q [193, 194]) + (countLit q [195, 196]) := List.countP_append (p := literal q) (l₁ := [193, 194]) (l₂ := [195, 196])
  have hm := merge_left (literal (valuationOf q) (379)) (literal (valuationOf q) (383)) (countLit q [193, 194]) (countLit q [195, 196]) (count383 q) 1 (meaning379 q) (meaning383 q) hs
  change valuationOf q 379 = false ∨ valuationOf q 383 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause839 (q : Snake 81) (h : Conditions q) : valuation q 379 = false ∨ valuation q 383 = true := counterClause839 (baseVal q)

theorem counterClause840 (q : Nat → Bool) : valuationOf q 383 = false ∨ valuationOf q 385 = true := by
  have hs : count385 q = (countLit q [190, 191, 192]) + (countLit q [193, 194, 195, 196]) := List.countP_append (p := literal q) (l₁ := [190, 191, 192]) (l₂ := [193, 194, 195, 196])
  have hm := merge_right (literal (valuationOf q) (383)) (literal (valuationOf q) (385)) (countLit q [190, 191, 192]) (countLit q [193, 194, 195, 196]) (count385 q) 1 (meaning383 q) (meaning385 q) hs
  change valuationOf q 383 = false ∨ valuationOf q 385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause840 (q : Snake 81) (h : Conditions q) : valuation q 383 = false ∨ valuation q 385 = true := counterClause840 (baseVal q)

theorem counterClause841 (q : Nat → Bool) : valuationOf q 377 = false ∨ valuationOf q 385 = true := by
  have hs : count385 q = (countLit q [190, 191, 192]) + (countLit q [193, 194, 195, 196]) := List.countP_append (p := literal q) (l₁ := [190, 191, 192]) (l₂ := [193, 194, 195, 196])
  have hm := merge_left (literal (valuationOf q) (377)) (literal (valuationOf q) (385)) (countLit q [190, 191, 192]) (countLit q [193, 194, 195, 196]) (count385 q) 1 (meaning377 q) (meaning385 q) hs
  change valuationOf q 377 = false ∨ valuationOf q 385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause841 (q : Snake 81) (h : Conditions q) : valuation q 377 = false ∨ valuation q 385 = true := counterClause841 (baseVal q)

theorem counterClause842 (q : Nat → Bool) : valuationOf q 197 = false ∨ valuationOf q 387 = true := by
  have hs : count387 q = (countLit q [197]) + (countLit q [198]) := List.countP_append (p := literal q) (l₁ := [197]) (l₂ := [198])
  have hm := merge_left (literal (valuationOf q) (197)) (literal (valuationOf q) (387)) (countLit q [197]) (countLit q [198]) (count387 q) 1 (meaning197 q) (meaning387 q) hs
  change valuationOf q 197 = false ∨ valuationOf q 387 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause842 (q : Snake 81) (h : Conditions q) : valuation q 197 = false ∨ valuation q 387 = true := counterClause842 (baseVal q)

theorem counterClause843 (q : Nat → Bool) : valuationOf q 387 = false ∨ valuationOf q 391 = true := by
  have hs : count391 q = (countLit q [197, 198]) + (countLit q [199, 200]) := List.countP_append (p := literal q) (l₁ := [197, 198]) (l₂ := [199, 200])
  have hm := merge_left (literal (valuationOf q) (387)) (literal (valuationOf q) (391)) (countLit q [197, 198]) (countLit q [199, 200]) (count391 q) 1 (meaning387 q) (meaning391 q) hs
  change valuationOf q 387 = false ∨ valuationOf q 391 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause843 (q : Snake 81) (h : Conditions q) : valuation q 387 = false ∨ valuation q 391 = true := counterClause843 (baseVal q)

theorem counterClause844 (q : Nat → Bool) : valuationOf q 202 = false ∨ valuationOf q 393 = true := by
  have hs : count393 q = (countLit q [201]) + (countLit q [202]) := List.countP_append (p := literal q) (l₁ := [201]) (l₂ := [202])
  have hm := merge_right (literal (valuationOf q) (202)) (literal (valuationOf q) (393)) (countLit q [201]) (countLit q [202]) (count393 q) 1 (meaning202 q) (meaning393 q) hs
  change valuationOf q 202 = false ∨ valuationOf q 393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause844 (q : Snake 81) (h : Conditions q) : valuation q 202 = false ∨ valuation q 393 = true := counterClause844 (baseVal q)

theorem counterClause845 (q : Nat → Bool) : valuationOf q 201 = false ∨ valuationOf q 393 = true := by
  have hs : count393 q = (countLit q [201]) + (countLit q [202]) := List.countP_append (p := literal q) (l₁ := [201]) (l₂ := [202])
  have hm := merge_left (literal (valuationOf q) (201)) (literal (valuationOf q) (393)) (countLit q [201]) (countLit q [202]) (count393 q) 1 (meaning201 q) (meaning393 q) hs
  change valuationOf q 201 = false ∨ valuationOf q 393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause845 (q : Snake 81) (h : Conditions q) : valuation q 201 = false ∨ valuation q 393 = true := counterClause845 (baseVal q)

theorem counterClause846 (q : Nat → Bool) : valuationOf q 204 = false ∨ valuationOf q 395 = true := by
  have hs : count395 q = (countLit q [203]) + (countLit q [204]) := List.countP_append (p := literal q) (l₁ := [203]) (l₂ := [204])
  have hm := merge_right (literal (valuationOf q) (204)) (literal (valuationOf q) (395)) (countLit q [203]) (countLit q [204]) (count395 q) 1 (meaning204 q) (meaning395 q) hs
  change valuationOf q 204 = false ∨ valuationOf q 395 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause846 (q : Snake 81) (h : Conditions q) : valuation q 204 = false ∨ valuation q 395 = true := counterClause846 (baseVal q)

theorem counterClause847 (q : Nat → Bool) : valuationOf q 395 = false ∨ valuationOf q 397 = true := by
  have hs : count397 q = (countLit q [201, 202]) + (countLit q [203, 204]) := List.countP_append (p := literal q) (l₁ := [201, 202]) (l₂ := [203, 204])
  have hm := merge_right (literal (valuationOf q) (395)) (literal (valuationOf q) (397)) (countLit q [201, 202]) (countLit q [203, 204]) (count397 q) 1 (meaning395 q) (meaning397 q) hs
  change valuationOf q 395 = false ∨ valuationOf q 397 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause847 (q : Snake 81) (h : Conditions q) : valuation q 395 = false ∨ valuation q 397 = true := counterClause847 (baseVal q)

theorem counterClause848 (q : Nat → Bool) : valuationOf q 393 = false ∨ valuationOf q 397 = true := by
  have hs : count397 q = (countLit q [201, 202]) + (countLit q [203, 204]) := List.countP_append (p := literal q) (l₁ := [201, 202]) (l₂ := [203, 204])
  have hm := merge_left (literal (valuationOf q) (393)) (literal (valuationOf q) (397)) (countLit q [201, 202]) (countLit q [203, 204]) (count397 q) 1 (meaning393 q) (meaning397 q) hs
  change valuationOf q 393 = false ∨ valuationOf q 397 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause848 (q : Snake 81) (h : Conditions q) : valuation q 393 = false ∨ valuation q 397 = true := counterClause848 (baseVal q)

theorem counterClause849 (q : Nat → Bool) : valuationOf q 397 = false ∨ valuationOf q 399 = true := by
  have hs : count399 q = (countLit q [197, 198, 199, 200]) + (countLit q [201, 202, 203, 204]) := List.countP_append (p := literal q) (l₁ := [197, 198, 199, 200]) (l₂ := [201, 202, 203, 204])
  have hm := merge_right (literal (valuationOf q) (397)) (literal (valuationOf q) (399)) (countLit q [197, 198, 199, 200]) (countLit q [201, 202, 203, 204]) (count399 q) 1 (meaning397 q) (meaning399 q) hs
  change valuationOf q 397 = false ∨ valuationOf q 399 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause849 (q : Snake 81) (h : Conditions q) : valuation q 397 = false ∨ valuation q 399 = true := counterClause849 (baseVal q)

theorem counterClause850 (q : Nat → Bool) : valuationOf q 391 = false ∨ valuationOf q 399 = true := by
  have hs : count399 q = (countLit q [197, 198, 199, 200]) + (countLit q [201, 202, 203, 204]) := List.countP_append (p := literal q) (l₁ := [197, 198, 199, 200]) (l₂ := [201, 202, 203, 204])
  have hm := merge_left (literal (valuationOf q) (391)) (literal (valuationOf q) (399)) (countLit q [197, 198, 199, 200]) (countLit q [201, 202, 203, 204]) (count399 q) 1 (meaning391 q) (meaning399 q) hs
  change valuationOf q 391 = false ∨ valuationOf q 399 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause850 (q : Snake 81) (h : Conditions q) : valuation q 391 = false ∨ valuation q 399 = true := counterClause850 (baseVal q)

theorem counterClause851 (q : Nat → Bool) : valuationOf q 399 = false ∨ valuationOf q 401 = true := by
  have hs : count401 q = (countLit q [190, 191, 192, 193, 194, 195, 196]) + (countLit q [197, 198, 199, 200, 201, 202, 203, 204]) := List.countP_append (p := literal q) (l₁ := [190, 191, 192, 193, 194, 195, 196]) (l₂ := [197, 198, 199, 200, 201, 202, 203, 204])
  have hm := merge_right (literal (valuationOf q) (399)) (literal (valuationOf q) (401)) (countLit q [190, 191, 192, 193, 194, 195, 196]) (countLit q [197, 198, 199, 200, 201, 202, 203, 204]) (count401 q) 1 (meaning399 q) (meaning401 q) hs
  change valuationOf q 399 = false ∨ valuationOf q 401 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause851 (q : Snake 81) (h : Conditions q) : valuation q 399 = false ∨ valuation q 401 = true := counterClause851 (baseVal q)

theorem counterClause852 (q : Nat → Bool) : valuationOf q 385 = false ∨ valuationOf q 401 = true := by
  have hs : count401 q = (countLit q [190, 191, 192, 193, 194, 195, 196]) + (countLit q [197, 198, 199, 200, 201, 202, 203, 204]) := List.countP_append (p := literal q) (l₁ := [190, 191, 192, 193, 194, 195, 196]) (l₂ := [197, 198, 199, 200, 201, 202, 203, 204])
  have hm := merge_left (literal (valuationOf q) (385)) (literal (valuationOf q) (401)) (countLit q [190, 191, 192, 193, 194, 195, 196]) (countLit q [197, 198, 199, 200, 201, 202, 203, 204]) (count401 q) 1 (meaning385 q) (meaning401 q) hs
  change valuationOf q 385 = false ∨ valuationOf q 401 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause852 (q : Snake 81) (h : Conditions q) : valuation q 385 = false ∨ valuation q 401 = true := counterClause852 (baseVal q)

theorem counterClause853 (q : Nat → Bool) : valuationOf q 401 = false ∨ valuationOf q 403 = true := by
  have hs : count403 q = (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189]) + (countLit q [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]) := List.countP_append (p := literal q) (l₁ := [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189]) (l₂ := [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204])
  have hm := merge_right (literal (valuationOf q) (401)) (literal (valuationOf q) (403)) (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189]) (countLit q [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]) (count403 q) 1 (meaning401 q) (meaning403 q) hs
  change valuationOf q 401 = false ∨ valuationOf q 403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause853 (q : Snake 81) (h : Conditions q) : valuation q 401 = false ∨ valuation q 403 = true := counterClause853 (baseVal q)

theorem counterClause854 (q : Nat → Bool) : valuationOf q 373 = false ∨ valuationOf q 403 = true := by
  have hs : count403 q = (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189]) + (countLit q [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]) := List.countP_append (p := literal q) (l₁ := [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189]) (l₂ := [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204])
  have hm := merge_left (literal (valuationOf q) (373)) (literal (valuationOf q) (403)) (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189]) (countLit q [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]) (count403 q) 1 (meaning373 q) (meaning403 q) hs
  change valuationOf q 373 = false ∨ valuationOf q 403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause854 (q : Snake 81) (h : Conditions q) : valuation q 373 = false ∨ valuation q 403 = true := counterClause854 (baseVal q)

theorem counterClause855 (q : Nat → Bool) : valuationOf q 373 = false ∨ valuationOf q 401 = false ∨ valuationOf q 404 = true := by
  have hs : count403 q = (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189]) + (countLit q [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]) := List.countP_append (p := literal q) (l₁ := [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189]) (l₂ := [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204])
  have hm := merge_two (literal (valuationOf q) (373)) (literal (valuationOf q) (401)) (literal (valuationOf q) (404)) (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189]) (countLit q [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]) (count403 q) 1 1 (meaning373 q) (meaning401 q) (meaning404 q) hs
  change valuationOf q 373 = false ∨ valuationOf q 401 = false ∨ valuationOf q 404 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause855 (q : Snake 81) (h : Conditions q) : valuation q 373 = false ∨ valuation q 401 = false ∨ valuation q 404 = true := counterClause855 (baseVal q)

theorem counterClause856 (q : Nat → Bool) : valuationOf q 374 = false ∨ valuationOf q 404 = true := by
  have hs : count403 q = (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189]) + (countLit q [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]) := List.countP_append (p := literal q) (l₁ := [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189]) (l₂ := [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204])
  have hm := merge_left (literal (valuationOf q) (374)) (literal (valuationOf q) (404)) (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189]) (countLit q [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]) (count403 q) 2 (meaning374 q) (meaning404 q) hs
  change valuationOf q 374 = false ∨ valuationOf q 404 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause856 (q : Snake 81) (h : Conditions q) : valuation q 374 = false ∨ valuation q 404 = true := counterClause856 (baseVal q)

theorem counterClause857 (q : Nat → Bool) : valuationOf q 205 = false ∨ valuationOf q 407 = true := by
  have hs : count407 q = (countLit q [205]) + (countLit q [206, 207]) := List.countP_append (p := literal q) (l₁ := [205]) (l₂ := [206, 207])
  have hm := merge_left (literal (valuationOf q) (205)) (literal (valuationOf q) (407)) (countLit q [205]) (countLit q [206, 207]) (count407 q) 1 (meaning205 q) (meaning407 q) hs
  change valuationOf q 205 = false ∨ valuationOf q 407 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause857 (q : Snake 81) (h : Conditions q) : valuation q 205 = false ∨ valuation q 407 = true := counterClause857 (baseVal q)

theorem counterClause858 (q : Nat → Bool) : valuationOf q 211 = false ∨ valuationOf q 411 = true := by
  have hs : count411 q = (countLit q [210]) + (countLit q [211]) := List.countP_append (p := literal q) (l₁ := [210]) (l₂ := [211])
  have hm := merge_right (literal (valuationOf q) (211)) (literal (valuationOf q) (411)) (countLit q [210]) (countLit q [211]) (count411 q) 1 (meaning211 q) (meaning411 q) hs
  change valuationOf q 211 = false ∨ valuationOf q 411 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause858 (q : Snake 81) (h : Conditions q) : valuation q 211 = false ∨ valuation q 411 = true := counterClause858 (baseVal q)

theorem counterClause859 (q : Nat → Bool) : valuationOf q 210 = false ∨ valuationOf q 411 = true := by
  have hs : count411 q = (countLit q [210]) + (countLit q [211]) := List.countP_append (p := literal q) (l₁ := [210]) (l₂ := [211])
  have hm := merge_left (literal (valuationOf q) (210)) (literal (valuationOf q) (411)) (countLit q [210]) (countLit q [211]) (count411 q) 1 (meaning210 q) (meaning411 q) hs
  change valuationOf q 210 = false ∨ valuationOf q 411 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause859 (q : Snake 81) (h : Conditions q) : valuation q 210 = false ∨ valuation q 411 = true := counterClause859 (baseVal q)

theorem counterClause860 (q : Nat → Bool) : valuationOf q 411 = false ∨ valuationOf q 413 = true := by
  have hs : count413 q = (countLit q [208, 209]) + (countLit q [210, 211]) := List.countP_append (p := literal q) (l₁ := [208, 209]) (l₂ := [210, 211])
  have hm := merge_right (literal (valuationOf q) (411)) (literal (valuationOf q) (413)) (countLit q [208, 209]) (countLit q [210, 211]) (count413 q) 1 (meaning411 q) (meaning413 q) hs
  change valuationOf q 411 = false ∨ valuationOf q 413 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause860 (q : Snake 81) (h : Conditions q) : valuation q 411 = false ∨ valuation q 413 = true := counterClause860 (baseVal q)

theorem counterClause861 (q : Nat → Bool) : valuationOf q 413 = false ∨ valuationOf q 415 = true := by
  have hs : count415 q = (countLit q [205, 206, 207]) + (countLit q [208, 209, 210, 211]) := List.countP_append (p := literal q) (l₁ := [205, 206, 207]) (l₂ := [208, 209, 210, 211])
  have hm := merge_right (literal (valuationOf q) (413)) (literal (valuationOf q) (415)) (countLit q [205, 206, 207]) (countLit q [208, 209, 210, 211]) (count415 q) 1 (meaning413 q) (meaning415 q) hs
  change valuationOf q 413 = false ∨ valuationOf q 415 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause861 (q : Snake 81) (h : Conditions q) : valuation q 413 = false ∨ valuation q 415 = true := counterClause861 (baseVal q)

theorem counterClause862 (q : Nat → Bool) : valuationOf q 407 = false ∨ valuationOf q 415 = true := by
  have hs : count415 q = (countLit q [205, 206, 207]) + (countLit q [208, 209, 210, 211]) := List.countP_append (p := literal q) (l₁ := [205, 206, 207]) (l₂ := [208, 209, 210, 211])
  have hm := merge_left (literal (valuationOf q) (407)) (literal (valuationOf q) (415)) (countLit q [205, 206, 207]) (countLit q [208, 209, 210, 211]) (count415 q) 1 (meaning407 q) (meaning415 q) hs
  change valuationOf q 407 = false ∨ valuationOf q 415 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause862 (q : Snake 81) (h : Conditions q) : valuation q 407 = false ∨ valuation q 415 = true := counterClause862 (baseVal q)

theorem counterClause863 (q : Nat → Bool) : valuationOf q 215 = false ∨ valuationOf q 417 = true := by
  have hs : count417 q = (countLit q [213]) + (countLit q [215]) := List.countP_append (p := literal q) (l₁ := [213]) (l₂ := [215])
  have hm := merge_right (literal (valuationOf q) (215)) (literal (valuationOf q) (417)) (countLit q [213]) (countLit q [215]) (count417 q) 1 (meaning215 q) (meaning417 q) hs
  change valuationOf q 215 = false ∨ valuationOf q 417 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause863 (q : Snake 81) (h : Conditions q) : valuation q 215 = false ∨ valuation q 417 = true := counterClause863 (baseVal q)

theorem counterClause864 (q : Nat → Bool) : valuationOf q 417 = false ∨ valuationOf q 419 = true := by
  have hs : count419 q = (countLit q [212]) + (countLit q [213, 215]) := List.countP_append (p := literal q) (l₁ := [212]) (l₂ := [213, 215])
  have hm := merge_right (literal (valuationOf q) (417)) (literal (valuationOf q) (419)) (countLit q [212]) (countLit q [213, 215]) (count419 q) 1 (meaning417 q) (meaning419 q) hs
  change valuationOf q 417 = false ∨ valuationOf q 419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause864 (q : Snake 81) (h : Conditions q) : valuation q 417 = false ∨ valuation q 419 = true := counterClause864 (baseVal q)

theorem block26 (q : Snake 81) (h : Conditions q) : B112E064.Block26 (valuation q) :=
  ⟨clause833 q h, clause834 q h, clause835 q h, clause836 q h, clause837 q h, clause838 q h, clause839 q h, clause840 q h, clause841 q h, clause842 q h, clause843 q h, clause844 q h, clause845 q h, clause846 q h, clause847 q h, clause848 q h, clause849 q h, clause850 q h, clause851 q h, clause852 q h, clause853 q h, clause854 q h, clause855 q h, clause856 q h, clause857 q h, clause858 q h, clause859 q h, clause860 q h, clause861 q h, clause862 q h, clause863 q h, clause864 q h⟩

end
end Snake9.Regrowth.E112064
