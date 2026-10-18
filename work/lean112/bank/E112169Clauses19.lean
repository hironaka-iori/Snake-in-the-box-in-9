import E112169Semantics
import B112E169Inputs
namespace Snake9.Regrowth.E112169
noncomputable section
local instance blockDec19 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause609 (q : Nat → Bool) : valuationOf q 194 = false ∨ valuationOf q 377 = true := by
  have hs : count377 q = (countLit q [194]) + (countLit q [195]) := List.countP_append (p := literal q) (l₁ := [194]) (l₂ := [195])
  have hm := merge_left (literal (valuationOf q) (194)) (literal (valuationOf q) (377)) (countLit q [194]) (countLit q [195]) (count377 q) 1 (meaning194 q) (meaning377 q) hs
  change valuationOf q 194 = false ∨ valuationOf q 377 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause609 (q : Snake 81) (h : Conditions q) : valuation q 194 = false ∨ valuation q 377 = true := counterClause609 (baseVal q)

theorem counterClause610 (q : Nat → Bool) : valuationOf q 377 = false ∨ valuationOf q 379 = true := by
  have hs : count379 q = (countLit q [192, 193]) + (countLit q [194, 195]) := List.countP_append (p := literal q) (l₁ := [192, 193]) (l₂ := [194, 195])
  have hm := merge_right (literal (valuationOf q) (377)) (literal (valuationOf q) (379)) (countLit q [192, 193]) (countLit q [194, 195]) (count379 q) 1 (meaning377 q) (meaning379 q) hs
  change valuationOf q 377 = false ∨ valuationOf q 379 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause610 (q : Snake 81) (h : Conditions q) : valuation q 377 = false ∨ valuation q 379 = true := counterClause610 (baseVal q)

theorem counterClause611 (q : Nat → Bool) : valuationOf q 375 = false ∨ valuationOf q 379 = true := by
  have hs : count379 q = (countLit q [192, 193]) + (countLit q [194, 195]) := List.countP_append (p := literal q) (l₁ := [192, 193]) (l₂ := [194, 195])
  have hm := merge_left (literal (valuationOf q) (375)) (literal (valuationOf q) (379)) (countLit q [192, 193]) (countLit q [194, 195]) (count379 q) 1 (meaning375 q) (meaning379 q) hs
  change valuationOf q 375 = false ∨ valuationOf q 379 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause611 (q : Snake 81) (h : Conditions q) : valuation q 375 = false ∨ valuation q 379 = true := counterClause611 (baseVal q)

theorem counterClause612 (q : Nat → Bool) : valuationOf q 379 = false ∨ valuationOf q 381 = true := by
  have hs : count381 q = (countLit q [189, 190, 191]) + (countLit q [192, 193, 194, 195]) := List.countP_append (p := literal q) (l₁ := [189, 190, 191]) (l₂ := [192, 193, 194, 195])
  have hm := merge_right (literal (valuationOf q) (379)) (literal (valuationOf q) (381)) (countLit q [189, 190, 191]) (countLit q [192, 193, 194, 195]) (count381 q) 1 (meaning379 q) (meaning381 q) hs
  change valuationOf q 379 = false ∨ valuationOf q 381 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause612 (q : Snake 81) (h : Conditions q) : valuation q 379 = false ∨ valuation q 381 = true := counterClause612 (baseVal q)

theorem counterClause613 (q : Nat → Bool) : valuationOf q 199 = false ∨ valuationOf q 385 = true := by
  have hs : count385 q = (countLit q [198]) + (countLit q [199]) := List.countP_append (p := literal q) (l₁ := [198]) (l₂ := [199])
  have hm := merge_right (literal (valuationOf q) (199)) (literal (valuationOf q) (385)) (countLit q [198]) (countLit q [199]) (count385 q) 1 (meaning199 q) (meaning385 q) hs
  change valuationOf q 199 = false ∨ valuationOf q 385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause613 (q : Snake 81) (h : Conditions q) : valuation q 199 = false ∨ valuation q 385 = true := counterClause613 (baseVal q)

theorem counterClause614 (q : Nat → Bool) : valuationOf q 385 = false ∨ valuationOf q 387 = true := by
  have hs : count387 q = (countLit q [196, 197]) + (countLit q [198, 199]) := List.countP_append (p := literal q) (l₁ := [196, 197]) (l₂ := [198, 199])
  have hm := merge_right (literal (valuationOf q) (385)) (literal (valuationOf q) (387)) (countLit q [196, 197]) (countLit q [198, 199]) (count387 q) 1 (meaning385 q) (meaning387 q) hs
  change valuationOf q 385 = false ∨ valuationOf q 387 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause614 (q : Snake 81) (h : Conditions q) : valuation q 385 = false ∨ valuation q 387 = true := counterClause614 (baseVal q)

theorem counterClause615 (q : Nat → Bool) : valuationOf q 201 = false ∨ valuationOf q 389 = true := by
  have hs : count389 q = (countLit q [200]) + (countLit q [201]) := List.countP_append (p := literal q) (l₁ := [200]) (l₂ := [201])
  have hm := merge_right (literal (valuationOf q) (201)) (literal (valuationOf q) (389)) (countLit q [200]) (countLit q [201]) (count389 q) 1 (meaning201 q) (meaning389 q) hs
  change valuationOf q 201 = false ∨ valuationOf q 389 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause615 (q : Snake 81) (h : Conditions q) : valuation q 201 = false ∨ valuation q 389 = true := counterClause615 (baseVal q)

theorem counterClause616 (q : Nat → Bool) : valuationOf q 202 = false ∨ valuationOf q 391 = true := by
  have hs : count391 q = (countLit q [202]) + (countLit q [203]) := List.countP_append (p := literal q) (l₁ := [202]) (l₂ := [203])
  have hm := merge_left (literal (valuationOf q) (202)) (literal (valuationOf q) (391)) (countLit q [202]) (countLit q [203]) (count391 q) 1 (meaning202 q) (meaning391 q) hs
  change valuationOf q 202 = false ∨ valuationOf q 391 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause616 (q : Snake 81) (h : Conditions q) : valuation q 202 = false ∨ valuation q 391 = true := counterClause616 (baseVal q)

theorem counterClause617 (q : Nat → Bool) : valuationOf q 391 = false ∨ valuationOf q 393 = true := by
  have hs : count393 q = (countLit q [200, 201]) + (countLit q [202, 203]) := List.countP_append (p := literal q) (l₁ := [200, 201]) (l₂ := [202, 203])
  have hm := merge_right (literal (valuationOf q) (391)) (literal (valuationOf q) (393)) (countLit q [200, 201]) (countLit q [202, 203]) (count393 q) 1 (meaning391 q) (meaning393 q) hs
  change valuationOf q 391 = false ∨ valuationOf q 393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause617 (q : Snake 81) (h : Conditions q) : valuation q 391 = false ∨ valuation q 393 = true := counterClause617 (baseVal q)

theorem counterClause618 (q : Nat → Bool) : valuationOf q 389 = false ∨ valuationOf q 393 = true := by
  have hs : count393 q = (countLit q [200, 201]) + (countLit q [202, 203]) := List.countP_append (p := literal q) (l₁ := [200, 201]) (l₂ := [202, 203])
  have hm := merge_left (literal (valuationOf q) (389)) (literal (valuationOf q) (393)) (countLit q [200, 201]) (countLit q [202, 203]) (count393 q) 1 (meaning389 q) (meaning393 q) hs
  change valuationOf q 389 = false ∨ valuationOf q 393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause618 (q : Snake 81) (h : Conditions q) : valuation q 389 = false ∨ valuation q 393 = true := counterClause618 (baseVal q)

theorem counterClause619 (q : Nat → Bool) : valuationOf q 393 = false ∨ valuationOf q 395 = true := by
  have hs : count395 q = (countLit q [196, 197, 198, 199]) + (countLit q [200, 201, 202, 203]) := List.countP_append (p := literal q) (l₁ := [196, 197, 198, 199]) (l₂ := [200, 201, 202, 203])
  have hm := merge_right (literal (valuationOf q) (393)) (literal (valuationOf q) (395)) (countLit q [196, 197, 198, 199]) (countLit q [200, 201, 202, 203]) (count395 q) 1 (meaning393 q) (meaning395 q) hs
  change valuationOf q 393 = false ∨ valuationOf q 395 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause619 (q : Snake 81) (h : Conditions q) : valuation q 393 = false ∨ valuation q 395 = true := counterClause619 (baseVal q)

theorem counterClause620 (q : Nat → Bool) : valuationOf q 387 = false ∨ valuationOf q 395 = true := by
  have hs : count395 q = (countLit q [196, 197, 198, 199]) + (countLit q [200, 201, 202, 203]) := List.countP_append (p := literal q) (l₁ := [196, 197, 198, 199]) (l₂ := [200, 201, 202, 203])
  have hm := merge_left (literal (valuationOf q) (387)) (literal (valuationOf q) (395)) (countLit q [196, 197, 198, 199]) (countLit q [200, 201, 202, 203]) (count395 q) 1 (meaning387 q) (meaning395 q) hs
  change valuationOf q 387 = false ∨ valuationOf q 395 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause620 (q : Snake 81) (h : Conditions q) : valuation q 387 = false ∨ valuation q 395 = true := counterClause620 (baseVal q)

theorem counterClause621 (q : Nat → Bool) : valuationOf q 395 = false ∨ valuationOf q 397 = true := by
  have hs : count397 q = (countLit q [189, 190, 191, 192, 193, 194, 195]) + (countLit q [196, 197, 198, 199, 200, 201, 202, 203]) := List.countP_append (p := literal q) (l₁ := [189, 190, 191, 192, 193, 194, 195]) (l₂ := [196, 197, 198, 199, 200, 201, 202, 203])
  have hm := merge_right (literal (valuationOf q) (395)) (literal (valuationOf q) (397)) (countLit q [189, 190, 191, 192, 193, 194, 195]) (countLit q [196, 197, 198, 199, 200, 201, 202, 203]) (count397 q) 1 (meaning395 q) (meaning397 q) hs
  change valuationOf q 395 = false ∨ valuationOf q 397 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause621 (q : Snake 81) (h : Conditions q) : valuation q 395 = false ∨ valuation q 397 = true := counterClause621 (baseVal q)

theorem counterClause622 (q : Nat → Bool) : valuationOf q 381 = false ∨ valuationOf q 397 = true := by
  have hs : count397 q = (countLit q [189, 190, 191, 192, 193, 194, 195]) + (countLit q [196, 197, 198, 199, 200, 201, 202, 203]) := List.countP_append (p := literal q) (l₁ := [189, 190, 191, 192, 193, 194, 195]) (l₂ := [196, 197, 198, 199, 200, 201, 202, 203])
  have hm := merge_left (literal (valuationOf q) (381)) (literal (valuationOf q) (397)) (countLit q [189, 190, 191, 192, 193, 194, 195]) (countLit q [196, 197, 198, 199, 200, 201, 202, 203]) (count397 q) 1 (meaning381 q) (meaning397 q) hs
  change valuationOf q 381 = false ∨ valuationOf q 397 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause622 (q : Snake 81) (h : Conditions q) : valuation q 381 = false ∨ valuation q 397 = true := counterClause622 (baseVal q)

theorem counterClause623 (q : Nat → Bool) : valuationOf q 397 = false ∨ valuationOf q 399 = true := by
  have hs : count399 q = (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188]) + (countLit q [189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203]) := List.countP_append (p := literal q) (l₁ := [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188]) (l₂ := [189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203])
  have hm := merge_right (literal (valuationOf q) (397)) (literal (valuationOf q) (399)) (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188]) (countLit q [189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203]) (count399 q) 1 (meaning397 q) (meaning399 q) hs
  change valuationOf q 397 = false ∨ valuationOf q 399 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause623 (q : Snake 81) (h : Conditions q) : valuation q 397 = false ∨ valuation q 399 = true := counterClause623 (baseVal q)

theorem counterClause624 (q : Nat → Bool) : valuationOf q 369 = false ∨ valuationOf q 399 = true := by
  have hs : count399 q = (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188]) + (countLit q [189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203]) := List.countP_append (p := literal q) (l₁ := [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188]) (l₂ := [189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203])
  have hm := merge_left (literal (valuationOf q) (369)) (literal (valuationOf q) (399)) (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188]) (countLit q [189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203]) (count399 q) 1 (meaning369 q) (meaning399 q) hs
  change valuationOf q 369 = false ∨ valuationOf q 399 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause624 (q : Snake 81) (h : Conditions q) : valuation q 369 = false ∨ valuation q 399 = true := counterClause624 (baseVal q)

theorem counterClause625 (q : Nat → Bool) : valuationOf q 369 = false ∨ valuationOf q 397 = false ∨ valuationOf q 400 = true := by
  have hs : count399 q = (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188]) + (countLit q [189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203]) := List.countP_append (p := literal q) (l₁ := [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188]) (l₂ := [189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203])
  have hm := merge_two (literal (valuationOf q) (369)) (literal (valuationOf q) (397)) (literal (valuationOf q) (400)) (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188]) (countLit q [189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203]) (count399 q) 1 1 (meaning369 q) (meaning397 q) (meaning400 q) hs
  change valuationOf q 369 = false ∨ valuationOf q 397 = false ∨ valuationOf q 400 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause625 (q : Snake 81) (h : Conditions q) : valuation q 369 = false ∨ valuation q 397 = false ∨ valuation q 400 = true := counterClause625 (baseVal q)

theorem counterClause626 (q : Nat → Bool) : valuationOf q 370 = false ∨ valuationOf q 400 = true := by
  have hs : count399 q = (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188]) + (countLit q [189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203]) := List.countP_append (p := literal q) (l₁ := [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188]) (l₂ := [189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203])
  have hm := merge_left (literal (valuationOf q) (370)) (literal (valuationOf q) (400)) (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188]) (countLit q [189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203]) (count399 q) 2 (meaning370 q) (meaning400 q) hs
  change valuationOf q 370 = false ∨ valuationOf q 400 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause626 (q : Snake 81) (h : Conditions q) : valuation q 370 = false ∨ valuation q 400 = true := counterClause626 (baseVal q)

theorem counterClause627 (q : Nat → Bool) : valuationOf q 204 = false ∨ valuationOf q 403 = true := by
  have hs : count403 q = (countLit q [204]) + (countLit q [205, 206]) := List.countP_append (p := literal q) (l₁ := [204]) (l₂ := [205, 206])
  have hm := merge_left (literal (valuationOf q) (204)) (literal (valuationOf q) (403)) (countLit q [204]) (countLit q [205, 206]) (count403 q) 1 (meaning204 q) (meaning403 q) hs
  change valuationOf q 204 = false ∨ valuationOf q 403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause627 (q : Snake 81) (h : Conditions q) : valuation q 204 = false ∨ valuation q 403 = true := counterClause627 (baseVal q)

theorem counterClause628 (q : Nat → Bool) : valuationOf q 207 = false ∨ valuationOf q 405 = true := by
  have hs : count405 q = (countLit q [207]) + (countLit q [208]) := List.countP_append (p := literal q) (l₁ := [207]) (l₂ := [208])
  have hm := merge_left (literal (valuationOf q) (207)) (literal (valuationOf q) (405)) (countLit q [207]) (countLit q [208]) (count405 q) 1 (meaning207 q) (meaning405 q) hs
  change valuationOf q 207 = false ∨ valuationOf q 405 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause628 (q : Snake 81) (h : Conditions q) : valuation q 207 = false ∨ valuation q 405 = true := counterClause628 (baseVal q)

theorem counterClause629 (q : Nat → Bool) : valuationOf q 210 = false ∨ valuationOf q 407 = true := by
  have hs : count407 q = (countLit q [209]) + (countLit q [210]) := List.countP_append (p := literal q) (l₁ := [209]) (l₂ := [210])
  have hm := merge_right (literal (valuationOf q) (210)) (literal (valuationOf q) (407)) (countLit q [209]) (countLit q [210]) (count407 q) 1 (meaning210 q) (meaning407 q) hs
  change valuationOf q 210 = false ∨ valuationOf q 407 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause629 (q : Snake 81) (h : Conditions q) : valuation q 210 = false ∨ valuation q 407 = true := counterClause629 (baseVal q)

theorem counterClause630 (q : Nat → Bool) : valuationOf q 209 = false ∨ valuationOf q 407 = true := by
  have hs : count407 q = (countLit q [209]) + (countLit q [210]) := List.countP_append (p := literal q) (l₁ := [209]) (l₂ := [210])
  have hm := merge_left (literal (valuationOf q) (209)) (literal (valuationOf q) (407)) (countLit q [209]) (countLit q [210]) (count407 q) 1 (meaning209 q) (meaning407 q) hs
  change valuationOf q 209 = false ∨ valuationOf q 407 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause630 (q : Snake 81) (h : Conditions q) : valuation q 209 = false ∨ valuation q 407 = true := counterClause630 (baseVal q)

theorem counterClause631 (q : Nat → Bool) : valuationOf q 209 = false ∨ valuationOf q 210 = false ∨ valuationOf q 408 = true := by
  have hs : count407 q = (countLit q [209]) + (countLit q [210]) := List.countP_append (p := literal q) (l₁ := [209]) (l₂ := [210])
  have hm := merge_two (literal (valuationOf q) (209)) (literal (valuationOf q) (210)) (literal (valuationOf q) (408)) (countLit q [209]) (countLit q [210]) (count407 q) 1 1 (meaning209 q) (meaning210 q) (meaning408 q) hs
  change valuationOf q 209 = false ∨ valuationOf q 210 = false ∨ valuationOf q 408 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause631 (q : Snake 81) (h : Conditions q) : valuation q 209 = false ∨ valuation q 210 = false ∨ valuation q 408 = true := counterClause631 (baseVal q)

theorem counterClause632 (q : Nat → Bool) : valuationOf q 407 = false ∨ valuationOf q 409 = true := by
  have hs : count409 q = (countLit q [207, 208]) + (countLit q [209, 210]) := List.countP_append (p := literal q) (l₁ := [207, 208]) (l₂ := [209, 210])
  have hm := merge_right (literal (valuationOf q) (407)) (literal (valuationOf q) (409)) (countLit q [207, 208]) (countLit q [209, 210]) (count409 q) 1 (meaning407 q) (meaning409 q) hs
  change valuationOf q 407 = false ∨ valuationOf q 409 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause632 (q : Snake 81) (h : Conditions q) : valuation q 407 = false ∨ valuation q 409 = true := counterClause632 (baseVal q)

theorem counterClause633 (q : Nat → Bool) : valuationOf q 408 = false ∨ valuationOf q 410 = true := by
  have hs : count409 q = (countLit q [207, 208]) + (countLit q [209, 210]) := List.countP_append (p := literal q) (l₁ := [207, 208]) (l₂ := [209, 210])
  have hm := merge_right (literal (valuationOf q) (408)) (literal (valuationOf q) (410)) (countLit q [207, 208]) (countLit q [209, 210]) (count409 q) 2 (meaning408 q) (meaning410 q) hs
  change valuationOf q 408 = false ∨ valuationOf q 410 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause633 (q : Snake 81) (h : Conditions q) : valuation q 408 = false ∨ valuation q 410 = true := counterClause633 (baseVal q)

theorem counterClause634 (q : Nat → Bool) : valuationOf q 405 = false ∨ valuationOf q 409 = true := by
  have hs : count409 q = (countLit q [207, 208]) + (countLit q [209, 210]) := List.countP_append (p := literal q) (l₁ := [207, 208]) (l₂ := [209, 210])
  have hm := merge_left (literal (valuationOf q) (405)) (literal (valuationOf q) (409)) (countLit q [207, 208]) (countLit q [209, 210]) (count409 q) 1 (meaning405 q) (meaning409 q) hs
  change valuationOf q 405 = false ∨ valuationOf q 409 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause634 (q : Snake 81) (h : Conditions q) : valuation q 405 = false ∨ valuation q 409 = true := counterClause634 (baseVal q)

theorem counterClause635 (q : Nat → Bool) : valuationOf q 409 = false ∨ valuationOf q 411 = true := by
  have hs : count411 q = (countLit q [204, 205, 206]) + (countLit q [207, 208, 209, 210]) := List.countP_append (p := literal q) (l₁ := [204, 205, 206]) (l₂ := [207, 208, 209, 210])
  have hm := merge_right (literal (valuationOf q) (409)) (literal (valuationOf q) (411)) (countLit q [204, 205, 206]) (countLit q [207, 208, 209, 210]) (count411 q) 1 (meaning409 q) (meaning411 q) hs
  change valuationOf q 409 = false ∨ valuationOf q 411 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause635 (q : Snake 81) (h : Conditions q) : valuation q 409 = false ∨ valuation q 411 = true := counterClause635 (baseVal q)

theorem counterClause636 (q : Nat → Bool) : valuationOf q 410 = false ∨ valuationOf q 412 = true := by
  have hs : count411 q = (countLit q [204, 205, 206]) + (countLit q [207, 208, 209, 210]) := List.countP_append (p := literal q) (l₁ := [204, 205, 206]) (l₂ := [207, 208, 209, 210])
  have hm := merge_right (literal (valuationOf q) (410)) (literal (valuationOf q) (412)) (countLit q [204, 205, 206]) (countLit q [207, 208, 209, 210]) (count411 q) 2 (meaning410 q) (meaning412 q) hs
  change valuationOf q 410 = false ∨ valuationOf q 412 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause636 (q : Snake 81) (h : Conditions q) : valuation q 410 = false ∨ valuation q 412 = true := counterClause636 (baseVal q)

theorem counterClause637 (q : Nat → Bool) : valuationOf q 403 = false ∨ valuationOf q 411 = true := by
  have hs : count411 q = (countLit q [204, 205, 206]) + (countLit q [207, 208, 209, 210]) := List.countP_append (p := literal q) (l₁ := [204, 205, 206]) (l₂ := [207, 208, 209, 210])
  have hm := merge_left (literal (valuationOf q) (403)) (literal (valuationOf q) (411)) (countLit q [204, 205, 206]) (countLit q [207, 208, 209, 210]) (count411 q) 1 (meaning403 q) (meaning411 q) hs
  change valuationOf q 403 = false ∨ valuationOf q 411 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause637 (q : Snake 81) (h : Conditions q) : valuation q 403 = false ∨ valuation q 411 = true := counterClause637 (baseVal q)

theorem counterClause638 (q : Nat → Bool) : valuationOf q 403 = false ∨ valuationOf q 409 = false ∨ valuationOf q 412 = true := by
  have hs : count411 q = (countLit q [204, 205, 206]) + (countLit q [207, 208, 209, 210]) := List.countP_append (p := literal q) (l₁ := [204, 205, 206]) (l₂ := [207, 208, 209, 210])
  have hm := merge_two (literal (valuationOf q) (403)) (literal (valuationOf q) (409)) (literal (valuationOf q) (412)) (countLit q [204, 205, 206]) (countLit q [207, 208, 209, 210]) (count411 q) 1 1 (meaning403 q) (meaning409 q) (meaning412 q) hs
  change valuationOf q 403 = false ∨ valuationOf q 409 = false ∨ valuationOf q 412 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause638 (q : Snake 81) (h : Conditions q) : valuation q 403 = false ∨ valuation q 409 = false ∨ valuation q 412 = true := counterClause638 (baseVal q)

theorem counterClause639 (q : Nat → Bool) : valuationOf q 213 = false ∨ valuationOf q 413 = true := by
  have hs : count413 q = (countLit q [212]) + (countLit q [213]) := List.countP_append (p := literal q) (l₁ := [212]) (l₂ := [213])
  have hm := merge_right (literal (valuationOf q) (213)) (literal (valuationOf q) (413)) (countLit q [212]) (countLit q [213]) (count413 q) 1 (meaning213 q) (meaning413 q) hs
  change valuationOf q 213 = false ∨ valuationOf q 413 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause639 (q : Snake 81) (h : Conditions q) : valuation q 213 = false ∨ valuation q 413 = true := counterClause639 (baseVal q)

theorem counterClause640 (q : Nat → Bool) : valuationOf q 413 = false ∨ valuationOf q 415 = true := by
  have hs : count415 q = (countLit q [211]) + (countLit q [212, 213]) := List.countP_append (p := literal q) (l₁ := [211]) (l₂ := [212, 213])
  have hm := merge_right (literal (valuationOf q) (413)) (literal (valuationOf q) (415)) (countLit q [211]) (countLit q [212, 213]) (count415 q) 1 (meaning413 q) (meaning415 q) hs
  change valuationOf q 413 = false ∨ valuationOf q 415 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause640 (q : Snake 81) (h : Conditions q) : valuation q 413 = false ∨ valuation q 415 = true := counterClause640 (baseVal q)

theorem block19 (q : Snake 81) (h : Conditions q) : B112E169.Block19 (valuation q) :=
  ⟨clause609 q h, clause610 q h, clause611 q h, clause612 q h, clause613 q h, clause614 q h, clause615 q h, clause616 q h, clause617 q h, clause618 q h, clause619 q h, clause620 q h, clause621 q h, clause622 q h, clause623 q h, clause624 q h, clause625 q h, clause626 q h, clause627 q h, clause628 q h, clause629 q h, clause630 q h, clause631 q h, clause632 q h, clause633 q h, clause634 q h, clause635 q h, clause636 q h, clause637 q h, clause638 q h, clause639 q h, clause640 q h⟩

end
end Snake9.Regrowth.E112169
