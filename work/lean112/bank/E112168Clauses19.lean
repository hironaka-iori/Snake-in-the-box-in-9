import E112168Semantics
import B112E168Inputs
namespace Snake9.Regrowth.E112168
noncomputable section
local instance blockDec19 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause609 (q : Nat → Bool) : valuationOf q 373 = false ∨ valuationOf q 375 = true := by
  have hs : count375 q = (countLit q [186, 187, 188]) + (countLit q [189, 190, 191, 192]) := List.countP_append (p := literal q) (l₁ := [186, 187, 188]) (l₂ := [189, 190, 191, 192])
  have hm := merge_right (literal (valuationOf q) (373)) (literal (valuationOf q) (375)) (countLit q [186, 187, 188]) (countLit q [189, 190, 191, 192]) (count375 q) 1 (meaning373 q) (meaning375 q) hs
  change valuationOf q 373 = false ∨ valuationOf q 375 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause609 (q : Snake 81) (h : Conditions q) : valuation q 373 = false ∨ valuation q 375 = true := counterClause609 (baseVal q)

theorem counterClause610 (q : Nat → Bool) : valuationOf q 367 = false ∨ valuationOf q 375 = true := by
  have hs : count375 q = (countLit q [186, 187, 188]) + (countLit q [189, 190, 191, 192]) := List.countP_append (p := literal q) (l₁ := [186, 187, 188]) (l₂ := [189, 190, 191, 192])
  have hm := merge_left (literal (valuationOf q) (367)) (literal (valuationOf q) (375)) (countLit q [186, 187, 188]) (countLit q [189, 190, 191, 192]) (count375 q) 1 (meaning367 q) (meaning375 q) hs
  change valuationOf q 367 = false ∨ valuationOf q 375 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause610 (q : Snake 81) (h : Conditions q) : valuation q 367 = false ∨ valuation q 375 = true := counterClause610 (baseVal q)

theorem counterClause611 (q : Nat → Bool) : valuationOf q 195 = false ∨ valuationOf q 377 = true := by
  have hs : count377 q = (countLit q [194]) + (countLit q [195]) := List.countP_append (p := literal q) (l₁ := [194]) (l₂ := [195])
  have hm := merge_right (literal (valuationOf q) (195)) (literal (valuationOf q) (377)) (countLit q [194]) (countLit q [195]) (count377 q) 1 (meaning195 q) (meaning377 q) hs
  change valuationOf q 195 = false ∨ valuationOf q 377 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause611 (q : Snake 81) (h : Conditions q) : valuation q 195 = false ∨ valuation q 377 = true := counterClause611 (baseVal q)

theorem counterClause612 (q : Nat → Bool) : valuationOf q 194 = false ∨ valuationOf q 377 = true := by
  have hs : count377 q = (countLit q [194]) + (countLit q [195]) := List.countP_append (p := literal q) (l₁ := [194]) (l₂ := [195])
  have hm := merge_left (literal (valuationOf q) (194)) (literal (valuationOf q) (377)) (countLit q [194]) (countLit q [195]) (count377 q) 1 (meaning194 q) (meaning377 q) hs
  change valuationOf q 194 = false ∨ valuationOf q 377 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause612 (q : Snake 81) (h : Conditions q) : valuation q 194 = false ∨ valuation q 377 = true := counterClause612 (baseVal q)

theorem counterClause613 (q : Nat → Bool) : valuationOf q 377 = false ∨ valuationOf q 379 = true := by
  have hs : count379 q = (countLit q [193]) + (countLit q [194, 195]) := List.countP_append (p := literal q) (l₁ := [193]) (l₂ := [194, 195])
  have hm := merge_right (literal (valuationOf q) (377)) (literal (valuationOf q) (379)) (countLit q [193]) (countLit q [194, 195]) (count379 q) 1 (meaning377 q) (meaning379 q) hs
  change valuationOf q 377 = false ∨ valuationOf q 379 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause613 (q : Snake 81) (h : Conditions q) : valuation q 377 = false ∨ valuation q 379 = true := counterClause613 (baseVal q)

theorem counterClause614 (q : Nat → Bool) : valuationOf q 193 = false ∨ valuationOf q 379 = true := by
  have hs : count379 q = (countLit q [193]) + (countLit q [194, 195]) := List.countP_append (p := literal q) (l₁ := [193]) (l₂ := [194, 195])
  have hm := merge_left (literal (valuationOf q) (193)) (literal (valuationOf q) (379)) (countLit q [193]) (countLit q [194, 195]) (count379 q) 1 (meaning193 q) (meaning379 q) hs
  change valuationOf q 193 = false ∨ valuationOf q 379 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause614 (q : Snake 81) (h : Conditions q) : valuation q 193 = false ∨ valuation q 379 = true := counterClause614 (baseVal q)

theorem counterClause615 (q : Nat → Bool) : valuationOf q 193 = false ∨ valuationOf q 377 = false ∨ valuationOf q 380 = true := by
  have hs : count379 q = (countLit q [193]) + (countLit q [194, 195]) := List.countP_append (p := literal q) (l₁ := [193]) (l₂ := [194, 195])
  have hm := merge_two (literal (valuationOf q) (193)) (literal (valuationOf q) (377)) (literal (valuationOf q) (380)) (countLit q [193]) (countLit q [194, 195]) (count379 q) 1 1 (meaning193 q) (meaning377 q) (meaning380 q) hs
  change valuationOf q 193 = false ∨ valuationOf q 377 = false ∨ valuationOf q 380 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause615 (q : Snake 81) (h : Conditions q) : valuation q 193 = false ∨ valuation q 377 = false ∨ valuation q 380 = true := counterClause615 (baseVal q)

theorem counterClause616 (q : Nat → Bool) : valuationOf q 197 = false ∨ valuationOf q 381 = true := by
  have hs : count381 q = (countLit q [196]) + (countLit q [197]) := List.countP_append (p := literal q) (l₁ := [196]) (l₂ := [197])
  have hm := merge_right (literal (valuationOf q) (197)) (literal (valuationOf q) (381)) (countLit q [196]) (countLit q [197]) (count381 q) 1 (meaning197 q) (meaning381 q) hs
  change valuationOf q 197 = false ∨ valuationOf q 381 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause616 (q : Snake 81) (h : Conditions q) : valuation q 197 = false ∨ valuation q 381 = true := counterClause616 (baseVal q)

theorem counterClause617 (q : Nat → Bool) : valuationOf q 381 = false ∨ valuationOf q 385 = true := by
  have hs : count385 q = (countLit q [196, 197]) + (countLit q [198, 199]) := List.countP_append (p := literal q) (l₁ := [196, 197]) (l₂ := [198, 199])
  have hm := merge_left (literal (valuationOf q) (381)) (literal (valuationOf q) (385)) (countLit q [196, 197]) (countLit q [198, 199]) (count385 q) 1 (meaning381 q) (meaning385 q) hs
  change valuationOf q 381 = false ∨ valuationOf q 385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause617 (q : Snake 81) (h : Conditions q) : valuation q 381 = false ∨ valuation q 385 = true := counterClause617 (baseVal q)

theorem counterClause618 (q : Nat → Bool) : valuationOf q 385 = false ∨ valuationOf q 387 = true := by
  have hs : count387 q = (countLit q [193, 194, 195]) + (countLit q [196, 197, 198, 199]) := List.countP_append (p := literal q) (l₁ := [193, 194, 195]) (l₂ := [196, 197, 198, 199])
  have hm := merge_right (literal (valuationOf q) (385)) (literal (valuationOf q) (387)) (countLit q [193, 194, 195]) (countLit q [196, 197, 198, 199]) (count387 q) 1 (meaning385 q) (meaning387 q) hs
  change valuationOf q 385 = false ∨ valuationOf q 387 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause618 (q : Snake 81) (h : Conditions q) : valuation q 385 = false ∨ valuation q 387 = true := counterClause618 (baseVal q)

theorem counterClause619 (q : Nat → Bool) : valuationOf q 379 = false ∨ valuationOf q 387 = true := by
  have hs : count387 q = (countLit q [193, 194, 195]) + (countLit q [196, 197, 198, 199]) := List.countP_append (p := literal q) (l₁ := [193, 194, 195]) (l₂ := [196, 197, 198, 199])
  have hm := merge_left (literal (valuationOf q) (379)) (literal (valuationOf q) (387)) (countLit q [193, 194, 195]) (countLit q [196, 197, 198, 199]) (count387 q) 1 (meaning379 q) (meaning387 q) hs
  change valuationOf q 379 = false ∨ valuationOf q 387 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause619 (q : Snake 81) (h : Conditions q) : valuation q 379 = false ∨ valuation q 387 = true := counterClause619 (baseVal q)

theorem counterClause620 (q : Nat → Bool) : valuationOf q 380 = false ∨ valuationOf q 388 = true := by
  have hs : count387 q = (countLit q [193, 194, 195]) + (countLit q [196, 197, 198, 199]) := List.countP_append (p := literal q) (l₁ := [193, 194, 195]) (l₂ := [196, 197, 198, 199])
  have hm := merge_left (literal (valuationOf q) (380)) (literal (valuationOf q) (388)) (countLit q [193, 194, 195]) (countLit q [196, 197, 198, 199]) (count387 q) 2 (meaning380 q) (meaning388 q) hs
  change valuationOf q 380 = false ∨ valuationOf q 388 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause620 (q : Snake 81) (h : Conditions q) : valuation q 380 = false ∨ valuation q 388 = true := counterClause620 (baseVal q)

theorem counterClause621 (q : Nat → Bool) : valuationOf q 387 = false ∨ valuationOf q 389 = true := by
  have hs : count389 q = (countLit q [186, 187, 188, 189, 190, 191, 192]) + (countLit q [193, 194, 195, 196, 197, 198, 199]) := List.countP_append (p := literal q) (l₁ := [186, 187, 188, 189, 190, 191, 192]) (l₂ := [193, 194, 195, 196, 197, 198, 199])
  have hm := merge_right (literal (valuationOf q) (387)) (literal (valuationOf q) (389)) (countLit q [186, 187, 188, 189, 190, 191, 192]) (countLit q [193, 194, 195, 196, 197, 198, 199]) (count389 q) 1 (meaning387 q) (meaning389 q) hs
  change valuationOf q 387 = false ∨ valuationOf q 389 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause621 (q : Snake 81) (h : Conditions q) : valuation q 387 = false ∨ valuation q 389 = true := counterClause621 (baseVal q)

theorem counterClause622 (q : Nat → Bool) : valuationOf q 388 = false ∨ valuationOf q 390 = true := by
  have hs : count389 q = (countLit q [186, 187, 188, 189, 190, 191, 192]) + (countLit q [193, 194, 195, 196, 197, 198, 199]) := List.countP_append (p := literal q) (l₁ := [186, 187, 188, 189, 190, 191, 192]) (l₂ := [193, 194, 195, 196, 197, 198, 199])
  have hm := merge_right (literal (valuationOf q) (388)) (literal (valuationOf q) (390)) (countLit q [186, 187, 188, 189, 190, 191, 192]) (countLit q [193, 194, 195, 196, 197, 198, 199]) (count389 q) 2 (meaning388 q) (meaning390 q) hs
  change valuationOf q 388 = false ∨ valuationOf q 390 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause622 (q : Snake 81) (h : Conditions q) : valuation q 388 = false ∨ valuation q 390 = true := counterClause622 (baseVal q)

theorem counterClause623 (q : Nat → Bool) : valuationOf q 375 = false ∨ valuationOf q 389 = true := by
  have hs : count389 q = (countLit q [186, 187, 188, 189, 190, 191, 192]) + (countLit q [193, 194, 195, 196, 197, 198, 199]) := List.countP_append (p := literal q) (l₁ := [186, 187, 188, 189, 190, 191, 192]) (l₂ := [193, 194, 195, 196, 197, 198, 199])
  have hm := merge_left (literal (valuationOf q) (375)) (literal (valuationOf q) (389)) (countLit q [186, 187, 188, 189, 190, 191, 192]) (countLit q [193, 194, 195, 196, 197, 198, 199]) (count389 q) 1 (meaning375 q) (meaning389 q) hs
  change valuationOf q 375 = false ∨ valuationOf q 389 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause623 (q : Snake 81) (h : Conditions q) : valuation q 375 = false ∨ valuation q 389 = true := counterClause623 (baseVal q)

theorem counterClause624 (q : Nat → Bool) : valuationOf q 375 = false ∨ valuationOf q 387 = false ∨ valuationOf q 390 = true := by
  have hs : count389 q = (countLit q [186, 187, 188, 189, 190, 191, 192]) + (countLit q [193, 194, 195, 196, 197, 198, 199]) := List.countP_append (p := literal q) (l₁ := [186, 187, 188, 189, 190, 191, 192]) (l₂ := [193, 194, 195, 196, 197, 198, 199])
  have hm := merge_two (literal (valuationOf q) (375)) (literal (valuationOf q) (387)) (literal (valuationOf q) (390)) (countLit q [186, 187, 188, 189, 190, 191, 192]) (countLit q [193, 194, 195, 196, 197, 198, 199]) (count389 q) 1 1 (meaning375 q) (meaning387 q) (meaning390 q) hs
  change valuationOf q 375 = false ∨ valuationOf q 387 = false ∨ valuationOf q 390 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause624 (q : Snake 81) (h : Conditions q) : valuation q 375 = false ∨ valuation q 387 = false ∨ valuation q 390 = true := counterClause624 (baseVal q)

theorem counterClause625 (q : Nat → Bool) : valuationOf q 389 = false ∨ valuationOf q 391 = true := by
  have hs : count391 q = (countLit q [171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 184, 185]) + (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199]) := List.countP_append (p := literal q) (l₁ := [171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 184, 185]) (l₂ := [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199])
  have hm := merge_right (literal (valuationOf q) (389)) (literal (valuationOf q) (391)) (countLit q [171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 184, 185]) (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199]) (count391 q) 1 (meaning389 q) (meaning391 q) hs
  change valuationOf q 389 = false ∨ valuationOf q 391 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause625 (q : Snake 81) (h : Conditions q) : valuation q 389 = false ∨ valuation q 391 = true := counterClause625 (baseVal q)

theorem counterClause626 (q : Nat → Bool) : valuationOf q 390 = false ∨ valuationOf q 392 = true := by
  have hs : count391 q = (countLit q [171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 184, 185]) + (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199]) := List.countP_append (p := literal q) (l₁ := [171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 184, 185]) (l₂ := [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199])
  have hm := merge_right (literal (valuationOf q) (390)) (literal (valuationOf q) (392)) (countLit q [171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 184, 185]) (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199]) (count391 q) 2 (meaning390 q) (meaning392 q) hs
  change valuationOf q 390 = false ∨ valuationOf q 392 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause626 (q : Snake 81) (h : Conditions q) : valuation q 390 = false ∨ valuation q 392 = true := counterClause626 (baseVal q)

theorem counterClause627 (q : Nat → Bool) : valuationOf q 363 = false ∨ valuationOf q 391 = true := by
  have hs : count391 q = (countLit q [171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 184, 185]) + (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199]) := List.countP_append (p := literal q) (l₁ := [171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 184, 185]) (l₂ := [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199])
  have hm := merge_left (literal (valuationOf q) (363)) (literal (valuationOf q) (391)) (countLit q [171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 184, 185]) (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199]) (count391 q) 1 (meaning363 q) (meaning391 q) hs
  change valuationOf q 363 = false ∨ valuationOf q 391 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause627 (q : Snake 81) (h : Conditions q) : valuation q 363 = false ∨ valuation q 391 = true := counterClause627 (baseVal q)

theorem counterClause628 (q : Nat → Bool) : valuationOf q 363 = false ∨ valuationOf q 389 = false ∨ valuationOf q 392 = true := by
  have hs : count391 q = (countLit q [171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 184, 185]) + (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199]) := List.countP_append (p := literal q) (l₁ := [171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 184, 185]) (l₂ := [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199])
  have hm := merge_two (literal (valuationOf q) (363)) (literal (valuationOf q) (389)) (literal (valuationOf q) (392)) (countLit q [171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 184, 185]) (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199]) (count391 q) 1 1 (meaning363 q) (meaning389 q) (meaning392 q) hs
  change valuationOf q 363 = false ∨ valuationOf q 389 = false ∨ valuationOf q 392 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause628 (q : Snake 81) (h : Conditions q) : valuation q 363 = false ∨ valuation q 389 = false ∨ valuation q 392 = true := counterClause628 (baseVal q)

theorem counterClause629 (q : Nat → Bool) : valuationOf q 202 = false ∨ valuationOf q 393 = true := by
  have hs : count393 q = (countLit q [201]) + (countLit q [202]) := List.countP_append (p := literal q) (l₁ := [201]) (l₂ := [202])
  have hm := merge_right (literal (valuationOf q) (202)) (literal (valuationOf q) (393)) (countLit q [201]) (countLit q [202]) (count393 q) 1 (meaning202 q) (meaning393 q) hs
  change valuationOf q 202 = false ∨ valuationOf q 393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause629 (q : Snake 81) (h : Conditions q) : valuation q 202 = false ∨ valuation q 393 = true := counterClause629 (baseVal q)

theorem counterClause630 (q : Nat → Bool) : valuationOf q 393 = false ∨ valuationOf q 395 = true := by
  have hs : count395 q = (countLit q [200]) + (countLit q [201, 202]) := List.countP_append (p := literal q) (l₁ := [200]) (l₂ := [201, 202])
  have hm := merge_right (literal (valuationOf q) (393)) (literal (valuationOf q) (395)) (countLit q [200]) (countLit q [201, 202]) (count395 q) 1 (meaning393 q) (meaning395 q) hs
  change valuationOf q 393 = false ∨ valuationOf q 395 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause630 (q : Snake 81) (h : Conditions q) : valuation q 393 = false ∨ valuation q 395 = true := counterClause630 (baseVal q)

theorem counterClause631 (q : Nat → Bool) : valuationOf q 200 = false ∨ valuationOf q 395 = true := by
  have hs : count395 q = (countLit q [200]) + (countLit q [201, 202]) := List.countP_append (p := literal q) (l₁ := [200]) (l₂ := [201, 202])
  have hm := merge_left (literal (valuationOf q) (200)) (literal (valuationOf q) (395)) (countLit q [200]) (countLit q [201, 202]) (count395 q) 1 (meaning200 q) (meaning395 q) hs
  change valuationOf q 200 = false ∨ valuationOf q 395 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause631 (q : Snake 81) (h : Conditions q) : valuation q 200 = false ∨ valuation q 395 = true := counterClause631 (baseVal q)

theorem counterClause632 (q : Nat → Bool) : valuationOf q 204 = false ∨ valuationOf q 397 = true := by
  have hs : count397 q = (countLit q [203]) + (countLit q [204]) := List.countP_append (p := literal q) (l₁ := [203]) (l₂ := [204])
  have hm := merge_right (literal (valuationOf q) (204)) (literal (valuationOf q) (397)) (countLit q [203]) (countLit q [204]) (count397 q) 1 (meaning204 q) (meaning397 q) hs
  change valuationOf q 204 = false ∨ valuationOf q 397 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause632 (q : Snake 81) (h : Conditions q) : valuation q 204 = false ∨ valuation q 397 = true := counterClause632 (baseVal q)

theorem counterClause633 (q : Nat → Bool) : valuationOf q 203 = false ∨ valuationOf q 397 = true := by
  have hs : count397 q = (countLit q [203]) + (countLit q [204]) := List.countP_append (p := literal q) (l₁ := [203]) (l₂ := [204])
  have hm := merge_left (literal (valuationOf q) (203)) (literal (valuationOf q) (397)) (countLit q [203]) (countLit q [204]) (count397 q) 1 (meaning203 q) (meaning397 q) hs
  change valuationOf q 203 = false ∨ valuationOf q 397 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause633 (q : Snake 81) (h : Conditions q) : valuation q 203 = false ∨ valuation q 397 = true := counterClause633 (baseVal q)

theorem counterClause634 (q : Nat → Bool) : valuationOf q 397 = false ∨ valuationOf q 401 = true := by
  have hs : count401 q = (countLit q [203, 204]) + (countLit q [205, 206]) := List.countP_append (p := literal q) (l₁ := [203, 204]) (l₂ := [205, 206])
  have hm := merge_left (literal (valuationOf q) (397)) (literal (valuationOf q) (401)) (countLit q [203, 204]) (countLit q [205, 206]) (count401 q) 1 (meaning397 q) (meaning401 q) hs
  change valuationOf q 397 = false ∨ valuationOf q 401 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause634 (q : Snake 81) (h : Conditions q) : valuation q 397 = false ∨ valuation q 401 = true := counterClause634 (baseVal q)

theorem counterClause635 (q : Nat → Bool) : valuationOf q 401 = false ∨ valuationOf q 403 = true := by
  have hs : count403 q = (countLit q [200, 201, 202]) + (countLit q [203, 204, 205, 206]) := List.countP_append (p := literal q) (l₁ := [200, 201, 202]) (l₂ := [203, 204, 205, 206])
  have hm := merge_right (literal (valuationOf q) (401)) (literal (valuationOf q) (403)) (countLit q [200, 201, 202]) (countLit q [203, 204, 205, 206]) (count403 q) 1 (meaning401 q) (meaning403 q) hs
  change valuationOf q 401 = false ∨ valuationOf q 403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause635 (q : Snake 81) (h : Conditions q) : valuation q 401 = false ∨ valuation q 403 = true := counterClause635 (baseVal q)

theorem counterClause636 (q : Nat → Bool) : valuationOf q 395 = false ∨ valuationOf q 403 = true := by
  have hs : count403 q = (countLit q [200, 201, 202]) + (countLit q [203, 204, 205, 206]) := List.countP_append (p := literal q) (l₁ := [200, 201, 202]) (l₂ := [203, 204, 205, 206])
  have hm := merge_left (literal (valuationOf q) (395)) (literal (valuationOf q) (403)) (countLit q [200, 201, 202]) (countLit q [203, 204, 205, 206]) (count403 q) 1 (meaning395 q) (meaning403 q) hs
  change valuationOf q 395 = false ∨ valuationOf q 403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause636 (q : Snake 81) (h : Conditions q) : valuation q 395 = false ∨ valuation q 403 = true := counterClause636 (baseVal q)

theorem counterClause637 (q : Nat → Bool) : valuationOf q 209 = false ∨ valuationOf q 405 = true := by
  have hs : count405 q = (countLit q [208]) + (countLit q [209]) := List.countP_append (p := literal q) (l₁ := [208]) (l₂ := [209])
  have hm := merge_right (literal (valuationOf q) (209)) (literal (valuationOf q) (405)) (countLit q [208]) (countLit q [209]) (count405 q) 1 (meaning209 q) (meaning405 q) hs
  change valuationOf q 209 = false ∨ valuationOf q 405 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause637 (q : Snake 81) (h : Conditions q) : valuation q 209 = false ∨ valuation q 405 = true := counterClause637 (baseVal q)

theorem counterClause638 (q : Nat → Bool) : valuationOf q 405 = false ∨ valuationOf q 407 = true := by
  have hs : count407 q = (countLit q [207]) + (countLit q [208, 209]) := List.countP_append (p := literal q) (l₁ := [207]) (l₂ := [208, 209])
  have hm := merge_right (literal (valuationOf q) (405)) (literal (valuationOf q) (407)) (countLit q [207]) (countLit q [208, 209]) (count407 q) 1 (meaning405 q) (meaning407 q) hs
  change valuationOf q 405 = false ∨ valuationOf q 407 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause638 (q : Snake 81) (h : Conditions q) : valuation q 405 = false ∨ valuation q 407 = true := counterClause638 (baseVal q)

theorem counterClause639 (q : Nat → Bool) : valuationOf q 211 = false ∨ valuationOf q 409 = true := by
  have hs : count409 q = (countLit q [210]) + (countLit q [211]) := List.countP_append (p := literal q) (l₁ := [210]) (l₂ := [211])
  have hm := merge_right (literal (valuationOf q) (211)) (literal (valuationOf q) (409)) (countLit q [210]) (countLit q [211]) (count409 q) 1 (meaning211 q) (meaning409 q) hs
  change valuationOf q 211 = false ∨ valuationOf q 409 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause639 (q : Snake 81) (h : Conditions q) : valuation q 211 = false ∨ valuation q 409 = true := counterClause639 (baseVal q)

theorem counterClause640 (q : Nat → Bool) : valuationOf q 210 = false ∨ valuationOf q 409 = true := by
  have hs : count409 q = (countLit q [210]) + (countLit q [211]) := List.countP_append (p := literal q) (l₁ := [210]) (l₂ := [211])
  have hm := merge_left (literal (valuationOf q) (210)) (literal (valuationOf q) (409)) (countLit q [210]) (countLit q [211]) (count409 q) 1 (meaning210 q) (meaning409 q) hs
  change valuationOf q 210 = false ∨ valuationOf q 409 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause640 (q : Snake 81) (h : Conditions q) : valuation q 210 = false ∨ valuation q 409 = true := counterClause640 (baseVal q)

theorem block19 (q : Snake 81) (h : Conditions q) : B112E168.Block19 (valuation q) :=
  ⟨clause609 q h, clause610 q h, clause611 q h, clause612 q h, clause613 q h, clause614 q h, clause615 q h, clause616 q h, clause617 q h, clause618 q h, clause619 q h, clause620 q h, clause621 q h, clause622 q h, clause623 q h, clause624 q h, clause625 q h, clause626 q h, clause627 q h, clause628 q h, clause629 q h, clause630 q h, clause631 q h, clause632 q h, clause633 q h, clause634 q h, clause635 q h, clause636 q h, clause637 q h, clause638 q h, clause639 q h, clause640 q h⟩

end
end Snake9.Regrowth.E112168
