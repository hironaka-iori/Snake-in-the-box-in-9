import E112078Semantics
import B112E078Inputs
namespace Snake9.Regrowth.E112078
noncomputable section
local instance blockDec21 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause673 (q : Nat → Bool) : valuationOf q 364 = false ∨ valuationOf q 366 = true := by
  have hs : count365 q = (countLit q [179, 180, 181]) + (countLit q [182, 183, 184, 185]) := List.countP_append (p := literal q) (l₁ := [179, 180, 181]) (l₂ := [182, 183, 184, 185])
  have hm := merge_right (literal (valuationOf q) (364)) (literal (valuationOf q) (366)) (countLit q [179, 180, 181]) (countLit q [182, 183, 184, 185]) (count365 q) 2 (meaning364 q) (meaning366 q) hs
  change valuationOf q 364 = false ∨ valuationOf q 366 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause673 (q : Snake 81) (h : Conditions q) : valuation q 364 = false ∨ valuation q 366 = true := counterClause673 (baseVal q)

theorem counterClause674 (q : Nat → Bool) : valuationOf q 188 = false ∨ valuationOf q 367 = true := by
  have hs : count367 q = (countLit q [188]) + (countLit q [189]) := List.countP_append (p := literal q) (l₁ := [188]) (l₂ := [189])
  have hm := merge_left (literal (valuationOf q) (188)) (literal (valuationOf q) (367)) (countLit q [188]) (countLit q [189]) (count367 q) 1 (meaning188 q) (meaning367 q) hs
  change valuationOf q 188 = false ∨ valuationOf q 367 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause674 (q : Snake 81) (h : Conditions q) : valuation q 188 = false ∨ valuation q 367 = true := counterClause674 (baseVal q)

theorem counterClause675 (q : Nat → Bool) : valuationOf q 367 = false ∨ valuationOf q 369 = true := by
  have hs : count369 q = (countLit q [187]) + (countLit q [188, 189]) := List.countP_append (p := literal q) (l₁ := [187]) (l₂ := [188, 189])
  have hm := merge_right (literal (valuationOf q) (367)) (literal (valuationOf q) (369)) (countLit q [187]) (countLit q [188, 189]) (count369 q) 1 (meaning367 q) (meaning369 q) hs
  change valuationOf q 367 = false ∨ valuationOf q 369 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause675 (q : Snake 81) (h : Conditions q) : valuation q 367 = false ∨ valuation q 369 = true := counterClause675 (baseVal q)

theorem counterClause676 (q : Nat → Bool) : valuationOf q 187 = false ∨ valuationOf q 369 = true := by
  have hs : count369 q = (countLit q [187]) + (countLit q [188, 189]) := List.countP_append (p := literal q) (l₁ := [187]) (l₂ := [188, 189])
  have hm := merge_left (literal (valuationOf q) (187)) (literal (valuationOf q) (369)) (countLit q [187]) (countLit q [188, 189]) (count369 q) 1 (meaning187 q) (meaning369 q) hs
  change valuationOf q 187 = false ∨ valuationOf q 369 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause676 (q : Snake 81) (h : Conditions q) : valuation q 187 = false ∨ valuation q 369 = true := counterClause676 (baseVal q)

theorem counterClause677 (q : Nat → Bool) : valuationOf q 369 = false ∨ valuationOf q 377 = true := by
  have hs : count377 q = (countLit q [187, 188, 189]) + (countLit q [190, 191, 192, 193]) := List.countP_append (p := literal q) (l₁ := [187, 188, 189]) (l₂ := [190, 191, 192, 193])
  have hm := merge_left (literal (valuationOf q) (369)) (literal (valuationOf q) (377)) (countLit q [187, 188, 189]) (countLit q [190, 191, 192, 193]) (count377 q) 1 (meaning369 q) (meaning377 q) hs
  change valuationOf q 369 = false ∨ valuationOf q 377 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause677 (q : Snake 81) (h : Conditions q) : valuation q 369 = false ∨ valuation q 377 = true := counterClause677 (baseVal q)

theorem counterClause678 (q : Nat → Bool) : valuationOf q 377 = false ∨ valuationOf q 379 = true := by
  have hs : count379 q = (countLit q [179, 180, 181, 182, 183, 184, 185]) + (countLit q [187, 188, 189, 190, 191, 192, 193]) := List.countP_append (p := literal q) (l₁ := [179, 180, 181, 182, 183, 184, 185]) (l₂ := [187, 188, 189, 190, 191, 192, 193])
  have hm := merge_right (literal (valuationOf q) (377)) (literal (valuationOf q) (379)) (countLit q [179, 180, 181, 182, 183, 184, 185]) (countLit q [187, 188, 189, 190, 191, 192, 193]) (count379 q) 1 (meaning377 q) (meaning379 q) hs
  change valuationOf q 377 = false ∨ valuationOf q 379 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause678 (q : Snake 81) (h : Conditions q) : valuation q 377 = false ∨ valuation q 379 = true := counterClause678 (baseVal q)

theorem counterClause679 (q : Nat → Bool) : valuationOf q 365 = false ∨ valuationOf q 379 = true := by
  have hs : count379 q = (countLit q [179, 180, 181, 182, 183, 184, 185]) + (countLit q [187, 188, 189, 190, 191, 192, 193]) := List.countP_append (p := literal q) (l₁ := [179, 180, 181, 182, 183, 184, 185]) (l₂ := [187, 188, 189, 190, 191, 192, 193])
  have hm := merge_left (literal (valuationOf q) (365)) (literal (valuationOf q) (379)) (countLit q [179, 180, 181, 182, 183, 184, 185]) (countLit q [187, 188, 189, 190, 191, 192, 193]) (count379 q) 1 (meaning365 q) (meaning379 q) hs
  change valuationOf q 365 = false ∨ valuationOf q 379 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause679 (q : Snake 81) (h : Conditions q) : valuation q 365 = false ∨ valuation q 379 = true := counterClause679 (baseVal q)

theorem counterClause680 (q : Nat → Bool) : valuationOf q 366 = false ∨ valuationOf q 380 = true := by
  have hs : count379 q = (countLit q [179, 180, 181, 182, 183, 184, 185]) + (countLit q [187, 188, 189, 190, 191, 192, 193]) := List.countP_append (p := literal q) (l₁ := [179, 180, 181, 182, 183, 184, 185]) (l₂ := [187, 188, 189, 190, 191, 192, 193])
  have hm := merge_left (literal (valuationOf q) (366)) (literal (valuationOf q) (380)) (countLit q [179, 180, 181, 182, 183, 184, 185]) (countLit q [187, 188, 189, 190, 191, 192, 193]) (count379 q) 2 (meaning366 q) (meaning380 q) hs
  change valuationOf q 366 = false ∨ valuationOf q 380 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause680 (q : Snake 81) (h : Conditions q) : valuation q 366 = false ∨ valuation q 380 = true := counterClause680 (baseVal q)

theorem counterClause681 (q : Nat → Bool) : valuationOf q 196 = false ∨ valuationOf q 381 = true := by
  have hs : count381 q = (countLit q [195]) + (countLit q [196]) := List.countP_append (p := literal q) (l₁ := [195]) (l₂ := [196])
  have hm := merge_right (literal (valuationOf q) (196)) (literal (valuationOf q) (381)) (countLit q [195]) (countLit q [196]) (count381 q) 1 (meaning196 q) (meaning381 q) hs
  change valuationOf q 196 = false ∨ valuationOf q 381 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause681 (q : Snake 81) (h : Conditions q) : valuation q 196 = false ∨ valuation q 381 = true := counterClause681 (baseVal q)

theorem counterClause682 (q : Nat → Bool) : valuationOf q 195 = false ∨ valuationOf q 381 = true := by
  have hs : count381 q = (countLit q [195]) + (countLit q [196]) := List.countP_append (p := literal q) (l₁ := [195]) (l₂ := [196])
  have hm := merge_left (literal (valuationOf q) (195)) (literal (valuationOf q) (381)) (countLit q [195]) (countLit q [196]) (count381 q) 1 (meaning195 q) (meaning381 q) hs
  change valuationOf q 195 = false ∨ valuationOf q 381 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause682 (q : Snake 81) (h : Conditions q) : valuation q 195 = false ∨ valuation q 381 = true := counterClause682 (baseVal q)

theorem counterClause683 (q : Nat → Bool) : valuationOf q 381 = false ∨ valuationOf q 383 = true := by
  have hs : count383 q = (countLit q [194]) + (countLit q [195, 196]) := List.countP_append (p := literal q) (l₁ := [194]) (l₂ := [195, 196])
  have hm := merge_right (literal (valuationOf q) (381)) (literal (valuationOf q) (383)) (countLit q [194]) (countLit q [195, 196]) (count383 q) 1 (meaning381 q) (meaning383 q) hs
  change valuationOf q 381 = false ∨ valuationOf q 383 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause683 (q : Snake 81) (h : Conditions q) : valuation q 381 = false ∨ valuation q 383 = true := counterClause683 (baseVal q)

theorem counterClause684 (q : Nat → Bool) : valuationOf q 197 = false ∨ valuationOf q 385 = true := by
  have hs : count385 q = (countLit q [197]) + (countLit q [198]) := List.countP_append (p := literal q) (l₁ := [197]) (l₂ := [198])
  have hm := merge_left (literal (valuationOf q) (197)) (literal (valuationOf q) (385)) (countLit q [197]) (countLit q [198]) (count385 q) 1 (meaning197 q) (meaning385 q) hs
  change valuationOf q 197 = false ∨ valuationOf q 385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause684 (q : Snake 81) (h : Conditions q) : valuation q 197 = false ∨ valuation q 385 = true := counterClause684 (baseVal q)

theorem counterClause685 (q : Nat → Bool) : valuationOf q 385 = false ∨ valuationOf q 389 = true := by
  have hs : count389 q = (countLit q [197, 198]) + (countLit q [199, 200]) := List.countP_append (p := literal q) (l₁ := [197, 198]) (l₂ := [199, 200])
  have hm := merge_left (literal (valuationOf q) (385)) (literal (valuationOf q) (389)) (countLit q [197, 198]) (countLit q [199, 200]) (count389 q) 1 (meaning385 q) (meaning389 q) hs
  change valuationOf q 385 = false ∨ valuationOf q 389 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause685 (q : Snake 81) (h : Conditions q) : valuation q 385 = false ∨ valuation q 389 = true := counterClause685 (baseVal q)

theorem counterClause686 (q : Nat → Bool) : valuationOf q 389 = false ∨ valuationOf q 391 = true := by
  have hs : count391 q = (countLit q [194, 195, 196]) + (countLit q [197, 198, 199, 200]) := List.countP_append (p := literal q) (l₁ := [194, 195, 196]) (l₂ := [197, 198, 199, 200])
  have hm := merge_right (literal (valuationOf q) (389)) (literal (valuationOf q) (391)) (countLit q [194, 195, 196]) (countLit q [197, 198, 199, 200]) (count391 q) 1 (meaning389 q) (meaning391 q) hs
  change valuationOf q 389 = false ∨ valuationOf q 391 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause686 (q : Snake 81) (h : Conditions q) : valuation q 389 = false ∨ valuation q 391 = true := counterClause686 (baseVal q)

theorem counterClause687 (q : Nat → Bool) : valuationOf q 383 = false ∨ valuationOf q 391 = true := by
  have hs : count391 q = (countLit q [194, 195, 196]) + (countLit q [197, 198, 199, 200]) := List.countP_append (p := literal q) (l₁ := [194, 195, 196]) (l₂ := [197, 198, 199, 200])
  have hm := merge_left (literal (valuationOf q) (383)) (literal (valuationOf q) (391)) (countLit q [194, 195, 196]) (countLit q [197, 198, 199, 200]) (count391 q) 1 (meaning383 q) (meaning391 q) hs
  change valuationOf q 383 = false ∨ valuationOf q 391 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause687 (q : Snake 81) (h : Conditions q) : valuation q 383 = false ∨ valuation q 391 = true := counterClause687 (baseVal q)

theorem counterClause688 (q : Nat → Bool) : valuationOf q 202 = false ∨ valuationOf q 393 = true := by
  have hs : count393 q = (countLit q [201]) + (countLit q [202]) := List.countP_append (p := literal q) (l₁ := [201]) (l₂ := [202])
  have hm := merge_right (literal (valuationOf q) (202)) (literal (valuationOf q) (393)) (countLit q [201]) (countLit q [202]) (count393 q) 1 (meaning202 q) (meaning393 q) hs
  change valuationOf q 202 = false ∨ valuationOf q 393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause688 (q : Snake 81) (h : Conditions q) : valuation q 202 = false ∨ valuation q 393 = true := counterClause688 (baseVal q)

theorem counterClause689 (q : Nat → Bool) : valuationOf q 204 = false ∨ valuationOf q 395 = true := by
  have hs : count395 q = (countLit q [203]) + (countLit q [204]) := List.countP_append (p := literal q) (l₁ := [203]) (l₂ := [204])
  have hm := merge_right (literal (valuationOf q) (204)) (literal (valuationOf q) (395)) (countLit q [203]) (countLit q [204]) (count395 q) 1 (meaning204 q) (meaning395 q) hs
  change valuationOf q 204 = false ∨ valuationOf q 395 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause689 (q : Snake 81) (h : Conditions q) : valuation q 204 = false ∨ valuation q 395 = true := counterClause689 (baseVal q)

theorem counterClause690 (q : Nat → Bool) : valuationOf q 395 = false ∨ valuationOf q 397 = true := by
  have hs : count397 q = (countLit q [201, 202]) + (countLit q [203, 204]) := List.countP_append (p := literal q) (l₁ := [201, 202]) (l₂ := [203, 204])
  have hm := merge_right (literal (valuationOf q) (395)) (literal (valuationOf q) (397)) (countLit q [201, 202]) (countLit q [203, 204]) (count397 q) 1 (meaning395 q) (meaning397 q) hs
  change valuationOf q 395 = false ∨ valuationOf q 397 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause690 (q : Snake 81) (h : Conditions q) : valuation q 395 = false ∨ valuation q 397 = true := counterClause690 (baseVal q)

theorem counterClause691 (q : Nat → Bool) : valuationOf q 393 = false ∨ valuationOf q 397 = true := by
  have hs : count397 q = (countLit q [201, 202]) + (countLit q [203, 204]) := List.countP_append (p := literal q) (l₁ := [201, 202]) (l₂ := [203, 204])
  have hm := merge_left (literal (valuationOf q) (393)) (literal (valuationOf q) (397)) (countLit q [201, 202]) (countLit q [203, 204]) (count397 q) 1 (meaning393 q) (meaning397 q) hs
  change valuationOf q 393 = false ∨ valuationOf q 397 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause691 (q : Snake 81) (h : Conditions q) : valuation q 393 = false ∨ valuation q 397 = true := counterClause691 (baseVal q)

theorem counterClause692 (q : Nat → Bool) : valuationOf q 397 = false ∨ valuationOf q 405 = true := by
  have hs : count405 q = (countLit q [201, 202, 203, 204]) + (countLit q [205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [201, 202, 203, 204]) (l₂ := [205, 206, 207, 208])
  have hm := merge_left (literal (valuationOf q) (397)) (literal (valuationOf q) (405)) (countLit q [201, 202, 203, 204]) (countLit q [205, 206, 207, 208]) (count405 q) 1 (meaning397 q) (meaning405 q) hs
  change valuationOf q 397 = false ∨ valuationOf q 405 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause692 (q : Snake 81) (h : Conditions q) : valuation q 397 = false ∨ valuation q 405 = true := counterClause692 (baseVal q)

theorem counterClause693 (q : Nat → Bool) : valuationOf q 405 = false ∨ valuationOf q 407 = true := by
  have hs : count407 q = (countLit q [194, 195, 196, 197, 198, 199, 200]) + (countLit q [201, 202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [194, 195, 196, 197, 198, 199, 200]) (l₂ := [201, 202, 203, 204, 205, 206, 207, 208])
  have hm := merge_right (literal (valuationOf q) (405)) (literal (valuationOf q) (407)) (countLit q [194, 195, 196, 197, 198, 199, 200]) (countLit q [201, 202, 203, 204, 205, 206, 207, 208]) (count407 q) 1 (meaning405 q) (meaning407 q) hs
  change valuationOf q 405 = false ∨ valuationOf q 407 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause693 (q : Snake 81) (h : Conditions q) : valuation q 405 = false ∨ valuation q 407 = true := counterClause693 (baseVal q)

theorem counterClause694 (q : Nat → Bool) : valuationOf q 391 = false ∨ valuationOf q 407 = true := by
  have hs : count407 q = (countLit q [194, 195, 196, 197, 198, 199, 200]) + (countLit q [201, 202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [194, 195, 196, 197, 198, 199, 200]) (l₂ := [201, 202, 203, 204, 205, 206, 207, 208])
  have hm := merge_left (literal (valuationOf q) (391)) (literal (valuationOf q) (407)) (countLit q [194, 195, 196, 197, 198, 199, 200]) (countLit q [201, 202, 203, 204, 205, 206, 207, 208]) (count407 q) 1 (meaning391 q) (meaning407 q) hs
  change valuationOf q 391 = false ∨ valuationOf q 407 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause694 (q : Snake 81) (h : Conditions q) : valuation q 391 = false ∨ valuation q 407 = true := counterClause694 (baseVal q)

theorem counterClause695 (q : Nat → Bool) : valuationOf q 407 = false ∨ valuationOf q 409 = true := by
  have hs : count409 q = (countLit q [179, 180, 181, 182, 183, 184, 185, 187, 188, 189, 190, 191, 192, 193]) + (countLit q [194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [179, 180, 181, 182, 183, 184, 185, 187, 188, 189, 190, 191, 192, 193]) (l₂ := [194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208])
  have hm := merge_right (literal (valuationOf q) (407)) (literal (valuationOf q) (409)) (countLit q [179, 180, 181, 182, 183, 184, 185, 187, 188, 189, 190, 191, 192, 193]) (countLit q [194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (count409 q) 1 (meaning407 q) (meaning409 q) hs
  change valuationOf q 407 = false ∨ valuationOf q 409 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause695 (q : Snake 81) (h : Conditions q) : valuation q 407 = false ∨ valuation q 409 = true := counterClause695 (baseVal q)

theorem counterClause696 (q : Nat → Bool) : valuationOf q 379 = false ∨ valuationOf q 409 = true := by
  have hs : count409 q = (countLit q [179, 180, 181, 182, 183, 184, 185, 187, 188, 189, 190, 191, 192, 193]) + (countLit q [194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [179, 180, 181, 182, 183, 184, 185, 187, 188, 189, 190, 191, 192, 193]) (l₂ := [194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208])
  have hm := merge_left (literal (valuationOf q) (379)) (literal (valuationOf q) (409)) (countLit q [179, 180, 181, 182, 183, 184, 185, 187, 188, 189, 190, 191, 192, 193]) (countLit q [194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (count409 q) 1 (meaning379 q) (meaning409 q) hs
  change valuationOf q 379 = false ∨ valuationOf q 409 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause696 (q : Snake 81) (h : Conditions q) : valuation q 379 = false ∨ valuation q 409 = true := counterClause696 (baseVal q)

theorem counterClause697 (q : Nat → Bool) : valuationOf q 380 = false ∨ valuationOf q 410 = true := by
  have hs : count409 q = (countLit q [179, 180, 181, 182, 183, 184, 185, 187, 188, 189, 190, 191, 192, 193]) + (countLit q [194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [179, 180, 181, 182, 183, 184, 185, 187, 188, 189, 190, 191, 192, 193]) (l₂ := [194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208])
  have hm := merge_left (literal (valuationOf q) (380)) (literal (valuationOf q) (410)) (countLit q [179, 180, 181, 182, 183, 184, 185, 187, 188, 189, 190, 191, 192, 193]) (countLit q [194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (count409 q) 2 (meaning380 q) (meaning410 q) hs
  change valuationOf q 380 = false ∨ valuationOf q 410 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause697 (q : Snake 81) (h : Conditions q) : valuation q 380 = false ∨ valuation q 410 = true := counterClause697 (baseVal q)

theorem counterClause698 (q : Nat → Bool) : valuationOf q 213 = false ∨ valuationOf q 415 = true := by
  have hs : count415 q = (countLit q [212]) + (countLit q [213]) := List.countP_append (p := literal q) (l₁ := [212]) (l₂ := [213])
  have hm := merge_right (literal (valuationOf q) (213)) (literal (valuationOf q) (415)) (countLit q [212]) (countLit q [213]) (count415 q) 1 (meaning213 q) (meaning415 q) hs
  change valuationOf q 213 = false ∨ valuationOf q 415 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause698 (q : Snake 81) (h : Conditions q) : valuation q 213 = false ∨ valuation q 415 = true := counterClause698 (baseVal q)

theorem counterClause699 (q : Nat → Bool) : valuationOf q 212 = false ∨ valuationOf q 415 = true := by
  have hs : count415 q = (countLit q [212]) + (countLit q [213]) := List.countP_append (p := literal q) (l₁ := [212]) (l₂ := [213])
  have hm := merge_left (literal (valuationOf q) (212)) (literal (valuationOf q) (415)) (countLit q [212]) (countLit q [213]) (count415 q) 1 (meaning212 q) (meaning415 q) hs
  change valuationOf q 212 = false ∨ valuationOf q 415 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause699 (q : Snake 81) (h : Conditions q) : valuation q 212 = false ∨ valuation q 415 = true := counterClause699 (baseVal q)

theorem counterClause700 (q : Nat → Bool) : valuationOf q 415 = false ∨ valuationOf q 419 = true := by
  have hs : count419 q = (countLit q [212, 213]) + (countLit q [214, 215]) := List.countP_append (p := literal q) (l₁ := [212, 213]) (l₂ := [214, 215])
  have hm := merge_left (literal (valuationOf q) (415)) (literal (valuationOf q) (419)) (countLit q [212, 213]) (countLit q [214, 215]) (count419 q) 1 (meaning415 q) (meaning419 q) hs
  change valuationOf q 415 = false ∨ valuationOf q 419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause700 (q : Snake 81) (h : Conditions q) : valuation q 415 = false ∨ valuation q 419 = true := counterClause700 (baseVal q)

theorem counterClause701 (q : Nat → Bool) : valuationOf q 419 = false ∨ valuationOf q 421 = true := by
  have hs : count421 q = (countLit q [209, 210, 211]) + (countLit q [212, 213, 214, 215]) := List.countP_append (p := literal q) (l₁ := [209, 210, 211]) (l₂ := [212, 213, 214, 215])
  have hm := merge_right (literal (valuationOf q) (419)) (literal (valuationOf q) (421)) (countLit q [209, 210, 211]) (countLit q [212, 213, 214, 215]) (count421 q) 1 (meaning419 q) (meaning421 q) hs
  change valuationOf q 419 = false ∨ valuationOf q 421 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause701 (q : Snake 81) (h : Conditions q) : valuation q 419 = false ∨ valuation q 421 = true := counterClause701 (baseVal q)

theorem counterClause702 (q : Nat → Bool) : valuationOf q 219 = false ∨ valuationOf q 425 = true := by
  have hs : count425 q = (countLit q [218]) + (countLit q [219]) := List.countP_append (p := literal q) (l₁ := [218]) (l₂ := [219])
  have hm := merge_right (literal (valuationOf q) (219)) (literal (valuationOf q) (425)) (countLit q [218]) (countLit q [219]) (count425 q) 1 (meaning219 q) (meaning425 q) hs
  change valuationOf q 219 = false ∨ valuationOf q 425 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause702 (q : Snake 81) (h : Conditions q) : valuation q 219 = false ∨ valuation q 425 = true := counterClause702 (baseVal q)

theorem counterClause703 (q : Nat → Bool) : valuationOf q 425 = false ∨ valuationOf q 427 = true := by
  have hs : count427 q = (countLit q [216, 217]) + (countLit q [218, 219]) := List.countP_append (p := literal q) (l₁ := [216, 217]) (l₂ := [218, 219])
  have hm := merge_right (literal (valuationOf q) (425)) (literal (valuationOf q) (427)) (countLit q [216, 217]) (countLit q [218, 219]) (count427 q) 1 (meaning425 q) (meaning427 q) hs
  change valuationOf q 425 = false ∨ valuationOf q 427 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause703 (q : Snake 81) (h : Conditions q) : valuation q 425 = false ∨ valuation q 427 = true := counterClause703 (baseVal q)

theorem counterClause704 (q : Nat → Bool) : valuationOf q 221 = false ∨ valuationOf q 429 = true := by
  have hs : count429 q = (countLit q [220]) + (countLit q [221]) := List.countP_append (p := literal q) (l₁ := [220]) (l₂ := [221])
  have hm := merge_right (literal (valuationOf q) (221)) (literal (valuationOf q) (429)) (countLit q [220]) (countLit q [221]) (count429 q) 1 (meaning221 q) (meaning429 q) hs
  change valuationOf q 221 = false ∨ valuationOf q 429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause704 (q : Snake 81) (h : Conditions q) : valuation q 221 = false ∨ valuation q 429 = true := counterClause704 (baseVal q)

theorem block21 (q : Snake 81) (h : Conditions q) : B112E078.Block21 (valuation q) :=
  ⟨clause673 q h, clause674 q h, clause675 q h, clause676 q h, clause677 q h, clause678 q h, clause679 q h, clause680 q h, clause681 q h, clause682 q h, clause683 q h, clause684 q h, clause685 q h, clause686 q h, clause687 q h, clause688 q h, clause689 q h, clause690 q h, clause691 q h, clause692 q h, clause693 q h, clause694 q h, clause695 q h, clause696 q h, clause697 q h, clause698 q h, clause699 q h, clause700 q h, clause701 q h, clause702 q h, clause703 q h, clause704 q h⟩

end
end Snake9.Regrowth.E112078
