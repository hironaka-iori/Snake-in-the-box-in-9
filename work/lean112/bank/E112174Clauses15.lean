import E112174Semantics
import B112E174Inputs
namespace Snake9.Regrowth.E112174
noncomputable section
local instance blockDec15 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause481 (q : Nat → Bool) : valuationOf q 208 = false ∨ valuationOf q 399 = true := by
  have hs : count399 q = (countLit q [207]) + (countLit q [208]) := List.countP_append (p := literal q) (l₁ := [207]) (l₂ := [208])
  have hm := merge_right (literal (valuationOf q) (208)) (literal (valuationOf q) (399)) (countLit q [207]) (countLit q [208]) (count399 q) 1 (meaning208 q) (meaning399 q) hs
  change valuationOf q 208 = false ∨ valuationOf q 399 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause481 (q : Snake 81) (h : Conditions q) : valuation q 208 = false ∨ valuation q 399 = true := counterClause481 (baseVal q)

theorem counterClause482 (q : Nat → Bool) : valuationOf q 399 = false ∨ valuationOf q 401 = true := by
  have hs : count401 q = (countLit q [205, 206]) + (countLit q [207, 208]) := List.countP_append (p := literal q) (l₁ := [205, 206]) (l₂ := [207, 208])
  have hm := merge_right (literal (valuationOf q) (399)) (literal (valuationOf q) (401)) (countLit q [205, 206]) (countLit q [207, 208]) (count401 q) 1 (meaning399 q) (meaning401 q) hs
  change valuationOf q 399 = false ∨ valuationOf q 401 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause482 (q : Snake 81) (h : Conditions q) : valuation q 399 = false ∨ valuation q 401 = true := counterClause482 (baseVal q)

theorem counterClause483 (q : Nat → Bool) : valuationOf q 397 = false ∨ valuationOf q 401 = true := by
  have hs : count401 q = (countLit q [205, 206]) + (countLit q [207, 208]) := List.countP_append (p := literal q) (l₁ := [205, 206]) (l₂ := [207, 208])
  have hm := merge_left (literal (valuationOf q) (397)) (literal (valuationOf q) (401)) (countLit q [205, 206]) (countLit q [207, 208]) (count401 q) 1 (meaning397 q) (meaning401 q) hs
  change valuationOf q 397 = false ∨ valuationOf q 401 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause483 (q : Snake 81) (h : Conditions q) : valuation q 397 = false ∨ valuation q 401 = true := counterClause483 (baseVal q)

theorem counterClause484 (q : Nat → Bool) : valuationOf q 401 = false ∨ valuationOf q 403 = true := by
  have hs : count403 q = (countLit q [202, 203, 204]) + (countLit q [205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [202, 203, 204]) (l₂ := [205, 206, 207, 208])
  have hm := merge_right (literal (valuationOf q) (401)) (literal (valuationOf q) (403)) (countLit q [202, 203, 204]) (countLit q [205, 206, 207, 208]) (count403 q) 1 (meaning401 q) (meaning403 q) hs
  change valuationOf q 401 = false ∨ valuationOf q 403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause484 (q : Snake 81) (h : Conditions q) : valuation q 401 = false ∨ valuation q 403 = true := counterClause484 (baseVal q)

theorem counterClause485 (q : Nat → Bool) : valuationOf q 395 = false ∨ valuationOf q 403 = true := by
  have hs : count403 q = (countLit q [202, 203, 204]) + (countLit q [205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [202, 203, 204]) (l₂ := [205, 206, 207, 208])
  have hm := merge_left (literal (valuationOf q) (395)) (literal (valuationOf q) (403)) (countLit q [202, 203, 204]) (countLit q [205, 206, 207, 208]) (count403 q) 1 (meaning395 q) (meaning403 q) hs
  change valuationOf q 395 = false ∨ valuationOf q 403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause485 (q : Snake 81) (h : Conditions q) : valuation q 395 = false ∨ valuation q 403 = true := counterClause485 (baseVal q)

theorem counterClause486 (q : Nat → Bool) : valuationOf q 403 = false ∨ valuationOf q 405 = true := by
  have hs : count405 q = (countLit q [196, 197, 198, 199, 200, 201]) + (countLit q [202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [196, 197, 198, 199, 200, 201]) (l₂ := [202, 203, 204, 205, 206, 207, 208])
  have hm := merge_right (literal (valuationOf q) (403)) (literal (valuationOf q) (405)) (countLit q [196, 197, 198, 199, 200, 201]) (countLit q [202, 203, 204, 205, 206, 207, 208]) (count405 q) 1 (meaning403 q) (meaning405 q) hs
  change valuationOf q 403 = false ∨ valuationOf q 405 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause486 (q : Snake 81) (h : Conditions q) : valuation q 403 = false ∨ valuation q 405 = true := counterClause486 (baseVal q)

theorem counterClause487 (q : Nat → Bool) : valuationOf q 391 = false ∨ valuationOf q 405 = true := by
  have hs : count405 q = (countLit q [196, 197, 198, 199, 200, 201]) + (countLit q [202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [196, 197, 198, 199, 200, 201]) (l₂ := [202, 203, 204, 205, 206, 207, 208])
  have hm := merge_left (literal (valuationOf q) (391)) (literal (valuationOf q) (405)) (countLit q [196, 197, 198, 199, 200, 201]) (countLit q [202, 203, 204, 205, 206, 207, 208]) (count405 q) 1 (meaning391 q) (meaning405 q) hs
  change valuationOf q 391 = false ∨ valuationOf q 405 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause487 (q : Snake 81) (h : Conditions q) : valuation q 391 = false ∨ valuation q 405 = true := counterClause487 (baseVal q)

theorem counterClause488 (q : Nat → Bool) : valuationOf q 405 = false ∨ valuationOf q 407 = true := by
  have hs : count407 q = (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195]) + (countLit q [196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195]) (l₂ := [196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208])
  have hm := merge_right (literal (valuationOf q) (405)) (literal (valuationOf q) (407)) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195]) (countLit q [196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (count407 q) 1 (meaning405 q) (meaning407 q) hs
  change valuationOf q 405 = false ∨ valuationOf q 407 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause488 (q : Snake 81) (h : Conditions q) : valuation q 405 = false ∨ valuation q 407 = true := counterClause488 (baseVal q)

theorem counterClause489 (q : Nat → Bool) : valuationOf q 381 = false ∨ valuationOf q 407 = true := by
  have hs : count407 q = (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195]) + (countLit q [196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195]) (l₂ := [196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208])
  have hm := merge_left (literal (valuationOf q) (381)) (literal (valuationOf q) (407)) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195]) (countLit q [196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (count407 q) 1 (meaning381 q) (meaning407 q) hs
  change valuationOf q 381 = false ∨ valuationOf q 407 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause489 (q : Snake 81) (h : Conditions q) : valuation q 381 = false ∨ valuation q 407 = true := counterClause489 (baseVal q)

theorem counterClause490 (q : Nat → Bool) : valuationOf q 381 = false ∨ valuationOf q 405 = false ∨ valuationOf q 408 = true := by
  have hs : count407 q = (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195]) + (countLit q [196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195]) (l₂ := [196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208])
  have hm := merge_two (literal (valuationOf q) (381)) (literal (valuationOf q) (405)) (literal (valuationOf q) (408)) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195]) (countLit q [196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (count407 q) 1 1 (meaning381 q) (meaning405 q) (meaning408 q) hs
  change valuationOf q 381 = false ∨ valuationOf q 405 = false ∨ valuationOf q 408 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause490 (q : Snake 81) (h : Conditions q) : valuation q 381 = false ∨ valuation q 405 = false ∨ valuation q 408 = true := counterClause490 (baseVal q)

theorem counterClause491 (q : Nat → Bool) : valuationOf q 407 = false ∨ valuationOf q 409 = true := by
  have hs : count409 q = (countLit q [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 175, 176, 177, 178, 179, 180, 181, 182]) + (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 175, 176, 177, 178, 179, 180, 181, 182]) (l₂ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208])
  have hm := merge_right (literal (valuationOf q) (407)) (literal (valuationOf q) (409)) (countLit q [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 175, 176, 177, 178, 179, 180, 181, 182]) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (count409 q) 1 (meaning407 q) (meaning409 q) hs
  change valuationOf q 407 = false ∨ valuationOf q 409 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause491 (q : Snake 81) (h : Conditions q) : valuation q 407 = false ∨ valuation q 409 = true := counterClause491 (baseVal q)

theorem counterClause492 (q : Nat → Bool) : valuationOf q 408 = false ∨ valuationOf q 410 = true := by
  have hs : count409 q = (countLit q [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 175, 176, 177, 178, 179, 180, 181, 182]) + (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 175, 176, 177, 178, 179, 180, 181, 182]) (l₂ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208])
  have hm := merge_right (literal (valuationOf q) (408)) (literal (valuationOf q) (410)) (countLit q [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 175, 176, 177, 178, 179, 180, 181, 182]) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (count409 q) 2 (meaning408 q) (meaning410 q) hs
  change valuationOf q 408 = false ∨ valuationOf q 410 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause492 (q : Snake 81) (h : Conditions q) : valuation q 408 = false ∨ valuation q 410 = true := counterClause492 (baseVal q)

theorem counterClause493 (q : Nat → Bool) : valuationOf q 357 = false ∨ valuationOf q 409 = true := by
  have hs : count409 q = (countLit q [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 175, 176, 177, 178, 179, 180, 181, 182]) + (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 175, 176, 177, 178, 179, 180, 181, 182]) (l₂ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208])
  have hm := merge_left (literal (valuationOf q) (357)) (literal (valuationOf q) (409)) (countLit q [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 175, 176, 177, 178, 179, 180, 181, 182]) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (count409 q) 1 (meaning357 q) (meaning409 q) hs
  change valuationOf q 357 = false ∨ valuationOf q 409 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause493 (q : Snake 81) (h : Conditions q) : valuation q 357 = false ∨ valuation q 409 = true := counterClause493 (baseVal q)

theorem counterClause494 (q : Nat → Bool) : valuationOf q 357 = false ∨ valuationOf q 407 = false ∨ valuationOf q 410 = true := by
  have hs : count409 q = (countLit q [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 175, 176, 177, 178, 179, 180, 181, 182]) + (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 175, 176, 177, 178, 179, 180, 181, 182]) (l₂ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208])
  have hm := merge_two (literal (valuationOf q) (357)) (literal (valuationOf q) (407)) (literal (valuationOf q) (410)) (countLit q [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 175, 176, 177, 178, 179, 180, 181, 182]) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (count409 q) 1 1 (meaning357 q) (meaning407 q) (meaning410 q) hs
  change valuationOf q 357 = false ∨ valuationOf q 407 = false ∨ valuationOf q 410 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause494 (q : Snake 81) (h : Conditions q) : valuation q 357 = false ∨ valuation q 407 = false ∨ valuation q 410 = true := counterClause494 (baseVal q)

theorem counterClause495 (q : Nat → Bool) : valuationOf q 358 = false ∨ valuationOf q 410 = true := by
  have hs : count409 q = (countLit q [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 175, 176, 177, 178, 179, 180, 181, 182]) + (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 175, 176, 177, 178, 179, 180, 181, 182]) (l₂ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208])
  have hm := merge_left (literal (valuationOf q) (358)) (literal (valuationOf q) (410)) (countLit q [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 175, 176, 177, 178, 179, 180, 181, 182]) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (count409 q) 2 (meaning358 q) (meaning410 q) hs
  change valuationOf q 358 = false ∨ valuationOf q 410 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause495 (q : Snake 81) (h : Conditions q) : valuation q 358 = false ∨ valuation q 410 = true := counterClause495 (baseVal q)

theorem counterClause496 (q : Nat → Bool) : valuationOf q 410 = false ∨ valuationOf q 412 = true := by
  have hs : count411 q = (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) + (countLit q [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (l₂ := [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208])
  have hm := merge_right (literal (valuationOf q) (410)) (literal (valuationOf q) (412)) (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (countLit q [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (count411 q) 2 (meaning410 q) (meaning412 q) hs
  change valuationOf q 410 = false ∨ valuationOf q 412 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause496 (q : Snake 81) (h : Conditions q) : valuation q 410 = false ∨ valuation q 412 = true := counterClause496 (baseVal q)

theorem counterClause497 (q : Nat → Bool) : valuationOf q 307 = false ∨ valuationOf q 409 = false ∨ valuationOf q 412 = true := by
  have hs : count411 q = (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) + (countLit q [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (l₂ := [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208])
  have hm := merge_two (literal (valuationOf q) (307)) (literal (valuationOf q) (409)) (literal (valuationOf q) (412)) (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (countLit q [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (count411 q) 1 1 (meaning307 q) (meaning409 q) (meaning412 q) hs
  change valuationOf q 307 = false ∨ valuationOf q 409 = false ∨ valuationOf q 412 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause497 (q : Snake 81) (h : Conditions q) : valuation q 307 = false ∨ valuation q 409 = false ∨ valuation q 412 = true := counterClause497 (baseVal q)

theorem counterClause498 (q : Nat → Bool) : valuationOf q 308 = false ∨ valuationOf q 412 = true := by
  have hs : count411 q = (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) + (countLit q [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (l₂ := [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208])
  have hm := merge_left (literal (valuationOf q) (308)) (literal (valuationOf q) (412)) (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (countLit q [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (count411 q) 2 (meaning308 q) (meaning412 q) hs
  change valuationOf q 308 = false ∨ valuationOf q 412 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause498 (q : Snake 81) (h : Conditions q) : valuation q 308 = false ∨ valuation q 412 = true := counterClause498 (baseVal q)

theorem clause499 (q : Snake 81) (h : Conditions q) : valuation q 412 = false := by
  rw [value412]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count411 (baseVal q) = (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := other_count_bound q h
  rw [he]
  omega

theorem clause500 (q : Snake 81) (h : Conditions q) : valuation q 105 = true ∨ valuation q 106 = true ∨ valuation q 107 = true ∨ valuation q 108 = true ∨ valuation q 109 = true ∨ valuation q 110 = true ∨ valuation q 111 = true ∨ valuation q 112 = true ∨ valuation q 113 = true ∨ valuation q 114 = true ∨ valuation q 115 = true ∨ valuation q 116 = true ∨ valuation q 117 = true ∨ valuation q 118 = true ∨ valuation q 119 = true ∨ valuation q 120 = true ∨ valuation q 121 = true ∨ valuation q 122 = true ∨ valuation q 123 = true ∨ valuation q 124 = true ∨ valuation q 125 = true ∨ valuation q 126 = true ∨ valuation q 127 = true ∨ valuation q 128 = true ∨ valuation q 129 = true ∨ valuation q 130 = true ∨ valuation q 131 = true ∨ valuation q 132 = true ∨ valuation q 133 = true ∨ valuation q 134 = true ∨ valuation q 135 = true ∨ valuation q 136 = true ∨ valuation q 137 = true ∨ valuation q 138 = true ∨ valuation q 139 = true ∨ valuation q 140 = true ∨ valuation q 141 = true ∨ valuation q 142 = true ∨ valuation q 143 = true ∨ valuation q 144 = true ∨ valuation q 145 = true ∨ valuation q 146 = true ∨ valuation q 147 = true ∨ valuation q 148 = true ∨ valuation q 149 = true ∨ valuation q 150 = true ∨ valuation q 151 = true ∨ valuation q 152 = true ∨ valuation q 153 = true ∨ valuation q 154 = true ∨ valuation q 155 = true ∨ valuation q 156 = true ∨ valuation q 157 = true ∨ valuation q 158 = true ∨ valuation q 159 = true ∨ valuation q 160 = true ∨ valuation q 161 = true ∨ valuation q 162 = true ∨ valuation q 163 = true ∨ valuation q 164 = true ∨ valuation q 165 = true ∨ valuation q 166 = true ∨ valuation q 167 = true ∨ valuation q 168 = true ∨ valuation q 169 = true ∨ valuation q 170 = true ∨ valuation q 171 = true ∨ valuation q 172 = true ∨ valuation q 173 = true ∨ valuation q 175 = true ∨ valuation q 176 = true ∨ valuation q 177 = true ∨ valuation q 178 = true ∨ valuation q 179 = true ∨ valuation q 180 = true ∨ valuation q 181 = true ∨ valuation q 182 = true ∨ valuation q 183 = true ∨ valuation q 184 = true ∨ valuation q 185 = true ∨ valuation q 186 = true ∨ valuation q 187 = true ∨ valuation q 188 = true ∨ valuation q 189 = true ∨ valuation q 190 = true ∨ valuation q 191 = true ∨ valuation q 192 = true ∨ valuation q 193 = true ∨ valuation q 194 = true ∨ valuation q 195 = true ∨ valuation q 196 = true ∨ valuation q 197 = true ∨ valuation q 198 = true ∨ valuation q 199 = true ∨ valuation q 200 = true ∨ valuation q 201 = true ∨ valuation q 202 = true ∨ valuation q 203 = true ∨ valuation q 204 = true ∨ valuation q 205 = true ∨ valuation q 206 = true ∨ valuation q 207 = true ∨ valuation q 208 = true := by
  rw [value105, value106, value107, value108, value109, value110, value111, value112, value113, value114, value115, value116, value117, value118, value119, value120, value121, value122, value123, value124, value125, value126, value127, value128, value129, value130, value131, value132, value133, value134, value135, value136, value137, value138, value139, value140, value141, value142, value143, value144, value145, value146, value147, value148, value149, value150, value151, value152, value153, value154, value155, value156, value157, value158, value159, value160, value161, value162, value163, value164, value165, value166, value167, value168, value169, value170, value171, value172, value173, value175, value176, value177, value178, value179, value180, value181, value182, value183, value184, value185, value186, value187, value188, value189, value190, value191, value192, value193, value194, value195, value196, value197, value198, value199, value200, value201, value202, value203, value204, value205, value206, value207, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hg := other_endpoint q others (fun v hv hn => others_mem v (h.covered v hv) (by simpa only [h.head_fixed] using hn))
  simpa only [others, List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem counterClause501 (q : Nat → Bool) : valuationOf q 6 = true ∨ valuationOf q 697 = true := by
  have hs : count697 q = (countLit q [-4]) + (countLit q [-6]) := List.countP_append (p := literal q) (l₁ := [-4]) (l₂ := [-6])
  have hm := merge_right (literal (valuationOf q) (-6)) (literal (valuationOf q) (697)) (countLit q [-4]) (countLit q [-6]) (count697 q) 1 (meaningNeg6 q) (meaning697 q) hs
  change (! (valuationOf q 6)) = false ∨ valuationOf q 697 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause501 (q : Snake 81) (h : Conditions q) : valuation q 6 = true ∨ valuation q 697 = true := counterClause501 (baseVal q)

theorem counterClause502 (q : Nat → Bool) : valuationOf q 4 = true ∨ valuationOf q 697 = true := by
  have hs : count697 q = (countLit q [-4]) + (countLit q [-6]) := List.countP_append (p := literal q) (l₁ := [-4]) (l₂ := [-6])
  have hm := merge_left (literal (valuationOf q) (-4)) (literal (valuationOf q) (697)) (countLit q [-4]) (countLit q [-6]) (count697 q) 1 (meaningNeg4 q) (meaning697 q) hs
  change (! (valuationOf q 4)) = false ∨ valuationOf q 697 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause502 (q : Snake 81) (h : Conditions q) : valuation q 4 = true ∨ valuation q 697 = true := counterClause502 (baseVal q)

theorem counterClause503 (q : Nat → Bool) : valuationOf q 4 = true ∨ valuationOf q 6 = true ∨ valuationOf q 698 = true := by
  have hs : count697 q = (countLit q [-4]) + (countLit q [-6]) := List.countP_append (p := literal q) (l₁ := [-4]) (l₂ := [-6])
  have hm := merge_two (literal (valuationOf q) (-4)) (literal (valuationOf q) (-6)) (literal (valuationOf q) (698)) (countLit q [-4]) (countLit q [-6]) (count697 q) 1 1 (meaningNeg4 q) (meaningNeg6 q) (meaning698 q) hs
  change (! (valuationOf q 4)) = false ∨ (! (valuationOf q 6)) = false ∨ valuationOf q 698 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause503 (q : Snake 81) (h : Conditions q) : valuation q 4 = true ∨ valuation q 6 = true ∨ valuation q 698 = true := counterClause503 (baseVal q)

theorem counterClause504 (q : Nat → Bool) : valuationOf q 697 = false ∨ valuationOf q 699 = true := by
  have hs : count699 q = (countLit q [-3]) + (countLit q [-4, -6]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-4, -6])
  have hm := merge_right (literal (valuationOf q) (697)) (literal (valuationOf q) (699)) (countLit q [-3]) (countLit q [-4, -6]) (count699 q) 1 (meaning697 q) (meaning699 q) hs
  change valuationOf q 697 = false ∨ valuationOf q 699 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause504 (q : Snake 81) (h : Conditions q) : valuation q 697 = false ∨ valuation q 699 = true := counterClause504 (baseVal q)

theorem counterClause505 (q : Nat → Bool) : valuationOf q 698 = false ∨ valuationOf q 700 = true := by
  have hs : count699 q = (countLit q [-3]) + (countLit q [-4, -6]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-4, -6])
  have hm := merge_right (literal (valuationOf q) (698)) (literal (valuationOf q) (700)) (countLit q [-3]) (countLit q [-4, -6]) (count699 q) 2 (meaning698 q) (meaning700 q) hs
  change valuationOf q 698 = false ∨ valuationOf q 700 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause505 (q : Snake 81) (h : Conditions q) : valuation q 698 = false ∨ valuation q 700 = true := counterClause505 (baseVal q)

theorem counterClause506 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 699 = true := by
  have hs : count699 q = (countLit q [-3]) + (countLit q [-4, -6]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-4, -6])
  have hm := merge_left (literal (valuationOf q) (-3)) (literal (valuationOf q) (699)) (countLit q [-3]) (countLit q [-4, -6]) (count699 q) 1 (meaningNeg3 q) (meaning699 q) hs
  change (! (valuationOf q 3)) = false ∨ valuationOf q 699 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause506 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 699 = true := counterClause506 (baseVal q)

theorem counterClause507 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 697 = false ∨ valuationOf q 700 = true := by
  have hs : count699 q = (countLit q [-3]) + (countLit q [-4, -6]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-4, -6])
  have hm := merge_two (literal (valuationOf q) (-3)) (literal (valuationOf q) (697)) (literal (valuationOf q) (700)) (countLit q [-3]) (countLit q [-4, -6]) (count699 q) 1 1 (meaningNeg3 q) (meaning697 q) (meaning700 q) hs
  change (! (valuationOf q 3)) = false ∨ valuationOf q 697 = false ∨ valuationOf q 700 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause507 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 697 = false ∨ valuation q 700 = true := counterClause507 (baseVal q)

theorem counterClause508 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 698 = false ∨ valuationOf q 701 = true := by
  have hs : count699 q = (countLit q [-3]) + (countLit q [-4, -6]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-4, -6])
  have hm := merge_two (literal (valuationOf q) (-3)) (literal (valuationOf q) (698)) (literal (valuationOf q) (701)) (countLit q [-3]) (countLit q [-4, -6]) (count699 q) 1 2 (meaningNeg3 q) (meaning698 q) (meaning701 q) hs
  change (! (valuationOf q 3)) = false ∨ valuationOf q 698 = false ∨ valuationOf q 701 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause508 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 698 = false ∨ valuation q 701 = true := counterClause508 (baseVal q)

theorem counterClause509 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 702 = true := by
  have hs : count702 q = (countLit q [-12]) + (countLit q [-14]) := List.countP_append (p := literal q) (l₁ := [-12]) (l₂ := [-14])
  have hm := merge_right (literal (valuationOf q) (-14)) (literal (valuationOf q) (702)) (countLit q [-12]) (countLit q [-14]) (count702 q) 1 (meaningNeg14 q) (meaning702 q) hs
  change (! (valuationOf q 14)) = false ∨ valuationOf q 702 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause509 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 702 = true := counterClause509 (baseVal q)

theorem counterClause510 (q : Nat → Bool) : valuationOf q 12 = true ∨ valuationOf q 702 = true := by
  have hs : count702 q = (countLit q [-12]) + (countLit q [-14]) := List.countP_append (p := literal q) (l₁ := [-12]) (l₂ := [-14])
  have hm := merge_left (literal (valuationOf q) (-12)) (literal (valuationOf q) (702)) (countLit q [-12]) (countLit q [-14]) (count702 q) 1 (meaningNeg12 q) (meaning702 q) hs
  change (! (valuationOf q 12)) = false ∨ valuationOf q 702 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause510 (q : Snake 81) (h : Conditions q) : valuation q 12 = true ∨ valuation q 702 = true := counterClause510 (baseVal q)

theorem counterClause511 (q : Nat → Bool) : valuationOf q 12 = true ∨ valuationOf q 14 = true ∨ valuationOf q 703 = true := by
  have hs : count702 q = (countLit q [-12]) + (countLit q [-14]) := List.countP_append (p := literal q) (l₁ := [-12]) (l₂ := [-14])
  have hm := merge_two (literal (valuationOf q) (-12)) (literal (valuationOf q) (-14)) (literal (valuationOf q) (703)) (countLit q [-12]) (countLit q [-14]) (count702 q) 1 1 (meaningNeg12 q) (meaningNeg14 q) (meaning703 q) hs
  change (! (valuationOf q 12)) = false ∨ (! (valuationOf q 14)) = false ∨ valuationOf q 703 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause511 (q : Snake 81) (h : Conditions q) : valuation q 12 = true ∨ valuation q 14 = true ∨ valuation q 703 = true := counterClause511 (baseVal q)

theorem counterClause512 (q : Nat → Bool) : valuationOf q 702 = false ∨ valuationOf q 704 = true := by
  have hs : count704 q = (countLit q [-10]) + (countLit q [-12, -14]) := List.countP_append (p := literal q) (l₁ := [-10]) (l₂ := [-12, -14])
  have hm := merge_right (literal (valuationOf q) (702)) (literal (valuationOf q) (704)) (countLit q [-10]) (countLit q [-12, -14]) (count704 q) 1 (meaning702 q) (meaning704 q) hs
  change valuationOf q 702 = false ∨ valuationOf q 704 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause512 (q : Snake 81) (h : Conditions q) : valuation q 702 = false ∨ valuation q 704 = true := counterClause512 (baseVal q)

theorem block15 (q : Snake 81) (h : Conditions q) : B112E174.Block15 (valuation q) :=
  ⟨clause481 q h, clause482 q h, clause483 q h, clause484 q h, clause485 q h, clause486 q h, clause487 q h, clause488 q h, clause489 q h, clause490 q h, clause491 q h, clause492 q h, clause493 q h, clause494 q h, clause495 q h, clause496 q h, clause497 q h, clause498 q h, clause499 q h, clause500 q h, clause501 q h, clause502 q h, clause503 q h, clause504 q h, clause505 q h, clause506 q h, clause507 q h, clause508 q h, clause509 q h, clause510 q h, clause511 q h, clause512 q h⟩

end
end Snake9.Regrowth.E112174
