import E112123Semantics
import B112E123Inputs
namespace Snake9.Regrowth.E112123
noncomputable section
local instance blockDec11 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause353 (q : Nat → Bool) : valuationOf q 378 = false ∨ valuationOf q 434 = true := by
  have hs : count433 q = (countLit q [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) + (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) := List.countP_append (p := literal q) (l₁ := [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) (l₂ := [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220])
  have hm := merge_left (literal (valuationOf q) (378)) (literal (valuationOf q) (434)) (countLit q [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) (count433 q) 2 (meaning378 q) (meaning434 q) hs
  change valuationOf q 378 = false ∨ valuationOf q 434 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause353 (q : Snake 81) (h : Conditions q) : valuation q 378 = false ∨ valuation q 434 = true := counterClause353 (baseVal q)

theorem counterClause354 (q : Nat → Bool) : valuationOf q 434 = false ∨ valuationOf q 436 = true := by
  have hs : count435 q = (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 161, 162, 163, 164, 165]) + (countLit q [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) := List.countP_append (p := literal q) (l₁ := [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 161, 162, 163, 164, 165]) (l₂ := [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220])
  have hm := merge_right (literal (valuationOf q) (434)) (literal (valuationOf q) (436)) (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 161, 162, 163, 164, 165]) (countLit q [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) (count435 q) 2 (meaning434 q) (meaning436 q) hs
  change valuationOf q 434 = false ∨ valuationOf q 436 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause354 (q : Snake 81) (h : Conditions q) : valuation q 434 = false ∨ valuation q 436 = true := counterClause354 (baseVal q)

theorem counterClause355 (q : Nat → Bool) : valuationOf q 325 = false ∨ valuationOf q 433 = false ∨ valuationOf q 436 = true := by
  have hs : count435 q = (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 161, 162, 163, 164, 165]) + (countLit q [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) := List.countP_append (p := literal q) (l₁ := [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 161, 162, 163, 164, 165]) (l₂ := [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220])
  have hm := merge_two (literal (valuationOf q) (325)) (literal (valuationOf q) (433)) (literal (valuationOf q) (436)) (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 161, 162, 163, 164, 165]) (countLit q [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) (count435 q) 1 1 (meaning325 q) (meaning433 q) (meaning436 q) hs
  change valuationOf q 325 = false ∨ valuationOf q 433 = false ∨ valuationOf q 436 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause355 (q : Snake 81) (h : Conditions q) : valuation q 325 = false ∨ valuation q 433 = false ∨ valuation q 436 = true := counterClause355 (baseVal q)

theorem counterClause356 (q : Nat → Bool) : valuationOf q 326 = false ∨ valuationOf q 436 = true := by
  have hs : count435 q = (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 161, 162, 163, 164, 165]) + (countLit q [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) := List.countP_append (p := literal q) (l₁ := [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 161, 162, 163, 164, 165]) (l₂ := [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220])
  have hm := merge_left (literal (valuationOf q) (326)) (literal (valuationOf q) (436)) (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 161, 162, 163, 164, 165]) (countLit q [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) (count435 q) 2 (meaning326 q) (meaning436 q) hs
  change valuationOf q 326 = false ∨ valuationOf q 436 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause356 (q : Snake 81) (h : Conditions q) : valuation q 326 = false ∨ valuation q 436 = true := counterClause356 (baseVal q)

theorem clause357 (q : Snake 81) (h : Conditions q) : valuation q 436 = false := by
  rw [value436]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count435 (baseVal q) = (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := other_count_bound q h
  rw [he]
  omega

theorem counterClause358 (q : Nat → Bool) : valuationOf q 5 = true ∨ valuationOf q 757 = true := by
  have hs : count757 q = (countLit q [-4]) + (countLit q [-5]) := List.countP_append (p := literal q) (l₁ := [-4]) (l₂ := [-5])
  have hm := merge_right (literal (valuationOf q) (-5)) (literal (valuationOf q) (757)) (countLit q [-4]) (countLit q [-5]) (count757 q) 1 (meaningNeg5 q) (meaning757 q) hs
  change (! (valuationOf q 5)) = false ∨ valuationOf q 757 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause358 (q : Snake 81) (h : Conditions q) : valuation q 5 = true ∨ valuation q 757 = true := counterClause358 (baseVal q)

theorem counterClause359 (q : Nat → Bool) : valuationOf q 4 = true ∨ valuationOf q 757 = true := by
  have hs : count757 q = (countLit q [-4]) + (countLit q [-5]) := List.countP_append (p := literal q) (l₁ := [-4]) (l₂ := [-5])
  have hm := merge_left (literal (valuationOf q) (-4)) (literal (valuationOf q) (757)) (countLit q [-4]) (countLit q [-5]) (count757 q) 1 (meaningNeg4 q) (meaning757 q) hs
  change (! (valuationOf q 4)) = false ∨ valuationOf q 757 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause359 (q : Snake 81) (h : Conditions q) : valuation q 4 = true ∨ valuation q 757 = true := counterClause359 (baseVal q)

theorem counterClause360 (q : Nat → Bool) : valuationOf q 4 = true ∨ valuationOf q 5 = true ∨ valuationOf q 758 = true := by
  have hs : count757 q = (countLit q [-4]) + (countLit q [-5]) := List.countP_append (p := literal q) (l₁ := [-4]) (l₂ := [-5])
  have hm := merge_two (literal (valuationOf q) (-4)) (literal (valuationOf q) (-5)) (literal (valuationOf q) (758)) (countLit q [-4]) (countLit q [-5]) (count757 q) 1 1 (meaningNeg4 q) (meaningNeg5 q) (meaning758 q) hs
  change (! (valuationOf q 4)) = false ∨ (! (valuationOf q 5)) = false ∨ valuationOf q 758 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause360 (q : Snake 81) (h : Conditions q) : valuation q 4 = true ∨ valuation q 5 = true ∨ valuation q 758 = true := counterClause360 (baseVal q)

theorem counterClause361 (q : Nat → Bool) : valuationOf q 757 = false ∨ valuationOf q 759 = true := by
  have hs : count759 q = (countLit q [-1]) + (countLit q [-4, -5]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-4, -5])
  have hm := merge_right (literal (valuationOf q) (757)) (literal (valuationOf q) (759)) (countLit q [-1]) (countLit q [-4, -5]) (count759 q) 1 (meaning757 q) (meaning759 q) hs
  change valuationOf q 757 = false ∨ valuationOf q 759 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause361 (q : Snake 81) (h : Conditions q) : valuation q 757 = false ∨ valuation q 759 = true := counterClause361 (baseVal q)

theorem counterClause362 (q : Nat → Bool) : valuationOf q 758 = false ∨ valuationOf q 760 = true := by
  have hs : count759 q = (countLit q [-1]) + (countLit q [-4, -5]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-4, -5])
  have hm := merge_right (literal (valuationOf q) (758)) (literal (valuationOf q) (760)) (countLit q [-1]) (countLit q [-4, -5]) (count759 q) 2 (meaning758 q) (meaning760 q) hs
  change valuationOf q 758 = false ∨ valuationOf q 760 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause362 (q : Snake 81) (h : Conditions q) : valuation q 758 = false ∨ valuation q 760 = true := counterClause362 (baseVal q)

theorem counterClause363 (q : Nat → Bool) : valuationOf q 1 = true ∨ valuationOf q 759 = true := by
  have hs : count759 q = (countLit q [-1]) + (countLit q [-4, -5]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-4, -5])
  have hm := merge_left (literal (valuationOf q) (-1)) (literal (valuationOf q) (759)) (countLit q [-1]) (countLit q [-4, -5]) (count759 q) 1 (meaningNeg1 q) (meaning759 q) hs
  change (! (valuationOf q 1)) = false ∨ valuationOf q 759 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause363 (q : Snake 81) (h : Conditions q) : valuation q 1 = true ∨ valuation q 759 = true := counterClause363 (baseVal q)

theorem counterClause364 (q : Nat → Bool) : valuationOf q 1 = true ∨ valuationOf q 757 = false ∨ valuationOf q 760 = true := by
  have hs : count759 q = (countLit q [-1]) + (countLit q [-4, -5]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-4, -5])
  have hm := merge_two (literal (valuationOf q) (-1)) (literal (valuationOf q) (757)) (literal (valuationOf q) (760)) (countLit q [-1]) (countLit q [-4, -5]) (count759 q) 1 1 (meaningNeg1 q) (meaning757 q) (meaning760 q) hs
  change (! (valuationOf q 1)) = false ∨ valuationOf q 757 = false ∨ valuationOf q 760 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause364 (q : Snake 81) (h : Conditions q) : valuation q 1 = true ∨ valuation q 757 = false ∨ valuation q 760 = true := counterClause364 (baseVal q)

theorem counterClause365 (q : Nat → Bool) : valuationOf q 1 = true ∨ valuationOf q 758 = false ∨ valuationOf q 761 = true := by
  have hs : count759 q = (countLit q [-1]) + (countLit q [-4, -5]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-4, -5])
  have hm := merge_two (literal (valuationOf q) (-1)) (literal (valuationOf q) (758)) (literal (valuationOf q) (761)) (countLit q [-1]) (countLit q [-4, -5]) (count759 q) 1 2 (meaningNeg1 q) (meaning758 q) (meaning761 q) hs
  change (! (valuationOf q 1)) = false ∨ valuationOf q 758 = false ∨ valuationOf q 761 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause365 (q : Snake 81) (h : Conditions q) : valuation q 1 = true ∨ valuation q 758 = false ∨ valuation q 761 = true := counterClause365 (baseVal q)

theorem counterClause366 (q : Nat → Bool) : valuationOf q 9 = true ∨ valuationOf q 762 = true := by
  have hs : count762 q = (countLit q [-6]) + (countLit q [-9]) := List.countP_append (p := literal q) (l₁ := [-6]) (l₂ := [-9])
  have hm := merge_right (literal (valuationOf q) (-9)) (literal (valuationOf q) (762)) (countLit q [-6]) (countLit q [-9]) (count762 q) 1 (meaningNeg9 q) (meaning762 q) hs
  change (! (valuationOf q 9)) = false ∨ valuationOf q 762 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause366 (q : Snake 81) (h : Conditions q) : valuation q 9 = true ∨ valuation q 762 = true := counterClause366 (baseVal q)

theorem counterClause367 (q : Nat → Bool) : valuationOf q 6 = true ∨ valuationOf q 762 = true := by
  have hs : count762 q = (countLit q [-6]) + (countLit q [-9]) := List.countP_append (p := literal q) (l₁ := [-6]) (l₂ := [-9])
  have hm := merge_left (literal (valuationOf q) (-6)) (literal (valuationOf q) (762)) (countLit q [-6]) (countLit q [-9]) (count762 q) 1 (meaningNeg6 q) (meaning762 q) hs
  change (! (valuationOf q 6)) = false ∨ valuationOf q 762 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause367 (q : Snake 81) (h : Conditions q) : valuation q 6 = true ∨ valuation q 762 = true := counterClause367 (baseVal q)

theorem counterClause368 (q : Nat → Bool) : valuationOf q 6 = true ∨ valuationOf q 9 = true ∨ valuationOf q 763 = true := by
  have hs : count762 q = (countLit q [-6]) + (countLit q [-9]) := List.countP_append (p := literal q) (l₁ := [-6]) (l₂ := [-9])
  have hm := merge_two (literal (valuationOf q) (-6)) (literal (valuationOf q) (-9)) (literal (valuationOf q) (763)) (countLit q [-6]) (countLit q [-9]) (count762 q) 1 1 (meaningNeg6 q) (meaningNeg9 q) (meaning763 q) hs
  change (! (valuationOf q 6)) = false ∨ (! (valuationOf q 9)) = false ∨ valuationOf q 763 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause368 (q : Snake 81) (h : Conditions q) : valuation q 6 = true ∨ valuation q 9 = true ∨ valuation q 763 = true := counterClause368 (baseVal q)

theorem counterClause369 (q : Nat → Bool) : valuationOf q 12 = true ∨ valuationOf q 764 = true := by
  have hs : count764 q = (countLit q [-11]) + (countLit q [-12]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-12])
  have hm := merge_right (literal (valuationOf q) (-12)) (literal (valuationOf q) (764)) (countLit q [-11]) (countLit q [-12]) (count764 q) 1 (meaningNeg12 q) (meaning764 q) hs
  change (! (valuationOf q 12)) = false ∨ valuationOf q 764 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause369 (q : Snake 81) (h : Conditions q) : valuation q 12 = true ∨ valuation q 764 = true := counterClause369 (baseVal q)

theorem counterClause370 (q : Nat → Bool) : valuationOf q 11 = true ∨ valuationOf q 764 = true := by
  have hs : count764 q = (countLit q [-11]) + (countLit q [-12]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-12])
  have hm := merge_left (literal (valuationOf q) (-11)) (literal (valuationOf q) (764)) (countLit q [-11]) (countLit q [-12]) (count764 q) 1 (meaningNeg11 q) (meaning764 q) hs
  change (! (valuationOf q 11)) = false ∨ valuationOf q 764 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause370 (q : Snake 81) (h : Conditions q) : valuation q 11 = true ∨ valuation q 764 = true := counterClause370 (baseVal q)

theorem counterClause371 (q : Nat → Bool) : valuationOf q 11 = true ∨ valuationOf q 12 = true ∨ valuationOf q 765 = true := by
  have hs : count764 q = (countLit q [-11]) + (countLit q [-12]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-12])
  have hm := merge_two (literal (valuationOf q) (-11)) (literal (valuationOf q) (-12)) (literal (valuationOf q) (765)) (countLit q [-11]) (countLit q [-12]) (count764 q) 1 1 (meaningNeg11 q) (meaningNeg12 q) (meaning765 q) hs
  change (! (valuationOf q 11)) = false ∨ (! (valuationOf q 12)) = false ∨ valuationOf q 765 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause371 (q : Snake 81) (h : Conditions q) : valuation q 11 = true ∨ valuation q 12 = true ∨ valuation q 765 = true := counterClause371 (baseVal q)

theorem counterClause372 (q : Nat → Bool) : valuationOf q 764 = false ∨ valuationOf q 766 = true := by
  have hs : count766 q = (countLit q [-6, -9]) + (countLit q [-11, -12]) := List.countP_append (p := literal q) (l₁ := [-6, -9]) (l₂ := [-11, -12])
  have hm := merge_right (literal (valuationOf q) (764)) (literal (valuationOf q) (766)) (countLit q [-6, -9]) (countLit q [-11, -12]) (count766 q) 1 (meaning764 q) (meaning766 q) hs
  change valuationOf q 764 = false ∨ valuationOf q 766 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause372 (q : Snake 81) (h : Conditions q) : valuation q 764 = false ∨ valuation q 766 = true := counterClause372 (baseVal q)

theorem counterClause373 (q : Nat → Bool) : valuationOf q 765 = false ∨ valuationOf q 767 = true := by
  have hs : count766 q = (countLit q [-6, -9]) + (countLit q [-11, -12]) := List.countP_append (p := literal q) (l₁ := [-6, -9]) (l₂ := [-11, -12])
  have hm := merge_right (literal (valuationOf q) (765)) (literal (valuationOf q) (767)) (countLit q [-6, -9]) (countLit q [-11, -12]) (count766 q) 2 (meaning765 q) (meaning767 q) hs
  change valuationOf q 765 = false ∨ valuationOf q 767 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause373 (q : Snake 81) (h : Conditions q) : valuation q 765 = false ∨ valuation q 767 = true := counterClause373 (baseVal q)

theorem counterClause374 (q : Nat → Bool) : valuationOf q 762 = false ∨ valuationOf q 766 = true := by
  have hs : count766 q = (countLit q [-6, -9]) + (countLit q [-11, -12]) := List.countP_append (p := literal q) (l₁ := [-6, -9]) (l₂ := [-11, -12])
  have hm := merge_left (literal (valuationOf q) (762)) (literal (valuationOf q) (766)) (countLit q [-6, -9]) (countLit q [-11, -12]) (count766 q) 1 (meaning762 q) (meaning766 q) hs
  change valuationOf q 762 = false ∨ valuationOf q 766 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause374 (q : Snake 81) (h : Conditions q) : valuation q 762 = false ∨ valuation q 766 = true := counterClause374 (baseVal q)

theorem counterClause375 (q : Nat → Bool) : valuationOf q 762 = false ∨ valuationOf q 764 = false ∨ valuationOf q 767 = true := by
  have hs : count766 q = (countLit q [-6, -9]) + (countLit q [-11, -12]) := List.countP_append (p := literal q) (l₁ := [-6, -9]) (l₂ := [-11, -12])
  have hm := merge_two (literal (valuationOf q) (762)) (literal (valuationOf q) (764)) (literal (valuationOf q) (767)) (countLit q [-6, -9]) (countLit q [-11, -12]) (count766 q) 1 1 (meaning762 q) (meaning764 q) (meaning767 q) hs
  change valuationOf q 762 = false ∨ valuationOf q 764 = false ∨ valuationOf q 767 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause375 (q : Snake 81) (h : Conditions q) : valuation q 762 = false ∨ valuation q 764 = false ∨ valuation q 767 = true := counterClause375 (baseVal q)

theorem counterClause376 (q : Nat → Bool) : valuationOf q 762 = false ∨ valuationOf q 765 = false ∨ valuationOf q 768 = true := by
  have hs : count766 q = (countLit q [-6, -9]) + (countLit q [-11, -12]) := List.countP_append (p := literal q) (l₁ := [-6, -9]) (l₂ := [-11, -12])
  have hm := merge_two (literal (valuationOf q) (762)) (literal (valuationOf q) (765)) (literal (valuationOf q) (768)) (countLit q [-6, -9]) (countLit q [-11, -12]) (count766 q) 1 2 (meaning762 q) (meaning765 q) (meaning768 q) hs
  change valuationOf q 762 = false ∨ valuationOf q 765 = false ∨ valuationOf q 768 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause376 (q : Snake 81) (h : Conditions q) : valuation q 762 = false ∨ valuation q 765 = false ∨ valuation q 768 = true := counterClause376 (baseVal q)

theorem counterClause377 (q : Nat → Bool) : valuationOf q 763 = false ∨ valuationOf q 767 = true := by
  have hs : count766 q = (countLit q [-6, -9]) + (countLit q [-11, -12]) := List.countP_append (p := literal q) (l₁ := [-6, -9]) (l₂ := [-11, -12])
  have hm := merge_left (literal (valuationOf q) (763)) (literal (valuationOf q) (767)) (countLit q [-6, -9]) (countLit q [-11, -12]) (count766 q) 2 (meaning763 q) (meaning767 q) hs
  change valuationOf q 763 = false ∨ valuationOf q 767 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause377 (q : Snake 81) (h : Conditions q) : valuation q 763 = false ∨ valuation q 767 = true := counterClause377 (baseVal q)

theorem counterClause378 (q : Nat → Bool) : valuationOf q 763 = false ∨ valuationOf q 764 = false ∨ valuationOf q 768 = true := by
  have hs : count766 q = (countLit q [-6, -9]) + (countLit q [-11, -12]) := List.countP_append (p := literal q) (l₁ := [-6, -9]) (l₂ := [-11, -12])
  have hm := merge_two (literal (valuationOf q) (763)) (literal (valuationOf q) (764)) (literal (valuationOf q) (768)) (countLit q [-6, -9]) (countLit q [-11, -12]) (count766 q) 2 1 (meaning763 q) (meaning764 q) (meaning768 q) hs
  change valuationOf q 763 = false ∨ valuationOf q 764 = false ∨ valuationOf q 768 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause378 (q : Snake 81) (h : Conditions q) : valuation q 763 = false ∨ valuation q 764 = false ∨ valuation q 768 = true := counterClause378 (baseVal q)

theorem counterClause379 (q : Nat → Bool) : valuationOf q 763 = false ∨ valuationOf q 765 = false ∨ valuationOf q 769 = true := by
  have hs : count766 q = (countLit q [-6, -9]) + (countLit q [-11, -12]) := List.countP_append (p := literal q) (l₁ := [-6, -9]) (l₂ := [-11, -12])
  have hm := merge_two (literal (valuationOf q) (763)) (literal (valuationOf q) (765)) (literal (valuationOf q) (769)) (countLit q [-6, -9]) (countLit q [-11, -12]) (count766 q) 2 2 (meaning763 q) (meaning765 q) (meaning769 q) hs
  change valuationOf q 763 = false ∨ valuationOf q 765 = false ∨ valuationOf q 769 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause379 (q : Snake 81) (h : Conditions q) : valuation q 763 = false ∨ valuation q 765 = false ∨ valuation q 769 = true := counterClause379 (baseVal q)

theorem counterClause380 (q : Nat → Bool) : valuationOf q 767 = false ∨ valuationOf q 771 = true := by
  have hs : count770 q = (countLit q [-1, -4, -5]) + (countLit q [-6, -9, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5]) (l₂ := [-6, -9, -11, -12])
  have hm := merge_right (literal (valuationOf q) (767)) (literal (valuationOf q) (771)) (countLit q [-1, -4, -5]) (countLit q [-6, -9, -11, -12]) (count770 q) 2 (meaning767 q) (meaning771 q) hs
  change valuationOf q 767 = false ∨ valuationOf q 771 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause380 (q : Snake 81) (h : Conditions q) : valuation q 767 = false ∨ valuation q 771 = true := counterClause380 (baseVal q)

theorem counterClause381 (q : Nat → Bool) : valuationOf q 768 = false ∨ valuationOf q 772 = true := by
  have hs : count770 q = (countLit q [-1, -4, -5]) + (countLit q [-6, -9, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5]) (l₂ := [-6, -9, -11, -12])
  have hm := merge_right (literal (valuationOf q) (768)) (literal (valuationOf q) (772)) (countLit q [-1, -4, -5]) (countLit q [-6, -9, -11, -12]) (count770 q) 3 (meaning768 q) (meaning772 q) hs
  change valuationOf q 768 = false ∨ valuationOf q 772 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause381 (q : Snake 81) (h : Conditions q) : valuation q 768 = false ∨ valuation q 772 = true := counterClause381 (baseVal q)

theorem counterClause382 (q : Nat → Bool) : valuationOf q 769 = false ∨ valuationOf q 773 = true := by
  have hs : count770 q = (countLit q [-1, -4, -5]) + (countLit q [-6, -9, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5]) (l₂ := [-6, -9, -11, -12])
  have hm := merge_right (literal (valuationOf q) (769)) (literal (valuationOf q) (773)) (countLit q [-1, -4, -5]) (countLit q [-6, -9, -11, -12]) (count770 q) 4 (meaning769 q) (meaning773 q) hs
  change valuationOf q 769 = false ∨ valuationOf q 773 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause382 (q : Snake 81) (h : Conditions q) : valuation q 769 = false ∨ valuation q 773 = true := counterClause382 (baseVal q)

theorem counterClause383 (q : Nat → Bool) : valuationOf q 759 = false ∨ valuationOf q 770 = true := by
  have hs : count770 q = (countLit q [-1, -4, -5]) + (countLit q [-6, -9, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5]) (l₂ := [-6, -9, -11, -12])
  have hm := merge_left (literal (valuationOf q) (759)) (literal (valuationOf q) (770)) (countLit q [-1, -4, -5]) (countLit q [-6, -9, -11, -12]) (count770 q) 1 (meaning759 q) (meaning770 q) hs
  change valuationOf q 759 = false ∨ valuationOf q 770 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause383 (q : Snake 81) (h : Conditions q) : valuation q 759 = false ∨ valuation q 770 = true := counterClause383 (baseVal q)

theorem counterClause384 (q : Nat → Bool) : valuationOf q 759 = false ∨ valuationOf q 766 = false ∨ valuationOf q 771 = true := by
  have hs : count770 q = (countLit q [-1, -4, -5]) + (countLit q [-6, -9, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5]) (l₂ := [-6, -9, -11, -12])
  have hm := merge_two (literal (valuationOf q) (759)) (literal (valuationOf q) (766)) (literal (valuationOf q) (771)) (countLit q [-1, -4, -5]) (countLit q [-6, -9, -11, -12]) (count770 q) 1 1 (meaning759 q) (meaning766 q) (meaning771 q) hs
  change valuationOf q 759 = false ∨ valuationOf q 766 = false ∨ valuationOf q 771 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause384 (q : Snake 81) (h : Conditions q) : valuation q 759 = false ∨ valuation q 766 = false ∨ valuation q 771 = true := counterClause384 (baseVal q)

theorem block11 (q : Snake 81) (h : Conditions q) : B112E123.Block11 (valuation q) :=
  ⟨clause353 q h, clause354 q h, clause355 q h, clause356 q h, clause357 q h, clause358 q h, clause359 q h, clause360 q h, clause361 q h, clause362 q h, clause363 q h, clause364 q h, clause365 q h, clause366 q h, clause367 q h, clause368 q h, clause369 q h, clause370 q h, clause371 q h, clause372 q h, clause373 q h, clause374 q h, clause375 q h, clause376 q h, clause377 q h, clause378 q h, clause379 q h, clause380 q h, clause381 q h, clause382 q h, clause383 q h, clause384 q h⟩

end
end Snake9.Regrowth.E112123
