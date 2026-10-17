import E112051Semantics
import B112E051Inputs
namespace Snake9.Regrowth.E112051
noncomputable section
local instance blockDec14 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause449 (q : Nat → Bool) : valuationOf q 441 = false ∨ valuationOf q 443 = true := by
  have hs : count443 q = (countLit q [224, 225]) + (countLit q [226, 227]) := List.countP_append (p := literal q) (l₁ := [224, 225]) (l₂ := [226, 227])
  have hm := merge_right (literal (valuationOf q) (441)) (literal (valuationOf q) (443)) (countLit q [224, 225]) (countLit q [226, 227]) (count443 q) 1 (meaning441 q) (meaning443 q) hs
  change valuationOf q 441 = false ∨ valuationOf q 443 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause449 (q : Snake 81) (h : Conditions q) : valuation q 441 = false ∨ valuation q 443 = true := counterClause449 (baseVal q)

theorem counterClause450 (q : Nat → Bool) : valuationOf q 231 = false ∨ valuationOf q 447 = true := by
  have hs : count447 q = (countLit q [231]) + (countLit q [232]) := List.countP_append (p := literal q) (l₁ := [231]) (l₂ := [232])
  have hm := merge_left (literal (valuationOf q) (231)) (literal (valuationOf q) (447)) (countLit q [231]) (countLit q [232]) (count447 q) 1 (meaning231 q) (meaning447 q) hs
  change valuationOf q 231 = false ∨ valuationOf q 447 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause450 (q : Snake 81) (h : Conditions q) : valuation q 231 = false ∨ valuation q 447 = true := counterClause450 (baseVal q)

theorem counterClause451 (q : Nat → Bool) : valuationOf q 447 = false ∨ valuationOf q 449 = true := by
  have hs : count449 q = (countLit q [228, 230]) + (countLit q [231, 232]) := List.countP_append (p := literal q) (l₁ := [228, 230]) (l₂ := [231, 232])
  have hm := merge_right (literal (valuationOf q) (447)) (literal (valuationOf q) (449)) (countLit q [228, 230]) (countLit q [231, 232]) (count449 q) 1 (meaning447 q) (meaning449 q) hs
  change valuationOf q 447 = false ∨ valuationOf q 449 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause451 (q : Snake 81) (h : Conditions q) : valuation q 447 = false ∨ valuation q 449 = true := counterClause451 (baseVal q)

theorem counterClause452 (q : Nat → Bool) : valuationOf q 449 = false ∨ valuationOf q 451 = true := by
  have hs : count451 q = (countLit q [224, 225, 226, 227]) + (countLit q [228, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [224, 225, 226, 227]) (l₂ := [228, 230, 231, 232])
  have hm := merge_right (literal (valuationOf q) (449)) (literal (valuationOf q) (451)) (countLit q [224, 225, 226, 227]) (countLit q [228, 230, 231, 232]) (count451 q) 1 (meaning449 q) (meaning451 q) hs
  change valuationOf q 449 = false ∨ valuationOf q 451 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause452 (q : Snake 81) (h : Conditions q) : valuation q 449 = false ∨ valuation q 451 = true := counterClause452 (baseVal q)

theorem counterClause453 (q : Nat → Bool) : valuationOf q 443 = false ∨ valuationOf q 451 = true := by
  have hs : count451 q = (countLit q [224, 225, 226, 227]) + (countLit q [228, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [224, 225, 226, 227]) (l₂ := [228, 230, 231, 232])
  have hm := merge_left (literal (valuationOf q) (443)) (literal (valuationOf q) (451)) (countLit q [224, 225, 226, 227]) (countLit q [228, 230, 231, 232]) (count451 q) 1 (meaning443 q) (meaning451 q) hs
  change valuationOf q 443 = false ∨ valuationOf q 451 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause453 (q : Snake 81) (h : Conditions q) : valuation q 443 = false ∨ valuation q 451 = true := counterClause453 (baseVal q)

theorem counterClause454 (q : Nat → Bool) : valuationOf q 451 = false ∨ valuationOf q 453 = true := by
  have hs : count453 q = (countLit q [217, 218, 219, 220, 221, 222, 223]) + (countLit q [224, 225, 226, 227, 228, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [217, 218, 219, 220, 221, 222, 223]) (l₂ := [224, 225, 226, 227, 228, 230, 231, 232])
  have hm := merge_right (literal (valuationOf q) (451)) (literal (valuationOf q) (453)) (countLit q [217, 218, 219, 220, 221, 222, 223]) (countLit q [224, 225, 226, 227, 228, 230, 231, 232]) (count453 q) 1 (meaning451 q) (meaning453 q) hs
  change valuationOf q 451 = false ∨ valuationOf q 453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause454 (q : Snake 81) (h : Conditions q) : valuation q 451 = false ∨ valuation q 453 = true := counterClause454 (baseVal q)

theorem counterClause455 (q : Nat → Bool) : valuationOf q 437 = false ∨ valuationOf q 453 = true := by
  have hs : count453 q = (countLit q [217, 218, 219, 220, 221, 222, 223]) + (countLit q [224, 225, 226, 227, 228, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [217, 218, 219, 220, 221, 222, 223]) (l₂ := [224, 225, 226, 227, 228, 230, 231, 232])
  have hm := merge_left (literal (valuationOf q) (437)) (literal (valuationOf q) (453)) (countLit q [217, 218, 219, 220, 221, 222, 223]) (countLit q [224, 225, 226, 227, 228, 230, 231, 232]) (count453 q) 1 (meaning437 q) (meaning453 q) hs
  change valuationOf q 437 = false ∨ valuationOf q 453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause455 (q : Snake 81) (h : Conditions q) : valuation q 437 = false ∨ valuation q 453 = true := counterClause455 (baseVal q)

theorem counterClause456 (q : Nat → Bool) : valuationOf q 453 = false ∨ valuationOf q 455 = true := by
  have hs : count455 q = (countLit q [203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216]) + (countLit q [217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216]) (l₂ := [217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 230, 231, 232])
  have hm := merge_right (literal (valuationOf q) (453)) (literal (valuationOf q) (455)) (countLit q [203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216]) (countLit q [217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 230, 231, 232]) (count455 q) 1 (meaning453 q) (meaning455 q) hs
  change valuationOf q 453 = false ∨ valuationOf q 455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause456 (q : Snake 81) (h : Conditions q) : valuation q 453 = false ∨ valuation q 455 = true := counterClause456 (baseVal q)

theorem counterClause457 (q : Nat → Bool) : valuationOf q 455 = false ∨ valuationOf q 457 = true := by
  have hs : count457 q = (countLit q [174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202]) + (countLit q [203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202]) (l₂ := [203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 230, 231, 232])
  have hm := merge_right (literal (valuationOf q) (455)) (literal (valuationOf q) (457)) (countLit q [174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202]) (countLit q [203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 230, 231, 232]) (count457 q) 1 (meaning455 q) (meaning457 q) hs
  change valuationOf q 455 = false ∨ valuationOf q 457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause457 (q : Snake 81) (h : Conditions q) : valuation q 455 = false ∨ valuation q 457 = true := counterClause457 (baseVal q)

theorem counterClause458 (q : Nat → Bool) : valuationOf q 399 = false ∨ valuationOf q 457 = true := by
  have hs : count457 q = (countLit q [174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202]) + (countLit q [203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202]) (l₂ := [203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 230, 231, 232])
  have hm := merge_left (literal (valuationOf q) (399)) (literal (valuationOf q) (457)) (countLit q [174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202]) (countLit q [203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 230, 231, 232]) (count457 q) 1 (meaning399 q) (meaning457 q) hs
  change valuationOf q 399 = false ∨ valuationOf q 457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause458 (q : Snake 81) (h : Conditions q) : valuation q 399 = false ∨ valuation q 457 = true := counterClause458 (baseVal q)

theorem counterClause459 (q : Nat → Bool) : valuationOf q 343 = false ∨ valuationOf q 457 = false ∨ valuationOf q 460 = true := by
  have hs : count459 q = (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173]) + (countLit q [174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173]) (l₂ := [174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 230, 231, 232])
  have hm := merge_two (literal (valuationOf q) (343)) (literal (valuationOf q) (457)) (literal (valuationOf q) (460)) (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173]) (countLit q [174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 230, 231, 232]) (count459 q) 1 1 (meaning343 q) (meaning457 q) (meaning460 q) hs
  change valuationOf q 343 = false ∨ valuationOf q 457 = false ∨ valuationOf q 460 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause459 (q : Snake 81) (h : Conditions q) : valuation q 343 = false ∨ valuation q 457 = false ∨ valuation q 460 = true := counterClause459 (baseVal q)

theorem counterClause460 (q : Nat → Bool) : valuationOf q 344 = false ∨ valuationOf q 460 = true := by
  have hs : count459 q = (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173]) + (countLit q [174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173]) (l₂ := [174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 230, 231, 232])
  have hm := merge_left (literal (valuationOf q) (344)) (literal (valuationOf q) (460)) (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173]) (countLit q [174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 230, 231, 232]) (count459 q) 2 (meaning344 q) (meaning460 q) hs
  change valuationOf q 344 = false ∨ valuationOf q 460 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause460 (q : Snake 81) (h : Conditions q) : valuation q 344 = false ∨ valuation q 460 = true := counterClause460 (baseVal q)

theorem clause461 (q : Snake 81) (h : Conditions q) : valuation q 460 = false := by
  rw [value460]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count459 (baseVal q) = (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := other_count_bound q h
  rw [he]
  omega

theorem counterClause462 (q : Nat → Bool) : valuationOf q 6 = true ∨ valuationOf q 781 = true := by
  have hs : count781 q = (countLit q [-3]) + (countLit q [-6]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-6])
  have hm := merge_right (literal (valuationOf q) (-6)) (literal (valuationOf q) (781)) (countLit q [-3]) (countLit q [-6]) (count781 q) 1 (meaningNeg6 q) (meaning781 q) hs
  change (! (valuationOf q 6)) = false ∨ valuationOf q 781 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause462 (q : Snake 81) (h : Conditions q) : valuation q 6 = true ∨ valuation q 781 = true := counterClause462 (baseVal q)

theorem counterClause463 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 781 = true := by
  have hs : count781 q = (countLit q [-3]) + (countLit q [-6]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-6])
  have hm := merge_left (literal (valuationOf q) (-3)) (literal (valuationOf q) (781)) (countLit q [-3]) (countLit q [-6]) (count781 q) 1 (meaningNeg3 q) (meaning781 q) hs
  change (! (valuationOf q 3)) = false ∨ valuationOf q 781 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause463 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 781 = true := counterClause463 (baseVal q)

theorem counterClause464 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 6 = true ∨ valuationOf q 782 = true := by
  have hs : count781 q = (countLit q [-3]) + (countLit q [-6]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-6])
  have hm := merge_two (literal (valuationOf q) (-3)) (literal (valuationOf q) (-6)) (literal (valuationOf q) (782)) (countLit q [-3]) (countLit q [-6]) (count781 q) 1 1 (meaningNeg3 q) (meaningNeg6 q) (meaning782 q) hs
  change (! (valuationOf q 3)) = false ∨ (! (valuationOf q 6)) = false ∨ valuationOf q 782 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause464 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 6 = true ∨ valuation q 782 = true := counterClause464 (baseVal q)

theorem counterClause465 (q : Nat → Bool) : valuationOf q 781 = false ∨ valuationOf q 783 = true := by
  have hs : count783 q = (countLit q [-1]) + (countLit q [-3, -6]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-3, -6])
  have hm := merge_right (literal (valuationOf q) (781)) (literal (valuationOf q) (783)) (countLit q [-1]) (countLit q [-3, -6]) (count783 q) 1 (meaning781 q) (meaning783 q) hs
  change valuationOf q 781 = false ∨ valuationOf q 783 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause465 (q : Snake 81) (h : Conditions q) : valuation q 781 = false ∨ valuation q 783 = true := counterClause465 (baseVal q)

theorem counterClause466 (q : Nat → Bool) : valuationOf q 782 = false ∨ valuationOf q 784 = true := by
  have hs : count783 q = (countLit q [-1]) + (countLit q [-3, -6]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-3, -6])
  have hm := merge_right (literal (valuationOf q) (782)) (literal (valuationOf q) (784)) (countLit q [-1]) (countLit q [-3, -6]) (count783 q) 2 (meaning782 q) (meaning784 q) hs
  change valuationOf q 782 = false ∨ valuationOf q 784 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause466 (q : Snake 81) (h : Conditions q) : valuation q 782 = false ∨ valuation q 784 = true := counterClause466 (baseVal q)

theorem counterClause467 (q : Nat → Bool) : valuationOf q 1 = true ∨ valuationOf q 783 = true := by
  have hs : count783 q = (countLit q [-1]) + (countLit q [-3, -6]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-3, -6])
  have hm := merge_left (literal (valuationOf q) (-1)) (literal (valuationOf q) (783)) (countLit q [-1]) (countLit q [-3, -6]) (count783 q) 1 (meaningNeg1 q) (meaning783 q) hs
  change (! (valuationOf q 1)) = false ∨ valuationOf q 783 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause467 (q : Snake 81) (h : Conditions q) : valuation q 1 = true ∨ valuation q 783 = true := counterClause467 (baseVal q)

theorem counterClause468 (q : Nat → Bool) : valuationOf q 1 = true ∨ valuationOf q 781 = false ∨ valuationOf q 784 = true := by
  have hs : count783 q = (countLit q [-1]) + (countLit q [-3, -6]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-3, -6])
  have hm := merge_two (literal (valuationOf q) (-1)) (literal (valuationOf q) (781)) (literal (valuationOf q) (784)) (countLit q [-1]) (countLit q [-3, -6]) (count783 q) 1 1 (meaningNeg1 q) (meaning781 q) (meaning784 q) hs
  change (! (valuationOf q 1)) = false ∨ valuationOf q 781 = false ∨ valuationOf q 784 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause468 (q : Snake 81) (h : Conditions q) : valuation q 1 = true ∨ valuation q 781 = false ∨ valuation q 784 = true := counterClause468 (baseVal q)

theorem counterClause469 (q : Nat → Bool) : valuationOf q 9 = true ∨ valuationOf q 786 = true := by
  have hs : count786 q = (countLit q [-8]) + (countLit q [-9]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-9])
  have hm := merge_right (literal (valuationOf q) (-9)) (literal (valuationOf q) (786)) (countLit q [-8]) (countLit q [-9]) (count786 q) 1 (meaningNeg9 q) (meaning786 q) hs
  change (! (valuationOf q 9)) = false ∨ valuationOf q 786 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause469 (q : Snake 81) (h : Conditions q) : valuation q 9 = true ∨ valuation q 786 = true := counterClause469 (baseVal q)

theorem counterClause470 (q : Nat → Bool) : valuationOf q 8 = true ∨ valuationOf q 786 = true := by
  have hs : count786 q = (countLit q [-8]) + (countLit q [-9]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-9])
  have hm := merge_left (literal (valuationOf q) (-8)) (literal (valuationOf q) (786)) (countLit q [-8]) (countLit q [-9]) (count786 q) 1 (meaningNeg8 q) (meaning786 q) hs
  change (! (valuationOf q 8)) = false ∨ valuationOf q 786 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause470 (q : Snake 81) (h : Conditions q) : valuation q 8 = true ∨ valuation q 786 = true := counterClause470 (baseVal q)

theorem counterClause471 (q : Nat → Bool) : valuationOf q 8 = true ∨ valuationOf q 9 = true ∨ valuationOf q 787 = true := by
  have hs : count786 q = (countLit q [-8]) + (countLit q [-9]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-9])
  have hm := merge_two (literal (valuationOf q) (-8)) (literal (valuationOf q) (-9)) (literal (valuationOf q) (787)) (countLit q [-8]) (countLit q [-9]) (count786 q) 1 1 (meaningNeg8 q) (meaningNeg9 q) (meaning787 q) hs
  change (! (valuationOf q 8)) = false ∨ (! (valuationOf q 9)) = false ∨ valuationOf q 787 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause471 (q : Snake 81) (h : Conditions q) : valuation q 8 = true ∨ valuation q 9 = true ∨ valuation q 787 = true := counterClause471 (baseVal q)

theorem counterClause472 (q : Nat → Bool) : valuationOf q 15 = true ∨ valuationOf q 788 = true := by
  have hs : count788 q = (countLit q [-10]) + (countLit q [-15]) := List.countP_append (p := literal q) (l₁ := [-10]) (l₂ := [-15])
  have hm := merge_right (literal (valuationOf q) (-15)) (literal (valuationOf q) (788)) (countLit q [-10]) (countLit q [-15]) (count788 q) 1 (meaningNeg15 q) (meaning788 q) hs
  change (! (valuationOf q 15)) = false ∨ valuationOf q 788 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause472 (q : Snake 81) (h : Conditions q) : valuation q 15 = true ∨ valuation q 788 = true := counterClause472 (baseVal q)

theorem counterClause473 (q : Nat → Bool) : valuationOf q 10 = true ∨ valuationOf q 788 = true := by
  have hs : count788 q = (countLit q [-10]) + (countLit q [-15]) := List.countP_append (p := literal q) (l₁ := [-10]) (l₂ := [-15])
  have hm := merge_left (literal (valuationOf q) (-10)) (literal (valuationOf q) (788)) (countLit q [-10]) (countLit q [-15]) (count788 q) 1 (meaningNeg10 q) (meaning788 q) hs
  change (! (valuationOf q 10)) = false ∨ valuationOf q 788 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause473 (q : Snake 81) (h : Conditions q) : valuation q 10 = true ∨ valuation q 788 = true := counterClause473 (baseVal q)

theorem counterClause474 (q : Nat → Bool) : valuationOf q 10 = true ∨ valuationOf q 15 = true ∨ valuationOf q 789 = true := by
  have hs : count788 q = (countLit q [-10]) + (countLit q [-15]) := List.countP_append (p := literal q) (l₁ := [-10]) (l₂ := [-15])
  have hm := merge_two (literal (valuationOf q) (-10)) (literal (valuationOf q) (-15)) (literal (valuationOf q) (789)) (countLit q [-10]) (countLit q [-15]) (count788 q) 1 1 (meaningNeg10 q) (meaningNeg15 q) (meaning789 q) hs
  change (! (valuationOf q 10)) = false ∨ (! (valuationOf q 15)) = false ∨ valuationOf q 789 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause474 (q : Snake 81) (h : Conditions q) : valuation q 10 = true ∨ valuation q 15 = true ∨ valuation q 789 = true := counterClause474 (baseVal q)

theorem counterClause475 (q : Nat → Bool) : valuationOf q 788 = false ∨ valuationOf q 790 = true := by
  have hs : count790 q = (countLit q [-8, -9]) + (countLit q [-10, -15]) := List.countP_append (p := literal q) (l₁ := [-8, -9]) (l₂ := [-10, -15])
  have hm := merge_right (literal (valuationOf q) (788)) (literal (valuationOf q) (790)) (countLit q [-8, -9]) (countLit q [-10, -15]) (count790 q) 1 (meaning788 q) (meaning790 q) hs
  change valuationOf q 788 = false ∨ valuationOf q 790 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause475 (q : Snake 81) (h : Conditions q) : valuation q 788 = false ∨ valuation q 790 = true := counterClause475 (baseVal q)

theorem counterClause476 (q : Nat → Bool) : valuationOf q 789 = false ∨ valuationOf q 791 = true := by
  have hs : count790 q = (countLit q [-8, -9]) + (countLit q [-10, -15]) := List.countP_append (p := literal q) (l₁ := [-8, -9]) (l₂ := [-10, -15])
  have hm := merge_right (literal (valuationOf q) (789)) (literal (valuationOf q) (791)) (countLit q [-8, -9]) (countLit q [-10, -15]) (count790 q) 2 (meaning789 q) (meaning791 q) hs
  change valuationOf q 789 = false ∨ valuationOf q 791 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause476 (q : Snake 81) (h : Conditions q) : valuation q 789 = false ∨ valuation q 791 = true := counterClause476 (baseVal q)

theorem counterClause477 (q : Nat → Bool) : valuationOf q 786 = false ∨ valuationOf q 790 = true := by
  have hs : count790 q = (countLit q [-8, -9]) + (countLit q [-10, -15]) := List.countP_append (p := literal q) (l₁ := [-8, -9]) (l₂ := [-10, -15])
  have hm := merge_left (literal (valuationOf q) (786)) (literal (valuationOf q) (790)) (countLit q [-8, -9]) (countLit q [-10, -15]) (count790 q) 1 (meaning786 q) (meaning790 q) hs
  change valuationOf q 786 = false ∨ valuationOf q 790 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause477 (q : Snake 81) (h : Conditions q) : valuation q 786 = false ∨ valuation q 790 = true := counterClause477 (baseVal q)

theorem counterClause478 (q : Nat → Bool) : valuationOf q 786 = false ∨ valuationOf q 788 = false ∨ valuationOf q 791 = true := by
  have hs : count790 q = (countLit q [-8, -9]) + (countLit q [-10, -15]) := List.countP_append (p := literal q) (l₁ := [-8, -9]) (l₂ := [-10, -15])
  have hm := merge_two (literal (valuationOf q) (786)) (literal (valuationOf q) (788)) (literal (valuationOf q) (791)) (countLit q [-8, -9]) (countLit q [-10, -15]) (count790 q) 1 1 (meaning786 q) (meaning788 q) (meaning791 q) hs
  change valuationOf q 786 = false ∨ valuationOf q 788 = false ∨ valuationOf q 791 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause478 (q : Snake 81) (h : Conditions q) : valuation q 786 = false ∨ valuation q 788 = false ∨ valuation q 791 = true := counterClause478 (baseVal q)

theorem counterClause479 (q : Nat → Bool) : valuationOf q 786 = false ∨ valuationOf q 789 = false ∨ valuationOf q 792 = true := by
  have hs : count790 q = (countLit q [-8, -9]) + (countLit q [-10, -15]) := List.countP_append (p := literal q) (l₁ := [-8, -9]) (l₂ := [-10, -15])
  have hm := merge_two (literal (valuationOf q) (786)) (literal (valuationOf q) (789)) (literal (valuationOf q) (792)) (countLit q [-8, -9]) (countLit q [-10, -15]) (count790 q) 1 2 (meaning786 q) (meaning789 q) (meaning792 q) hs
  change valuationOf q 786 = false ∨ valuationOf q 789 = false ∨ valuationOf q 792 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause479 (q : Snake 81) (h : Conditions q) : valuation q 786 = false ∨ valuation q 789 = false ∨ valuation q 792 = true := counterClause479 (baseVal q)

theorem counterClause480 (q : Nat → Bool) : valuationOf q 787 = false ∨ valuationOf q 791 = true := by
  have hs : count790 q = (countLit q [-8, -9]) + (countLit q [-10, -15]) := List.countP_append (p := literal q) (l₁ := [-8, -9]) (l₂ := [-10, -15])
  have hm := merge_left (literal (valuationOf q) (787)) (literal (valuationOf q) (791)) (countLit q [-8, -9]) (countLit q [-10, -15]) (count790 q) 2 (meaning787 q) (meaning791 q) hs
  change valuationOf q 787 = false ∨ valuationOf q 791 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause480 (q : Snake 81) (h : Conditions q) : valuation q 787 = false ∨ valuation q 791 = true := counterClause480 (baseVal q)

theorem block14 (q : Snake 81) (h : Conditions q) : B112E051.Block14 (valuation q) :=
  ⟨clause449 q h, clause450 q h, clause451 q h, clause452 q h, clause453 q h, clause454 q h, clause455 q h, clause456 q h, clause457 q h, clause458 q h, clause459 q h, clause460 q h, clause461 q h, clause462 q h, clause463 q h, clause464 q h, clause465 q h, clause466 q h, clause467 q h, clause468 q h, clause469 q h, clause470 q h, clause471 q h, clause472 q h, clause473 q h, clause474 q h, clause475 q h, clause476 q h, clause477 q h, clause478 q h, clause479 q h, clause480 q h⟩

end
end Snake9.Regrowth.E112051
