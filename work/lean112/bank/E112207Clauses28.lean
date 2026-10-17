import E112207Semantics
import B112E207Inputs
namespace Snake9.Regrowth.E112207
noncomputable section
local instance blockDec28 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause897 (q : Nat → Bool) : valuationOf q 404 = false ∨ valuationOf q 462 = true := by
  have hs : count461 q = (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]) + (countLit q [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234]) := List.countP_append (p := literal q) (l₁ := [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]) (l₂ := [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234])
  have hm := merge_left (literal (valuationOf q) (404)) (literal (valuationOf q) (462)) (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]) (countLit q [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234]) (count461 q) 2 (meaning404 q) (meaning462 q) hs
  change valuationOf q 404 = false ∨ valuationOf q 462 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause897 (q : Snake 81) (h : Conditions q) : valuation q 404 = false ∨ valuation q 462 = true := counterClause897 (baseVal q)

theorem counterClause898 (q : Nat → Bool) : valuationOf q 462 = false ∨ valuationOf q 464 = true := by
  have hs : count463 q = (countLit q [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]) + (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234]) := List.countP_append (p := literal q) (l₁ := [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]) (l₂ := [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234])
  have hm := merge_right (literal (valuationOf q) (462)) (literal (valuationOf q) (464)) (countLit q [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]) (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234]) (count463 q) 2 (meaning462 q) (meaning464 q) hs
  change valuationOf q 462 = false ∨ valuationOf q 464 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause898 (q : Snake 81) (h : Conditions q) : valuation q 462 = false ∨ valuation q 464 = true := counterClause898 (baseVal q)

theorem counterClause899 (q : Nat → Bool) : valuationOf q 347 = false ∨ valuationOf q 461 = false ∨ valuationOf q 464 = true := by
  have hs : count463 q = (countLit q [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]) + (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234]) := List.countP_append (p := literal q) (l₁ := [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]) (l₂ := [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234])
  have hm := merge_two (literal (valuationOf q) (347)) (literal (valuationOf q) (461)) (literal (valuationOf q) (464)) (countLit q [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]) (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234]) (count463 q) 1 1 (meaning347 q) (meaning461 q) (meaning464 q) hs
  change valuationOf q 347 = false ∨ valuationOf q 461 = false ∨ valuationOf q 464 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause899 (q : Snake 81) (h : Conditions q) : valuation q 347 = false ∨ valuation q 461 = false ∨ valuation q 464 = true := counterClause899 (baseVal q)

theorem counterClause900 (q : Nat → Bool) : valuationOf q 348 = false ∨ valuationOf q 464 = true := by
  have hs : count463 q = (countLit q [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]) + (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234]) := List.countP_append (p := literal q) (l₁ := [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]) (l₂ := [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234])
  have hm := merge_left (literal (valuationOf q) (348)) (literal (valuationOf q) (464)) (countLit q [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]) (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234]) (count463 q) 2 (meaning348 q) (meaning464 q) hs
  change valuationOf q 348 = false ∨ valuationOf q 464 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause900 (q : Snake 81) (h : Conditions q) : valuation q 348 = false ∨ valuation q 464 = true := counterClause900 (baseVal q)

theorem clause901 (q : Snake 81) (h : Conditions q) : valuation q 464 = false := by
  rw [value464]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count463 (baseVal q) = (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := other_count_bound q h
  rw [he]
  omega

theorem counterClause902 (q : Nat → Bool) : valuationOf q 5 = true ∨ valuationOf q 1411 = true := by
  have hs : count1411 q = (countLit q [-4]) + (countLit q [-5]) := List.countP_append (p := literal q) (l₁ := [-4]) (l₂ := [-5])
  have hm := merge_right (literal (valuationOf q) (-5)) (literal (valuationOf q) (1411)) (countLit q [-4]) (countLit q [-5]) (count1411 q) 1 (meaningNeg5 q) (meaning1411 q) hs
  change (! (valuationOf q 5)) = false ∨ valuationOf q 1411 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause902 (q : Snake 81) (h : Conditions q) : valuation q 5 = true ∨ valuation q 1411 = true := counterClause902 (baseVal q)

theorem counterClause903 (q : Nat → Bool) : valuationOf q 4 = true ∨ valuationOf q 1411 = true := by
  have hs : count1411 q = (countLit q [-4]) + (countLit q [-5]) := List.countP_append (p := literal q) (l₁ := [-4]) (l₂ := [-5])
  have hm := merge_left (literal (valuationOf q) (-4)) (literal (valuationOf q) (1411)) (countLit q [-4]) (countLit q [-5]) (count1411 q) 1 (meaningNeg4 q) (meaning1411 q) hs
  change (! (valuationOf q 4)) = false ∨ valuationOf q 1411 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause903 (q : Snake 81) (h : Conditions q) : valuation q 4 = true ∨ valuation q 1411 = true := counterClause903 (baseVal q)

theorem counterClause904 (q : Nat → Bool) : valuationOf q 4 = true ∨ valuationOf q 5 = true ∨ valuationOf q 1412 = true := by
  have hs : count1411 q = (countLit q [-4]) + (countLit q [-5]) := List.countP_append (p := literal q) (l₁ := [-4]) (l₂ := [-5])
  have hm := merge_two (literal (valuationOf q) (-4)) (literal (valuationOf q) (-5)) (literal (valuationOf q) (1412)) (countLit q [-4]) (countLit q [-5]) (count1411 q) 1 1 (meaningNeg4 q) (meaningNeg5 q) (meaning1412 q) hs
  change (! (valuationOf q 4)) = false ∨ (! (valuationOf q 5)) = false ∨ valuationOf q 1412 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause904 (q : Snake 81) (h : Conditions q) : valuation q 4 = true ∨ valuation q 5 = true ∨ valuation q 1412 = true := counterClause904 (baseVal q)

theorem counterClause905 (q : Nat → Bool) : valuationOf q 1411 = false ∨ valuationOf q 1413 = true := by
  have hs : count1413 q = (countLit q [-2]) + (countLit q [-4, -5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-4, -5])
  have hm := merge_right (literal (valuationOf q) (1411)) (literal (valuationOf q) (1413)) (countLit q [-2]) (countLit q [-4, -5]) (count1413 q) 1 (meaning1411 q) (meaning1413 q) hs
  change valuationOf q 1411 = false ∨ valuationOf q 1413 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause905 (q : Snake 81) (h : Conditions q) : valuation q 1411 = false ∨ valuation q 1413 = true := counterClause905 (baseVal q)

theorem counterClause906 (q : Nat → Bool) : valuationOf q 1412 = false ∨ valuationOf q 1414 = true := by
  have hs : count1413 q = (countLit q [-2]) + (countLit q [-4, -5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-4, -5])
  have hm := merge_right (literal (valuationOf q) (1412)) (literal (valuationOf q) (1414)) (countLit q [-2]) (countLit q [-4, -5]) (count1413 q) 2 (meaning1412 q) (meaning1414 q) hs
  change valuationOf q 1412 = false ∨ valuationOf q 1414 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause906 (q : Snake 81) (h : Conditions q) : valuation q 1412 = false ∨ valuation q 1414 = true := counterClause906 (baseVal q)

theorem counterClause907 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1413 = true := by
  have hs : count1413 q = (countLit q [-2]) + (countLit q [-4, -5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-4, -5])
  have hm := merge_left (literal (valuationOf q) (-2)) (literal (valuationOf q) (1413)) (countLit q [-2]) (countLit q [-4, -5]) (count1413 q) 1 (meaningNeg2 q) (meaning1413 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1413 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause907 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1413 = true := counterClause907 (baseVal q)

theorem counterClause908 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1411 = false ∨ valuationOf q 1414 = true := by
  have hs : count1413 q = (countLit q [-2]) + (countLit q [-4, -5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-4, -5])
  have hm := merge_two (literal (valuationOf q) (-2)) (literal (valuationOf q) (1411)) (literal (valuationOf q) (1414)) (countLit q [-2]) (countLit q [-4, -5]) (count1413 q) 1 1 (meaningNeg2 q) (meaning1411 q) (meaning1414 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1414 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause908 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1411 = false ∨ valuation q 1414 = true := counterClause908 (baseVal q)

theorem counterClause909 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1412 = false ∨ valuationOf q 1415 = true := by
  have hs : count1413 q = (countLit q [-2]) + (countLit q [-4, -5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-4, -5])
  have hm := merge_two (literal (valuationOf q) (-2)) (literal (valuationOf q) (1412)) (literal (valuationOf q) (1415)) (countLit q [-2]) (countLit q [-4, -5]) (count1413 q) 1 2 (meaningNeg2 q) (meaning1412 q) (meaning1415 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1412 = false ∨ valuationOf q 1415 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause909 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1412 = false ∨ valuation q 1415 = true := counterClause909 (baseVal q)

theorem counterClause910 (q : Nat → Bool) : valuationOf q 10 = true ∨ valuationOf q 1416 = true := by
  have hs : count1416 q = (countLit q [-6]) + (countLit q [-10]) := List.countP_append (p := literal q) (l₁ := [-6]) (l₂ := [-10])
  have hm := merge_right (literal (valuationOf q) (-10)) (literal (valuationOf q) (1416)) (countLit q [-6]) (countLit q [-10]) (count1416 q) 1 (meaningNeg10 q) (meaning1416 q) hs
  change (! (valuationOf q 10)) = false ∨ valuationOf q 1416 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause910 (q : Snake 81) (h : Conditions q) : valuation q 10 = true ∨ valuation q 1416 = true := counterClause910 (baseVal q)

theorem counterClause911 (q : Nat → Bool) : valuationOf q 6 = true ∨ valuationOf q 1416 = true := by
  have hs : count1416 q = (countLit q [-6]) + (countLit q [-10]) := List.countP_append (p := literal q) (l₁ := [-6]) (l₂ := [-10])
  have hm := merge_left (literal (valuationOf q) (-6)) (literal (valuationOf q) (1416)) (countLit q [-6]) (countLit q [-10]) (count1416 q) 1 (meaningNeg6 q) (meaning1416 q) hs
  change (! (valuationOf q 6)) = false ∨ valuationOf q 1416 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause911 (q : Snake 81) (h : Conditions q) : valuation q 6 = true ∨ valuation q 1416 = true := counterClause911 (baseVal q)

theorem counterClause912 (q : Nat → Bool) : valuationOf q 6 = true ∨ valuationOf q 10 = true ∨ valuationOf q 1417 = true := by
  have hs : count1416 q = (countLit q [-6]) + (countLit q [-10]) := List.countP_append (p := literal q) (l₁ := [-6]) (l₂ := [-10])
  have hm := merge_two (literal (valuationOf q) (-6)) (literal (valuationOf q) (-10)) (literal (valuationOf q) (1417)) (countLit q [-6]) (countLit q [-10]) (count1416 q) 1 1 (meaningNeg6 q) (meaningNeg10 q) (meaning1417 q) hs
  change (! (valuationOf q 6)) = false ∨ (! (valuationOf q 10)) = false ∨ valuationOf q 1417 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause912 (q : Snake 81) (h : Conditions q) : valuation q 6 = true ∨ valuation q 10 = true ∨ valuation q 1417 = true := counterClause912 (baseVal q)

theorem counterClause913 (q : Nat → Bool) : valuationOf q 12 = true ∨ valuationOf q 1418 = true := by
  have hs : count1418 q = (countLit q [-11]) + (countLit q [-12]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-12])
  have hm := merge_right (literal (valuationOf q) (-12)) (literal (valuationOf q) (1418)) (countLit q [-11]) (countLit q [-12]) (count1418 q) 1 (meaningNeg12 q) (meaning1418 q) hs
  change (! (valuationOf q 12)) = false ∨ valuationOf q 1418 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause913 (q : Snake 81) (h : Conditions q) : valuation q 12 = true ∨ valuation q 1418 = true := counterClause913 (baseVal q)

theorem counterClause914 (q : Nat → Bool) : valuationOf q 11 = true ∨ valuationOf q 1418 = true := by
  have hs : count1418 q = (countLit q [-11]) + (countLit q [-12]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-12])
  have hm := merge_left (literal (valuationOf q) (-11)) (literal (valuationOf q) (1418)) (countLit q [-11]) (countLit q [-12]) (count1418 q) 1 (meaningNeg11 q) (meaning1418 q) hs
  change (! (valuationOf q 11)) = false ∨ valuationOf q 1418 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause914 (q : Snake 81) (h : Conditions q) : valuation q 11 = true ∨ valuation q 1418 = true := counterClause914 (baseVal q)

theorem counterClause915 (q : Nat → Bool) : valuationOf q 11 = true ∨ valuationOf q 12 = true ∨ valuationOf q 1419 = true := by
  have hs : count1418 q = (countLit q [-11]) + (countLit q [-12]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-12])
  have hm := merge_two (literal (valuationOf q) (-11)) (literal (valuationOf q) (-12)) (literal (valuationOf q) (1419)) (countLit q [-11]) (countLit q [-12]) (count1418 q) 1 1 (meaningNeg11 q) (meaningNeg12 q) (meaning1419 q) hs
  change (! (valuationOf q 11)) = false ∨ (! (valuationOf q 12)) = false ∨ valuationOf q 1419 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause915 (q : Snake 81) (h : Conditions q) : valuation q 11 = true ∨ valuation q 12 = true ∨ valuation q 1419 = true := counterClause915 (baseVal q)

theorem counterClause916 (q : Nat → Bool) : valuationOf q 1418 = false ∨ valuationOf q 1420 = true := by
  have hs : count1420 q = (countLit q [-6, -10]) + (countLit q [-11, -12]) := List.countP_append (p := literal q) (l₁ := [-6, -10]) (l₂ := [-11, -12])
  have hm := merge_right (literal (valuationOf q) (1418)) (literal (valuationOf q) (1420)) (countLit q [-6, -10]) (countLit q [-11, -12]) (count1420 q) 1 (meaning1418 q) (meaning1420 q) hs
  change valuationOf q 1418 = false ∨ valuationOf q 1420 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause916 (q : Snake 81) (h : Conditions q) : valuation q 1418 = false ∨ valuation q 1420 = true := counterClause916 (baseVal q)

theorem counterClause917 (q : Nat → Bool) : valuationOf q 1419 = false ∨ valuationOf q 1421 = true := by
  have hs : count1420 q = (countLit q [-6, -10]) + (countLit q [-11, -12]) := List.countP_append (p := literal q) (l₁ := [-6, -10]) (l₂ := [-11, -12])
  have hm := merge_right (literal (valuationOf q) (1419)) (literal (valuationOf q) (1421)) (countLit q [-6, -10]) (countLit q [-11, -12]) (count1420 q) 2 (meaning1419 q) (meaning1421 q) hs
  change valuationOf q 1419 = false ∨ valuationOf q 1421 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause917 (q : Snake 81) (h : Conditions q) : valuation q 1419 = false ∨ valuation q 1421 = true := counterClause917 (baseVal q)

theorem counterClause918 (q : Nat → Bool) : valuationOf q 1416 = false ∨ valuationOf q 1420 = true := by
  have hs : count1420 q = (countLit q [-6, -10]) + (countLit q [-11, -12]) := List.countP_append (p := literal q) (l₁ := [-6, -10]) (l₂ := [-11, -12])
  have hm := merge_left (literal (valuationOf q) (1416)) (literal (valuationOf q) (1420)) (countLit q [-6, -10]) (countLit q [-11, -12]) (count1420 q) 1 (meaning1416 q) (meaning1420 q) hs
  change valuationOf q 1416 = false ∨ valuationOf q 1420 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause918 (q : Snake 81) (h : Conditions q) : valuation q 1416 = false ∨ valuation q 1420 = true := counterClause918 (baseVal q)

theorem counterClause919 (q : Nat → Bool) : valuationOf q 1416 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1421 = true := by
  have hs : count1420 q = (countLit q [-6, -10]) + (countLit q [-11, -12]) := List.countP_append (p := literal q) (l₁ := [-6, -10]) (l₂ := [-11, -12])
  have hm := merge_two (literal (valuationOf q) (1416)) (literal (valuationOf q) (1418)) (literal (valuationOf q) (1421)) (countLit q [-6, -10]) (countLit q [-11, -12]) (count1420 q) 1 1 (meaning1416 q) (meaning1418 q) (meaning1421 q) hs
  change valuationOf q 1416 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1421 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause919 (q : Snake 81) (h : Conditions q) : valuation q 1416 = false ∨ valuation q 1418 = false ∨ valuation q 1421 = true := counterClause919 (baseVal q)

theorem counterClause920 (q : Nat → Bool) : valuationOf q 1416 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1422 = true := by
  have hs : count1420 q = (countLit q [-6, -10]) + (countLit q [-11, -12]) := List.countP_append (p := literal q) (l₁ := [-6, -10]) (l₂ := [-11, -12])
  have hm := merge_two (literal (valuationOf q) (1416)) (literal (valuationOf q) (1419)) (literal (valuationOf q) (1422)) (countLit q [-6, -10]) (countLit q [-11, -12]) (count1420 q) 1 2 (meaning1416 q) (meaning1419 q) (meaning1422 q) hs
  change valuationOf q 1416 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1422 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause920 (q : Snake 81) (h : Conditions q) : valuation q 1416 = false ∨ valuation q 1419 = false ∨ valuation q 1422 = true := counterClause920 (baseVal q)

theorem counterClause921 (q : Nat → Bool) : valuationOf q 1417 = false ∨ valuationOf q 1421 = true := by
  have hs : count1420 q = (countLit q [-6, -10]) + (countLit q [-11, -12]) := List.countP_append (p := literal q) (l₁ := [-6, -10]) (l₂ := [-11, -12])
  have hm := merge_left (literal (valuationOf q) (1417)) (literal (valuationOf q) (1421)) (countLit q [-6, -10]) (countLit q [-11, -12]) (count1420 q) 2 (meaning1417 q) (meaning1421 q) hs
  change valuationOf q 1417 = false ∨ valuationOf q 1421 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause921 (q : Snake 81) (h : Conditions q) : valuation q 1417 = false ∨ valuation q 1421 = true := counterClause921 (baseVal q)

theorem counterClause922 (q : Nat → Bool) : valuationOf q 1417 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1422 = true := by
  have hs : count1420 q = (countLit q [-6, -10]) + (countLit q [-11, -12]) := List.countP_append (p := literal q) (l₁ := [-6, -10]) (l₂ := [-11, -12])
  have hm := merge_two (literal (valuationOf q) (1417)) (literal (valuationOf q) (1418)) (literal (valuationOf q) (1422)) (countLit q [-6, -10]) (countLit q [-11, -12]) (count1420 q) 2 1 (meaning1417 q) (meaning1418 q) (meaning1422 q) hs
  change valuationOf q 1417 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1422 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause922 (q : Snake 81) (h : Conditions q) : valuation q 1417 = false ∨ valuation q 1418 = false ∨ valuation q 1422 = true := counterClause922 (baseVal q)

theorem counterClause923 (q : Nat → Bool) : valuationOf q 1417 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1423 = true := by
  have hs : count1420 q = (countLit q [-6, -10]) + (countLit q [-11, -12]) := List.countP_append (p := literal q) (l₁ := [-6, -10]) (l₂ := [-11, -12])
  have hm := merge_two (literal (valuationOf q) (1417)) (literal (valuationOf q) (1419)) (literal (valuationOf q) (1423)) (countLit q [-6, -10]) (countLit q [-11, -12]) (count1420 q) 2 2 (meaning1417 q) (meaning1419 q) (meaning1423 q) hs
  change valuationOf q 1417 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1423 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause923 (q : Snake 81) (h : Conditions q) : valuation q 1417 = false ∨ valuation q 1419 = false ∨ valuation q 1423 = true := counterClause923 (baseVal q)

theorem counterClause924 (q : Nat → Bool) : valuationOf q 1420 = false ∨ valuationOf q 1424 = true := by
  have hs : count1424 q = (countLit q [-2, -4, -5]) + (countLit q [-6, -10, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-6, -10, -11, -12])
  have hm := merge_right (literal (valuationOf q) (1420)) (literal (valuationOf q) (1424)) (countLit q [-2, -4, -5]) (countLit q [-6, -10, -11, -12]) (count1424 q) 1 (meaning1420 q) (meaning1424 q) hs
  change valuationOf q 1420 = false ∨ valuationOf q 1424 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause924 (q : Snake 81) (h : Conditions q) : valuation q 1420 = false ∨ valuation q 1424 = true := counterClause924 (baseVal q)

theorem counterClause925 (q : Nat → Bool) : valuationOf q 1421 = false ∨ valuationOf q 1425 = true := by
  have hs : count1424 q = (countLit q [-2, -4, -5]) + (countLit q [-6, -10, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-6, -10, -11, -12])
  have hm := merge_right (literal (valuationOf q) (1421)) (literal (valuationOf q) (1425)) (countLit q [-2, -4, -5]) (countLit q [-6, -10, -11, -12]) (count1424 q) 2 (meaning1421 q) (meaning1425 q) hs
  change valuationOf q 1421 = false ∨ valuationOf q 1425 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause925 (q : Snake 81) (h : Conditions q) : valuation q 1421 = false ∨ valuation q 1425 = true := counterClause925 (baseVal q)

theorem counterClause926 (q : Nat → Bool) : valuationOf q 1422 = false ∨ valuationOf q 1426 = true := by
  have hs : count1424 q = (countLit q [-2, -4, -5]) + (countLit q [-6, -10, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-6, -10, -11, -12])
  have hm := merge_right (literal (valuationOf q) (1422)) (literal (valuationOf q) (1426)) (countLit q [-2, -4, -5]) (countLit q [-6, -10, -11, -12]) (count1424 q) 3 (meaning1422 q) (meaning1426 q) hs
  change valuationOf q 1422 = false ∨ valuationOf q 1426 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause926 (q : Snake 81) (h : Conditions q) : valuation q 1422 = false ∨ valuation q 1426 = true := counterClause926 (baseVal q)

theorem counterClause927 (q : Nat → Bool) : valuationOf q 1423 = false ∨ valuationOf q 1427 = true := by
  have hs : count1424 q = (countLit q [-2, -4, -5]) + (countLit q [-6, -10, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-6, -10, -11, -12])
  have hm := merge_right (literal (valuationOf q) (1423)) (literal (valuationOf q) (1427)) (countLit q [-2, -4, -5]) (countLit q [-6, -10, -11, -12]) (count1424 q) 4 (meaning1423 q) (meaning1427 q) hs
  change valuationOf q 1423 = false ∨ valuationOf q 1427 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause927 (q : Snake 81) (h : Conditions q) : valuation q 1423 = false ∨ valuation q 1427 = true := counterClause927 (baseVal q)

theorem counterClause928 (q : Nat → Bool) : valuationOf q 1413 = false ∨ valuationOf q 1424 = true := by
  have hs : count1424 q = (countLit q [-2, -4, -5]) + (countLit q [-6, -10, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-6, -10, -11, -12])
  have hm := merge_left (literal (valuationOf q) (1413)) (literal (valuationOf q) (1424)) (countLit q [-2, -4, -5]) (countLit q [-6, -10, -11, -12]) (count1424 q) 1 (meaning1413 q) (meaning1424 q) hs
  change valuationOf q 1413 = false ∨ valuationOf q 1424 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause928 (q : Snake 81) (h : Conditions q) : valuation q 1413 = false ∨ valuation q 1424 = true := counterClause928 (baseVal q)

theorem block28 (q : Snake 81) (h : Conditions q) : B112E207.Block28 (valuation q) :=
  ⟨clause897 q h, clause898 q h, clause899 q h, clause900 q h, clause901 q h, clause902 q h, clause903 q h, clause904 q h, clause905 q h, clause906 q h, clause907 q h, clause908 q h, clause909 q h, clause910 q h, clause911 q h, clause912 q h, clause913 q h, clause914 q h, clause915 q h, clause916 q h, clause917 q h, clause918 q h, clause919 q h, clause920 q h, clause921 q h, clause922 q h, clause923 q h, clause924 q h, clause925 q h, clause926 q h, clause927 q h, clause928 q h⟩

end
end Snake9.Regrowth.E112207
