import E112110Semantics
import B112E110Inputs
namespace Snake9.Regrowth.E112110
noncomputable section
local instance blockDec24 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause769 (q : Nat → Bool) : valuationOf q 463 = false ∨ valuationOf q 465 = true := by
  have hs : count465 q = (countLit q [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) + (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (l₂ := [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236])
  have hm := merge_right (literal (valuationOf q) (463)) (literal (valuationOf q) (465)) (countLit q [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) (count465 q) 1 (meaning463 q) (meaning465 q) hs
  change valuationOf q 463 = false ∨ valuationOf q 465 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause769 (q : Snake 81) (h : Conditions q) : valuation q 463 = false ∨ valuation q 465 = true := counterClause769 (baseVal q)

theorem counterClause770 (q : Nat → Bool) : valuationOf q 464 = false ∨ valuationOf q 466 = true := by
  have hs : count465 q = (countLit q [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) + (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (l₂ := [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236])
  have hm := merge_right (literal (valuationOf q) (464)) (literal (valuationOf q) (466)) (countLit q [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) (count465 q) 2 (meaning464 q) (meaning466 q) hs
  change valuationOf q 464 = false ∨ valuationOf q 466 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause770 (q : Snake 81) (h : Conditions q) : valuation q 464 = false ∨ valuation q 466 = true := counterClause770 (baseVal q)

theorem counterClause771 (q : Nat → Bool) : valuationOf q 405 = false ∨ valuationOf q 465 = true := by
  have hs : count465 q = (countLit q [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) + (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (l₂ := [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236])
  have hm := merge_left (literal (valuationOf q) (405)) (literal (valuationOf q) (465)) (countLit q [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) (count465 q) 1 (meaning405 q) (meaning465 q) hs
  change valuationOf q 405 = false ∨ valuationOf q 465 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause771 (q : Snake 81) (h : Conditions q) : valuation q 405 = false ∨ valuation q 465 = true := counterClause771 (baseVal q)

theorem counterClause772 (q : Nat → Bool) : valuationOf q 405 = false ∨ valuationOf q 463 = false ∨ valuationOf q 466 = true := by
  have hs : count465 q = (countLit q [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) + (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (l₂ := [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236])
  have hm := merge_two (literal (valuationOf q) (405)) (literal (valuationOf q) (463)) (literal (valuationOf q) (466)) (countLit q [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) (count465 q) 1 1 (meaning405 q) (meaning463 q) (meaning466 q) hs
  change valuationOf q 405 = false ∨ valuationOf q 463 = false ∨ valuationOf q 466 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause772 (q : Snake 81) (h : Conditions q) : valuation q 405 = false ∨ valuation q 463 = false ∨ valuation q 466 = true := counterClause772 (baseVal q)

theorem counterClause773 (q : Nat → Bool) : valuationOf q 466 = false ∨ valuationOf q 468 = true := by
  have hs : count467 q = (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 173, 174, 175, 176, 177]) + (countLit q [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 173, 174, 175, 176, 177]) (l₂ := [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236])
  have hm := merge_right (literal (valuationOf q) (466)) (literal (valuationOf q) (468)) (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 173, 174, 175, 176, 177]) (countLit q [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) (count467 q) 2 (meaning466 q) (meaning468 q) hs
  change valuationOf q 466 = false ∨ valuationOf q 468 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause773 (q : Snake 81) (h : Conditions q) : valuation q 466 = false ∨ valuation q 468 = true := counterClause773 (baseVal q)

theorem counterClause774 (q : Nat → Bool) : valuationOf q 349 = false ∨ valuationOf q 465 = false ∨ valuationOf q 468 = true := by
  have hs : count467 q = (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 173, 174, 175, 176, 177]) + (countLit q [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 173, 174, 175, 176, 177]) (l₂ := [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236])
  have hm := merge_two (literal (valuationOf q) (349)) (literal (valuationOf q) (465)) (literal (valuationOf q) (468)) (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 173, 174, 175, 176, 177]) (countLit q [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) (count467 q) 1 1 (meaning349 q) (meaning465 q) (meaning468 q) hs
  change valuationOf q 349 = false ∨ valuationOf q 465 = false ∨ valuationOf q 468 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause774 (q : Snake 81) (h : Conditions q) : valuation q 349 = false ∨ valuation q 465 = false ∨ valuation q 468 = true := counterClause774 (baseVal q)

theorem counterClause775 (q : Nat → Bool) : valuationOf q 350 = false ∨ valuationOf q 468 = true := by
  have hs : count467 q = (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 173, 174, 175, 176, 177]) + (countLit q [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 173, 174, 175, 176, 177]) (l₂ := [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236])
  have hm := merge_left (literal (valuationOf q) (350)) (literal (valuationOf q) (468)) (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 173, 174, 175, 176, 177]) (countLit q [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) (count467 q) 2 (meaning350 q) (meaning468 q) hs
  change valuationOf q 350 = false ∨ valuationOf q 468 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause775 (q : Snake 81) (h : Conditions q) : valuation q 350 = false ∨ valuation q 468 = true := counterClause775 (baseVal q)

theorem clause776 (q : Snake 81) (h : Conditions q) : valuation q 468 = false := by
  rw [value468]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count467 (baseVal q) = (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := other_count_bound q h
  rw [he]
  omega

theorem counterClause777 (q : Nat → Bool) : valuationOf q 5 = true ∨ valuationOf q 1413 = true := by
  have hs : count1413 q = (countLit q [-4]) + (countLit q [-5]) := List.countP_append (p := literal q) (l₁ := [-4]) (l₂ := [-5])
  have hm := merge_right (literal (valuationOf q) (-5)) (literal (valuationOf q) (1413)) (countLit q [-4]) (countLit q [-5]) (count1413 q) 1 (meaningNeg5 q) (meaning1413 q) hs
  change (! (valuationOf q 5)) = false ∨ valuationOf q 1413 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause777 (q : Snake 81) (h : Conditions q) : valuation q 5 = true ∨ valuation q 1413 = true := counterClause777 (baseVal q)

theorem counterClause778 (q : Nat → Bool) : valuationOf q 4 = true ∨ valuationOf q 5 = true ∨ valuationOf q 1414 = true := by
  have hs : count1413 q = (countLit q [-4]) + (countLit q [-5]) := List.countP_append (p := literal q) (l₁ := [-4]) (l₂ := [-5])
  have hm := merge_two (literal (valuationOf q) (-4)) (literal (valuationOf q) (-5)) (literal (valuationOf q) (1414)) (countLit q [-4]) (countLit q [-5]) (count1413 q) 1 1 (meaningNeg4 q) (meaningNeg5 q) (meaning1414 q) hs
  change (! (valuationOf q 4)) = false ∨ (! (valuationOf q 5)) = false ∨ valuationOf q 1414 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause778 (q : Snake 81) (h : Conditions q) : valuation q 4 = true ∨ valuation q 5 = true ∨ valuation q 1414 = true := counterClause778 (baseVal q)

theorem counterClause779 (q : Nat → Bool) : valuationOf q 1413 = false ∨ valuationOf q 1415 = true := by
  have hs : count1415 q = (countLit q [-2]) + (countLit q [-4, -5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-4, -5])
  have hm := merge_right (literal (valuationOf q) (1413)) (literal (valuationOf q) (1415)) (countLit q [-2]) (countLit q [-4, -5]) (count1415 q) 1 (meaning1413 q) (meaning1415 q) hs
  change valuationOf q 1413 = false ∨ valuationOf q 1415 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause779 (q : Snake 81) (h : Conditions q) : valuation q 1413 = false ∨ valuation q 1415 = true := counterClause779 (baseVal q)

theorem counterClause780 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1413 = false ∨ valuationOf q 1416 = true := by
  have hs : count1415 q = (countLit q [-2]) + (countLit q [-4, -5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-4, -5])
  have hm := merge_two (literal (valuationOf q) (-2)) (literal (valuationOf q) (1413)) (literal (valuationOf q) (1416)) (countLit q [-2]) (countLit q [-4, -5]) (count1415 q) 1 1 (meaningNeg2 q) (meaning1413 q) (meaning1416 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1413 = false ∨ valuationOf q 1416 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause780 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1413 = false ∨ valuation q 1416 = true := counterClause780 (baseVal q)

theorem counterClause781 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1414 = false ∨ valuationOf q 1417 = true := by
  have hs : count1415 q = (countLit q [-2]) + (countLit q [-4, -5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-4, -5])
  have hm := merge_two (literal (valuationOf q) (-2)) (literal (valuationOf q) (1414)) (literal (valuationOf q) (1417)) (countLit q [-2]) (countLit q [-4, -5]) (count1415 q) 1 2 (meaningNeg2 q) (meaning1414 q) (meaning1417 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1414 = false ∨ valuationOf q 1417 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause781 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1414 = false ∨ valuation q 1417 = true := counterClause781 (baseVal q)

theorem counterClause782 (q : Nat → Bool) : valuationOf q 9 = true ∨ valuationOf q 1418 = true := by
  have hs : count1418 q = (countLit q [-6]) + (countLit q [-9]) := List.countP_append (p := literal q) (l₁ := [-6]) (l₂ := [-9])
  have hm := merge_right (literal (valuationOf q) (-9)) (literal (valuationOf q) (1418)) (countLit q [-6]) (countLit q [-9]) (count1418 q) 1 (meaningNeg9 q) (meaning1418 q) hs
  change (! (valuationOf q 9)) = false ∨ valuationOf q 1418 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause782 (q : Snake 81) (h : Conditions q) : valuation q 9 = true ∨ valuation q 1418 = true := counterClause782 (baseVal q)

theorem counterClause783 (q : Nat → Bool) : valuationOf q 6 = true ∨ valuationOf q 1418 = true := by
  have hs : count1418 q = (countLit q [-6]) + (countLit q [-9]) := List.countP_append (p := literal q) (l₁ := [-6]) (l₂ := [-9])
  have hm := merge_left (literal (valuationOf q) (-6)) (literal (valuationOf q) (1418)) (countLit q [-6]) (countLit q [-9]) (count1418 q) 1 (meaningNeg6 q) (meaning1418 q) hs
  change (! (valuationOf q 6)) = false ∨ valuationOf q 1418 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause783 (q : Snake 81) (h : Conditions q) : valuation q 6 = true ∨ valuation q 1418 = true := counterClause783 (baseVal q)

theorem counterClause784 (q : Nat → Bool) : valuationOf q 6 = true ∨ valuationOf q 9 = true ∨ valuationOf q 1419 = true := by
  have hs : count1418 q = (countLit q [-6]) + (countLit q [-9]) := List.countP_append (p := literal q) (l₁ := [-6]) (l₂ := [-9])
  have hm := merge_two (literal (valuationOf q) (-6)) (literal (valuationOf q) (-9)) (literal (valuationOf q) (1419)) (countLit q [-6]) (countLit q [-9]) (count1418 q) 1 1 (meaningNeg6 q) (meaningNeg9 q) (meaning1419 q) hs
  change (! (valuationOf q 6)) = false ∨ (! (valuationOf q 9)) = false ∨ valuationOf q 1419 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause784 (q : Snake 81) (h : Conditions q) : valuation q 6 = true ∨ valuation q 9 = true ∨ valuation q 1419 = true := counterClause784 (baseVal q)

theorem counterClause785 (q : Nat → Bool) : valuationOf q 13 = true ∨ valuationOf q 1420 = true := by
  have hs : count1420 q = (countLit q [-11]) + (countLit q [-13]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-13])
  have hm := merge_right (literal (valuationOf q) (-13)) (literal (valuationOf q) (1420)) (countLit q [-11]) (countLit q [-13]) (count1420 q) 1 (meaningNeg13 q) (meaning1420 q) hs
  change (! (valuationOf q 13)) = false ∨ valuationOf q 1420 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause785 (q : Snake 81) (h : Conditions q) : valuation q 13 = true ∨ valuation q 1420 = true := counterClause785 (baseVal q)

theorem counterClause786 (q : Nat → Bool) : valuationOf q 11 = true ∨ valuationOf q 1420 = true := by
  have hs : count1420 q = (countLit q [-11]) + (countLit q [-13]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-13])
  have hm := merge_left (literal (valuationOf q) (-11)) (literal (valuationOf q) (1420)) (countLit q [-11]) (countLit q [-13]) (count1420 q) 1 (meaningNeg11 q) (meaning1420 q) hs
  change (! (valuationOf q 11)) = false ∨ valuationOf q 1420 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause786 (q : Snake 81) (h : Conditions q) : valuation q 11 = true ∨ valuation q 1420 = true := counterClause786 (baseVal q)

theorem counterClause787 (q : Nat → Bool) : valuationOf q 11 = true ∨ valuationOf q 13 = true ∨ valuationOf q 1421 = true := by
  have hs : count1420 q = (countLit q [-11]) + (countLit q [-13]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-13])
  have hm := merge_two (literal (valuationOf q) (-11)) (literal (valuationOf q) (-13)) (literal (valuationOf q) (1421)) (countLit q [-11]) (countLit q [-13]) (count1420 q) 1 1 (meaningNeg11 q) (meaningNeg13 q) (meaning1421 q) hs
  change (! (valuationOf q 11)) = false ∨ (! (valuationOf q 13)) = false ∨ valuationOf q 1421 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause787 (q : Snake 81) (h : Conditions q) : valuation q 11 = true ∨ valuation q 13 = true ∨ valuation q 1421 = true := counterClause787 (baseVal q)

theorem counterClause788 (q : Nat → Bool) : valuationOf q 1420 = false ∨ valuationOf q 1422 = true := by
  have hs : count1422 q = (countLit q [-6, -9]) + (countLit q [-11, -13]) := List.countP_append (p := literal q) (l₁ := [-6, -9]) (l₂ := [-11, -13])
  have hm := merge_right (literal (valuationOf q) (1420)) (literal (valuationOf q) (1422)) (countLit q [-6, -9]) (countLit q [-11, -13]) (count1422 q) 1 (meaning1420 q) (meaning1422 q) hs
  change valuationOf q 1420 = false ∨ valuationOf q 1422 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause788 (q : Snake 81) (h : Conditions q) : valuation q 1420 = false ∨ valuation q 1422 = true := counterClause788 (baseVal q)

theorem counterClause789 (q : Nat → Bool) : valuationOf q 1418 = false ∨ valuationOf q 1422 = true := by
  have hs : count1422 q = (countLit q [-6, -9]) + (countLit q [-11, -13]) := List.countP_append (p := literal q) (l₁ := [-6, -9]) (l₂ := [-11, -13])
  have hm := merge_left (literal (valuationOf q) (1418)) (literal (valuationOf q) (1422)) (countLit q [-6, -9]) (countLit q [-11, -13]) (count1422 q) 1 (meaning1418 q) (meaning1422 q) hs
  change valuationOf q 1418 = false ∨ valuationOf q 1422 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause789 (q : Snake 81) (h : Conditions q) : valuation q 1418 = false ∨ valuation q 1422 = true := counterClause789 (baseVal q)

theorem counterClause790 (q : Nat → Bool) : valuationOf q 1418 = false ∨ valuationOf q 1420 = false ∨ valuationOf q 1423 = true := by
  have hs : count1422 q = (countLit q [-6, -9]) + (countLit q [-11, -13]) := List.countP_append (p := literal q) (l₁ := [-6, -9]) (l₂ := [-11, -13])
  have hm := merge_two (literal (valuationOf q) (1418)) (literal (valuationOf q) (1420)) (literal (valuationOf q) (1423)) (countLit q [-6, -9]) (countLit q [-11, -13]) (count1422 q) 1 1 (meaning1418 q) (meaning1420 q) (meaning1423 q) hs
  change valuationOf q 1418 = false ∨ valuationOf q 1420 = false ∨ valuationOf q 1423 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause790 (q : Snake 81) (h : Conditions q) : valuation q 1418 = false ∨ valuation q 1420 = false ∨ valuation q 1423 = true := counterClause790 (baseVal q)

theorem counterClause791 (q : Nat → Bool) : valuationOf q 1418 = false ∨ valuationOf q 1421 = false ∨ valuationOf q 1424 = true := by
  have hs : count1422 q = (countLit q [-6, -9]) + (countLit q [-11, -13]) := List.countP_append (p := literal q) (l₁ := [-6, -9]) (l₂ := [-11, -13])
  have hm := merge_two (literal (valuationOf q) (1418)) (literal (valuationOf q) (1421)) (literal (valuationOf q) (1424)) (countLit q [-6, -9]) (countLit q [-11, -13]) (count1422 q) 1 2 (meaning1418 q) (meaning1421 q) (meaning1424 q) hs
  change valuationOf q 1418 = false ∨ valuationOf q 1421 = false ∨ valuationOf q 1424 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause791 (q : Snake 81) (h : Conditions q) : valuation q 1418 = false ∨ valuation q 1421 = false ∨ valuation q 1424 = true := counterClause791 (baseVal q)

theorem counterClause792 (q : Nat → Bool) : valuationOf q 1419 = false ∨ valuationOf q 1423 = true := by
  have hs : count1422 q = (countLit q [-6, -9]) + (countLit q [-11, -13]) := List.countP_append (p := literal q) (l₁ := [-6, -9]) (l₂ := [-11, -13])
  have hm := merge_left (literal (valuationOf q) (1419)) (literal (valuationOf q) (1423)) (countLit q [-6, -9]) (countLit q [-11, -13]) (count1422 q) 2 (meaning1419 q) (meaning1423 q) hs
  change valuationOf q 1419 = false ∨ valuationOf q 1423 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause792 (q : Snake 81) (h : Conditions q) : valuation q 1419 = false ∨ valuation q 1423 = true := counterClause792 (baseVal q)

theorem counterClause793 (q : Nat → Bool) : valuationOf q 1419 = false ∨ valuationOf q 1420 = false ∨ valuationOf q 1424 = true := by
  have hs : count1422 q = (countLit q [-6, -9]) + (countLit q [-11, -13]) := List.countP_append (p := literal q) (l₁ := [-6, -9]) (l₂ := [-11, -13])
  have hm := merge_two (literal (valuationOf q) (1419)) (literal (valuationOf q) (1420)) (literal (valuationOf q) (1424)) (countLit q [-6, -9]) (countLit q [-11, -13]) (count1422 q) 2 1 (meaning1419 q) (meaning1420 q) (meaning1424 q) hs
  change valuationOf q 1419 = false ∨ valuationOf q 1420 = false ∨ valuationOf q 1424 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause793 (q : Snake 81) (h : Conditions q) : valuation q 1419 = false ∨ valuation q 1420 = false ∨ valuation q 1424 = true := counterClause793 (baseVal q)

theorem counterClause794 (q : Nat → Bool) : valuationOf q 1415 = false ∨ valuationOf q 1423 = false ∨ valuationOf q 1428 = true := by
  have hs : count1426 q = (countLit q [-2, -4, -5]) + (countLit q [-6, -9, -11, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-6, -9, -11, -13])
  have hm := merge_two (literal (valuationOf q) (1415)) (literal (valuationOf q) (1423)) (literal (valuationOf q) (1428)) (countLit q [-2, -4, -5]) (countLit q [-6, -9, -11, -13]) (count1426 q) 1 2 (meaning1415 q) (meaning1423 q) (meaning1428 q) hs
  change valuationOf q 1415 = false ∨ valuationOf q 1423 = false ∨ valuationOf q 1428 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause794 (q : Snake 81) (h : Conditions q) : valuation q 1415 = false ∨ valuation q 1423 = false ∨ valuation q 1428 = true := counterClause794 (baseVal q)

theorem counterClause795 (q : Nat → Bool) : valuationOf q 1416 = false ∨ valuationOf q 1427 = true := by
  have hs : count1426 q = (countLit q [-2, -4, -5]) + (countLit q [-6, -9, -11, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-6, -9, -11, -13])
  have hm := merge_left (literal (valuationOf q) (1416)) (literal (valuationOf q) (1427)) (countLit q [-2, -4, -5]) (countLit q [-6, -9, -11, -13]) (count1426 q) 2 (meaning1416 q) (meaning1427 q) hs
  change valuationOf q 1416 = false ∨ valuationOf q 1427 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause795 (q : Snake 81) (h : Conditions q) : valuation q 1416 = false ∨ valuation q 1427 = true := counterClause795 (baseVal q)

theorem counterClause796 (q : Nat → Bool) : valuationOf q 1416 = false ∨ valuationOf q 1422 = false ∨ valuationOf q 1428 = true := by
  have hs : count1426 q = (countLit q [-2, -4, -5]) + (countLit q [-6, -9, -11, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-6, -9, -11, -13])
  have hm := merge_two (literal (valuationOf q) (1416)) (literal (valuationOf q) (1422)) (literal (valuationOf q) (1428)) (countLit q [-2, -4, -5]) (countLit q [-6, -9, -11, -13]) (count1426 q) 2 1 (meaning1416 q) (meaning1422 q) (meaning1428 q) hs
  change valuationOf q 1416 = false ∨ valuationOf q 1422 = false ∨ valuationOf q 1428 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause796 (q : Snake 81) (h : Conditions q) : valuation q 1416 = false ∨ valuation q 1422 = false ∨ valuation q 1428 = true := counterClause796 (baseVal q)

theorem counterClause797 (q : Nat → Bool) : valuationOf q 1416 = false ∨ valuationOf q 1423 = false ∨ valuationOf q 1429 = true := by
  have hs : count1426 q = (countLit q [-2, -4, -5]) + (countLit q [-6, -9, -11, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-6, -9, -11, -13])
  have hm := merge_two (literal (valuationOf q) (1416)) (literal (valuationOf q) (1423)) (literal (valuationOf q) (1429)) (countLit q [-2, -4, -5]) (countLit q [-6, -9, -11, -13]) (count1426 q) 2 2 (meaning1416 q) (meaning1423 q) (meaning1429 q) hs
  change valuationOf q 1416 = false ∨ valuationOf q 1423 = false ∨ valuationOf q 1429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause797 (q : Snake 81) (h : Conditions q) : valuation q 1416 = false ∨ valuation q 1423 = false ∨ valuation q 1429 = true := counterClause797 (baseVal q)

theorem counterClause798 (q : Nat → Bool) : valuationOf q 1416 = false ∨ valuationOf q 1424 = false ∨ valuationOf q 1430 = true := by
  have hs : count1426 q = (countLit q [-2, -4, -5]) + (countLit q [-6, -9, -11, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-6, -9, -11, -13])
  have hm := merge_two (literal (valuationOf q) (1416)) (literal (valuationOf q) (1424)) (literal (valuationOf q) (1430)) (countLit q [-2, -4, -5]) (countLit q [-6, -9, -11, -13]) (count1426 q) 2 3 (meaning1416 q) (meaning1424 q) (meaning1430 q) hs
  change valuationOf q 1416 = false ∨ valuationOf q 1424 = false ∨ valuationOf q 1430 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause798 (q : Snake 81) (h : Conditions q) : valuation q 1416 = false ∨ valuation q 1424 = false ∨ valuation q 1430 = true := counterClause798 (baseVal q)

theorem counterClause799 (q : Nat → Bool) : valuationOf q 1417 = false ∨ valuationOf q 1428 = true := by
  have hs : count1426 q = (countLit q [-2, -4, -5]) + (countLit q [-6, -9, -11, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-6, -9, -11, -13])
  have hm := merge_left (literal (valuationOf q) (1417)) (literal (valuationOf q) (1428)) (countLit q [-2, -4, -5]) (countLit q [-6, -9, -11, -13]) (count1426 q) 3 (meaning1417 q) (meaning1428 q) hs
  change valuationOf q 1417 = false ∨ valuationOf q 1428 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause799 (q : Snake 81) (h : Conditions q) : valuation q 1417 = false ∨ valuation q 1428 = true := counterClause799 (baseVal q)

theorem counterClause800 (q : Nat → Bool) : valuationOf q 1417 = false ∨ valuationOf q 1422 = false ∨ valuationOf q 1429 = true := by
  have hs : count1426 q = (countLit q [-2, -4, -5]) + (countLit q [-6, -9, -11, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-6, -9, -11, -13])
  have hm := merge_two (literal (valuationOf q) (1417)) (literal (valuationOf q) (1422)) (literal (valuationOf q) (1429)) (countLit q [-2, -4, -5]) (countLit q [-6, -9, -11, -13]) (count1426 q) 3 1 (meaning1417 q) (meaning1422 q) (meaning1429 q) hs
  change valuationOf q 1417 = false ∨ valuationOf q 1422 = false ∨ valuationOf q 1429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause800 (q : Snake 81) (h : Conditions q) : valuation q 1417 = false ∨ valuation q 1422 = false ∨ valuation q 1429 = true := counterClause800 (baseVal q)

theorem block24 (q : Snake 81) (h : Conditions q) : B112E110.Block24 (valuation q) :=
  ⟨clause769 q h, clause770 q h, clause771 q h, clause772 q h, clause773 q h, clause774 q h, clause775 q h, clause776 q h, clause777 q h, clause778 q h, clause779 q h, clause780 q h, clause781 q h, clause782 q h, clause783 q h, clause784 q h, clause785 q h, clause786 q h, clause787 q h, clause788 q h, clause789 q h, clause790 q h, clause791 q h, clause792 q h, clause793 q h, clause794 q h, clause795 q h, clause796 q h, clause797 q h, clause798 q h, clause799 q h, clause800 q h⟩

end
end Snake9.Regrowth.E112110
