import E112158Semantics
import B112E158Inputs
namespace Snake9.Regrowth.E112158
noncomputable section
local instance blockDec28 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause897 (q : Nat → Bool) : valuationOf q 405 = false ∨ valuationOf q 465 = true := by
  have hs : count465 q = (countLit q [177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) + (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (l₂ := [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236])
  have hm := merge_left (literal (valuationOf q) (405)) (literal (valuationOf q) (465)) (countLit q [177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) (count465 q) 1 (meaning405 q) (meaning465 q) hs
  change valuationOf q 405 = false ∨ valuationOf q 465 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause897 (q : Snake 81) (h : Conditions q) : valuation q 405 = false ∨ valuation q 465 = true := counterClause897 (baseVal q)

theorem counterClause898 (q : Nat → Bool) : valuationOf q 405 = false ∨ valuationOf q 463 = false ∨ valuationOf q 466 = true := by
  have hs : count465 q = (countLit q [177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) + (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (l₂ := [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236])
  have hm := merge_two (literal (valuationOf q) (405)) (literal (valuationOf q) (463)) (literal (valuationOf q) (466)) (countLit q [177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) (count465 q) 1 1 (meaning405 q) (meaning463 q) (meaning466 q) hs
  change valuationOf q 405 = false ∨ valuationOf q 463 = false ∨ valuationOf q 466 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause898 (q : Snake 81) (h : Conditions q) : valuation q 405 = false ∨ valuation q 463 = false ∨ valuation q 466 = true := counterClause898 (baseVal q)

theorem counterClause899 (q : Nat → Bool) : valuationOf q 406 = false ∨ valuationOf q 466 = true := by
  have hs : count465 q = (countLit q [177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) + (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (l₂ := [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236])
  have hm := merge_left (literal (valuationOf q) (406)) (literal (valuationOf q) (466)) (countLit q [177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) (count465 q) 2 (meaning406 q) (meaning466 q) hs
  change valuationOf q 406 = false ∨ valuationOf q 466 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause899 (q : Snake 81) (h : Conditions q) : valuation q 406 = false ∨ valuation q 466 = true := counterClause899 (baseVal q)

theorem counterClause900 (q : Nat → Bool) : valuationOf q 466 = false ∨ valuationOf q 468 = true := by
  have hs : count467 q = (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) + (countLit q [177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) (l₂ := [177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236])
  have hm := merge_right (literal (valuationOf q) (466)) (literal (valuationOf q) (468)) (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) (countLit q [177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) (count467 q) 2 (meaning466 q) (meaning468 q) hs
  change valuationOf q 466 = false ∨ valuationOf q 468 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause900 (q : Snake 81) (h : Conditions q) : valuation q 466 = false ∨ valuation q 468 = true := counterClause900 (baseVal q)

theorem counterClause901 (q : Nat → Bool) : valuationOf q 349 = false ∨ valuationOf q 465 = false ∨ valuationOf q 468 = true := by
  have hs : count467 q = (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) + (countLit q [177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) (l₂ := [177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236])
  have hm := merge_two (literal (valuationOf q) (349)) (literal (valuationOf q) (465)) (literal (valuationOf q) (468)) (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) (countLit q [177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) (count467 q) 1 1 (meaning349 q) (meaning465 q) (meaning468 q) hs
  change valuationOf q 349 = false ∨ valuationOf q 465 = false ∨ valuationOf q 468 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause901 (q : Snake 81) (h : Conditions q) : valuation q 349 = false ∨ valuation q 465 = false ∨ valuation q 468 = true := counterClause901 (baseVal q)

theorem counterClause902 (q : Nat → Bool) : valuationOf q 350 = false ∨ valuationOf q 468 = true := by
  have hs : count467 q = (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) + (countLit q [177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) (l₂ := [177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236])
  have hm := merge_left (literal (valuationOf q) (350)) (literal (valuationOf q) (468)) (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) (countLit q [177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) (count467 q) 2 (meaning350 q) (meaning468 q) hs
  change valuationOf q 350 = false ∨ valuationOf q 468 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause902 (q : Snake 81) (h : Conditions q) : valuation q 350 = false ∨ valuation q 468 = true := counterClause902 (baseVal q)

theorem clause903 (q : Snake 81) (h : Conditions q) : valuation q 468 = false := by
  rw [value468]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count467 (baseVal q) = (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := other_count_bound q h
  rw [he]
  omega

theorem counterClause904 (q : Nat → Bool) : valuationOf q 4 = true ∨ valuationOf q 801 = true := by
  have hs : count801 q = (countLit q [-2]) + (countLit q [-4]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-4])
  have hm := merge_right (literal (valuationOf q) (-4)) (literal (valuationOf q) (801)) (countLit q [-2]) (countLit q [-4]) (count801 q) 1 (meaningNeg4 q) (meaning801 q) hs
  change (! (valuationOf q 4)) = false ∨ valuationOf q 801 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause904 (q : Snake 81) (h : Conditions q) : valuation q 4 = true ∨ valuation q 801 = true := counterClause904 (baseVal q)

theorem counterClause905 (q : Nat → Bool) : valuationOf q 801 = false ∨ valuationOf q 803 = true := by
  have hs : count803 q = (countLit q [-1]) + (countLit q [-2, -4]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-2, -4])
  have hm := merge_right (literal (valuationOf q) (801)) (literal (valuationOf q) (803)) (countLit q [-1]) (countLit q [-2, -4]) (count803 q) 1 (meaning801 q) (meaning803 q) hs
  change valuationOf q 801 = false ∨ valuationOf q 803 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause905 (q : Snake 81) (h : Conditions q) : valuation q 801 = false ∨ valuation q 803 = true := counterClause905 (baseVal q)

theorem counterClause906 (q : Nat → Bool) : valuationOf q 803 = false ∨ valuationOf q 814 = true := by
  have hs : count814 q = (countLit q [-1, -2, -4]) + (countLit q [-5, -8, -10, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4]) (l₂ := [-5, -8, -10, -12])
  have hm := merge_left (literal (valuationOf q) (803)) (literal (valuationOf q) (814)) (countLit q [-1, -2, -4]) (countLit q [-5, -8, -10, -12]) (count814 q) 1 (meaning803 q) (meaning814 q) hs
  change valuationOf q 803 = false ∨ valuationOf q 814 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause906 (q : Snake 81) (h : Conditions q) : valuation q 803 = false ∨ valuation q 814 = true := counterClause906 (baseVal q)

theorem counterClause907 (q : Nat → Bool) : valuationOf q 16 = true ∨ valuationOf q 821 = true := by
  have hs : count821 q = (countLit q [-15]) + (countLit q [-16]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-16])
  have hm := merge_right (literal (valuationOf q) (-16)) (literal (valuationOf q) (821)) (countLit q [-15]) (countLit q [-16]) (count821 q) 1 (meaningNeg16 q) (meaning821 q) hs
  change (! (valuationOf q 16)) = false ∨ valuationOf q 821 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause907 (q : Snake 81) (h : Conditions q) : valuation q 16 = true ∨ valuation q 821 = true := counterClause907 (baseVal q)

theorem counterClause908 (q : Nat → Bool) : valuationOf q 821 = false ∨ valuationOf q 823 = true := by
  have hs : count823 q = (countLit q [-14]) + (countLit q [-15, -16]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-15, -16])
  have hm := merge_right (literal (valuationOf q) (821)) (literal (valuationOf q) (823)) (countLit q [-14]) (countLit q [-15, -16]) (count823 q) 1 (meaning821 q) (meaning823 q) hs
  change valuationOf q 821 = false ∨ valuationOf q 823 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause908 (q : Snake 81) (h : Conditions q) : valuation q 821 = false ∨ valuation q 823 = true := counterClause908 (baseVal q)

theorem counterClause909 (q : Nat → Bool) : valuationOf q 18 = true ∨ valuationOf q 22 = true ∨ valuationOf q 827 = true := by
  have hs : count826 q = (countLit q [-18]) + (countLit q [-22]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-22])
  have hm := merge_two (literal (valuationOf q) (-18)) (literal (valuationOf q) (-22)) (literal (valuationOf q) (827)) (countLit q [-18]) (countLit q [-22]) (count826 q) 1 1 (meaningNeg18 q) (meaningNeg22 q) (meaning827 q) hs
  change (! (valuationOf q 18)) = false ∨ (! (valuationOf q 22)) = false ∨ valuationOf q 827 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause909 (q : Snake 81) (h : Conditions q) : valuation q 18 = true ∨ valuation q 22 = true ∨ valuation q 827 = true := counterClause909 (baseVal q)

theorem counterClause910 (q : Nat → Bool) : valuationOf q 26 = true ∨ valuationOf q 828 = true := by
  have hs : count828 q = (countLit q [-23]) + (countLit q [-26]) := List.countP_append (p := literal q) (l₁ := [-23]) (l₂ := [-26])
  have hm := merge_right (literal (valuationOf q) (-26)) (literal (valuationOf q) (828)) (countLit q [-23]) (countLit q [-26]) (count828 q) 1 (meaningNeg26 q) (meaning828 q) hs
  change (! (valuationOf q 26)) = false ∨ valuationOf q 828 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause910 (q : Snake 81) (h : Conditions q) : valuation q 26 = true ∨ valuation q 828 = true := counterClause910 (baseVal q)

theorem counterClause911 (q : Nat → Bool) : valuationOf q 23 = true ∨ valuationOf q 26 = true ∨ valuationOf q 829 = true := by
  have hs : count828 q = (countLit q [-23]) + (countLit q [-26]) := List.countP_append (p := literal q) (l₁ := [-23]) (l₂ := [-26])
  have hm := merge_two (literal (valuationOf q) (-23)) (literal (valuationOf q) (-26)) (literal (valuationOf q) (829)) (countLit q [-23]) (countLit q [-26]) (count828 q) 1 1 (meaningNeg23 q) (meaningNeg26 q) (meaning829 q) hs
  change (! (valuationOf q 23)) = false ∨ (! (valuationOf q 26)) = false ∨ valuationOf q 829 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause911 (q : Snake 81) (h : Conditions q) : valuation q 23 = true ∨ valuation q 26 = true ∨ valuation q 829 = true := counterClause911 (baseVal q)

theorem counterClause912 (q : Nat → Bool) : valuationOf q 827 = false ∨ valuationOf q 831 = true := by
  have hs : count830 q = (countLit q [-18, -22]) + (countLit q [-23, -26]) := List.countP_append (p := literal q) (l₁ := [-18, -22]) (l₂ := [-23, -26])
  have hm := merge_left (literal (valuationOf q) (827)) (literal (valuationOf q) (831)) (countLit q [-18, -22]) (countLit q [-23, -26]) (count830 q) 2 (meaning827 q) (meaning831 q) hs
  change valuationOf q 827 = false ∨ valuationOf q 831 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause912 (q : Snake 81) (h : Conditions q) : valuation q 827 = false ∨ valuation q 831 = true := counterClause912 (baseVal q)

theorem counterClause913 (q : Nat → Bool) : valuationOf q 827 = false ∨ valuationOf q 828 = false ∨ valuationOf q 832 = true := by
  have hs : count830 q = (countLit q [-18, -22]) + (countLit q [-23, -26]) := List.countP_append (p := literal q) (l₁ := [-18, -22]) (l₂ := [-23, -26])
  have hm := merge_two (literal (valuationOf q) (827)) (literal (valuationOf q) (828)) (literal (valuationOf q) (832)) (countLit q [-18, -22]) (countLit q [-23, -26]) (count830 q) 2 1 (meaning827 q) (meaning828 q) (meaning832 q) hs
  change valuationOf q 827 = false ∨ valuationOf q 828 = false ∨ valuationOf q 832 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause913 (q : Snake 81) (h : Conditions q) : valuation q 827 = false ∨ valuation q 828 = false ∨ valuation q 832 = true := counterClause913 (baseVal q)

theorem counterClause914 (q : Nat → Bool) : valuationOf q 827 = false ∨ valuationOf q 829 = false ∨ valuationOf q 833 = true := by
  have hs : count830 q = (countLit q [-18, -22]) + (countLit q [-23, -26]) := List.countP_append (p := literal q) (l₁ := [-18, -22]) (l₂ := [-23, -26])
  have hm := merge_two (literal (valuationOf q) (827)) (literal (valuationOf q) (829)) (literal (valuationOf q) (833)) (countLit q [-18, -22]) (countLit q [-23, -26]) (count830 q) 2 2 (meaning827 q) (meaning829 q) (meaning833 q) hs
  change valuationOf q 827 = false ∨ valuationOf q 829 = false ∨ valuationOf q 833 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause914 (q : Snake 81) (h : Conditions q) : valuation q 827 = false ∨ valuation q 829 = false ∨ valuation q 833 = true := counterClause914 (baseVal q)

theorem counterClause915 (q : Nat → Bool) : valuationOf q 832 = false ∨ valuationOf q 836 = true := by
  have hs : count834 q = (countLit q [-14, -15, -16]) + (countLit q [-18, -22, -23, -26]) := List.countP_append (p := literal q) (l₁ := [-14, -15, -16]) (l₂ := [-18, -22, -23, -26])
  have hm := merge_right (literal (valuationOf q) (832)) (literal (valuationOf q) (836)) (countLit q [-14, -15, -16]) (countLit q [-18, -22, -23, -26]) (count834 q) 3 (meaning832 q) (meaning836 q) hs
  change valuationOf q 832 = false ∨ valuationOf q 836 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause915 (q : Snake 81) (h : Conditions q) : valuation q 832 = false ∨ valuation q 836 = true := counterClause915 (baseVal q)

theorem counterClause916 (q : Nat → Bool) : valuationOf q 823 = false ∨ valuationOf q 831 = false ∨ valuationOf q 836 = true := by
  have hs : count834 q = (countLit q [-14, -15, -16]) + (countLit q [-18, -22, -23, -26]) := List.countP_append (p := literal q) (l₁ := [-14, -15, -16]) (l₂ := [-18, -22, -23, -26])
  have hm := merge_two (literal (valuationOf q) (823)) (literal (valuationOf q) (831)) (literal (valuationOf q) (836)) (countLit q [-14, -15, -16]) (countLit q [-18, -22, -23, -26]) (count834 q) 1 2 (meaning823 q) (meaning831 q) (meaning836 q) hs
  change valuationOf q 823 = false ∨ valuationOf q 831 = false ∨ valuationOf q 836 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause916 (q : Snake 81) (h : Conditions q) : valuation q 823 = false ∨ valuation q 831 = false ∨ valuation q 836 = true := counterClause916 (baseVal q)

theorem counterClause917 (q : Nat → Bool) : valuationOf q 823 = false ∨ valuationOf q 833 = false ∨ valuationOf q 838 = true := by
  have hs : count834 q = (countLit q [-14, -15, -16]) + (countLit q [-18, -22, -23, -26]) := List.countP_append (p := literal q) (l₁ := [-14, -15, -16]) (l₂ := [-18, -22, -23, -26])
  have hm := merge_two (literal (valuationOf q) (823)) (literal (valuationOf q) (833)) (literal (valuationOf q) (838)) (countLit q [-14, -15, -16]) (countLit q [-18, -22, -23, -26]) (count834 q) 1 4 (meaning823 q) (meaning833 q) (meaning838 q) hs
  change valuationOf q 823 = false ∨ valuationOf q 833 = false ∨ valuationOf q 838 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause917 (q : Snake 81) (h : Conditions q) : valuation q 823 = false ∨ valuation q 833 = false ∨ valuation q 838 = true := counterClause917 (baseVal q)

theorem counterClause918 (q : Nat → Bool) : valuationOf q 814 = false ∨ valuationOf q 836 = false ∨ valuationOf q 844 = true := by
  have hs : count841 q = (countLit q [-1, -2, -4, -5, -8, -10, -12]) + (countLit q [-14, -15, -16, -18, -22, -23, -26]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -5, -8, -10, -12]) (l₂ := [-14, -15, -16, -18, -22, -23, -26])
  have hm := merge_two (literal (valuationOf q) (814)) (literal (valuationOf q) (836)) (literal (valuationOf q) (844)) (countLit q [-1, -2, -4, -5, -8, -10, -12]) (countLit q [-14, -15, -16, -18, -22, -23, -26]) (count841 q) 1 3 (meaning814 q) (meaning836 q) (meaning844 q) hs
  change valuationOf q 814 = false ∨ valuationOf q 836 = false ∨ valuationOf q 844 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause918 (q : Snake 81) (h : Conditions q) : valuation q 814 = false ∨ valuation q 836 = false ∨ valuation q 844 = true := counterClause918 (baseVal q)

theorem counterClause919 (q : Nat → Bool) : valuationOf q 814 = false ∨ valuationOf q 838 = false ∨ valuationOf q 846 = true := by
  have hs : count841 q = (countLit q [-1, -2, -4, -5, -8, -10, -12]) + (countLit q [-14, -15, -16, -18, -22, -23, -26]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -5, -8, -10, -12]) (l₂ := [-14, -15, -16, -18, -22, -23, -26])
  have hm := merge_two (literal (valuationOf q) (814)) (literal (valuationOf q) (838)) (literal (valuationOf q) (846)) (countLit q [-1, -2, -4, -5, -8, -10, -12]) (countLit q [-14, -15, -16, -18, -22, -23, -26]) (count841 q) 1 5 (meaning814 q) (meaning838 q) (meaning846 q) hs
  change valuationOf q 814 = false ∨ valuationOf q 838 = false ∨ valuationOf q 846 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause919 (q : Snake 81) (h : Conditions q) : valuation q 814 = false ∨ valuation q 838 = false ∨ valuation q 846 = true := counterClause919 (baseVal q)

theorem counterClause920 (q : Nat → Bool) : valuationOf q 31 = true ∨ valuationOf q 855 = true := by
  have hs : count855 q = (countLit q [-29]) + (countLit q [-31]) := List.countP_append (p := literal q) (l₁ := [-29]) (l₂ := [-31])
  have hm := merge_right (literal (valuationOf q) (-31)) (literal (valuationOf q) (855)) (countLit q [-29]) (countLit q [-31]) (count855 q) 1 (meaningNeg31 q) (meaning855 q) hs
  change (! (valuationOf q 31)) = false ∨ valuationOf q 855 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause920 (q : Snake 81) (h : Conditions q) : valuation q 31 = true ∨ valuation q 855 = true := counterClause920 (baseVal q)

theorem counterClause921 (q : Nat → Bool) : valuationOf q 855 = false ∨ valuationOf q 857 = true := by
  have hs : count857 q = (countLit q [-27]) + (countLit q [-29, -31]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-29, -31])
  have hm := merge_right (literal (valuationOf q) (855)) (literal (valuationOf q) (857)) (countLit q [-27]) (countLit q [-29, -31]) (count857 q) 1 (meaning855 q) (meaning857 q) hs
  change valuationOf q 855 = false ∨ valuationOf q 857 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause921 (q : Snake 81) (h : Conditions q) : valuation q 855 = false ∨ valuation q 857 = true := counterClause921 (baseVal q)

theorem counterClause922 (q : Nat → Bool) : valuationOf q 27 = true ∨ valuationOf q 855 = false ∨ valuationOf q 858 = true := by
  have hs : count857 q = (countLit q [-27]) + (countLit q [-29, -31]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-29, -31])
  have hm := merge_two (literal (valuationOf q) (-27)) (literal (valuationOf q) (855)) (literal (valuationOf q) (858)) (countLit q [-27]) (countLit q [-29, -31]) (count857 q) 1 1 (meaningNeg27 q) (meaning855 q) (meaning858 q) hs
  change (! (valuationOf q 27)) = false ∨ valuationOf q 855 = false ∨ valuationOf q 858 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause922 (q : Snake 81) (h : Conditions q) : valuation q 27 = true ∨ valuation q 855 = false ∨ valuation q 858 = true := counterClause922 (baseVal q)

theorem counterClause923 (q : Nat → Bool) : valuationOf q 36 = true ∨ valuationOf q 860 = true := by
  have hs : count860 q = (countLit q [-33]) + (countLit q [-36]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-36])
  have hm := merge_right (literal (valuationOf q) (-36)) (literal (valuationOf q) (860)) (countLit q [-33]) (countLit q [-36]) (count860 q) 1 (meaningNeg36 q) (meaning860 q) hs
  change (! (valuationOf q 36)) = false ∨ valuationOf q 860 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause923 (q : Snake 81) (h : Conditions q) : valuation q 36 = true ∨ valuation q 860 = true := counterClause923 (baseVal q)

theorem counterClause924 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 860 = true := by
  have hs : count860 q = (countLit q [-33]) + (countLit q [-36]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-36])
  have hm := merge_left (literal (valuationOf q) (-33)) (literal (valuationOf q) (860)) (countLit q [-33]) (countLit q [-36]) (count860 q) 1 (meaningNeg33 q) (meaning860 q) hs
  change (! (valuationOf q 33)) = false ∨ valuationOf q 860 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause924 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 860 = true := counterClause924 (baseVal q)

theorem counterClause925 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 36 = true ∨ valuationOf q 861 = true := by
  have hs : count860 q = (countLit q [-33]) + (countLit q [-36]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-36])
  have hm := merge_two (literal (valuationOf q) (-33)) (literal (valuationOf q) (-36)) (literal (valuationOf q) (861)) (countLit q [-33]) (countLit q [-36]) (count860 q) 1 1 (meaningNeg33 q) (meaningNeg36 q) (meaning861 q) hs
  change (! (valuationOf q 33)) = false ∨ (! (valuationOf q 36)) = false ∨ valuationOf q 861 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause925 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 36 = true ∨ valuation q 861 = true := counterClause925 (baseVal q)

theorem counterClause926 (q : Nat → Bool) : valuationOf q 37 = true ∨ valuationOf q 862 = true := by
  have hs : count862 q = (countLit q [-37]) + (countLit q [-38]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-38])
  have hm := merge_left (literal (valuationOf q) (-37)) (literal (valuationOf q) (862)) (countLit q [-37]) (countLit q [-38]) (count862 q) 1 (meaningNeg37 q) (meaning862 q) hs
  change (! (valuationOf q 37)) = false ∨ valuationOf q 862 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause926 (q : Snake 81) (h : Conditions q) : valuation q 37 = true ∨ valuation q 862 = true := counterClause926 (baseVal q)

theorem counterClause927 (q : Nat → Bool) : valuationOf q 37 = true ∨ valuationOf q 38 = true ∨ valuationOf q 863 = true := by
  have hs : count862 q = (countLit q [-37]) + (countLit q [-38]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-38])
  have hm := merge_two (literal (valuationOf q) (-37)) (literal (valuationOf q) (-38)) (literal (valuationOf q) (863)) (countLit q [-37]) (countLit q [-38]) (count862 q) 1 1 (meaningNeg37 q) (meaningNeg38 q) (meaning863 q) hs
  change (! (valuationOf q 37)) = false ∨ (! (valuationOf q 38)) = false ∨ valuationOf q 863 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause927 (q : Snake 81) (h : Conditions q) : valuation q 37 = true ∨ valuation q 38 = true ∨ valuation q 863 = true := counterClause927 (baseVal q)

theorem counterClause928 (q : Nat → Bool) : valuationOf q 862 = false ∨ valuationOf q 864 = true := by
  have hs : count864 q = (countLit q [-33, -36]) + (countLit q [-37, -38]) := List.countP_append (p := literal q) (l₁ := [-33, -36]) (l₂ := [-37, -38])
  have hm := merge_right (literal (valuationOf q) (862)) (literal (valuationOf q) (864)) (countLit q [-33, -36]) (countLit q [-37, -38]) (count864 q) 1 (meaning862 q) (meaning864 q) hs
  change valuationOf q 862 = false ∨ valuationOf q 864 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause928 (q : Snake 81) (h : Conditions q) : valuation q 862 = false ∨ valuation q 864 = true := counterClause928 (baseVal q)

theorem block28 (q : Snake 81) (h : Conditions q) : B112E158.Block28 (valuation q) :=
  ⟨clause897 q h, clause898 q h, clause899 q h, clause900 q h, clause901 q h, clause902 q h, clause903 q h, clause904 q h, clause905 q h, clause906 q h, clause907 q h, clause908 q h, clause909 q h, clause910 q h, clause911 q h, clause912 q h, clause913 q h, clause914 q h, clause915 q h, clause916 q h, clause917 q h, clause918 q h, clause919 q h, clause920 q h, clause921 q h, clause922 q h, clause923 q h, clause924 q h, clause925 q h, clause926 q h, clause927 q h, clause928 q h⟩

end
end Snake9.Regrowth.E112158
