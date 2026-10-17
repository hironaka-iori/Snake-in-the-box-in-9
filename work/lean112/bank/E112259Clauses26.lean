import E112259Semantics
import B112E259Inputs
namespace Snake9.Regrowth.E112259
noncomputable section
local instance blockDec26 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause833 (q : Nat → Bool) : valuationOf q 455 = false ∨ valuationOf q 457 = true := by
  have hs : count457 q = (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203]) + (countLit q [204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203]) (l₂ := [204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232])
  have hm := merge_right (literal (valuationOf q) (455)) (literal (valuationOf q) (457)) (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203]) (countLit q [204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) (count457 q) 1 (meaning455 q) (meaning457 q) hs
  change valuationOf q 455 = false ∨ valuationOf q 457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause833 (q : Snake 81) (h : Conditions q) : valuation q 455 = false ∨ valuation q 457 = true := counterClause833 (baseVal q)

theorem counterClause834 (q : Nat → Bool) : valuationOf q 456 = false ∨ valuationOf q 458 = true := by
  have hs : count457 q = (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203]) + (countLit q [204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203]) (l₂ := [204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232])
  have hm := merge_right (literal (valuationOf q) (456)) (literal (valuationOf q) (458)) (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203]) (countLit q [204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) (count457 q) 2 (meaning456 q) (meaning458 q) hs
  change valuationOf q 456 = false ∨ valuationOf q 458 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause834 (q : Snake 81) (h : Conditions q) : valuation q 456 = false ∨ valuation q 458 = true := counterClause834 (baseVal q)

theorem counterClause835 (q : Nat → Bool) : valuationOf q 399 = false ∨ valuationOf q 457 = true := by
  have hs : count457 q = (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203]) + (countLit q [204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203]) (l₂ := [204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232])
  have hm := merge_left (literal (valuationOf q) (399)) (literal (valuationOf q) (457)) (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203]) (countLit q [204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) (count457 q) 1 (meaning399 q) (meaning457 q) hs
  change valuationOf q 399 = false ∨ valuationOf q 457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause835 (q : Snake 81) (h : Conditions q) : valuation q 399 = false ∨ valuation q 457 = true := counterClause835 (baseVal q)

theorem counterClause836 (q : Nat → Bool) : valuationOf q 399 = false ∨ valuationOf q 455 = false ∨ valuationOf q 458 = true := by
  have hs : count457 q = (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203]) + (countLit q [204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203]) (l₂ := [204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232])
  have hm := merge_two (literal (valuationOf q) (399)) (literal (valuationOf q) (455)) (literal (valuationOf q) (458)) (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203]) (countLit q [204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) (count457 q) 1 1 (meaning399 q) (meaning455 q) (meaning458 q) hs
  change valuationOf q 399 = false ∨ valuationOf q 455 = false ∨ valuationOf q 458 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause836 (q : Snake 81) (h : Conditions q) : valuation q 399 = false ∨ valuation q 455 = false ∨ valuation q 458 = true := counterClause836 (baseVal q)

theorem counterClause837 (q : Nat → Bool) : valuationOf q 400 = false ∨ valuationOf q 458 = true := by
  have hs : count457 q = (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203]) + (countLit q [204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203]) (l₂ := [204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232])
  have hm := merge_left (literal (valuationOf q) (400)) (literal (valuationOf q) (458)) (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203]) (countLit q [204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) (count457 q) 2 (meaning400 q) (meaning458 q) hs
  change valuationOf q 400 = false ∨ valuationOf q 458 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause837 (q : Snake 81) (h : Conditions q) : valuation q 400 = false ∨ valuation q 458 = true := counterClause837 (baseVal q)

theorem counterClause838 (q : Nat → Bool) : valuationOf q 458 = false ∨ valuationOf q 460 = true := by
  have hs : count459 q = (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) + (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) (l₂ := [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232])
  have hm := merge_right (literal (valuationOf q) (458)) (literal (valuationOf q) (460)) (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) (count459 q) 2 (meaning458 q) (meaning460 q) hs
  change valuationOf q 458 = false ∨ valuationOf q 460 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause838 (q : Snake 81) (h : Conditions q) : valuation q 458 = false ∨ valuation q 460 = true := counterClause838 (baseVal q)

theorem counterClause839 (q : Nat → Bool) : valuationOf q 343 = false ∨ valuationOf q 457 = false ∨ valuationOf q 460 = true := by
  have hs : count459 q = (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) + (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) (l₂ := [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232])
  have hm := merge_two (literal (valuationOf q) (343)) (literal (valuationOf q) (457)) (literal (valuationOf q) (460)) (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) (count459 q) 1 1 (meaning343 q) (meaning457 q) (meaning460 q) hs
  change valuationOf q 343 = false ∨ valuationOf q 457 = false ∨ valuationOf q 460 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause839 (q : Snake 81) (h : Conditions q) : valuation q 343 = false ∨ valuation q 457 = false ∨ valuation q 460 = true := counterClause839 (baseVal q)

theorem counterClause840 (q : Nat → Bool) : valuationOf q 344 = false ∨ valuationOf q 460 = true := by
  have hs : count459 q = (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) + (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) (l₂ := [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232])
  have hm := merge_left (literal (valuationOf q) (344)) (literal (valuationOf q) (460)) (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) (count459 q) 2 (meaning344 q) (meaning460 q) hs
  change valuationOf q 344 = false ∨ valuationOf q 460 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause840 (q : Snake 81) (h : Conditions q) : valuation q 344 = false ∨ valuation q 460 = true := counterClause840 (baseVal q)

theorem clause841 (q : Snake 81) (h : Conditions q) : valuation q 460 = false := by
  rw [value460]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count459 (baseVal q) = (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := other_count_bound q h
  rw [he]
  omega

theorem counterClause842 (q : Nat → Bool) : valuationOf q 6 = true ∨ valuationOf q 787 = true := by
  have hs : count787 q = (countLit q [-2]) + (countLit q [-6]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-6])
  have hm := merge_right (literal (valuationOf q) (-6)) (literal (valuationOf q) (787)) (countLit q [-2]) (countLit q [-6]) (count787 q) 1 (meaningNeg6 q) (meaning787 q) hs
  change (! (valuationOf q 6)) = false ∨ valuationOf q 787 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause842 (q : Snake 81) (h : Conditions q) : valuation q 6 = true ∨ valuation q 787 = true := counterClause842 (baseVal q)

theorem counterClause843 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 787 = true := by
  have hs : count787 q = (countLit q [-2]) + (countLit q [-6]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-6])
  have hm := merge_left (literal (valuationOf q) (-2)) (literal (valuationOf q) (787)) (countLit q [-2]) (countLit q [-6]) (count787 q) 1 (meaningNeg2 q) (meaning787 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 787 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause843 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 787 = true := counterClause843 (baseVal q)

theorem counterClause844 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 6 = true ∨ valuationOf q 788 = true := by
  have hs : count787 q = (countLit q [-2]) + (countLit q [-6]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-6])
  have hm := merge_two (literal (valuationOf q) (-2)) (literal (valuationOf q) (-6)) (literal (valuationOf q) (788)) (countLit q [-2]) (countLit q [-6]) (count787 q) 1 1 (meaningNeg2 q) (meaningNeg6 q) (meaning788 q) hs
  change (! (valuationOf q 2)) = false ∨ (! (valuationOf q 6)) = false ∨ valuationOf q 788 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause844 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 6 = true ∨ valuation q 788 = true := counterClause844 (baseVal q)

theorem counterClause845 (q : Nat → Bool) : valuationOf q 787 = false ∨ valuationOf q 789 = true := by
  have hs : count789 q = (countLit q [-1]) + (countLit q [-2, -6]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-2, -6])
  have hm := merge_right (literal (valuationOf q) (787)) (literal (valuationOf q) (789)) (countLit q [-1]) (countLit q [-2, -6]) (count789 q) 1 (meaning787 q) (meaning789 q) hs
  change valuationOf q 787 = false ∨ valuationOf q 789 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause845 (q : Snake 81) (h : Conditions q) : valuation q 787 = false ∨ valuation q 789 = true := counterClause845 (baseVal q)

theorem counterClause846 (q : Nat → Bool) : valuationOf q 788 = false ∨ valuationOf q 790 = true := by
  have hs : count789 q = (countLit q [-1]) + (countLit q [-2, -6]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-2, -6])
  have hm := merge_right (literal (valuationOf q) (788)) (literal (valuationOf q) (790)) (countLit q [-1]) (countLit q [-2, -6]) (count789 q) 2 (meaning788 q) (meaning790 q) hs
  change valuationOf q 788 = false ∨ valuationOf q 790 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause846 (q : Snake 81) (h : Conditions q) : valuation q 788 = false ∨ valuation q 790 = true := counterClause846 (baseVal q)

theorem counterClause847 (q : Nat → Bool) : valuationOf q 1 = true ∨ valuationOf q 789 = true := by
  have hs : count789 q = (countLit q [-1]) + (countLit q [-2, -6]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-2, -6])
  have hm := merge_left (literal (valuationOf q) (-1)) (literal (valuationOf q) (789)) (countLit q [-1]) (countLit q [-2, -6]) (count789 q) 1 (meaningNeg1 q) (meaning789 q) hs
  change (! (valuationOf q 1)) = false ∨ valuationOf q 789 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause847 (q : Snake 81) (h : Conditions q) : valuation q 1 = true ∨ valuation q 789 = true := counterClause847 (baseVal q)

theorem counterClause848 (q : Nat → Bool) : valuationOf q 1 = true ∨ valuationOf q 787 = false ∨ valuationOf q 790 = true := by
  have hs : count789 q = (countLit q [-1]) + (countLit q [-2, -6]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-2, -6])
  have hm := merge_two (literal (valuationOf q) (-1)) (literal (valuationOf q) (787)) (literal (valuationOf q) (790)) (countLit q [-1]) (countLit q [-2, -6]) (count789 q) 1 1 (meaningNeg1 q) (meaning787 q) (meaning790 q) hs
  change (! (valuationOf q 1)) = false ∨ valuationOf q 787 = false ∨ valuationOf q 790 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause848 (q : Snake 81) (h : Conditions q) : valuation q 1 = true ∨ valuation q 787 = false ∨ valuation q 790 = true := counterClause848 (baseVal q)

theorem counterClause849 (q : Nat → Bool) : valuationOf q 1 = true ∨ valuationOf q 788 = false ∨ valuationOf q 791 = true := by
  have hs : count789 q = (countLit q [-1]) + (countLit q [-2, -6]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-2, -6])
  have hm := merge_two (literal (valuationOf q) (-1)) (literal (valuationOf q) (788)) (literal (valuationOf q) (791)) (countLit q [-1]) (countLit q [-2, -6]) (count789 q) 1 2 (meaningNeg1 q) (meaning788 q) (meaning791 q) hs
  change (! (valuationOf q 1)) = false ∨ valuationOf q 788 = false ∨ valuationOf q 791 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause849 (q : Snake 81) (h : Conditions q) : valuation q 1 = true ∨ valuation q 788 = false ∨ valuation q 791 = true := counterClause849 (baseVal q)

theorem counterClause850 (q : Nat → Bool) : valuationOf q 10 = true ∨ valuationOf q 792 = true := by
  have hs : count792 q = (countLit q [-7]) + (countLit q [-10]) := List.countP_append (p := literal q) (l₁ := [-7]) (l₂ := [-10])
  have hm := merge_right (literal (valuationOf q) (-10)) (literal (valuationOf q) (792)) (countLit q [-7]) (countLit q [-10]) (count792 q) 1 (meaningNeg10 q) (meaning792 q) hs
  change (! (valuationOf q 10)) = false ∨ valuationOf q 792 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause850 (q : Snake 81) (h : Conditions q) : valuation q 10 = true ∨ valuation q 792 = true := counterClause850 (baseVal q)

theorem counterClause851 (q : Nat → Bool) : valuationOf q 7 = true ∨ valuationOf q 792 = true := by
  have hs : count792 q = (countLit q [-7]) + (countLit q [-10]) := List.countP_append (p := literal q) (l₁ := [-7]) (l₂ := [-10])
  have hm := merge_left (literal (valuationOf q) (-7)) (literal (valuationOf q) (792)) (countLit q [-7]) (countLit q [-10]) (count792 q) 1 (meaningNeg7 q) (meaning792 q) hs
  change (! (valuationOf q 7)) = false ∨ valuationOf q 792 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause851 (q : Snake 81) (h : Conditions q) : valuation q 7 = true ∨ valuation q 792 = true := counterClause851 (baseVal q)

theorem counterClause852 (q : Nat → Bool) : valuationOf q 7 = true ∨ valuationOf q 10 = true ∨ valuationOf q 793 = true := by
  have hs : count792 q = (countLit q [-7]) + (countLit q [-10]) := List.countP_append (p := literal q) (l₁ := [-7]) (l₂ := [-10])
  have hm := merge_two (literal (valuationOf q) (-7)) (literal (valuationOf q) (-10)) (literal (valuationOf q) (793)) (countLit q [-7]) (countLit q [-10]) (count792 q) 1 1 (meaningNeg7 q) (meaningNeg10 q) (meaning793 q) hs
  change (! (valuationOf q 7)) = false ∨ (! (valuationOf q 10)) = false ∨ valuationOf q 793 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause852 (q : Snake 81) (h : Conditions q) : valuation q 7 = true ∨ valuation q 10 = true ∨ valuation q 793 = true := counterClause852 (baseVal q)

theorem counterClause853 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 794 = true := by
  have hs : count794 q = (countLit q [-11]) + (countLit q [-14]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-14])
  have hm := merge_right (literal (valuationOf q) (-14)) (literal (valuationOf q) (794)) (countLit q [-11]) (countLit q [-14]) (count794 q) 1 (meaningNeg14 q) (meaning794 q) hs
  change (! (valuationOf q 14)) = false ∨ valuationOf q 794 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause853 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 794 = true := counterClause853 (baseVal q)

theorem counterClause854 (q : Nat → Bool) : valuationOf q 11 = true ∨ valuationOf q 794 = true := by
  have hs : count794 q = (countLit q [-11]) + (countLit q [-14]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-14])
  have hm := merge_left (literal (valuationOf q) (-11)) (literal (valuationOf q) (794)) (countLit q [-11]) (countLit q [-14]) (count794 q) 1 (meaningNeg11 q) (meaning794 q) hs
  change (! (valuationOf q 11)) = false ∨ valuationOf q 794 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause854 (q : Snake 81) (h : Conditions q) : valuation q 11 = true ∨ valuation q 794 = true := counterClause854 (baseVal q)

theorem counterClause855 (q : Nat → Bool) : valuationOf q 11 = true ∨ valuationOf q 14 = true ∨ valuationOf q 795 = true := by
  have hs : count794 q = (countLit q [-11]) + (countLit q [-14]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-14])
  have hm := merge_two (literal (valuationOf q) (-11)) (literal (valuationOf q) (-14)) (literal (valuationOf q) (795)) (countLit q [-11]) (countLit q [-14]) (count794 q) 1 1 (meaningNeg11 q) (meaningNeg14 q) (meaning795 q) hs
  change (! (valuationOf q 11)) = false ∨ (! (valuationOf q 14)) = false ∨ valuationOf q 795 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause855 (q : Snake 81) (h : Conditions q) : valuation q 11 = true ∨ valuation q 14 = true ∨ valuation q 795 = true := counterClause855 (baseVal q)

theorem counterClause856 (q : Nat → Bool) : valuationOf q 794 = false ∨ valuationOf q 796 = true := by
  have hs : count796 q = (countLit q [-7, -10]) + (countLit q [-11, -14]) := List.countP_append (p := literal q) (l₁ := [-7, -10]) (l₂ := [-11, -14])
  have hm := merge_right (literal (valuationOf q) (794)) (literal (valuationOf q) (796)) (countLit q [-7, -10]) (countLit q [-11, -14]) (count796 q) 1 (meaning794 q) (meaning796 q) hs
  change valuationOf q 794 = false ∨ valuationOf q 796 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause856 (q : Snake 81) (h : Conditions q) : valuation q 794 = false ∨ valuation q 796 = true := counterClause856 (baseVal q)

theorem counterClause857 (q : Nat → Bool) : valuationOf q 795 = false ∨ valuationOf q 797 = true := by
  have hs : count796 q = (countLit q [-7, -10]) + (countLit q [-11, -14]) := List.countP_append (p := literal q) (l₁ := [-7, -10]) (l₂ := [-11, -14])
  have hm := merge_right (literal (valuationOf q) (795)) (literal (valuationOf q) (797)) (countLit q [-7, -10]) (countLit q [-11, -14]) (count796 q) 2 (meaning795 q) (meaning797 q) hs
  change valuationOf q 795 = false ∨ valuationOf q 797 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause857 (q : Snake 81) (h : Conditions q) : valuation q 795 = false ∨ valuation q 797 = true := counterClause857 (baseVal q)

theorem counterClause858 (q : Nat → Bool) : valuationOf q 792 = false ∨ valuationOf q 796 = true := by
  have hs : count796 q = (countLit q [-7, -10]) + (countLit q [-11, -14]) := List.countP_append (p := literal q) (l₁ := [-7, -10]) (l₂ := [-11, -14])
  have hm := merge_left (literal (valuationOf q) (792)) (literal (valuationOf q) (796)) (countLit q [-7, -10]) (countLit q [-11, -14]) (count796 q) 1 (meaning792 q) (meaning796 q) hs
  change valuationOf q 792 = false ∨ valuationOf q 796 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause858 (q : Snake 81) (h : Conditions q) : valuation q 792 = false ∨ valuation q 796 = true := counterClause858 (baseVal q)

theorem counterClause859 (q : Nat → Bool) : valuationOf q 792 = false ∨ valuationOf q 794 = false ∨ valuationOf q 797 = true := by
  have hs : count796 q = (countLit q [-7, -10]) + (countLit q [-11, -14]) := List.countP_append (p := literal q) (l₁ := [-7, -10]) (l₂ := [-11, -14])
  have hm := merge_two (literal (valuationOf q) (792)) (literal (valuationOf q) (794)) (literal (valuationOf q) (797)) (countLit q [-7, -10]) (countLit q [-11, -14]) (count796 q) 1 1 (meaning792 q) (meaning794 q) (meaning797 q) hs
  change valuationOf q 792 = false ∨ valuationOf q 794 = false ∨ valuationOf q 797 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause859 (q : Snake 81) (h : Conditions q) : valuation q 792 = false ∨ valuation q 794 = false ∨ valuation q 797 = true := counterClause859 (baseVal q)

theorem counterClause860 (q : Nat → Bool) : valuationOf q 792 = false ∨ valuationOf q 795 = false ∨ valuationOf q 798 = true := by
  have hs : count796 q = (countLit q [-7, -10]) + (countLit q [-11, -14]) := List.countP_append (p := literal q) (l₁ := [-7, -10]) (l₂ := [-11, -14])
  have hm := merge_two (literal (valuationOf q) (792)) (literal (valuationOf q) (795)) (literal (valuationOf q) (798)) (countLit q [-7, -10]) (countLit q [-11, -14]) (count796 q) 1 2 (meaning792 q) (meaning795 q) (meaning798 q) hs
  change valuationOf q 792 = false ∨ valuationOf q 795 = false ∨ valuationOf q 798 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause860 (q : Snake 81) (h : Conditions q) : valuation q 792 = false ∨ valuation q 795 = false ∨ valuation q 798 = true := counterClause860 (baseVal q)

theorem counterClause861 (q : Nat → Bool) : valuationOf q 793 = false ∨ valuationOf q 797 = true := by
  have hs : count796 q = (countLit q [-7, -10]) + (countLit q [-11, -14]) := List.countP_append (p := literal q) (l₁ := [-7, -10]) (l₂ := [-11, -14])
  have hm := merge_left (literal (valuationOf q) (793)) (literal (valuationOf q) (797)) (countLit q [-7, -10]) (countLit q [-11, -14]) (count796 q) 2 (meaning793 q) (meaning797 q) hs
  change valuationOf q 793 = false ∨ valuationOf q 797 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause861 (q : Snake 81) (h : Conditions q) : valuation q 793 = false ∨ valuation q 797 = true := counterClause861 (baseVal q)

theorem counterClause862 (q : Nat → Bool) : valuationOf q 793 = false ∨ valuationOf q 794 = false ∨ valuationOf q 798 = true := by
  have hs : count796 q = (countLit q [-7, -10]) + (countLit q [-11, -14]) := List.countP_append (p := literal q) (l₁ := [-7, -10]) (l₂ := [-11, -14])
  have hm := merge_two (literal (valuationOf q) (793)) (literal (valuationOf q) (794)) (literal (valuationOf q) (798)) (countLit q [-7, -10]) (countLit q [-11, -14]) (count796 q) 2 1 (meaning793 q) (meaning794 q) (meaning798 q) hs
  change valuationOf q 793 = false ∨ valuationOf q 794 = false ∨ valuationOf q 798 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause862 (q : Snake 81) (h : Conditions q) : valuation q 793 = false ∨ valuation q 794 = false ∨ valuation q 798 = true := counterClause862 (baseVal q)

theorem counterClause863 (q : Nat → Bool) : valuationOf q 793 = false ∨ valuationOf q 795 = false ∨ valuationOf q 799 = true := by
  have hs : count796 q = (countLit q [-7, -10]) + (countLit q [-11, -14]) := List.countP_append (p := literal q) (l₁ := [-7, -10]) (l₂ := [-11, -14])
  have hm := merge_two (literal (valuationOf q) (793)) (literal (valuationOf q) (795)) (literal (valuationOf q) (799)) (countLit q [-7, -10]) (countLit q [-11, -14]) (count796 q) 2 2 (meaning793 q) (meaning795 q) (meaning799 q) hs
  change valuationOf q 793 = false ∨ valuationOf q 795 = false ∨ valuationOf q 799 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause863 (q : Snake 81) (h : Conditions q) : valuation q 793 = false ∨ valuation q 795 = false ∨ valuation q 799 = true := counterClause863 (baseVal q)

theorem counterClause864 (q : Nat → Bool) : valuationOf q 796 = false ∨ valuationOf q 800 = true := by
  have hs : count800 q = (countLit q [-1, -2, -6]) + (countLit q [-7, -10, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6]) (l₂ := [-7, -10, -11, -14])
  have hm := merge_right (literal (valuationOf q) (796)) (literal (valuationOf q) (800)) (countLit q [-1, -2, -6]) (countLit q [-7, -10, -11, -14]) (count800 q) 1 (meaning796 q) (meaning800 q) hs
  change valuationOf q 796 = false ∨ valuationOf q 800 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause864 (q : Snake 81) (h : Conditions q) : valuation q 796 = false ∨ valuation q 800 = true := counterClause864 (baseVal q)

theorem block26 (q : Snake 81) (h : Conditions q) : B112E259.Block26 (valuation q) :=
  ⟨clause833 q h, clause834 q h, clause835 q h, clause836 q h, clause837 q h, clause838 q h, clause839 q h, clause840 q h, clause841 q h, clause842 q h, clause843 q h, clause844 q h, clause845 q h, clause846 q h, clause847 q h, clause848 q h, clause849 q h, clause850 q h, clause851 q h, clause852 q h, clause853 q h, clause854 q h, clause855 q h, clause856 q h, clause857 q h, clause858 q h, clause859 q h, clause860 q h, clause861 q h, clause862 q h, clause863 q h, clause864 q h⟩

end
end Snake9.Regrowth.E112259
