import E112213Semantics
import B112E213Inputs
namespace Snake9.Regrowth.E112213
noncomputable section
local instance blockDec22 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause705 (q : Nat → Bool) : valuationOf q 459 = false ∨ valuationOf q 461 = true := by
  have hs : count461 q = (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]) + (countLit q [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234]) := List.countP_append (p := literal q) (l₁ := [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]) (l₂ := [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234])
  have hm := merge_right (literal (valuationOf q) (459)) (literal (valuationOf q) (461)) (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]) (countLit q [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234]) (count461 q) 1 (meaning459 q) (meaning461 q) hs
  change valuationOf q 459 = false ∨ valuationOf q 461 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause705 (q : Snake 81) (h : Conditions q) : valuation q 459 = false ∨ valuation q 461 = true := counterClause705 (baseVal q)

theorem counterClause706 (q : Nat → Bool) : valuationOf q 460 = false ∨ valuationOf q 462 = true := by
  have hs : count461 q = (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]) + (countLit q [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234]) := List.countP_append (p := literal q) (l₁ := [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]) (l₂ := [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234])
  have hm := merge_right (literal (valuationOf q) (460)) (literal (valuationOf q) (462)) (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]) (countLit q [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234]) (count461 q) 2 (meaning460 q) (meaning462 q) hs
  change valuationOf q 460 = false ∨ valuationOf q 462 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause706 (q : Snake 81) (h : Conditions q) : valuation q 460 = false ∨ valuation q 462 = true := counterClause706 (baseVal q)

theorem counterClause707 (q : Nat → Bool) : valuationOf q 403 = false ∨ valuationOf q 461 = true := by
  have hs : count461 q = (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]) + (countLit q [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234]) := List.countP_append (p := literal q) (l₁ := [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]) (l₂ := [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234])
  have hm := merge_left (literal (valuationOf q) (403)) (literal (valuationOf q) (461)) (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]) (countLit q [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234]) (count461 q) 1 (meaning403 q) (meaning461 q) hs
  change valuationOf q 403 = false ∨ valuationOf q 461 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause707 (q : Snake 81) (h : Conditions q) : valuation q 403 = false ∨ valuation q 461 = true := counterClause707 (baseVal q)

theorem counterClause708 (q : Nat → Bool) : valuationOf q 403 = false ∨ valuationOf q 459 = false ∨ valuationOf q 462 = true := by
  have hs : count461 q = (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]) + (countLit q [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234]) := List.countP_append (p := literal q) (l₁ := [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]) (l₂ := [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234])
  have hm := merge_two (literal (valuationOf q) (403)) (literal (valuationOf q) (459)) (literal (valuationOf q) (462)) (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]) (countLit q [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234]) (count461 q) 1 1 (meaning403 q) (meaning459 q) (meaning462 q) hs
  change valuationOf q 403 = false ∨ valuationOf q 459 = false ∨ valuationOf q 462 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause708 (q : Snake 81) (h : Conditions q) : valuation q 403 = false ∨ valuation q 459 = false ∨ valuation q 462 = true := counterClause708 (baseVal q)

theorem counterClause709 (q : Nat → Bool) : valuationOf q 404 = false ∨ valuationOf q 462 = true := by
  have hs : count461 q = (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]) + (countLit q [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234]) := List.countP_append (p := literal q) (l₁ := [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]) (l₂ := [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234])
  have hm := merge_left (literal (valuationOf q) (404)) (literal (valuationOf q) (462)) (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]) (countLit q [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234]) (count461 q) 2 (meaning404 q) (meaning462 q) hs
  change valuationOf q 404 = false ∨ valuationOf q 462 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause709 (q : Snake 81) (h : Conditions q) : valuation q 404 = false ∨ valuation q 462 = true := counterClause709 (baseVal q)

theorem counterClause710 (q : Nat → Bool) : valuationOf q 462 = false ∨ valuationOf q 464 = true := by
  have hs : count463 q = (countLit q [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]) + (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234]) := List.countP_append (p := literal q) (l₁ := [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]) (l₂ := [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234])
  have hm := merge_right (literal (valuationOf q) (462)) (literal (valuationOf q) (464)) (countLit q [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]) (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234]) (count463 q) 2 (meaning462 q) (meaning464 q) hs
  change valuationOf q 462 = false ∨ valuationOf q 464 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause710 (q : Snake 81) (h : Conditions q) : valuation q 462 = false ∨ valuation q 464 = true := counterClause710 (baseVal q)

theorem counterClause711 (q : Nat → Bool) : valuationOf q 347 = false ∨ valuationOf q 461 = false ∨ valuationOf q 464 = true := by
  have hs : count463 q = (countLit q [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]) + (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234]) := List.countP_append (p := literal q) (l₁ := [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]) (l₂ := [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234])
  have hm := merge_two (literal (valuationOf q) (347)) (literal (valuationOf q) (461)) (literal (valuationOf q) (464)) (countLit q [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]) (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234]) (count463 q) 1 1 (meaning347 q) (meaning461 q) (meaning464 q) hs
  change valuationOf q 347 = false ∨ valuationOf q 461 = false ∨ valuationOf q 464 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause711 (q : Snake 81) (h : Conditions q) : valuation q 347 = false ∨ valuation q 461 = false ∨ valuation q 464 = true := counterClause711 (baseVal q)

theorem counterClause712 (q : Nat → Bool) : valuationOf q 348 = false ∨ valuationOf q 464 = true := by
  have hs : count463 q = (countLit q [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]) + (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234]) := List.countP_append (p := literal q) (l₁ := [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]) (l₂ := [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234])
  have hm := merge_left (literal (valuationOf q) (348)) (literal (valuationOf q) (464)) (countLit q [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]) (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234]) (count463 q) 2 (meaning348 q) (meaning464 q) hs
  change valuationOf q 348 = false ∨ valuationOf q 464 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause712 (q : Snake 81) (h : Conditions q) : valuation q 348 = false ∨ valuation q 464 = true := counterClause712 (baseVal q)

theorem clause713 (q : Snake 81) (h : Conditions q) : valuation q 464 = false := by
  rw [value464]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count463 (baseVal q) = (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := other_count_bound q h
  rw [he]
  omega

theorem counterClause714 (q : Nat → Bool) : valuationOf q 6 = true ∨ valuationOf q 797 = true := by
  have hs : count797 q = (countLit q [-3]) + (countLit q [-6]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-6])
  have hm := merge_right (literal (valuationOf q) (-6)) (literal (valuationOf q) (797)) (countLit q [-3]) (countLit q [-6]) (count797 q) 1 (meaningNeg6 q) (meaning797 q) hs
  change (! (valuationOf q 6)) = false ∨ valuationOf q 797 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause714 (q : Snake 81) (h : Conditions q) : valuation q 6 = true ∨ valuation q 797 = true := counterClause714 (baseVal q)

theorem counterClause715 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 797 = true := by
  have hs : count797 q = (countLit q [-3]) + (countLit q [-6]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-6])
  have hm := merge_left (literal (valuationOf q) (-3)) (literal (valuationOf q) (797)) (countLit q [-3]) (countLit q [-6]) (count797 q) 1 (meaningNeg3 q) (meaning797 q) hs
  change (! (valuationOf q 3)) = false ∨ valuationOf q 797 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause715 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 797 = true := counterClause715 (baseVal q)

theorem counterClause716 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 6 = true ∨ valuationOf q 798 = true := by
  have hs : count797 q = (countLit q [-3]) + (countLit q [-6]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-6])
  have hm := merge_two (literal (valuationOf q) (-3)) (literal (valuationOf q) (-6)) (literal (valuationOf q) (798)) (countLit q [-3]) (countLit q [-6]) (count797 q) 1 1 (meaningNeg3 q) (meaningNeg6 q) (meaning798 q) hs
  change (! (valuationOf q 3)) = false ∨ (! (valuationOf q 6)) = false ∨ valuationOf q 798 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause716 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 6 = true ∨ valuation q 798 = true := counterClause716 (baseVal q)

theorem counterClause717 (q : Nat → Bool) : valuationOf q 797 = false ∨ valuationOf q 799 = true := by
  have hs : count799 q = (countLit q [-1]) + (countLit q [-3, -6]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-3, -6])
  have hm := merge_right (literal (valuationOf q) (797)) (literal (valuationOf q) (799)) (countLit q [-1]) (countLit q [-3, -6]) (count799 q) 1 (meaning797 q) (meaning799 q) hs
  change valuationOf q 797 = false ∨ valuationOf q 799 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause717 (q : Snake 81) (h : Conditions q) : valuation q 797 = false ∨ valuation q 799 = true := counterClause717 (baseVal q)

theorem counterClause718 (q : Nat → Bool) : valuationOf q 798 = false ∨ valuationOf q 800 = true := by
  have hs : count799 q = (countLit q [-1]) + (countLit q [-3, -6]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-3, -6])
  have hm := merge_right (literal (valuationOf q) (798)) (literal (valuationOf q) (800)) (countLit q [-1]) (countLit q [-3, -6]) (count799 q) 2 (meaning798 q) (meaning800 q) hs
  change valuationOf q 798 = false ∨ valuationOf q 800 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause718 (q : Snake 81) (h : Conditions q) : valuation q 798 = false ∨ valuation q 800 = true := counterClause718 (baseVal q)

theorem counterClause719 (q : Nat → Bool) : valuationOf q 1 = true ∨ valuationOf q 799 = true := by
  have hs : count799 q = (countLit q [-1]) + (countLit q [-3, -6]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-3, -6])
  have hm := merge_left (literal (valuationOf q) (-1)) (literal (valuationOf q) (799)) (countLit q [-1]) (countLit q [-3, -6]) (count799 q) 1 (meaningNeg1 q) (meaning799 q) hs
  change (! (valuationOf q 1)) = false ∨ valuationOf q 799 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause719 (q : Snake 81) (h : Conditions q) : valuation q 1 = true ∨ valuation q 799 = true := counterClause719 (baseVal q)

theorem counterClause720 (q : Nat → Bool) : valuationOf q 1 = true ∨ valuationOf q 797 = false ∨ valuationOf q 800 = true := by
  have hs : count799 q = (countLit q [-1]) + (countLit q [-3, -6]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-3, -6])
  have hm := merge_two (literal (valuationOf q) (-1)) (literal (valuationOf q) (797)) (literal (valuationOf q) (800)) (countLit q [-1]) (countLit q [-3, -6]) (count799 q) 1 1 (meaningNeg1 q) (meaning797 q) (meaning800 q) hs
  change (! (valuationOf q 1)) = false ∨ valuationOf q 797 = false ∨ valuationOf q 800 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause720 (q : Snake 81) (h : Conditions q) : valuation q 1 = true ∨ valuation q 797 = false ∨ valuation q 800 = true := counterClause720 (baseVal q)

theorem counterClause721 (q : Nat → Bool) : valuationOf q 1 = true ∨ valuationOf q 798 = false ∨ valuationOf q 801 = true := by
  have hs : count799 q = (countLit q [-1]) + (countLit q [-3, -6]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-3, -6])
  have hm := merge_two (literal (valuationOf q) (-1)) (literal (valuationOf q) (798)) (literal (valuationOf q) (801)) (countLit q [-1]) (countLit q [-3, -6]) (count799 q) 1 2 (meaningNeg1 q) (meaning798 q) (meaning801 q) hs
  change (! (valuationOf q 1)) = false ∨ valuationOf q 798 = false ∨ valuationOf q 801 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause721 (q : Snake 81) (h : Conditions q) : valuation q 1 = true ∨ valuation q 798 = false ∨ valuation q 801 = true := counterClause721 (baseVal q)

theorem counterClause722 (q : Nat → Bool) : valuationOf q 11 = true ∨ valuationOf q 802 = true := by
  have hs : count802 q = (countLit q [-8]) + (countLit q [-11]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-11])
  have hm := merge_right (literal (valuationOf q) (-11)) (literal (valuationOf q) (802)) (countLit q [-8]) (countLit q [-11]) (count802 q) 1 (meaningNeg11 q) (meaning802 q) hs
  change (! (valuationOf q 11)) = false ∨ valuationOf q 802 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause722 (q : Snake 81) (h : Conditions q) : valuation q 11 = true ∨ valuation q 802 = true := counterClause722 (baseVal q)

theorem counterClause723 (q : Nat → Bool) : valuationOf q 8 = true ∨ valuationOf q 802 = true := by
  have hs : count802 q = (countLit q [-8]) + (countLit q [-11]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-11])
  have hm := merge_left (literal (valuationOf q) (-8)) (literal (valuationOf q) (802)) (countLit q [-8]) (countLit q [-11]) (count802 q) 1 (meaningNeg8 q) (meaning802 q) hs
  change (! (valuationOf q 8)) = false ∨ valuationOf q 802 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause723 (q : Snake 81) (h : Conditions q) : valuation q 8 = true ∨ valuation q 802 = true := counterClause723 (baseVal q)

theorem counterClause724 (q : Nat → Bool) : valuationOf q 8 = true ∨ valuationOf q 11 = true ∨ valuationOf q 803 = true := by
  have hs : count802 q = (countLit q [-8]) + (countLit q [-11]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-11])
  have hm := merge_two (literal (valuationOf q) (-8)) (literal (valuationOf q) (-11)) (literal (valuationOf q) (803)) (countLit q [-8]) (countLit q [-11]) (count802 q) 1 1 (meaningNeg8 q) (meaningNeg11 q) (meaning803 q) hs
  change (! (valuationOf q 8)) = false ∨ (! (valuationOf q 11)) = false ∨ valuationOf q 803 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause724 (q : Snake 81) (h : Conditions q) : valuation q 8 = true ∨ valuation q 11 = true ∨ valuation q 803 = true := counterClause724 (baseVal q)

theorem counterClause725 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 804 = true := by
  have hs : count804 q = (countLit q [-13]) + (countLit q [-14]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-14])
  have hm := merge_right (literal (valuationOf q) (-14)) (literal (valuationOf q) (804)) (countLit q [-13]) (countLit q [-14]) (count804 q) 1 (meaningNeg14 q) (meaning804 q) hs
  change (! (valuationOf q 14)) = false ∨ valuationOf q 804 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause725 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 804 = true := counterClause725 (baseVal q)

theorem counterClause726 (q : Nat → Bool) : valuationOf q 13 = true ∨ valuationOf q 804 = true := by
  have hs : count804 q = (countLit q [-13]) + (countLit q [-14]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-14])
  have hm := merge_left (literal (valuationOf q) (-13)) (literal (valuationOf q) (804)) (countLit q [-13]) (countLit q [-14]) (count804 q) 1 (meaningNeg13 q) (meaning804 q) hs
  change (! (valuationOf q 13)) = false ∨ valuationOf q 804 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause726 (q : Snake 81) (h : Conditions q) : valuation q 13 = true ∨ valuation q 804 = true := counterClause726 (baseVal q)

theorem counterClause727 (q : Nat → Bool) : valuationOf q 13 = true ∨ valuationOf q 14 = true ∨ valuationOf q 805 = true := by
  have hs : count804 q = (countLit q [-13]) + (countLit q [-14]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-14])
  have hm := merge_two (literal (valuationOf q) (-13)) (literal (valuationOf q) (-14)) (literal (valuationOf q) (805)) (countLit q [-13]) (countLit q [-14]) (count804 q) 1 1 (meaningNeg13 q) (meaningNeg14 q) (meaning805 q) hs
  change (! (valuationOf q 13)) = false ∨ (! (valuationOf q 14)) = false ∨ valuationOf q 805 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause727 (q : Snake 81) (h : Conditions q) : valuation q 13 = true ∨ valuation q 14 = true ∨ valuation q 805 = true := counterClause727 (baseVal q)

theorem counterClause728 (q : Nat → Bool) : valuationOf q 804 = false ∨ valuationOf q 806 = true := by
  have hs : count806 q = (countLit q [-8, -11]) + (countLit q [-13, -14]) := List.countP_append (p := literal q) (l₁ := [-8, -11]) (l₂ := [-13, -14])
  have hm := merge_right (literal (valuationOf q) (804)) (literal (valuationOf q) (806)) (countLit q [-8, -11]) (countLit q [-13, -14]) (count806 q) 1 (meaning804 q) (meaning806 q) hs
  change valuationOf q 804 = false ∨ valuationOf q 806 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause728 (q : Snake 81) (h : Conditions q) : valuation q 804 = false ∨ valuation q 806 = true := counterClause728 (baseVal q)

theorem counterClause729 (q : Nat → Bool) : valuationOf q 805 = false ∨ valuationOf q 807 = true := by
  have hs : count806 q = (countLit q [-8, -11]) + (countLit q [-13, -14]) := List.countP_append (p := literal q) (l₁ := [-8, -11]) (l₂ := [-13, -14])
  have hm := merge_right (literal (valuationOf q) (805)) (literal (valuationOf q) (807)) (countLit q [-8, -11]) (countLit q [-13, -14]) (count806 q) 2 (meaning805 q) (meaning807 q) hs
  change valuationOf q 805 = false ∨ valuationOf q 807 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause729 (q : Snake 81) (h : Conditions q) : valuation q 805 = false ∨ valuation q 807 = true := counterClause729 (baseVal q)

theorem counterClause730 (q : Nat → Bool) : valuationOf q 802 = false ∨ valuationOf q 806 = true := by
  have hs : count806 q = (countLit q [-8, -11]) + (countLit q [-13, -14]) := List.countP_append (p := literal q) (l₁ := [-8, -11]) (l₂ := [-13, -14])
  have hm := merge_left (literal (valuationOf q) (802)) (literal (valuationOf q) (806)) (countLit q [-8, -11]) (countLit q [-13, -14]) (count806 q) 1 (meaning802 q) (meaning806 q) hs
  change valuationOf q 802 = false ∨ valuationOf q 806 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause730 (q : Snake 81) (h : Conditions q) : valuation q 802 = false ∨ valuation q 806 = true := counterClause730 (baseVal q)

theorem counterClause731 (q : Nat → Bool) : valuationOf q 802 = false ∨ valuationOf q 804 = false ∨ valuationOf q 807 = true := by
  have hs : count806 q = (countLit q [-8, -11]) + (countLit q [-13, -14]) := List.countP_append (p := literal q) (l₁ := [-8, -11]) (l₂ := [-13, -14])
  have hm := merge_two (literal (valuationOf q) (802)) (literal (valuationOf q) (804)) (literal (valuationOf q) (807)) (countLit q [-8, -11]) (countLit q [-13, -14]) (count806 q) 1 1 (meaning802 q) (meaning804 q) (meaning807 q) hs
  change valuationOf q 802 = false ∨ valuationOf q 804 = false ∨ valuationOf q 807 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause731 (q : Snake 81) (h : Conditions q) : valuation q 802 = false ∨ valuation q 804 = false ∨ valuation q 807 = true := counterClause731 (baseVal q)

theorem counterClause732 (q : Nat → Bool) : valuationOf q 802 = false ∨ valuationOf q 805 = false ∨ valuationOf q 808 = true := by
  have hs : count806 q = (countLit q [-8, -11]) + (countLit q [-13, -14]) := List.countP_append (p := literal q) (l₁ := [-8, -11]) (l₂ := [-13, -14])
  have hm := merge_two (literal (valuationOf q) (802)) (literal (valuationOf q) (805)) (literal (valuationOf q) (808)) (countLit q [-8, -11]) (countLit q [-13, -14]) (count806 q) 1 2 (meaning802 q) (meaning805 q) (meaning808 q) hs
  change valuationOf q 802 = false ∨ valuationOf q 805 = false ∨ valuationOf q 808 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause732 (q : Snake 81) (h : Conditions q) : valuation q 802 = false ∨ valuation q 805 = false ∨ valuation q 808 = true := counterClause732 (baseVal q)

theorem counterClause733 (q : Nat → Bool) : valuationOf q 803 = false ∨ valuationOf q 807 = true := by
  have hs : count806 q = (countLit q [-8, -11]) + (countLit q [-13, -14]) := List.countP_append (p := literal q) (l₁ := [-8, -11]) (l₂ := [-13, -14])
  have hm := merge_left (literal (valuationOf q) (803)) (literal (valuationOf q) (807)) (countLit q [-8, -11]) (countLit q [-13, -14]) (count806 q) 2 (meaning803 q) (meaning807 q) hs
  change valuationOf q 803 = false ∨ valuationOf q 807 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause733 (q : Snake 81) (h : Conditions q) : valuation q 803 = false ∨ valuation q 807 = true := counterClause733 (baseVal q)

theorem counterClause734 (q : Nat → Bool) : valuationOf q 803 = false ∨ valuationOf q 804 = false ∨ valuationOf q 808 = true := by
  have hs : count806 q = (countLit q [-8, -11]) + (countLit q [-13, -14]) := List.countP_append (p := literal q) (l₁ := [-8, -11]) (l₂ := [-13, -14])
  have hm := merge_two (literal (valuationOf q) (803)) (literal (valuationOf q) (804)) (literal (valuationOf q) (808)) (countLit q [-8, -11]) (countLit q [-13, -14]) (count806 q) 2 1 (meaning803 q) (meaning804 q) (meaning808 q) hs
  change valuationOf q 803 = false ∨ valuationOf q 804 = false ∨ valuationOf q 808 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause734 (q : Snake 81) (h : Conditions q) : valuation q 803 = false ∨ valuation q 804 = false ∨ valuation q 808 = true := counterClause734 (baseVal q)

theorem counterClause735 (q : Nat → Bool) : valuationOf q 803 = false ∨ valuationOf q 805 = false ∨ valuationOf q 809 = true := by
  have hs : count806 q = (countLit q [-8, -11]) + (countLit q [-13, -14]) := List.countP_append (p := literal q) (l₁ := [-8, -11]) (l₂ := [-13, -14])
  have hm := merge_two (literal (valuationOf q) (803)) (literal (valuationOf q) (805)) (literal (valuationOf q) (809)) (countLit q [-8, -11]) (countLit q [-13, -14]) (count806 q) 2 2 (meaning803 q) (meaning805 q) (meaning809 q) hs
  change valuationOf q 803 = false ∨ valuationOf q 805 = false ∨ valuationOf q 809 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause735 (q : Snake 81) (h : Conditions q) : valuation q 803 = false ∨ valuation q 805 = false ∨ valuation q 809 = true := counterClause735 (baseVal q)

theorem counterClause736 (q : Nat → Bool) : valuationOf q 806 = false ∨ valuationOf q 810 = true := by
  have hs : count810 q = (countLit q [-1, -3, -6]) + (countLit q [-8, -11, -13, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6]) (l₂ := [-8, -11, -13, -14])
  have hm := merge_right (literal (valuationOf q) (806)) (literal (valuationOf q) (810)) (countLit q [-1, -3, -6]) (countLit q [-8, -11, -13, -14]) (count810 q) 1 (meaning806 q) (meaning810 q) hs
  change valuationOf q 806 = false ∨ valuationOf q 810 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause736 (q : Snake 81) (h : Conditions q) : valuation q 806 = false ∨ valuation q 810 = true := counterClause736 (baseVal q)

theorem block22 (q : Snake 81) (h : Conditions q) : B112E213.Block22 (valuation q) :=
  ⟨clause705 q h, clause706 q h, clause707 q h, clause708 q h, clause709 q h, clause710 q h, clause711 q h, clause712 q h, clause713 q h, clause714 q h, clause715 q h, clause716 q h, clause717 q h, clause718 q h, clause719 q h, clause720 q h, clause721 q h, clause722 q h, clause723 q h, clause724 q h, clause725 q h, clause726 q h, clause727 q h, clause728 q h, clause729 q h, clause730 q h, clause731 q h, clause732 q h, clause733 q h, clause734 q h, clause735 q h, clause736 q h⟩

end
end Snake9.Regrowth.E112213
