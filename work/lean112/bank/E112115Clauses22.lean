import E112115Semantics
import B112E115Inputs
namespace Snake9.Regrowth.E112115
noncomputable section
local instance blockDec22 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause705 (q : Nat → Bool) : valuationOf q 443 = false ∨ valuationOf q 445 = false ∨ valuationOf q 448 = true := by
  have hs : count447 q = (countLit q [227, 228]) + (countLit q [229, 230]) := List.countP_append (p := literal q) (l₁ := [227, 228]) (l₂ := [229, 230])
  have hm := merge_two (literal (valuationOf q) (443)) (literal (valuationOf q) (445)) (literal (valuationOf q) (448)) (countLit q [227, 228]) (countLit q [229, 230]) (count447 q) 1 1 (meaning443 q) (meaning445 q) (meaning448 q) hs
  change valuationOf q 443 = false ∨ valuationOf q 445 = false ∨ valuationOf q 448 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause705 (q : Snake 81) (h : Conditions q) : valuation q 443 = false ∨ valuation q 445 = false ∨ valuation q 448 = true := counterClause705 (baseVal q)

theorem counterClause706 (q : Nat → Bool) : valuationOf q 233 = false ∨ valuationOf q 451 = true := by
  have hs : count451 q = (countLit q [233]) + (countLit q [234]) := List.countP_append (p := literal q) (l₁ := [233]) (l₂ := [234])
  have hm := merge_left (literal (valuationOf q) (233)) (literal (valuationOf q) (451)) (countLit q [233]) (countLit q [234]) (count451 q) 1 (meaning233 q) (meaning451 q) hs
  change valuationOf q 233 = false ∨ valuationOf q 451 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause706 (q : Snake 81) (h : Conditions q) : valuation q 233 = false ∨ valuation q 451 = true := counterClause706 (baseVal q)

theorem counterClause707 (q : Nat → Bool) : valuationOf q 451 = false ∨ valuationOf q 453 = true := by
  have hs : count453 q = (countLit q [231, 232]) + (countLit q [233, 234]) := List.countP_append (p := literal q) (l₁ := [231, 232]) (l₂ := [233, 234])
  have hm := merge_right (literal (valuationOf q) (451)) (literal (valuationOf q) (453)) (countLit q [231, 232]) (countLit q [233, 234]) (count453 q) 1 (meaning451 q) (meaning453 q) hs
  change valuationOf q 451 = false ∨ valuationOf q 453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause707 (q : Snake 81) (h : Conditions q) : valuation q 451 = false ∨ valuation q 453 = true := counterClause707 (baseVal q)

theorem counterClause708 (q : Nat → Bool) : valuationOf q 453 = false ∨ valuationOf q 455 = true := by
  have hs : count455 q = (countLit q [227, 228, 229, 230]) + (countLit q [231, 232, 233, 234]) := List.countP_append (p := literal q) (l₁ := [227, 228, 229, 230]) (l₂ := [231, 232, 233, 234])
  have hm := merge_right (literal (valuationOf q) (453)) (literal (valuationOf q) (455)) (countLit q [227, 228, 229, 230]) (countLit q [231, 232, 233, 234]) (count455 q) 1 (meaning453 q) (meaning455 q) hs
  change valuationOf q 453 = false ∨ valuationOf q 455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause708 (q : Snake 81) (h : Conditions q) : valuation q 453 = false ∨ valuation q 455 = true := counterClause708 (baseVal q)

theorem counterClause709 (q : Nat → Bool) : valuationOf q 447 = false ∨ valuationOf q 455 = true := by
  have hs : count455 q = (countLit q [227, 228, 229, 230]) + (countLit q [231, 232, 233, 234]) := List.countP_append (p := literal q) (l₁ := [227, 228, 229, 230]) (l₂ := [231, 232, 233, 234])
  have hm := merge_left (literal (valuationOf q) (447)) (literal (valuationOf q) (455)) (countLit q [227, 228, 229, 230]) (countLit q [231, 232, 233, 234]) (count455 q) 1 (meaning447 q) (meaning455 q) hs
  change valuationOf q 447 = false ∨ valuationOf q 455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause709 (q : Snake 81) (h : Conditions q) : valuation q 447 = false ∨ valuation q 455 = true := counterClause709 (baseVal q)

theorem counterClause710 (q : Nat → Bool) : valuationOf q 447 = false ∨ valuationOf q 453 = false ∨ valuationOf q 456 = true := by
  have hs : count455 q = (countLit q [227, 228, 229, 230]) + (countLit q [231, 232, 233, 234]) := List.countP_append (p := literal q) (l₁ := [227, 228, 229, 230]) (l₂ := [231, 232, 233, 234])
  have hm := merge_two (literal (valuationOf q) (447)) (literal (valuationOf q) (453)) (literal (valuationOf q) (456)) (countLit q [227, 228, 229, 230]) (countLit q [231, 232, 233, 234]) (count455 q) 1 1 (meaning447 q) (meaning453 q) (meaning456 q) hs
  change valuationOf q 447 = false ∨ valuationOf q 453 = false ∨ valuationOf q 456 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause710 (q : Snake 81) (h : Conditions q) : valuation q 447 = false ∨ valuation q 453 = false ∨ valuation q 456 = true := counterClause710 (baseVal q)

theorem counterClause711 (q : Nat → Bool) : valuationOf q 448 = false ∨ valuationOf q 456 = true := by
  have hs : count455 q = (countLit q [227, 228, 229, 230]) + (countLit q [231, 232, 233, 234]) := List.countP_append (p := literal q) (l₁ := [227, 228, 229, 230]) (l₂ := [231, 232, 233, 234])
  have hm := merge_left (literal (valuationOf q) (448)) (literal (valuationOf q) (456)) (countLit q [227, 228, 229, 230]) (countLit q [231, 232, 233, 234]) (count455 q) 2 (meaning448 q) (meaning456 q) hs
  change valuationOf q 448 = false ∨ valuationOf q 456 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause711 (q : Snake 81) (h : Conditions q) : valuation q 448 = false ∨ valuation q 456 = true := counterClause711 (baseVal q)

theorem counterClause712 (q : Nat → Bool) : valuationOf q 455 = false ∨ valuationOf q 457 = true := by
  have hs : count457 q = (countLit q [220, 221, 222, 223, 224, 225, 226]) + (countLit q [227, 228, 229, 230, 231, 232, 233, 234]) := List.countP_append (p := literal q) (l₁ := [220, 221, 222, 223, 224, 225, 226]) (l₂ := [227, 228, 229, 230, 231, 232, 233, 234])
  have hm := merge_right (literal (valuationOf q) (455)) (literal (valuationOf q) (457)) (countLit q [220, 221, 222, 223, 224, 225, 226]) (countLit q [227, 228, 229, 230, 231, 232, 233, 234]) (count457 q) 1 (meaning455 q) (meaning457 q) hs
  change valuationOf q 455 = false ∨ valuationOf q 457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause712 (q : Snake 81) (h : Conditions q) : valuation q 455 = false ∨ valuation q 457 = true := counterClause712 (baseVal q)

theorem counterClause713 (q : Nat → Bool) : valuationOf q 456 = false ∨ valuationOf q 458 = true := by
  have hs : count457 q = (countLit q [220, 221, 222, 223, 224, 225, 226]) + (countLit q [227, 228, 229, 230, 231, 232, 233, 234]) := List.countP_append (p := literal q) (l₁ := [220, 221, 222, 223, 224, 225, 226]) (l₂ := [227, 228, 229, 230, 231, 232, 233, 234])
  have hm := merge_right (literal (valuationOf q) (456)) (literal (valuationOf q) (458)) (countLit q [220, 221, 222, 223, 224, 225, 226]) (countLit q [227, 228, 229, 230, 231, 232, 233, 234]) (count457 q) 2 (meaning456 q) (meaning458 q) hs
  change valuationOf q 456 = false ∨ valuationOf q 458 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause713 (q : Snake 81) (h : Conditions q) : valuation q 456 = false ∨ valuation q 458 = true := counterClause713 (baseVal q)

theorem counterClause714 (q : Nat → Bool) : valuationOf q 441 = false ∨ valuationOf q 457 = true := by
  have hs : count457 q = (countLit q [220, 221, 222, 223, 224, 225, 226]) + (countLit q [227, 228, 229, 230, 231, 232, 233, 234]) := List.countP_append (p := literal q) (l₁ := [220, 221, 222, 223, 224, 225, 226]) (l₂ := [227, 228, 229, 230, 231, 232, 233, 234])
  have hm := merge_left (literal (valuationOf q) (441)) (literal (valuationOf q) (457)) (countLit q [220, 221, 222, 223, 224, 225, 226]) (countLit q [227, 228, 229, 230, 231, 232, 233, 234]) (count457 q) 1 (meaning441 q) (meaning457 q) hs
  change valuationOf q 441 = false ∨ valuationOf q 457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause714 (q : Snake 81) (h : Conditions q) : valuation q 441 = false ∨ valuation q 457 = true := counterClause714 (baseVal q)

theorem counterClause715 (q : Nat → Bool) : valuationOf q 441 = false ∨ valuationOf q 455 = false ∨ valuationOf q 458 = true := by
  have hs : count457 q = (countLit q [220, 221, 222, 223, 224, 225, 226]) + (countLit q [227, 228, 229, 230, 231, 232, 233, 234]) := List.countP_append (p := literal q) (l₁ := [220, 221, 222, 223, 224, 225, 226]) (l₂ := [227, 228, 229, 230, 231, 232, 233, 234])
  have hm := merge_two (literal (valuationOf q) (441)) (literal (valuationOf q) (455)) (literal (valuationOf q) (458)) (countLit q [220, 221, 222, 223, 224, 225, 226]) (countLit q [227, 228, 229, 230, 231, 232, 233, 234]) (count457 q) 1 1 (meaning441 q) (meaning455 q) (meaning458 q) hs
  change valuationOf q 441 = false ∨ valuationOf q 455 = false ∨ valuationOf q 458 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause715 (q : Snake 81) (h : Conditions q) : valuation q 441 = false ∨ valuation q 455 = false ∨ valuation q 458 = true := counterClause715 (baseVal q)

theorem counterClause716 (q : Nat → Bool) : valuationOf q 457 = false ∨ valuationOf q 459 = true := by
  have hs : count459 q = (countLit q [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 218, 219]) + (countLit q [220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234]) := List.countP_append (p := literal q) (l₁ := [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 218, 219]) (l₂ := [220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234])
  have hm := merge_right (literal (valuationOf q) (457)) (literal (valuationOf q) (459)) (countLit q [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 218, 219]) (countLit q [220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234]) (count459 q) 1 (meaning457 q) (meaning459 q) hs
  change valuationOf q 457 = false ∨ valuationOf q 459 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause716 (q : Snake 81) (h : Conditions q) : valuation q 457 = false ∨ valuation q 459 = true := counterClause716 (baseVal q)

theorem counterClause717 (q : Nat → Bool) : valuationOf q 458 = false ∨ valuationOf q 460 = true := by
  have hs : count459 q = (countLit q [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 218, 219]) + (countLit q [220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234]) := List.countP_append (p := literal q) (l₁ := [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 218, 219]) (l₂ := [220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234])
  have hm := merge_right (literal (valuationOf q) (458)) (literal (valuationOf q) (460)) (countLit q [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 218, 219]) (countLit q [220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234]) (count459 q) 2 (meaning458 q) (meaning460 q) hs
  change valuationOf q 458 = false ∨ valuationOf q 460 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause717 (q : Snake 81) (h : Conditions q) : valuation q 458 = false ∨ valuation q 460 = true := counterClause717 (baseVal q)

theorem counterClause718 (q : Nat → Bool) : valuationOf q 429 = false ∨ valuationOf q 459 = true := by
  have hs : count459 q = (countLit q [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 218, 219]) + (countLit q [220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234]) := List.countP_append (p := literal q) (l₁ := [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 218, 219]) (l₂ := [220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234])
  have hm := merge_left (literal (valuationOf q) (429)) (literal (valuationOf q) (459)) (countLit q [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 218, 219]) (countLit q [220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234]) (count459 q) 1 (meaning429 q) (meaning459 q) hs
  change valuationOf q 429 = false ∨ valuationOf q 459 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause718 (q : Snake 81) (h : Conditions q) : valuation q 429 = false ∨ valuation q 459 = true := counterClause718 (baseVal q)

theorem counterClause719 (q : Nat → Bool) : valuationOf q 430 = false ∨ valuationOf q 460 = true := by
  have hs : count459 q = (countLit q [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 218, 219]) + (countLit q [220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234]) := List.countP_append (p := literal q) (l₁ := [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 218, 219]) (l₂ := [220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234])
  have hm := merge_left (literal (valuationOf q) (430)) (literal (valuationOf q) (460)) (countLit q [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 218, 219]) (countLit q [220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234]) (count459 q) 2 (meaning430 q) (meaning460 q) hs
  change valuationOf q 430 = false ∨ valuationOf q 460 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause719 (q : Snake 81) (h : Conditions q) : valuation q 430 = false ∨ valuation q 460 = true := counterClause719 (baseVal q)

theorem counterClause720 (q : Nat → Bool) : valuationOf q 459 = false ∨ valuationOf q 461 = true := by
  have hs : count461 q = (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]) + (countLit q [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234]) := List.countP_append (p := literal q) (l₁ := [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]) (l₂ := [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234])
  have hm := merge_right (literal (valuationOf q) (459)) (literal (valuationOf q) (461)) (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]) (countLit q [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234]) (count461 q) 1 (meaning459 q) (meaning461 q) hs
  change valuationOf q 459 = false ∨ valuationOf q 461 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause720 (q : Snake 81) (h : Conditions q) : valuation q 459 = false ∨ valuation q 461 = true := counterClause720 (baseVal q)

theorem counterClause721 (q : Nat → Bool) : valuationOf q 460 = false ∨ valuationOf q 462 = true := by
  have hs : count461 q = (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]) + (countLit q [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234]) := List.countP_append (p := literal q) (l₁ := [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]) (l₂ := [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234])
  have hm := merge_right (literal (valuationOf q) (460)) (literal (valuationOf q) (462)) (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]) (countLit q [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234]) (count461 q) 2 (meaning460 q) (meaning462 q) hs
  change valuationOf q 460 = false ∨ valuationOf q 462 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause721 (q : Snake 81) (h : Conditions q) : valuation q 460 = false ∨ valuation q 462 = true := counterClause721 (baseVal q)

theorem counterClause722 (q : Nat → Bool) : valuationOf q 403 = false ∨ valuationOf q 461 = true := by
  have hs : count461 q = (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]) + (countLit q [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234]) := List.countP_append (p := literal q) (l₁ := [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]) (l₂ := [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234])
  have hm := merge_left (literal (valuationOf q) (403)) (literal (valuationOf q) (461)) (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]) (countLit q [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234]) (count461 q) 1 (meaning403 q) (meaning461 q) hs
  change valuationOf q 403 = false ∨ valuationOf q 461 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause722 (q : Snake 81) (h : Conditions q) : valuation q 403 = false ∨ valuation q 461 = true := counterClause722 (baseVal q)

theorem counterClause723 (q : Nat → Bool) : valuationOf q 403 = false ∨ valuationOf q 459 = false ∨ valuationOf q 462 = true := by
  have hs : count461 q = (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]) + (countLit q [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234]) := List.countP_append (p := literal q) (l₁ := [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]) (l₂ := [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234])
  have hm := merge_two (literal (valuationOf q) (403)) (literal (valuationOf q) (459)) (literal (valuationOf q) (462)) (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]) (countLit q [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234]) (count461 q) 1 1 (meaning403 q) (meaning459 q) (meaning462 q) hs
  change valuationOf q 403 = false ∨ valuationOf q 459 = false ∨ valuationOf q 462 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause723 (q : Snake 81) (h : Conditions q) : valuation q 403 = false ∨ valuation q 459 = false ∨ valuation q 462 = true := counterClause723 (baseVal q)

theorem counterClause724 (q : Nat → Bool) : valuationOf q 404 = false ∨ valuationOf q 462 = true := by
  have hs : count461 q = (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]) + (countLit q [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234]) := List.countP_append (p := literal q) (l₁ := [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]) (l₂ := [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234])
  have hm := merge_left (literal (valuationOf q) (404)) (literal (valuationOf q) (462)) (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]) (countLit q [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234]) (count461 q) 2 (meaning404 q) (meaning462 q) hs
  change valuationOf q 404 = false ∨ valuationOf q 462 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause724 (q : Snake 81) (h : Conditions q) : valuation q 404 = false ∨ valuation q 462 = true := counterClause724 (baseVal q)

theorem counterClause725 (q : Nat → Bool) : valuationOf q 462 = false ∨ valuationOf q 464 = true := by
  have hs : count463 q = (countLit q [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]) + (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234]) := List.countP_append (p := literal q) (l₁ := [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]) (l₂ := [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234])
  have hm := merge_right (literal (valuationOf q) (462)) (literal (valuationOf q) (464)) (countLit q [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]) (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234]) (count463 q) 2 (meaning462 q) (meaning464 q) hs
  change valuationOf q 462 = false ∨ valuationOf q 464 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause725 (q : Snake 81) (h : Conditions q) : valuation q 462 = false ∨ valuation q 464 = true := counterClause725 (baseVal q)

theorem counterClause726 (q : Nat → Bool) : valuationOf q 347 = false ∨ valuationOf q 461 = false ∨ valuationOf q 464 = true := by
  have hs : count463 q = (countLit q [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]) + (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234]) := List.countP_append (p := literal q) (l₁ := [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]) (l₂ := [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234])
  have hm := merge_two (literal (valuationOf q) (347)) (literal (valuationOf q) (461)) (literal (valuationOf q) (464)) (countLit q [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]) (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234]) (count463 q) 1 1 (meaning347 q) (meaning461 q) (meaning464 q) hs
  change valuationOf q 347 = false ∨ valuationOf q 461 = false ∨ valuationOf q 464 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause726 (q : Snake 81) (h : Conditions q) : valuation q 347 = false ∨ valuation q 461 = false ∨ valuation q 464 = true := counterClause726 (baseVal q)

theorem counterClause727 (q : Nat → Bool) : valuationOf q 348 = false ∨ valuationOf q 464 = true := by
  have hs : count463 q = (countLit q [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]) + (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234]) := List.countP_append (p := literal q) (l₁ := [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]) (l₂ := [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234])
  have hm := merge_left (literal (valuationOf q) (348)) (literal (valuationOf q) (464)) (countLit q [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]) (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234]) (count463 q) 2 (meaning348 q) (meaning464 q) hs
  change valuationOf q 348 = false ∨ valuationOf q 464 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause727 (q : Snake 81) (h : Conditions q) : valuation q 348 = false ∨ valuation q 464 = true := counterClause727 (baseVal q)

theorem clause728 (q : Snake 81) (h : Conditions q) : valuation q 464 = false := by
  rw [value464]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count463 (baseVal q) = (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := other_count_bound q h
  rw [he]
  omega

theorem counterClause729 (q : Nat → Bool) : valuationOf q 7 = true ∨ valuationOf q 797 = true := by
  have hs : count797 q = (countLit q [-4]) + (countLit q [-7]) := List.countP_append (p := literal q) (l₁ := [-4]) (l₂ := [-7])
  have hm := merge_right (literal (valuationOf q) (-7)) (literal (valuationOf q) (797)) (countLit q [-4]) (countLit q [-7]) (count797 q) 1 (meaningNeg7 q) (meaning797 q) hs
  change (! (valuationOf q 7)) = false ∨ valuationOf q 797 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause729 (q : Snake 81) (h : Conditions q) : valuation q 7 = true ∨ valuation q 797 = true := counterClause729 (baseVal q)

theorem counterClause730 (q : Nat → Bool) : valuationOf q 4 = true ∨ valuationOf q 797 = true := by
  have hs : count797 q = (countLit q [-4]) + (countLit q [-7]) := List.countP_append (p := literal q) (l₁ := [-4]) (l₂ := [-7])
  have hm := merge_left (literal (valuationOf q) (-4)) (literal (valuationOf q) (797)) (countLit q [-4]) (countLit q [-7]) (count797 q) 1 (meaningNeg4 q) (meaning797 q) hs
  change (! (valuationOf q 4)) = false ∨ valuationOf q 797 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause730 (q : Snake 81) (h : Conditions q) : valuation q 4 = true ∨ valuation q 797 = true := counterClause730 (baseVal q)

theorem counterClause731 (q : Nat → Bool) : valuationOf q 4 = true ∨ valuationOf q 7 = true ∨ valuationOf q 798 = true := by
  have hs : count797 q = (countLit q [-4]) + (countLit q [-7]) := List.countP_append (p := literal q) (l₁ := [-4]) (l₂ := [-7])
  have hm := merge_two (literal (valuationOf q) (-4)) (literal (valuationOf q) (-7)) (literal (valuationOf q) (798)) (countLit q [-4]) (countLit q [-7]) (count797 q) 1 1 (meaningNeg4 q) (meaningNeg7 q) (meaning798 q) hs
  change (! (valuationOf q 4)) = false ∨ (! (valuationOf q 7)) = false ∨ valuationOf q 798 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause731 (q : Snake 81) (h : Conditions q) : valuation q 4 = true ∨ valuation q 7 = true ∨ valuation q 798 = true := counterClause731 (baseVal q)

theorem counterClause732 (q : Nat → Bool) : valuationOf q 797 = false ∨ valuationOf q 799 = true := by
  have hs : count799 q = (countLit q [-1]) + (countLit q [-4, -7]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-4, -7])
  have hm := merge_right (literal (valuationOf q) (797)) (literal (valuationOf q) (799)) (countLit q [-1]) (countLit q [-4, -7]) (count799 q) 1 (meaning797 q) (meaning799 q) hs
  change valuationOf q 797 = false ∨ valuationOf q 799 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause732 (q : Snake 81) (h : Conditions q) : valuation q 797 = false ∨ valuation q 799 = true := counterClause732 (baseVal q)

theorem counterClause733 (q : Nat → Bool) : valuationOf q 798 = false ∨ valuationOf q 800 = true := by
  have hs : count799 q = (countLit q [-1]) + (countLit q [-4, -7]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-4, -7])
  have hm := merge_right (literal (valuationOf q) (798)) (literal (valuationOf q) (800)) (countLit q [-1]) (countLit q [-4, -7]) (count799 q) 2 (meaning798 q) (meaning800 q) hs
  change valuationOf q 798 = false ∨ valuationOf q 800 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause733 (q : Snake 81) (h : Conditions q) : valuation q 798 = false ∨ valuation q 800 = true := counterClause733 (baseVal q)

theorem counterClause734 (q : Nat → Bool) : valuationOf q 1 = true ∨ valuationOf q 799 = true := by
  have hs : count799 q = (countLit q [-1]) + (countLit q [-4, -7]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-4, -7])
  have hm := merge_left (literal (valuationOf q) (-1)) (literal (valuationOf q) (799)) (countLit q [-1]) (countLit q [-4, -7]) (count799 q) 1 (meaningNeg1 q) (meaning799 q) hs
  change (! (valuationOf q 1)) = false ∨ valuationOf q 799 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause734 (q : Snake 81) (h : Conditions q) : valuation q 1 = true ∨ valuation q 799 = true := counterClause734 (baseVal q)

theorem counterClause735 (q : Nat → Bool) : valuationOf q 1 = true ∨ valuationOf q 797 = false ∨ valuationOf q 800 = true := by
  have hs : count799 q = (countLit q [-1]) + (countLit q [-4, -7]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-4, -7])
  have hm := merge_two (literal (valuationOf q) (-1)) (literal (valuationOf q) (797)) (literal (valuationOf q) (800)) (countLit q [-1]) (countLit q [-4, -7]) (count799 q) 1 1 (meaningNeg1 q) (meaning797 q) (meaning800 q) hs
  change (! (valuationOf q 1)) = false ∨ valuationOf q 797 = false ∨ valuationOf q 800 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause735 (q : Snake 81) (h : Conditions q) : valuation q 1 = true ∨ valuation q 797 = false ∨ valuation q 800 = true := counterClause735 (baseVal q)

theorem counterClause736 (q : Nat → Bool) : valuationOf q 1 = true ∨ valuationOf q 798 = false ∨ valuationOf q 801 = true := by
  have hs : count799 q = (countLit q [-1]) + (countLit q [-4, -7]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-4, -7])
  have hm := merge_two (literal (valuationOf q) (-1)) (literal (valuationOf q) (798)) (literal (valuationOf q) (801)) (countLit q [-1]) (countLit q [-4, -7]) (count799 q) 1 2 (meaningNeg1 q) (meaning798 q) (meaning801 q) hs
  change (! (valuationOf q 1)) = false ∨ valuationOf q 798 = false ∨ valuationOf q 801 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause736 (q : Snake 81) (h : Conditions q) : valuation q 1 = true ∨ valuation q 798 = false ∨ valuation q 801 = true := counterClause736 (baseVal q)

theorem block22 (q : Snake 81) (h : Conditions q) : B112E115.Block22 (valuation q) :=
  ⟨clause705 q h, clause706 q h, clause707 q h, clause708 q h, clause709 q h, clause710 q h, clause711 q h, clause712 q h, clause713 q h, clause714 q h, clause715 q h, clause716 q h, clause717 q h, clause718 q h, clause719 q h, clause720 q h, clause721 q h, clause722 q h, clause723 q h, clause724 q h, clause725 q h, clause726 q h, clause727 q h, clause728 q h, clause729 q h, clause730 q h, clause731 q h, clause732 q h, clause733 q h, clause734 q h, clause735 q h, clause736 q h⟩

end
end Snake9.Regrowth.E112115
