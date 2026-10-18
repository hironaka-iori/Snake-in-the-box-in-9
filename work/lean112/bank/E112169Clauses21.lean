import E112169Semantics
import B112E169Inputs
namespace Snake9.Regrowth.E112169
noncomputable section
local instance blockDec21 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause673 (q : Nat → Bool) : valuationOf q 437 = false ∨ valuationOf q 453 = true := by
  have hs : count453 q = (countLit q [218, 219, 220, 221, 222, 223, 224]) + (countLit q [225, 226, 227, 228, 229, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [218, 219, 220, 221, 222, 223, 224]) (l₂ := [225, 226, 227, 228, 229, 230, 231, 232])
  have hm := merge_left (literal (valuationOf q) (437)) (literal (valuationOf q) (453)) (countLit q [218, 219, 220, 221, 222, 223, 224]) (countLit q [225, 226, 227, 228, 229, 230, 231, 232]) (count453 q) 1 (meaning437 q) (meaning453 q) hs
  change valuationOf q 437 = false ∨ valuationOf q 453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause673 (q : Snake 81) (h : Conditions q) : valuation q 437 = false ∨ valuation q 453 = true := counterClause673 (baseVal q)

theorem counterClause674 (q : Nat → Bool) : valuationOf q 437 = false ∨ valuationOf q 451 = false ∨ valuationOf q 454 = true := by
  have hs : count453 q = (countLit q [218, 219, 220, 221, 222, 223, 224]) + (countLit q [225, 226, 227, 228, 229, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [218, 219, 220, 221, 222, 223, 224]) (l₂ := [225, 226, 227, 228, 229, 230, 231, 232])
  have hm := merge_two (literal (valuationOf q) (437)) (literal (valuationOf q) (451)) (literal (valuationOf q) (454)) (countLit q [218, 219, 220, 221, 222, 223, 224]) (countLit q [225, 226, 227, 228, 229, 230, 231, 232]) (count453 q) 1 1 (meaning437 q) (meaning451 q) (meaning454 q) hs
  change valuationOf q 437 = false ∨ valuationOf q 451 = false ∨ valuationOf q 454 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause674 (q : Snake 81) (h : Conditions q) : valuation q 437 = false ∨ valuation q 451 = false ∨ valuation q 454 = true := counterClause674 (baseVal q)

theorem counterClause675 (q : Nat → Bool) : valuationOf q 438 = false ∨ valuationOf q 454 = true := by
  have hs : count453 q = (countLit q [218, 219, 220, 221, 222, 223, 224]) + (countLit q [225, 226, 227, 228, 229, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [218, 219, 220, 221, 222, 223, 224]) (l₂ := [225, 226, 227, 228, 229, 230, 231, 232])
  have hm := merge_left (literal (valuationOf q) (438)) (literal (valuationOf q) (454)) (countLit q [218, 219, 220, 221, 222, 223, 224]) (countLit q [225, 226, 227, 228, 229, 230, 231, 232]) (count453 q) 2 (meaning438 q) (meaning454 q) hs
  change valuationOf q 438 = false ∨ valuationOf q 454 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause675 (q : Snake 81) (h : Conditions q) : valuation q 438 = false ∨ valuation q 454 = true := counterClause675 (baseVal q)

theorem counterClause676 (q : Nat → Bool) : valuationOf q 453 = false ∨ valuationOf q 455 = true := by
  have hs : count455 q = (countLit q [204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) + (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) (l₂ := [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232])
  have hm := merge_right (literal (valuationOf q) (453)) (literal (valuationOf q) (455)) (countLit q [204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) (count455 q) 1 (meaning453 q) (meaning455 q) hs
  change valuationOf q 453 = false ∨ valuationOf q 455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause676 (q : Snake 81) (h : Conditions q) : valuation q 453 = false ∨ valuation q 455 = true := counterClause676 (baseVal q)

theorem counterClause677 (q : Nat → Bool) : valuationOf q 454 = false ∨ valuationOf q 456 = true := by
  have hs : count455 q = (countLit q [204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) + (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) (l₂ := [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232])
  have hm := merge_right (literal (valuationOf q) (454)) (literal (valuationOf q) (456)) (countLit q [204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) (count455 q) 2 (meaning454 q) (meaning456 q) hs
  change valuationOf q 454 = false ∨ valuationOf q 456 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause677 (q : Snake 81) (h : Conditions q) : valuation q 454 = false ∨ valuation q 456 = true := counterClause677 (baseVal q)

theorem counterClause678 (q : Nat → Bool) : valuationOf q 425 = false ∨ valuationOf q 455 = true := by
  have hs : count455 q = (countLit q [204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) + (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) (l₂ := [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232])
  have hm := merge_left (literal (valuationOf q) (425)) (literal (valuationOf q) (455)) (countLit q [204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) (count455 q) 1 (meaning425 q) (meaning455 q) hs
  change valuationOf q 425 = false ∨ valuationOf q 455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause678 (q : Snake 81) (h : Conditions q) : valuation q 425 = false ∨ valuation q 455 = true := counterClause678 (baseVal q)

theorem counterClause679 (q : Nat → Bool) : valuationOf q 425 = false ∨ valuationOf q 453 = false ∨ valuationOf q 456 = true := by
  have hs : count455 q = (countLit q [204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) + (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) (l₂ := [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232])
  have hm := merge_two (literal (valuationOf q) (425)) (literal (valuationOf q) (453)) (literal (valuationOf q) (456)) (countLit q [204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) (count455 q) 1 1 (meaning425 q) (meaning453 q) (meaning456 q) hs
  change valuationOf q 425 = false ∨ valuationOf q 453 = false ∨ valuationOf q 456 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause679 (q : Snake 81) (h : Conditions q) : valuation q 425 = false ∨ valuation q 453 = false ∨ valuation q 456 = true := counterClause679 (baseVal q)

theorem counterClause680 (q : Nat → Bool) : valuationOf q 426 = false ∨ valuationOf q 456 = true := by
  have hs : count455 q = (countLit q [204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) + (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) (l₂ := [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232])
  have hm := merge_left (literal (valuationOf q) (426)) (literal (valuationOf q) (456)) (countLit q [204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) (count455 q) 2 (meaning426 q) (meaning456 q) hs
  change valuationOf q 426 = false ∨ valuationOf q 456 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause680 (q : Snake 81) (h : Conditions q) : valuation q 426 = false ∨ valuation q 456 = true := counterClause680 (baseVal q)

theorem counterClause681 (q : Nat → Bool) : valuationOf q 455 = false ∨ valuationOf q 457 = true := by
  have hs : count457 q = (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203]) + (countLit q [204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203]) (l₂ := [204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232])
  have hm := merge_right (literal (valuationOf q) (455)) (literal (valuationOf q) (457)) (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203]) (countLit q [204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) (count457 q) 1 (meaning455 q) (meaning457 q) hs
  change valuationOf q 455 = false ∨ valuationOf q 457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause681 (q : Snake 81) (h : Conditions q) : valuation q 455 = false ∨ valuation q 457 = true := counterClause681 (baseVal q)

theorem counterClause682 (q : Nat → Bool) : valuationOf q 456 = false ∨ valuationOf q 458 = true := by
  have hs : count457 q = (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203]) + (countLit q [204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203]) (l₂ := [204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232])
  have hm := merge_right (literal (valuationOf q) (456)) (literal (valuationOf q) (458)) (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203]) (countLit q [204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) (count457 q) 2 (meaning456 q) (meaning458 q) hs
  change valuationOf q 456 = false ∨ valuationOf q 458 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause682 (q : Snake 81) (h : Conditions q) : valuation q 456 = false ∨ valuation q 458 = true := counterClause682 (baseVal q)

theorem counterClause683 (q : Nat → Bool) : valuationOf q 399 = false ∨ valuationOf q 457 = true := by
  have hs : count457 q = (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203]) + (countLit q [204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203]) (l₂ := [204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232])
  have hm := merge_left (literal (valuationOf q) (399)) (literal (valuationOf q) (457)) (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203]) (countLit q [204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) (count457 q) 1 (meaning399 q) (meaning457 q) hs
  change valuationOf q 399 = false ∨ valuationOf q 457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause683 (q : Snake 81) (h : Conditions q) : valuation q 399 = false ∨ valuation q 457 = true := counterClause683 (baseVal q)

theorem counterClause684 (q : Nat → Bool) : valuationOf q 399 = false ∨ valuationOf q 455 = false ∨ valuationOf q 458 = true := by
  have hs : count457 q = (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203]) + (countLit q [204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203]) (l₂ := [204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232])
  have hm := merge_two (literal (valuationOf q) (399)) (literal (valuationOf q) (455)) (literal (valuationOf q) (458)) (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203]) (countLit q [204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) (count457 q) 1 1 (meaning399 q) (meaning455 q) (meaning458 q) hs
  change valuationOf q 399 = false ∨ valuationOf q 455 = false ∨ valuationOf q 458 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause684 (q : Snake 81) (h : Conditions q) : valuation q 399 = false ∨ valuation q 455 = false ∨ valuation q 458 = true := counterClause684 (baseVal q)

theorem counterClause685 (q : Nat → Bool) : valuationOf q 400 = false ∨ valuationOf q 458 = true := by
  have hs : count457 q = (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203]) + (countLit q [204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203]) (l₂ := [204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232])
  have hm := merge_left (literal (valuationOf q) (400)) (literal (valuationOf q) (458)) (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203]) (countLit q [204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) (count457 q) 2 (meaning400 q) (meaning458 q) hs
  change valuationOf q 400 = false ∨ valuationOf q 458 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause685 (q : Snake 81) (h : Conditions q) : valuation q 400 = false ∨ valuation q 458 = true := counterClause685 (baseVal q)

theorem counterClause686 (q : Nat → Bool) : valuationOf q 458 = false ∨ valuationOf q 460 = true := by
  have hs : count459 q = (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) + (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119, 120, 121, 122, 123, 124, 125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) (l₂ := [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232])
  have hm := merge_right (literal (valuationOf q) (458)) (literal (valuationOf q) (460)) (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) (count459 q) 2 (meaning458 q) (meaning460 q) hs
  change valuationOf q 458 = false ∨ valuationOf q 460 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause686 (q : Snake 81) (h : Conditions q) : valuation q 458 = false ∨ valuation q 460 = true := counterClause686 (baseVal q)

theorem counterClause687 (q : Nat → Bool) : valuationOf q 343 = false ∨ valuationOf q 457 = false ∨ valuationOf q 460 = true := by
  have hs : count459 q = (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) + (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119, 120, 121, 122, 123, 124, 125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) (l₂ := [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232])
  have hm := merge_two (literal (valuationOf q) (343)) (literal (valuationOf q) (457)) (literal (valuationOf q) (460)) (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) (count459 q) 1 1 (meaning343 q) (meaning457 q) (meaning460 q) hs
  change valuationOf q 343 = false ∨ valuationOf q 457 = false ∨ valuationOf q 460 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause687 (q : Snake 81) (h : Conditions q) : valuation q 343 = false ∨ valuation q 457 = false ∨ valuation q 460 = true := counterClause687 (baseVal q)

theorem counterClause688 (q : Nat → Bool) : valuationOf q 344 = false ∨ valuationOf q 460 = true := by
  have hs : count459 q = (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) + (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119, 120, 121, 122, 123, 124, 125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) (l₂ := [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232])
  have hm := merge_left (literal (valuationOf q) (344)) (literal (valuationOf q) (460)) (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) (count459 q) 2 (meaning344 q) (meaning460 q) hs
  change valuationOf q 344 = false ∨ valuationOf q 460 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause688 (q : Snake 81) (h : Conditions q) : valuation q 344 = false ∨ valuation q 460 = true := counterClause688 (baseVal q)

theorem clause689 (q : Snake 81) (h : Conditions q) : valuation q 460 = false := by
  rw [value460]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count459 (baseVal q) = (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := other_count_bound q h
  rw [he]
  omega

theorem counterClause690 (q : Nat → Bool) : valuationOf q 5 = true ∨ valuationOf q 1401 = true := by
  have hs : count1401 q = (countLit q [-4]) + (countLit q [-5]) := List.countP_append (p := literal q) (l₁ := [-4]) (l₂ := [-5])
  have hm := merge_right (literal (valuationOf q) (-5)) (literal (valuationOf q) (1401)) (countLit q [-4]) (countLit q [-5]) (count1401 q) 1 (meaningNeg5 q) (meaning1401 q) hs
  change (! (valuationOf q 5)) = false ∨ valuationOf q 1401 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause690 (q : Snake 81) (h : Conditions q) : valuation q 5 = true ∨ valuation q 1401 = true := counterClause690 (baseVal q)

theorem counterClause691 (q : Nat → Bool) : valuationOf q 4 = true ∨ valuationOf q 1401 = true := by
  have hs : count1401 q = (countLit q [-4]) + (countLit q [-5]) := List.countP_append (p := literal q) (l₁ := [-4]) (l₂ := [-5])
  have hm := merge_left (literal (valuationOf q) (-4)) (literal (valuationOf q) (1401)) (countLit q [-4]) (countLit q [-5]) (count1401 q) 1 (meaningNeg4 q) (meaning1401 q) hs
  change (! (valuationOf q 4)) = false ∨ valuationOf q 1401 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause691 (q : Snake 81) (h : Conditions q) : valuation q 4 = true ∨ valuation q 1401 = true := counterClause691 (baseVal q)

theorem counterClause692 (q : Nat → Bool) : valuationOf q 4 = true ∨ valuationOf q 5 = true ∨ valuationOf q 1402 = true := by
  have hs : count1401 q = (countLit q [-4]) + (countLit q [-5]) := List.countP_append (p := literal q) (l₁ := [-4]) (l₂ := [-5])
  have hm := merge_two (literal (valuationOf q) (-4)) (literal (valuationOf q) (-5)) (literal (valuationOf q) (1402)) (countLit q [-4]) (countLit q [-5]) (count1401 q) 1 1 (meaningNeg4 q) (meaningNeg5 q) (meaning1402 q) hs
  change (! (valuationOf q 4)) = false ∨ (! (valuationOf q 5)) = false ∨ valuationOf q 1402 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause692 (q : Snake 81) (h : Conditions q) : valuation q 4 = true ∨ valuation q 5 = true ∨ valuation q 1402 = true := counterClause692 (baseVal q)

theorem counterClause693 (q : Nat → Bool) : valuationOf q 1401 = false ∨ valuationOf q 1403 = true := by
  have hs : count1403 q = (countLit q [-2]) + (countLit q [-4, -5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-4, -5])
  have hm := merge_right (literal (valuationOf q) (1401)) (literal (valuationOf q) (1403)) (countLit q [-2]) (countLit q [-4, -5]) (count1403 q) 1 (meaning1401 q) (meaning1403 q) hs
  change valuationOf q 1401 = false ∨ valuationOf q 1403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause693 (q : Snake 81) (h : Conditions q) : valuation q 1401 = false ∨ valuation q 1403 = true := counterClause693 (baseVal q)

theorem counterClause694 (q : Nat → Bool) : valuationOf q 1402 = false ∨ valuationOf q 1404 = true := by
  have hs : count1403 q = (countLit q [-2]) + (countLit q [-4, -5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-4, -5])
  have hm := merge_right (literal (valuationOf q) (1402)) (literal (valuationOf q) (1404)) (countLit q [-2]) (countLit q [-4, -5]) (count1403 q) 2 (meaning1402 q) (meaning1404 q) hs
  change valuationOf q 1402 = false ∨ valuationOf q 1404 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause694 (q : Snake 81) (h : Conditions q) : valuation q 1402 = false ∨ valuation q 1404 = true := counterClause694 (baseVal q)

theorem counterClause695 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1403 = true := by
  have hs : count1403 q = (countLit q [-2]) + (countLit q [-4, -5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-4, -5])
  have hm := merge_left (literal (valuationOf q) (-2)) (literal (valuationOf q) (1403)) (countLit q [-2]) (countLit q [-4, -5]) (count1403 q) 1 (meaningNeg2 q) (meaning1403 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1403 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause695 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1403 = true := counterClause695 (baseVal q)

theorem counterClause696 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1401 = false ∨ valuationOf q 1404 = true := by
  have hs : count1403 q = (countLit q [-2]) + (countLit q [-4, -5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-4, -5])
  have hm := merge_two (literal (valuationOf q) (-2)) (literal (valuationOf q) (1401)) (literal (valuationOf q) (1404)) (countLit q [-2]) (countLit q [-4, -5]) (count1403 q) 1 1 (meaningNeg2 q) (meaning1401 q) (meaning1404 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1401 = false ∨ valuationOf q 1404 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause696 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1401 = false ∨ valuation q 1404 = true := counterClause696 (baseVal q)

theorem counterClause697 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1402 = false ∨ valuationOf q 1405 = true := by
  have hs : count1403 q = (countLit q [-2]) + (countLit q [-4, -5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-4, -5])
  have hm := merge_two (literal (valuationOf q) (-2)) (literal (valuationOf q) (1402)) (literal (valuationOf q) (1405)) (countLit q [-2]) (countLit q [-4, -5]) (count1403 q) 1 2 (meaningNeg2 q) (meaning1402 q) (meaning1405 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1402 = false ∨ valuationOf q 1405 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause697 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1402 = false ∨ valuation q 1405 = true := counterClause697 (baseVal q)

theorem counterClause698 (q : Nat → Bool) : valuationOf q 9 = true ∨ valuationOf q 1406 = true := by
  have hs : count1406 q = (countLit q [-8]) + (countLit q [-9]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-9])
  have hm := merge_right (literal (valuationOf q) (-9)) (literal (valuationOf q) (1406)) (countLit q [-8]) (countLit q [-9]) (count1406 q) 1 (meaningNeg9 q) (meaning1406 q) hs
  change (! (valuationOf q 9)) = false ∨ valuationOf q 1406 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause698 (q : Snake 81) (h : Conditions q) : valuation q 9 = true ∨ valuation q 1406 = true := counterClause698 (baseVal q)

theorem counterClause699 (q : Nat → Bool) : valuationOf q 8 = true ∨ valuationOf q 1406 = true := by
  have hs : count1406 q = (countLit q [-8]) + (countLit q [-9]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-9])
  have hm := merge_left (literal (valuationOf q) (-8)) (literal (valuationOf q) (1406)) (countLit q [-8]) (countLit q [-9]) (count1406 q) 1 (meaningNeg8 q) (meaning1406 q) hs
  change (! (valuationOf q 8)) = false ∨ valuationOf q 1406 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause699 (q : Snake 81) (h : Conditions q) : valuation q 8 = true ∨ valuation q 1406 = true := counterClause699 (baseVal q)

theorem counterClause700 (q : Nat → Bool) : valuationOf q 8 = true ∨ valuationOf q 9 = true ∨ valuationOf q 1407 = true := by
  have hs : count1406 q = (countLit q [-8]) + (countLit q [-9]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-9])
  have hm := merge_two (literal (valuationOf q) (-8)) (literal (valuationOf q) (-9)) (literal (valuationOf q) (1407)) (countLit q [-8]) (countLit q [-9]) (count1406 q) 1 1 (meaningNeg8 q) (meaningNeg9 q) (meaning1407 q) hs
  change (! (valuationOf q 8)) = false ∨ (! (valuationOf q 9)) = false ∨ valuationOf q 1407 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause700 (q : Snake 81) (h : Conditions q) : valuation q 8 = true ∨ valuation q 9 = true ∨ valuation q 1407 = true := counterClause700 (baseVal q)

theorem counterClause701 (q : Nat → Bool) : valuationOf q 13 = true ∨ valuationOf q 1408 = true := by
  have hs : count1408 q = (countLit q [-12]) + (countLit q [-13]) := List.countP_append (p := literal q) (l₁ := [-12]) (l₂ := [-13])
  have hm := merge_right (literal (valuationOf q) (-13)) (literal (valuationOf q) (1408)) (countLit q [-12]) (countLit q [-13]) (count1408 q) 1 (meaningNeg13 q) (meaning1408 q) hs
  change (! (valuationOf q 13)) = false ∨ valuationOf q 1408 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause701 (q : Snake 81) (h : Conditions q) : valuation q 13 = true ∨ valuation q 1408 = true := counterClause701 (baseVal q)

theorem counterClause702 (q : Nat → Bool) : valuationOf q 12 = true ∨ valuationOf q 1408 = true := by
  have hs : count1408 q = (countLit q [-12]) + (countLit q [-13]) := List.countP_append (p := literal q) (l₁ := [-12]) (l₂ := [-13])
  have hm := merge_left (literal (valuationOf q) (-12)) (literal (valuationOf q) (1408)) (countLit q [-12]) (countLit q [-13]) (count1408 q) 1 (meaningNeg12 q) (meaning1408 q) hs
  change (! (valuationOf q 12)) = false ∨ valuationOf q 1408 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause702 (q : Snake 81) (h : Conditions q) : valuation q 12 = true ∨ valuation q 1408 = true := counterClause702 (baseVal q)

theorem counterClause703 (q : Nat → Bool) : valuationOf q 12 = true ∨ valuationOf q 13 = true ∨ valuationOf q 1409 = true := by
  have hs : count1408 q = (countLit q [-12]) + (countLit q [-13]) := List.countP_append (p := literal q) (l₁ := [-12]) (l₂ := [-13])
  have hm := merge_two (literal (valuationOf q) (-12)) (literal (valuationOf q) (-13)) (literal (valuationOf q) (1409)) (countLit q [-12]) (countLit q [-13]) (count1408 q) 1 1 (meaningNeg12 q) (meaningNeg13 q) (meaning1409 q) hs
  change (! (valuationOf q 12)) = false ∨ (! (valuationOf q 13)) = false ∨ valuationOf q 1409 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause703 (q : Snake 81) (h : Conditions q) : valuation q 12 = true ∨ valuation q 13 = true ∨ valuation q 1409 = true := counterClause703 (baseVal q)

theorem counterClause704 (q : Nat → Bool) : valuationOf q 1408 = false ∨ valuationOf q 1410 = true := by
  have hs : count1410 q = (countLit q [-8, -9]) + (countLit q [-12, -13]) := List.countP_append (p := literal q) (l₁ := [-8, -9]) (l₂ := [-12, -13])
  have hm := merge_right (literal (valuationOf q) (1408)) (literal (valuationOf q) (1410)) (countLit q [-8, -9]) (countLit q [-12, -13]) (count1410 q) 1 (meaning1408 q) (meaning1410 q) hs
  change valuationOf q 1408 = false ∨ valuationOf q 1410 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause704 (q : Snake 81) (h : Conditions q) : valuation q 1408 = false ∨ valuation q 1410 = true := counterClause704 (baseVal q)

theorem block21 (q : Snake 81) (h : Conditions q) : B112E169.Block21 (valuation q) :=
  ⟨clause673 q h, clause674 q h, clause675 q h, clause676 q h, clause677 q h, clause678 q h, clause679 q h, clause680 q h, clause681 q h, clause682 q h, clause683 q h, clause684 q h, clause685 q h, clause686 q h, clause687 q h, clause688 q h, clause689 q h, clause690 q h, clause691 q h, clause692 q h, clause693 q h, clause694 q h, clause695 q h, clause696 q h, clause697 q h, clause698 q h, clause699 q h, clause700 q h, clause701 q h, clause702 q h, clause703 q h, clause704 q h⟩

end
end Snake9.Regrowth.E112169
