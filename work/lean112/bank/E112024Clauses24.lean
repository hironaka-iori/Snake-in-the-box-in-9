import E112024Semantics
import B112E024Inputs
namespace Snake9.Regrowth.E112024
noncomputable section
local instance blockDec24 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause769 (q : Nat → Bool) : valuationOf q 471 = false ∨ valuationOf q 473 = true := by
  have hs : count473 q = (countLit q [228, 229, 230, 231, 232, 233, 234]) + (countLit q [235, 236, 237, 238, 239, 240, 241, 242]) := List.countP_append (p := literal q) (l₁ := [228, 229, 230, 231, 232, 233, 234]) (l₂ := [235, 236, 237, 238, 239, 240, 241, 242])
  have hm := merge_right (literal (valuationOf q) (471)) (literal (valuationOf q) (473)) (countLit q [228, 229, 230, 231, 232, 233, 234]) (countLit q [235, 236, 237, 238, 239, 240, 241, 242]) (count473 q) 1 (meaning471 q) (meaning473 q) hs
  change valuationOf q 471 = false ∨ valuationOf q 473 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause769 (q : Snake 81) (h : Conditions q) : valuation q 471 = false ∨ valuation q 473 = true := counterClause769 (baseVal q)

theorem counterClause770 (q : Nat → Bool) : valuationOf q 457 = false ∨ valuationOf q 473 = true := by
  have hs : count473 q = (countLit q [228, 229, 230, 231, 232, 233, 234]) + (countLit q [235, 236, 237, 238, 239, 240, 241, 242]) := List.countP_append (p := literal q) (l₁ := [228, 229, 230, 231, 232, 233, 234]) (l₂ := [235, 236, 237, 238, 239, 240, 241, 242])
  have hm := merge_left (literal (valuationOf q) (457)) (literal (valuationOf q) (473)) (countLit q [228, 229, 230, 231, 232, 233, 234]) (countLit q [235, 236, 237, 238, 239, 240, 241, 242]) (count473 q) 1 (meaning457 q) (meaning473 q) hs
  change valuationOf q 457 = false ∨ valuationOf q 473 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause770 (q : Snake 81) (h : Conditions q) : valuation q 457 = false ∨ valuation q 473 = true := counterClause770 (baseVal q)

theorem counterClause771 (q : Nat → Bool) : valuationOf q 473 = false ∨ valuationOf q 475 = true := by
  have hs : count475 q = (countLit q [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227]) + (countLit q [228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) := List.countP_append (p := literal q) (l₁ := [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227]) (l₂ := [228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242])
  have hm := merge_right (literal (valuationOf q) (473)) (literal (valuationOf q) (475)) (countLit q [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227]) (countLit q [228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) (count475 q) 1 (meaning473 q) (meaning475 q) hs
  change valuationOf q 473 = false ∨ valuationOf q 475 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause771 (q : Snake 81) (h : Conditions q) : valuation q 473 = false ∨ valuation q 475 = true := counterClause771 (baseVal q)

theorem counterClause772 (q : Nat → Bool) : valuationOf q 445 = false ∨ valuationOf q 475 = true := by
  have hs : count475 q = (countLit q [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227]) + (countLit q [228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) := List.countP_append (p := literal q) (l₁ := [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227]) (l₂ := [228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242])
  have hm := merge_left (literal (valuationOf q) (445)) (literal (valuationOf q) (475)) (countLit q [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227]) (countLit q [228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) (count475 q) 1 (meaning445 q) (meaning475 q) hs
  change valuationOf q 445 = false ∨ valuationOf q 475 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause772 (q : Snake 81) (h : Conditions q) : valuation q 445 = false ∨ valuation q 475 = true := counterClause772 (baseVal q)

theorem counterClause773 (q : Nat → Bool) : valuationOf q 445 = false ∨ valuationOf q 473 = false ∨ valuationOf q 476 = true := by
  have hs : count475 q = (countLit q [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227]) + (countLit q [228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) := List.countP_append (p := literal q) (l₁ := [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227]) (l₂ := [228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242])
  have hm := merge_two (literal (valuationOf q) (445)) (literal (valuationOf q) (473)) (literal (valuationOf q) (476)) (countLit q [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227]) (countLit q [228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) (count475 q) 1 1 (meaning445 q) (meaning473 q) (meaning476 q) hs
  change valuationOf q 445 = false ∨ valuationOf q 473 = false ∨ valuationOf q 476 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause773 (q : Snake 81) (h : Conditions q) : valuation q 445 = false ∨ valuation q 473 = false ∨ valuation q 476 = true := counterClause773 (baseVal q)

theorem counterClause774 (q : Nat → Bool) : valuationOf q 446 = false ∨ valuationOf q 476 = true := by
  have hs : count475 q = (countLit q [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227]) + (countLit q [228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) := List.countP_append (p := literal q) (l₁ := [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227]) (l₂ := [228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242])
  have hm := merge_left (literal (valuationOf q) (446)) (literal (valuationOf q) (476)) (countLit q [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227]) (countLit q [228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) (count475 q) 2 (meaning446 q) (meaning476 q) hs
  change valuationOf q 446 = false ∨ valuationOf q 476 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause774 (q : Snake 81) (h : Conditions q) : valuation q 446 = false ∨ valuation q 476 = true := counterClause774 (baseVal q)

theorem counterClause775 (q : Nat → Bool) : valuationOf q 475 = false ∨ valuationOf q 477 = true := by
  have hs : count477 q = (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) + (countLit q [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) := List.countP_append (p := literal q) (l₁ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (l₂ := [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242])
  have hm := merge_right (literal (valuationOf q) (475)) (literal (valuationOf q) (477)) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (countLit q [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) (count477 q) 1 (meaning475 q) (meaning477 q) hs
  change valuationOf q 475 = false ∨ valuationOf q 477 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause775 (q : Snake 81) (h : Conditions q) : valuation q 475 = false ∨ valuation q 477 = true := counterClause775 (baseVal q)

theorem counterClause776 (q : Nat → Bool) : valuationOf q 476 = false ∨ valuationOf q 478 = true := by
  have hs : count477 q = (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) + (countLit q [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) := List.countP_append (p := literal q) (l₁ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (l₂ := [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242])
  have hm := merge_right (literal (valuationOf q) (476)) (literal (valuationOf q) (478)) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (countLit q [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) (count477 q) 2 (meaning476 q) (meaning478 q) hs
  change valuationOf q 476 = false ∨ valuationOf q 478 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause776 (q : Snake 81) (h : Conditions q) : valuation q 476 = false ∨ valuation q 478 = true := counterClause776 (baseVal q)

theorem counterClause777 (q : Nat → Bool) : valuationOf q 417 = false ∨ valuationOf q 477 = true := by
  have hs : count477 q = (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) + (countLit q [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) := List.countP_append (p := literal q) (l₁ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (l₂ := [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242])
  have hm := merge_left (literal (valuationOf q) (417)) (literal (valuationOf q) (477)) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (countLit q [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) (count477 q) 1 (meaning417 q) (meaning477 q) hs
  change valuationOf q 417 = false ∨ valuationOf q 477 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause777 (q : Snake 81) (h : Conditions q) : valuation q 417 = false ∨ valuation q 477 = true := counterClause777 (baseVal q)

theorem counterClause778 (q : Nat → Bool) : valuationOf q 417 = false ∨ valuationOf q 475 = false ∨ valuationOf q 478 = true := by
  have hs : count477 q = (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) + (countLit q [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) := List.countP_append (p := literal q) (l₁ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (l₂ := [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242])
  have hm := merge_two (literal (valuationOf q) (417)) (literal (valuationOf q) (475)) (literal (valuationOf q) (478)) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (countLit q [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) (count477 q) 1 1 (meaning417 q) (meaning475 q) (meaning478 q) hs
  change valuationOf q 417 = false ∨ valuationOf q 475 = false ∨ valuationOf q 478 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause778 (q : Snake 81) (h : Conditions q) : valuation q 417 = false ∨ valuation q 475 = false ∨ valuation q 478 = true := counterClause778 (baseVal q)

theorem counterClause779 (q : Nat → Bool) : valuationOf q 418 = false ∨ valuationOf q 478 = true := by
  have hs : count477 q = (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) + (countLit q [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) := List.countP_append (p := literal q) (l₁ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (l₂ := [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242])
  have hm := merge_left (literal (valuationOf q) (418)) (literal (valuationOf q) (478)) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (countLit q [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) (count477 q) 2 (meaning418 q) (meaning478 q) hs
  change valuationOf q 418 = false ∨ valuationOf q 478 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause779 (q : Snake 81) (h : Conditions q) : valuation q 418 = false ∨ valuation q 478 = true := counterClause779 (baseVal q)

theorem counterClause780 (q : Nat → Bool) : valuationOf q 478 = false ∨ valuationOf q 480 = true := by
  have hs : count479 q = (countLit q [122, 123, 124, 125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) + (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) := List.countP_append (p := literal q) (l₁ := [122, 123, 124, 125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) (l₂ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242])
  have hm := merge_right (literal (valuationOf q) (478)) (literal (valuationOf q) (480)) (countLit q [122, 123, 124, 125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) (count479 q) 2 (meaning478 q) (meaning480 q) hs
  change valuationOf q 478 = false ∨ valuationOf q 480 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause780 (q : Snake 81) (h : Conditions q) : valuation q 478 = false ∨ valuation q 480 = true := counterClause780 (baseVal q)

theorem counterClause781 (q : Nat → Bool) : valuationOf q 359 = false ∨ valuationOf q 477 = false ∨ valuationOf q 480 = true := by
  have hs : count479 q = (countLit q [122, 123, 124, 125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) + (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) := List.countP_append (p := literal q) (l₁ := [122, 123, 124, 125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) (l₂ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242])
  have hm := merge_two (literal (valuationOf q) (359)) (literal (valuationOf q) (477)) (literal (valuationOf q) (480)) (countLit q [122, 123, 124, 125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) (count479 q) 1 1 (meaning359 q) (meaning477 q) (meaning480 q) hs
  change valuationOf q 359 = false ∨ valuationOf q 477 = false ∨ valuationOf q 480 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause781 (q : Snake 81) (h : Conditions q) : valuation q 359 = false ∨ valuation q 477 = false ∨ valuation q 480 = true := counterClause781 (baseVal q)

theorem counterClause782 (q : Nat → Bool) : valuationOf q 360 = false ∨ valuationOf q 480 = true := by
  have hs : count479 q = (countLit q [122, 123, 124, 125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) + (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) := List.countP_append (p := literal q) (l₁ := [122, 123, 124, 125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) (l₂ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242])
  have hm := merge_left (literal (valuationOf q) (360)) (literal (valuationOf q) (480)) (countLit q [122, 123, 124, 125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) (count479 q) 2 (meaning360 q) (meaning480 q) hs
  change valuationOf q 360 = false ∨ valuationOf q 480 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause782 (q : Snake 81) (h : Conditions q) : valuation q 360 = false ∨ valuation q 480 = true := counterClause782 (baseVal q)

theorem clause783 (q : Snake 81) (h : Conditions q) : valuation q 480 = false := by
  rw [value480]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count479 (baseVal q) = (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := other_count_bound q h
  rw [he]
  omega

theorem counterClause784 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 1443 = true := by
  have hs : count1443 q = (countLit q [-3]) + (countLit q [-5]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-5])
  have hm := merge_left (literal (valuationOf q) (-3)) (literal (valuationOf q) (1443)) (countLit q [-3]) (countLit q [-5]) (count1443 q) 1 (meaningNeg3 q) (meaning1443 q) hs
  change (! (valuationOf q 3)) = false ∨ valuationOf q 1443 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause784 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 1443 = true := counterClause784 (baseVal q)

theorem counterClause785 (q : Nat → Bool) : valuationOf q 1443 = false ∨ valuationOf q 1445 = true := by
  have hs : count1445 q = (countLit q [-1]) + (countLit q [-3, -5]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-3, -5])
  have hm := merge_right (literal (valuationOf q) (1443)) (literal (valuationOf q) (1445)) (countLit q [-1]) (countLit q [-3, -5]) (count1445 q) 1 (meaning1443 q) (meaning1445 q) hs
  change valuationOf q 1443 = false ∨ valuationOf q 1445 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause785 (q : Snake 81) (h : Conditions q) : valuation q 1443 = false ∨ valuation q 1445 = true := counterClause785 (baseVal q)

theorem counterClause786 (q : Nat → Bool) : valuationOf q 1 = true ∨ valuationOf q 1445 = true := by
  have hs : count1445 q = (countLit q [-1]) + (countLit q [-3, -5]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-3, -5])
  have hm := merge_left (literal (valuationOf q) (-1)) (literal (valuationOf q) (1445)) (countLit q [-1]) (countLit q [-3, -5]) (count1445 q) 1 (meaningNeg1 q) (meaning1445 q) hs
  change (! (valuationOf q 1)) = false ∨ valuationOf q 1445 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause786 (q : Snake 81) (h : Conditions q) : valuation q 1 = true ∨ valuation q 1445 = true := counterClause786 (baseVal q)

theorem counterClause787 (q : Nat → Bool) : valuationOf q 1 = true ∨ valuationOf q 1443 = false ∨ valuationOf q 1446 = true := by
  have hs : count1445 q = (countLit q [-1]) + (countLit q [-3, -5]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-3, -5])
  have hm := merge_two (literal (valuationOf q) (-1)) (literal (valuationOf q) (1443)) (literal (valuationOf q) (1446)) (countLit q [-1]) (countLit q [-3, -5]) (count1445 q) 1 1 (meaningNeg1 q) (meaning1443 q) (meaning1446 q) hs
  change (! (valuationOf q 1)) = false ∨ valuationOf q 1443 = false ∨ valuationOf q 1446 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause787 (q : Snake 81) (h : Conditions q) : valuation q 1 = true ∨ valuation q 1443 = false ∨ valuation q 1446 = true := counterClause787 (baseVal q)

theorem counterClause788 (q : Nat → Bool) : valuationOf q 8 = true ∨ valuationOf q 1448 = true := by
  have hs : count1448 q = (countLit q [-6]) + (countLit q [-8]) := List.countP_append (p := literal q) (l₁ := [-6]) (l₂ := [-8])
  have hm := merge_right (literal (valuationOf q) (-8)) (literal (valuationOf q) (1448)) (countLit q [-6]) (countLit q [-8]) (count1448 q) 1 (meaningNeg8 q) (meaning1448 q) hs
  change (! (valuationOf q 8)) = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause788 (q : Snake 81) (h : Conditions q) : valuation q 8 = true ∨ valuation q 1448 = true := counterClause788 (baseVal q)

theorem counterClause789 (q : Nat → Bool) : valuationOf q 6 = true ∨ valuationOf q 1448 = true := by
  have hs : count1448 q = (countLit q [-6]) + (countLit q [-8]) := List.countP_append (p := literal q) (l₁ := [-6]) (l₂ := [-8])
  have hm := merge_left (literal (valuationOf q) (-6)) (literal (valuationOf q) (1448)) (countLit q [-6]) (countLit q [-8]) (count1448 q) 1 (meaningNeg6 q) (meaning1448 q) hs
  change (! (valuationOf q 6)) = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause789 (q : Snake 81) (h : Conditions q) : valuation q 6 = true ∨ valuation q 1448 = true := counterClause789 (baseVal q)

theorem counterClause790 (q : Nat → Bool) : valuationOf q 6 = true ∨ valuationOf q 8 = true ∨ valuationOf q 1449 = true := by
  have hs : count1448 q = (countLit q [-6]) + (countLit q [-8]) := List.countP_append (p := literal q) (l₁ := [-6]) (l₂ := [-8])
  have hm := merge_two (literal (valuationOf q) (-6)) (literal (valuationOf q) (-8)) (literal (valuationOf q) (1449)) (countLit q [-6]) (countLit q [-8]) (count1448 q) 1 1 (meaningNeg6 q) (meaningNeg8 q) (meaning1449 q) hs
  change (! (valuationOf q 6)) = false ∨ (! (valuationOf q 8)) = false ∨ valuationOf q 1449 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause790 (q : Snake 81) (h : Conditions q) : valuation q 6 = true ∨ valuation q 8 = true ∨ valuation q 1449 = true := counterClause790 (baseVal q)

theorem counterClause791 (q : Nat → Bool) : valuationOf q 11 = true ∨ valuationOf q 1450 = true := by
  have hs : count1450 q = (countLit q [-10]) + (countLit q [-11]) := List.countP_append (p := literal q) (l₁ := [-10]) (l₂ := [-11])
  have hm := merge_right (literal (valuationOf q) (-11)) (literal (valuationOf q) (1450)) (countLit q [-10]) (countLit q [-11]) (count1450 q) 1 (meaningNeg11 q) (meaning1450 q) hs
  change (! (valuationOf q 11)) = false ∨ valuationOf q 1450 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause791 (q : Snake 81) (h : Conditions q) : valuation q 11 = true ∨ valuation q 1450 = true := counterClause791 (baseVal q)

theorem counterClause792 (q : Nat → Bool) : valuationOf q 10 = true ∨ valuationOf q 1450 = true := by
  have hs : count1450 q = (countLit q [-10]) + (countLit q [-11]) := List.countP_append (p := literal q) (l₁ := [-10]) (l₂ := [-11])
  have hm := merge_left (literal (valuationOf q) (-10)) (literal (valuationOf q) (1450)) (countLit q [-10]) (countLit q [-11]) (count1450 q) 1 (meaningNeg10 q) (meaning1450 q) hs
  change (! (valuationOf q 10)) = false ∨ valuationOf q 1450 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause792 (q : Snake 81) (h : Conditions q) : valuation q 10 = true ∨ valuation q 1450 = true := counterClause792 (baseVal q)

theorem counterClause793 (q : Nat → Bool) : valuationOf q 10 = true ∨ valuationOf q 11 = true ∨ valuationOf q 1451 = true := by
  have hs : count1450 q = (countLit q [-10]) + (countLit q [-11]) := List.countP_append (p := literal q) (l₁ := [-10]) (l₂ := [-11])
  have hm := merge_two (literal (valuationOf q) (-10)) (literal (valuationOf q) (-11)) (literal (valuationOf q) (1451)) (countLit q [-10]) (countLit q [-11]) (count1450 q) 1 1 (meaningNeg10 q) (meaningNeg11 q) (meaning1451 q) hs
  change (! (valuationOf q 10)) = false ∨ (! (valuationOf q 11)) = false ∨ valuationOf q 1451 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause793 (q : Snake 81) (h : Conditions q) : valuation q 10 = true ∨ valuation q 11 = true ∨ valuation q 1451 = true := counterClause793 (baseVal q)

theorem counterClause794 (q : Nat → Bool) : valuationOf q 1450 = false ∨ valuationOf q 1452 = true := by
  have hs : count1452 q = (countLit q [-6, -8]) + (countLit q [-10, -11]) := List.countP_append (p := literal q) (l₁ := [-6, -8]) (l₂ := [-10, -11])
  have hm := merge_right (literal (valuationOf q) (1450)) (literal (valuationOf q) (1452)) (countLit q [-6, -8]) (countLit q [-10, -11]) (count1452 q) 1 (meaning1450 q) (meaning1452 q) hs
  change valuationOf q 1450 = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause794 (q : Snake 81) (h : Conditions q) : valuation q 1450 = false ∨ valuation q 1452 = true := counterClause794 (baseVal q)

theorem counterClause795 (q : Nat → Bool) : valuationOf q 1451 = false ∨ valuationOf q 1453 = true := by
  have hs : count1452 q = (countLit q [-6, -8]) + (countLit q [-10, -11]) := List.countP_append (p := literal q) (l₁ := [-6, -8]) (l₂ := [-10, -11])
  have hm := merge_right (literal (valuationOf q) (1451)) (literal (valuationOf q) (1453)) (countLit q [-6, -8]) (countLit q [-10, -11]) (count1452 q) 2 (meaning1451 q) (meaning1453 q) hs
  change valuationOf q 1451 = false ∨ valuationOf q 1453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause795 (q : Snake 81) (h : Conditions q) : valuation q 1451 = false ∨ valuation q 1453 = true := counterClause795 (baseVal q)

theorem counterClause796 (q : Nat → Bool) : valuationOf q 1448 = false ∨ valuationOf q 1452 = true := by
  have hs : count1452 q = (countLit q [-6, -8]) + (countLit q [-10, -11]) := List.countP_append (p := literal q) (l₁ := [-6, -8]) (l₂ := [-10, -11])
  have hm := merge_left (literal (valuationOf q) (1448)) (literal (valuationOf q) (1452)) (countLit q [-6, -8]) (countLit q [-10, -11]) (count1452 q) 1 (meaning1448 q) (meaning1452 q) hs
  change valuationOf q 1448 = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause796 (q : Snake 81) (h : Conditions q) : valuation q 1448 = false ∨ valuation q 1452 = true := counterClause796 (baseVal q)

theorem counterClause797 (q : Nat → Bool) : valuationOf q 1448 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1453 = true := by
  have hs : count1452 q = (countLit q [-6, -8]) + (countLit q [-10, -11]) := List.countP_append (p := literal q) (l₁ := [-6, -8]) (l₂ := [-10, -11])
  have hm := merge_two (literal (valuationOf q) (1448)) (literal (valuationOf q) (1450)) (literal (valuationOf q) (1453)) (countLit q [-6, -8]) (countLit q [-10, -11]) (count1452 q) 1 1 (meaning1448 q) (meaning1450 q) (meaning1453 q) hs
  change valuationOf q 1448 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause797 (q : Snake 81) (h : Conditions q) : valuation q 1448 = false ∨ valuation q 1450 = false ∨ valuation q 1453 = true := counterClause797 (baseVal q)

theorem counterClause798 (q : Nat → Bool) : valuationOf q 1448 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1454 = true := by
  have hs : count1452 q = (countLit q [-6, -8]) + (countLit q [-10, -11]) := List.countP_append (p := literal q) (l₁ := [-6, -8]) (l₂ := [-10, -11])
  have hm := merge_two (literal (valuationOf q) (1448)) (literal (valuationOf q) (1451)) (literal (valuationOf q) (1454)) (countLit q [-6, -8]) (countLit q [-10, -11]) (count1452 q) 1 2 (meaning1448 q) (meaning1451 q) (meaning1454 q) hs
  change valuationOf q 1448 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause798 (q : Snake 81) (h : Conditions q) : valuation q 1448 = false ∨ valuation q 1451 = false ∨ valuation q 1454 = true := counterClause798 (baseVal q)

theorem counterClause799 (q : Nat → Bool) : valuationOf q 1449 = false ∨ valuationOf q 1453 = true := by
  have hs : count1452 q = (countLit q [-6, -8]) + (countLit q [-10, -11]) := List.countP_append (p := literal q) (l₁ := [-6, -8]) (l₂ := [-10, -11])
  have hm := merge_left (literal (valuationOf q) (1449)) (literal (valuationOf q) (1453)) (countLit q [-6, -8]) (countLit q [-10, -11]) (count1452 q) 2 (meaning1449 q) (meaning1453 q) hs
  change valuationOf q 1449 = false ∨ valuationOf q 1453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause799 (q : Snake 81) (h : Conditions q) : valuation q 1449 = false ∨ valuation q 1453 = true := counterClause799 (baseVal q)

theorem counterClause800 (q : Nat → Bool) : valuationOf q 1449 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1454 = true := by
  have hs : count1452 q = (countLit q [-6, -8]) + (countLit q [-10, -11]) := List.countP_append (p := literal q) (l₁ := [-6, -8]) (l₂ := [-10, -11])
  have hm := merge_two (literal (valuationOf q) (1449)) (literal (valuationOf q) (1450)) (literal (valuationOf q) (1454)) (countLit q [-6, -8]) (countLit q [-10, -11]) (count1452 q) 2 1 (meaning1449 q) (meaning1450 q) (meaning1454 q) hs
  change valuationOf q 1449 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause800 (q : Snake 81) (h : Conditions q) : valuation q 1449 = false ∨ valuation q 1450 = false ∨ valuation q 1454 = true := counterClause800 (baseVal q)

theorem block24 (q : Snake 81) (h : Conditions q) : B112E024.Block24 (valuation q) :=
  ⟨clause769 q h, clause770 q h, clause771 q h, clause772 q h, clause773 q h, clause774 q h, clause775 q h, clause776 q h, clause777 q h, clause778 q h, clause779 q h, clause780 q h, clause781 q h, clause782 q h, clause783 q h, clause784 q h, clause785 q h, clause786 q h, clause787 q h, clause788 q h, clause789 q h, clause790 q h, clause791 q h, clause792 q h, clause793 q h, clause794 q h, clause795 q h, clause796 q h, clause797 q h, clause798 q h, clause799 q h, clause800 q h⟩

end
end Snake9.Regrowth.E112024
