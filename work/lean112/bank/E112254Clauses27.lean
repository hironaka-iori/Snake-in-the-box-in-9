import E112254Semantics
import B112E254Inputs
namespace Snake9.Regrowth.E112254
noncomputable section
local instance blockDec27 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause865 (q : Nat → Bool) : valuationOf q 465 = false ∨ valuationOf q 467 = true := by
  have hs : count467 q = (countLit q [237, 238]) + (countLit q [239, 240]) := List.countP_append (p := literal q) (l₁ := [237, 238]) (l₂ := [239, 240])
  have hm := merge_right (literal (valuationOf q) (465)) (literal (valuationOf q) (467)) (countLit q [237, 238]) (countLit q [239, 240]) (count467 q) 1 (meaning465 q) (meaning467 q) hs
  change valuationOf q 465 = false ∨ valuationOf q 467 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause865 (q : Snake 81) (h : Conditions q) : valuation q 465 = false ∨ valuation q 467 = true := counterClause865 (baseVal q)

theorem counterClause866 (q : Nat → Bool) : valuationOf q 463 = false ∨ valuationOf q 467 = true := by
  have hs : count467 q = (countLit q [237, 238]) + (countLit q [239, 240]) := List.countP_append (p := literal q) (l₁ := [237, 238]) (l₂ := [239, 240])
  have hm := merge_left (literal (valuationOf q) (463)) (literal (valuationOf q) (467)) (countLit q [237, 238]) (countLit q [239, 240]) (count467 q) 1 (meaning463 q) (meaning467 q) hs
  change valuationOf q 463 = false ∨ valuationOf q 467 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause866 (q : Snake 81) (h : Conditions q) : valuation q 463 = false ∨ valuation q 467 = true := counterClause866 (baseVal q)

theorem counterClause867 (q : Nat → Bool) : valuationOf q 242 = false ∨ valuationOf q 469 = true := by
  have hs : count469 q = (countLit q [241]) + (countLit q [242]) := List.countP_append (p := literal q) (l₁ := [241]) (l₂ := [242])
  have hm := merge_right (literal (valuationOf q) (242)) (literal (valuationOf q) (469)) (countLit q [241]) (countLit q [242]) (count469 q) 1 (meaning242 q) (meaning469 q) hs
  change valuationOf q 242 = false ∨ valuationOf q 469 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause867 (q : Snake 81) (h : Conditions q) : valuation q 242 = false ∨ valuation q 469 = true := counterClause867 (baseVal q)

theorem counterClause868 (q : Nat → Bool) : valuationOf q 241 = false ∨ valuationOf q 469 = true := by
  have hs : count469 q = (countLit q [241]) + (countLit q [242]) := List.countP_append (p := literal q) (l₁ := [241]) (l₂ := [242])
  have hm := merge_left (literal (valuationOf q) (241)) (literal (valuationOf q) (469)) (countLit q [241]) (countLit q [242]) (count469 q) 1 (meaning241 q) (meaning469 q) hs
  change valuationOf q 241 = false ∨ valuationOf q 469 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause868 (q : Snake 81) (h : Conditions q) : valuation q 241 = false ∨ valuation q 469 = true := counterClause868 (baseVal q)

theorem counterClause869 (q : Nat → Bool) : valuationOf q 469 = false ∨ valuationOf q 473 = true := by
  have hs : count473 q = (countLit q [241, 242]) + (countLit q [243, 244]) := List.countP_append (p := literal q) (l₁ := [241, 242]) (l₂ := [243, 244])
  have hm := merge_left (literal (valuationOf q) (469)) (literal (valuationOf q) (473)) (countLit q [241, 242]) (countLit q [243, 244]) (count473 q) 1 (meaning469 q) (meaning473 q) hs
  change valuationOf q 469 = false ∨ valuationOf q 473 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause869 (q : Snake 81) (h : Conditions q) : valuation q 469 = false ∨ valuation q 473 = true := counterClause869 (baseVal q)

theorem counterClause870 (q : Nat → Bool) : valuationOf q 473 = false ∨ valuationOf q 475 = true := by
  have hs : count475 q = (countLit q [237, 238, 239, 240]) + (countLit q [241, 242, 243, 244]) := List.countP_append (p := literal q) (l₁ := [237, 238, 239, 240]) (l₂ := [241, 242, 243, 244])
  have hm := merge_right (literal (valuationOf q) (473)) (literal (valuationOf q) (475)) (countLit q [237, 238, 239, 240]) (countLit q [241, 242, 243, 244]) (count475 q) 1 (meaning473 q) (meaning475 q) hs
  change valuationOf q 473 = false ∨ valuationOf q 475 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause870 (q : Snake 81) (h : Conditions q) : valuation q 473 = false ∨ valuation q 475 = true := counterClause870 (baseVal q)

theorem counterClause871 (q : Nat → Bool) : valuationOf q 467 = false ∨ valuationOf q 475 = true := by
  have hs : count475 q = (countLit q [237, 238, 239, 240]) + (countLit q [241, 242, 243, 244]) := List.countP_append (p := literal q) (l₁ := [237, 238, 239, 240]) (l₂ := [241, 242, 243, 244])
  have hm := merge_left (literal (valuationOf q) (467)) (literal (valuationOf q) (475)) (countLit q [237, 238, 239, 240]) (countLit q [241, 242, 243, 244]) (count475 q) 1 (meaning467 q) (meaning475 q) hs
  change valuationOf q 467 = false ∨ valuationOf q 475 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause871 (q : Snake 81) (h : Conditions q) : valuation q 467 = false ∨ valuation q 475 = true := counterClause871 (baseVal q)

theorem counterClause872 (q : Nat → Bool) : valuationOf q 475 = false ∨ valuationOf q 477 = true := by
  have hs : count477 q = (countLit q [229, 230, 231, 232, 233, 234, 235, 236]) + (countLit q [237, 238, 239, 240, 241, 242, 243, 244]) := List.countP_append (p := literal q) (l₁ := [229, 230, 231, 232, 233, 234, 235, 236]) (l₂ := [237, 238, 239, 240, 241, 242, 243, 244])
  have hm := merge_right (literal (valuationOf q) (475)) (literal (valuationOf q) (477)) (countLit q [229, 230, 231, 232, 233, 234, 235, 236]) (countLit q [237, 238, 239, 240, 241, 242, 243, 244]) (count477 q) 1 (meaning475 q) (meaning477 q) hs
  change valuationOf q 475 = false ∨ valuationOf q 477 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause872 (q : Snake 81) (h : Conditions q) : valuation q 475 = false ∨ valuation q 477 = true := counterClause872 (baseVal q)

theorem counterClause873 (q : Nat → Bool) : valuationOf q 461 = false ∨ valuationOf q 477 = true := by
  have hs : count477 q = (countLit q [229, 230, 231, 232, 233, 234, 235, 236]) + (countLit q [237, 238, 239, 240, 241, 242, 243, 244]) := List.countP_append (p := literal q) (l₁ := [229, 230, 231, 232, 233, 234, 235, 236]) (l₂ := [237, 238, 239, 240, 241, 242, 243, 244])
  have hm := merge_left (literal (valuationOf q) (461)) (literal (valuationOf q) (477)) (countLit q [229, 230, 231, 232, 233, 234, 235, 236]) (countLit q [237, 238, 239, 240, 241, 242, 243, 244]) (count477 q) 1 (meaning461 q) (meaning477 q) hs
  change valuationOf q 461 = false ∨ valuationOf q 477 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause873 (q : Snake 81) (h : Conditions q) : valuation q 461 = false ∨ valuation q 477 = true := counterClause873 (baseVal q)

theorem counterClause874 (q : Nat → Bool) : valuationOf q 477 = false ∨ valuationOf q 479 = true := by
  have hs : count479 q = (countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) + (countLit q [229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) := List.countP_append (p := literal q) (l₁ := [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) (l₂ := [229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244])
  have hm := merge_right (literal (valuationOf q) (477)) (literal (valuationOf q) (479)) (countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) (countLit q [229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) (count479 q) 1 (meaning477 q) (meaning479 q) hs
  change valuationOf q 477 = false ∨ valuationOf q 479 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause874 (q : Snake 81) (h : Conditions q) : valuation q 477 = false ∨ valuation q 479 = true := counterClause874 (baseVal q)

theorem counterClause875 (q : Nat → Bool) : valuationOf q 447 = false ∨ valuationOf q 479 = true := by
  have hs : count479 q = (countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) + (countLit q [229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) := List.countP_append (p := literal q) (l₁ := [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) (l₂ := [229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244])
  have hm := merge_left (literal (valuationOf q) (447)) (literal (valuationOf q) (479)) (countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) (countLit q [229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) (count479 q) 1 (meaning447 q) (meaning479 q) hs
  change valuationOf q 447 = false ∨ valuationOf q 479 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause875 (q : Snake 81) (h : Conditions q) : valuation q 447 = false ∨ valuation q 479 = true := counterClause875 (baseVal q)

theorem counterClause876 (q : Nat → Bool) : valuationOf q 447 = false ∨ valuationOf q 477 = false ∨ valuationOf q 480 = true := by
  have hs : count479 q = (countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) + (countLit q [229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) := List.countP_append (p := literal q) (l₁ := [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) (l₂ := [229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244])
  have hm := merge_two (literal (valuationOf q) (447)) (literal (valuationOf q) (477)) (literal (valuationOf q) (480)) (countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) (countLit q [229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) (count479 q) 1 1 (meaning447 q) (meaning477 q) (meaning480 q) hs
  change valuationOf q 447 = false ∨ valuationOf q 477 = false ∨ valuationOf q 480 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause876 (q : Snake 81) (h : Conditions q) : valuation q 447 = false ∨ valuation q 477 = false ∨ valuation q 480 = true := counterClause876 (baseVal q)

theorem counterClause877 (q : Nat → Bool) : valuationOf q 448 = false ∨ valuationOf q 480 = true := by
  have hs : count479 q = (countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) + (countLit q [229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) := List.countP_append (p := literal q) (l₁ := [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) (l₂ := [229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244])
  have hm := merge_left (literal (valuationOf q) (448)) (literal (valuationOf q) (480)) (countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) (countLit q [229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) (count479 q) 2 (meaning448 q) (meaning480 q) hs
  change valuationOf q 448 = false ∨ valuationOf q 480 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause877 (q : Snake 81) (h : Conditions q) : valuation q 448 = false ∨ valuation q 480 = true := counterClause877 (baseVal q)

theorem counterClause878 (q : Nat → Bool) : valuationOf q 479 = false ∨ valuationOf q 481 = true := by
  have hs : count481 q = (countLit q [184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) + (countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) := List.countP_append (p := literal q) (l₁ := [184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) (l₂ := [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244])
  have hm := merge_right (literal (valuationOf q) (479)) (literal (valuationOf q) (481)) (countLit q [184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) (countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) (count481 q) 1 (meaning479 q) (meaning481 q) hs
  change valuationOf q 479 = false ∨ valuationOf q 481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause878 (q : Snake 81) (h : Conditions q) : valuation q 479 = false ∨ valuation q 481 = true := counterClause878 (baseVal q)

theorem counterClause879 (q : Nat → Bool) : valuationOf q 480 = false ∨ valuationOf q 482 = true := by
  have hs : count481 q = (countLit q [184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) + (countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) := List.countP_append (p := literal q) (l₁ := [184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) (l₂ := [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244])
  have hm := merge_right (literal (valuationOf q) (480)) (literal (valuationOf q) (482)) (countLit q [184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) (countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) (count481 q) 2 (meaning480 q) (meaning482 q) hs
  change valuationOf q 480 = false ∨ valuationOf q 482 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause879 (q : Snake 81) (h : Conditions q) : valuation q 480 = false ∨ valuation q 482 = true := counterClause879 (baseVal q)

theorem counterClause880 (q : Nat → Bool) : valuationOf q 419 = false ∨ valuationOf q 481 = true := by
  have hs : count481 q = (countLit q [184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) + (countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) := List.countP_append (p := literal q) (l₁ := [184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) (l₂ := [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244])
  have hm := merge_left (literal (valuationOf q) (419)) (literal (valuationOf q) (481)) (countLit q [184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) (countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) (count481 q) 1 (meaning419 q) (meaning481 q) hs
  change valuationOf q 419 = false ∨ valuationOf q 481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause880 (q : Snake 81) (h : Conditions q) : valuation q 419 = false ∨ valuation q 481 = true := counterClause880 (baseVal q)

theorem counterClause881 (q : Nat → Bool) : valuationOf q 419 = false ∨ valuationOf q 479 = false ∨ valuationOf q 482 = true := by
  have hs : count481 q = (countLit q [184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) + (countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) := List.countP_append (p := literal q) (l₁ := [184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) (l₂ := [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244])
  have hm := merge_two (literal (valuationOf q) (419)) (literal (valuationOf q) (479)) (literal (valuationOf q) (482)) (countLit q [184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) (countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) (count481 q) 1 1 (meaning419 q) (meaning479 q) (meaning482 q) hs
  change valuationOf q 419 = false ∨ valuationOf q 479 = false ∨ valuationOf q 482 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause881 (q : Snake 81) (h : Conditions q) : valuation q 419 = false ∨ valuation q 479 = false ∨ valuation q 482 = true := counterClause881 (baseVal q)

theorem counterClause882 (q : Nat → Bool) : valuationOf q 420 = false ∨ valuationOf q 482 = true := by
  have hs : count481 q = (countLit q [184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) + (countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) := List.countP_append (p := literal q) (l₁ := [184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) (l₂ := [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244])
  have hm := merge_left (literal (valuationOf q) (420)) (literal (valuationOf q) (482)) (countLit q [184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) (countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) (count481 q) 2 (meaning420 q) (meaning482 q) hs
  change valuationOf q 420 = false ∨ valuationOf q 482 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause882 (q : Snake 81) (h : Conditions q) : valuation q 420 = false ∨ valuation q 482 = true := counterClause882 (baseVal q)

theorem counterClause883 (q : Nat → Bool) : valuationOf q 482 = false ∨ valuationOf q 484 = true := by
  have hs : count483 q = (countLit q [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183]) + (countLit q [184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) := List.countP_append (p := literal q) (l₁ := [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183]) (l₂ := [184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244])
  have hm := merge_right (literal (valuationOf q) (482)) (literal (valuationOf q) (484)) (countLit q [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183]) (countLit q [184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) (count483 q) 2 (meaning482 q) (meaning484 q) hs
  change valuationOf q 482 = false ∨ valuationOf q 484 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause883 (q : Snake 81) (h : Conditions q) : valuation q 482 = false ∨ valuation q 484 = true := counterClause883 (baseVal q)

theorem counterClause884 (q : Nat → Bool) : valuationOf q 361 = false ∨ valuationOf q 481 = false ∨ valuationOf q 484 = true := by
  have hs : count483 q = (countLit q [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183]) + (countLit q [184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) := List.countP_append (p := literal q) (l₁ := [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183]) (l₂ := [184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244])
  have hm := merge_two (literal (valuationOf q) (361)) (literal (valuationOf q) (481)) (literal (valuationOf q) (484)) (countLit q [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183]) (countLit q [184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) (count483 q) 1 1 (meaning361 q) (meaning481 q) (meaning484 q) hs
  change valuationOf q 361 = false ∨ valuationOf q 481 = false ∨ valuationOf q 484 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause884 (q : Snake 81) (h : Conditions q) : valuation q 361 = false ∨ valuation q 481 = false ∨ valuation q 484 = true := counterClause884 (baseVal q)

theorem counterClause885 (q : Nat → Bool) : valuationOf q 362 = false ∨ valuationOf q 484 = true := by
  have hs : count483 q = (countLit q [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183]) + (countLit q [184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) := List.countP_append (p := literal q) (l₁ := [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183]) (l₂ := [184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244])
  have hm := merge_left (literal (valuationOf q) (362)) (literal (valuationOf q) (484)) (countLit q [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183]) (countLit q [184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) (count483 q) 2 (meaning362 q) (meaning484 q) hs
  change valuationOf q 362 = false ∨ valuationOf q 484 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause885 (q : Snake 81) (h : Conditions q) : valuation q 362 = false ∨ valuation q 484 = true := counterClause885 (baseVal q)

theorem clause886 (q : Snake 81) (h : Conditions q) : valuation q 484 = false := by
  rw [value484]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count483 (baseVal q) = (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := other_count_bound q h
  rw [he]
  omega

theorem clause887 (q : Snake 81) (h : Conditions q) : valuation q 123 = true ∨ valuation q 124 = true ∨ valuation q 125 = true ∨ valuation q 126 = true ∨ valuation q 127 = true ∨ valuation q 128 = true ∨ valuation q 129 = true ∨ valuation q 130 = true ∨ valuation q 131 = true ∨ valuation q 132 = true ∨ valuation q 133 = true ∨ valuation q 134 = true ∨ valuation q 135 = true ∨ valuation q 136 = true ∨ valuation q 137 = true ∨ valuation q 138 = true ∨ valuation q 139 = true ∨ valuation q 140 = true ∨ valuation q 141 = true ∨ valuation q 142 = true ∨ valuation q 143 = true ∨ valuation q 144 = true ∨ valuation q 145 = true ∨ valuation q 146 = true ∨ valuation q 147 = true ∨ valuation q 148 = true ∨ valuation q 149 = true ∨ valuation q 150 = true ∨ valuation q 151 = true ∨ valuation q 152 = true ∨ valuation q 153 = true ∨ valuation q 154 = true ∨ valuation q 155 = true ∨ valuation q 156 = true ∨ valuation q 157 = true ∨ valuation q 158 = true ∨ valuation q 159 = true ∨ valuation q 160 = true ∨ valuation q 161 = true ∨ valuation q 162 = true ∨ valuation q 163 = true ∨ valuation q 164 = true ∨ valuation q 165 = true ∨ valuation q 166 = true ∨ valuation q 167 = true ∨ valuation q 168 = true ∨ valuation q 170 = true ∨ valuation q 171 = true ∨ valuation q 172 = true ∨ valuation q 173 = true ∨ valuation q 174 = true ∨ valuation q 175 = true ∨ valuation q 176 = true ∨ valuation q 177 = true ∨ valuation q 178 = true ∨ valuation q 179 = true ∨ valuation q 180 = true ∨ valuation q 181 = true ∨ valuation q 182 = true ∨ valuation q 183 = true ∨ valuation q 184 = true ∨ valuation q 185 = true ∨ valuation q 186 = true ∨ valuation q 187 = true ∨ valuation q 188 = true ∨ valuation q 189 = true ∨ valuation q 190 = true ∨ valuation q 191 = true ∨ valuation q 192 = true ∨ valuation q 193 = true ∨ valuation q 194 = true ∨ valuation q 195 = true ∨ valuation q 196 = true ∨ valuation q 197 = true ∨ valuation q 198 = true ∨ valuation q 199 = true ∨ valuation q 200 = true ∨ valuation q 201 = true ∨ valuation q 202 = true ∨ valuation q 203 = true ∨ valuation q 204 = true ∨ valuation q 205 = true ∨ valuation q 206 = true ∨ valuation q 207 = true ∨ valuation q 208 = true ∨ valuation q 209 = true ∨ valuation q 210 = true ∨ valuation q 211 = true ∨ valuation q 212 = true ∨ valuation q 213 = true ∨ valuation q 214 = true ∨ valuation q 215 = true ∨ valuation q 216 = true ∨ valuation q 217 = true ∨ valuation q 218 = true ∨ valuation q 219 = true ∨ valuation q 220 = true ∨ valuation q 221 = true ∨ valuation q 222 = true ∨ valuation q 223 = true ∨ valuation q 224 = true ∨ valuation q 225 = true ∨ valuation q 226 = true ∨ valuation q 227 = true ∨ valuation q 228 = true ∨ valuation q 229 = true ∨ valuation q 230 = true ∨ valuation q 231 = true ∨ valuation q 232 = true ∨ valuation q 233 = true ∨ valuation q 234 = true ∨ valuation q 235 = true ∨ valuation q 236 = true ∨ valuation q 237 = true ∨ valuation q 238 = true ∨ valuation q 239 = true ∨ valuation q 240 = true ∨ valuation q 241 = true ∨ valuation q 242 = true ∨ valuation q 243 = true ∨ valuation q 244 = true := by
  rw [value123, value124, value125, value126, value127, value128, value129, value130, value131, value132, value133, value134, value135, value136, value137, value138, value139, value140, value141, value142, value143, value144, value145, value146, value147, value148, value149, value150, value151, value152, value153, value154, value155, value156, value157, value158, value159, value160, value161, value162, value163, value164, value165, value166, value167, value168, value170, value171, value172, value173, value174, value175, value176, value177, value178, value179, value180, value181, value182, value183, value184, value185, value186, value187, value188, value189, value190, value191, value192, value193, value194, value195, value196, value197, value198, value199, value200, value201, value202, value203, value204, value205, value206, value207, value208, value209, value210, value211, value212, value213, value214, value215, value216, value217, value218, value219, value220, value221, value222, value223, value224, value225, value226, value227, value228, value229, value230, value231, value232, value233, value234, value235, value236, value237, value238, value239, value240, value241, value242, value243, value244]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hg := other_endpoint q others (fun v hv hn => others_mem v (h.covered v hv) (by simpa only [h.head_fixed] using hn))
  simpa only [others, List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem counterClause888 (q : Nat → Bool) : valuationOf q 5 = true ∨ valuationOf q 1501 = true := by
  have hs : count1501 q = (countLit q [-5]) + (countLit q [-8]) := List.countP_append (p := literal q) (l₁ := [-5]) (l₂ := [-8])
  have hm := merge_left (literal (valuationOf q) (-5)) (literal (valuationOf q) (1501)) (countLit q [-5]) (countLit q [-8]) (count1501 q) 1 (meaningNeg5 q) (meaning1501 q) hs
  change (! (valuationOf q 5)) = false ∨ valuationOf q 1501 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause888 (q : Snake 81) (h : Conditions q) : valuation q 5 = true ∨ valuation q 1501 = true := counterClause888 (baseVal q)

theorem counterClause889 (q : Nat → Bool) : valuationOf q 5 = true ∨ valuationOf q 8 = true ∨ valuationOf q 1502 = true := by
  have hs : count1501 q = (countLit q [-5]) + (countLit q [-8]) := List.countP_append (p := literal q) (l₁ := [-5]) (l₂ := [-8])
  have hm := merge_two (literal (valuationOf q) (-5)) (literal (valuationOf q) (-8)) (literal (valuationOf q) (1502)) (countLit q [-5]) (countLit q [-8]) (count1501 q) 1 1 (meaningNeg5 q) (meaningNeg8 q) (meaning1502 q) hs
  change (! (valuationOf q 5)) = false ∨ (! (valuationOf q 8)) = false ∨ valuationOf q 1502 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause889 (q : Snake 81) (h : Conditions q) : valuation q 5 = true ∨ valuation q 8 = true ∨ valuation q 1502 = true := counterClause889 (baseVal q)

theorem counterClause890 (q : Nat → Bool) : valuationOf q 1501 = false ∨ valuationOf q 1503 = true := by
  have hs : count1503 q = (countLit q [-2]) + (countLit q [-5, -8]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-5, -8])
  have hm := merge_right (literal (valuationOf q) (1501)) (literal (valuationOf q) (1503)) (countLit q [-2]) (countLit q [-5, -8]) (count1503 q) 1 (meaning1501 q) (meaning1503 q) hs
  change valuationOf q 1501 = false ∨ valuationOf q 1503 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause890 (q : Snake 81) (h : Conditions q) : valuation q 1501 = false ∨ valuation q 1503 = true := counterClause890 (baseVal q)

theorem counterClause891 (q : Nat → Bool) : valuationOf q 1502 = false ∨ valuationOf q 1504 = true := by
  have hs : count1503 q = (countLit q [-2]) + (countLit q [-5, -8]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-5, -8])
  have hm := merge_right (literal (valuationOf q) (1502)) (literal (valuationOf q) (1504)) (countLit q [-2]) (countLit q [-5, -8]) (count1503 q) 2 (meaning1502 q) (meaning1504 q) hs
  change valuationOf q 1502 = false ∨ valuationOf q 1504 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause891 (q : Snake 81) (h : Conditions q) : valuation q 1502 = false ∨ valuation q 1504 = true := counterClause891 (baseVal q)

theorem counterClause892 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1501 = false ∨ valuationOf q 1504 = true := by
  have hs : count1503 q = (countLit q [-2]) + (countLit q [-5, -8]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-5, -8])
  have hm := merge_two (literal (valuationOf q) (-2)) (literal (valuationOf q) (1501)) (literal (valuationOf q) (1504)) (countLit q [-2]) (countLit q [-5, -8]) (count1503 q) 1 1 (meaningNeg2 q) (meaning1501 q) (meaning1504 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1501 = false ∨ valuationOf q 1504 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause892 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1501 = false ∨ valuation q 1504 = true := counterClause892 (baseVal q)

theorem counterClause893 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1502 = false ∨ valuationOf q 1505 = true := by
  have hs : count1503 q = (countLit q [-2]) + (countLit q [-5, -8]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-5, -8])
  have hm := merge_two (literal (valuationOf q) (-2)) (literal (valuationOf q) (1502)) (literal (valuationOf q) (1505)) (countLit q [-2]) (countLit q [-5, -8]) (count1503 q) 1 2 (meaningNeg2 q) (meaning1502 q) (meaning1505 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1502 = false ∨ valuationOf q 1505 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause893 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1502 = false ∨ valuation q 1505 = true := counterClause893 (baseVal q)

theorem counterClause894 (q : Nat → Bool) : valuationOf q 12 = true ∨ valuationOf q 1506 = true := by
  have hs : count1506 q = (countLit q [-9]) + (countLit q [-12]) := List.countP_append (p := literal q) (l₁ := [-9]) (l₂ := [-12])
  have hm := merge_right (literal (valuationOf q) (-12)) (literal (valuationOf q) (1506)) (countLit q [-9]) (countLit q [-12]) (count1506 q) 1 (meaningNeg12 q) (meaning1506 q) hs
  change (! (valuationOf q 12)) = false ∨ valuationOf q 1506 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause894 (q : Snake 81) (h : Conditions q) : valuation q 12 = true ∨ valuation q 1506 = true := counterClause894 (baseVal q)

theorem counterClause895 (q : Nat → Bool) : valuationOf q 9 = true ∨ valuationOf q 1506 = true := by
  have hs : count1506 q = (countLit q [-9]) + (countLit q [-12]) := List.countP_append (p := literal q) (l₁ := [-9]) (l₂ := [-12])
  have hm := merge_left (literal (valuationOf q) (-9)) (literal (valuationOf q) (1506)) (countLit q [-9]) (countLit q [-12]) (count1506 q) 1 (meaningNeg9 q) (meaning1506 q) hs
  change (! (valuationOf q 9)) = false ∨ valuationOf q 1506 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause895 (q : Snake 81) (h : Conditions q) : valuation q 9 = true ∨ valuation q 1506 = true := counterClause895 (baseVal q)

theorem counterClause896 (q : Nat → Bool) : valuationOf q 9 = true ∨ valuationOf q 12 = true ∨ valuationOf q 1507 = true := by
  have hs : count1506 q = (countLit q [-9]) + (countLit q [-12]) := List.countP_append (p := literal q) (l₁ := [-9]) (l₂ := [-12])
  have hm := merge_two (literal (valuationOf q) (-9)) (literal (valuationOf q) (-12)) (literal (valuationOf q) (1507)) (countLit q [-9]) (countLit q [-12]) (count1506 q) 1 1 (meaningNeg9 q) (meaningNeg12 q) (meaning1507 q) hs
  change (! (valuationOf q 9)) = false ∨ (! (valuationOf q 12)) = false ∨ valuationOf q 1507 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause896 (q : Snake 81) (h : Conditions q) : valuation q 9 = true ∨ valuation q 12 = true ∨ valuation q 1507 = true := counterClause896 (baseVal q)

theorem block27 (q : Snake 81) (h : Conditions q) : B112E254.Block27 (valuation q) :=
  ⟨clause865 q h, clause866 q h, clause867 q h, clause868 q h, clause869 q h, clause870 q h, clause871 q h, clause872 q h, clause873 q h, clause874 q h, clause875 q h, clause876 q h, clause877 q h, clause878 q h, clause879 q h, clause880 q h, clause881 q h, clause882 q h, clause883 q h, clause884 q h, clause885 q h, clause886 q h, clause887 q h, clause888 q h, clause889 q h, clause890 q h, clause891 q h, clause892 q h, clause893 q h, clause894 q h, clause895 q h, clause896 q h⟩

end
end Snake9.Regrowth.E112254
