import E112258Semantics
import B112E258Inputs
namespace Snake9.Regrowth.E112258
noncomputable section
local instance blockDec28 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause897 (q : Nat → Bool) : valuationOf q 471 = false ∨ valuationOf q 473 = true := by
  have hs : count473 q = (countLit q [241, 242]) + (countLit q [243, 244]) := List.countP_append (p := literal q) (l₁ := [241, 242]) (l₂ := [243, 244])
  have hm := merge_right (literal (valuationOf q) (471)) (literal (valuationOf q) (473)) (countLit q [241, 242]) (countLit q [243, 244]) (count473 q) 1 (meaning471 q) (meaning473 q) hs
  change valuationOf q 471 = false ∨ valuationOf q 473 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause897 (q : Snake 81) (h : Conditions q) : valuation q 471 = false ∨ valuation q 473 = true := counterClause897 (baseVal q)

theorem counterClause898 (q : Nat → Bool) : valuationOf q 473 = false ∨ valuationOf q 475 = true := by
  have hs : count475 q = (countLit q [237, 238, 239, 240]) + (countLit q [241, 242, 243, 244]) := List.countP_append (p := literal q) (l₁ := [237, 238, 239, 240]) (l₂ := [241, 242, 243, 244])
  have hm := merge_right (literal (valuationOf q) (473)) (literal (valuationOf q) (475)) (countLit q [237, 238, 239, 240]) (countLit q [241, 242, 243, 244]) (count475 q) 1 (meaning473 q) (meaning475 q) hs
  change valuationOf q 473 = false ∨ valuationOf q 475 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause898 (q : Snake 81) (h : Conditions q) : valuation q 473 = false ∨ valuation q 475 = true := counterClause898 (baseVal q)

theorem counterClause899 (q : Nat → Bool) : valuationOf q 467 = false ∨ valuationOf q 475 = true := by
  have hs : count475 q = (countLit q [237, 238, 239, 240]) + (countLit q [241, 242, 243, 244]) := List.countP_append (p := literal q) (l₁ := [237, 238, 239, 240]) (l₂ := [241, 242, 243, 244])
  have hm := merge_left (literal (valuationOf q) (467)) (literal (valuationOf q) (475)) (countLit q [237, 238, 239, 240]) (countLit q [241, 242, 243, 244]) (count475 q) 1 (meaning467 q) (meaning475 q) hs
  change valuationOf q 467 = false ∨ valuationOf q 475 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause899 (q : Snake 81) (h : Conditions q) : valuation q 467 = false ∨ valuation q 475 = true := counterClause899 (baseVal q)

theorem counterClause900 (q : Nat → Bool) : valuationOf q 467 = false ∨ valuationOf q 473 = false ∨ valuationOf q 476 = true := by
  have hs : count475 q = (countLit q [237, 238, 239, 240]) + (countLit q [241, 242, 243, 244]) := List.countP_append (p := literal q) (l₁ := [237, 238, 239, 240]) (l₂ := [241, 242, 243, 244])
  have hm := merge_two (literal (valuationOf q) (467)) (literal (valuationOf q) (473)) (literal (valuationOf q) (476)) (countLit q [237, 238, 239, 240]) (countLit q [241, 242, 243, 244]) (count475 q) 1 1 (meaning467 q) (meaning473 q) (meaning476 q) hs
  change valuationOf q 467 = false ∨ valuationOf q 473 = false ∨ valuationOf q 476 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause900 (q : Snake 81) (h : Conditions q) : valuation q 467 = false ∨ valuation q 473 = false ∨ valuation q 476 = true := counterClause900 (baseVal q)

theorem counterClause901 (q : Nat → Bool) : valuationOf q 468 = false ∨ valuationOf q 476 = true := by
  have hs : count475 q = (countLit q [237, 238, 239, 240]) + (countLit q [241, 242, 243, 244]) := List.countP_append (p := literal q) (l₁ := [237, 238, 239, 240]) (l₂ := [241, 242, 243, 244])
  have hm := merge_left (literal (valuationOf q) (468)) (literal (valuationOf q) (476)) (countLit q [237, 238, 239, 240]) (countLit q [241, 242, 243, 244]) (count475 q) 2 (meaning468 q) (meaning476 q) hs
  change valuationOf q 468 = false ∨ valuationOf q 476 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause901 (q : Snake 81) (h : Conditions q) : valuation q 468 = false ∨ valuation q 476 = true := counterClause901 (baseVal q)

theorem counterClause902 (q : Nat → Bool) : valuationOf q 475 = false ∨ valuationOf q 477 = true := by
  have hs : count477 q = (countLit q [229, 230, 231, 232, 233, 234, 235, 236]) + (countLit q [237, 238, 239, 240, 241, 242, 243, 244]) := List.countP_append (p := literal q) (l₁ := [229, 230, 231, 232, 233, 234, 235, 236]) (l₂ := [237, 238, 239, 240, 241, 242, 243, 244])
  have hm := merge_right (literal (valuationOf q) (475)) (literal (valuationOf q) (477)) (countLit q [229, 230, 231, 232, 233, 234, 235, 236]) (countLit q [237, 238, 239, 240, 241, 242, 243, 244]) (count477 q) 1 (meaning475 q) (meaning477 q) hs
  change valuationOf q 475 = false ∨ valuationOf q 477 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause902 (q : Snake 81) (h : Conditions q) : valuation q 475 = false ∨ valuation q 477 = true := counterClause902 (baseVal q)

theorem counterClause903 (q : Nat → Bool) : valuationOf q 476 = false ∨ valuationOf q 478 = true := by
  have hs : count477 q = (countLit q [229, 230, 231, 232, 233, 234, 235, 236]) + (countLit q [237, 238, 239, 240, 241, 242, 243, 244]) := List.countP_append (p := literal q) (l₁ := [229, 230, 231, 232, 233, 234, 235, 236]) (l₂ := [237, 238, 239, 240, 241, 242, 243, 244])
  have hm := merge_right (literal (valuationOf q) (476)) (literal (valuationOf q) (478)) (countLit q [229, 230, 231, 232, 233, 234, 235, 236]) (countLit q [237, 238, 239, 240, 241, 242, 243, 244]) (count477 q) 2 (meaning476 q) (meaning478 q) hs
  change valuationOf q 476 = false ∨ valuationOf q 478 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause903 (q : Snake 81) (h : Conditions q) : valuation q 476 = false ∨ valuation q 478 = true := counterClause903 (baseVal q)

theorem counterClause904 (q : Nat → Bool) : valuationOf q 461 = false ∨ valuationOf q 477 = true := by
  have hs : count477 q = (countLit q [229, 230, 231, 232, 233, 234, 235, 236]) + (countLit q [237, 238, 239, 240, 241, 242, 243, 244]) := List.countP_append (p := literal q) (l₁ := [229, 230, 231, 232, 233, 234, 235, 236]) (l₂ := [237, 238, 239, 240, 241, 242, 243, 244])
  have hm := merge_left (literal (valuationOf q) (461)) (literal (valuationOf q) (477)) (countLit q [229, 230, 231, 232, 233, 234, 235, 236]) (countLit q [237, 238, 239, 240, 241, 242, 243, 244]) (count477 q) 1 (meaning461 q) (meaning477 q) hs
  change valuationOf q 461 = false ∨ valuationOf q 477 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause904 (q : Snake 81) (h : Conditions q) : valuation q 461 = false ∨ valuation q 477 = true := counterClause904 (baseVal q)

theorem counterClause905 (q : Nat → Bool) : valuationOf q 461 = false ∨ valuationOf q 475 = false ∨ valuationOf q 478 = true := by
  have hs : count477 q = (countLit q [229, 230, 231, 232, 233, 234, 235, 236]) + (countLit q [237, 238, 239, 240, 241, 242, 243, 244]) := List.countP_append (p := literal q) (l₁ := [229, 230, 231, 232, 233, 234, 235, 236]) (l₂ := [237, 238, 239, 240, 241, 242, 243, 244])
  have hm := merge_two (literal (valuationOf q) (461)) (literal (valuationOf q) (475)) (literal (valuationOf q) (478)) (countLit q [229, 230, 231, 232, 233, 234, 235, 236]) (countLit q [237, 238, 239, 240, 241, 242, 243, 244]) (count477 q) 1 1 (meaning461 q) (meaning475 q) (meaning478 q) hs
  change valuationOf q 461 = false ∨ valuationOf q 475 = false ∨ valuationOf q 478 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause905 (q : Snake 81) (h : Conditions q) : valuation q 461 = false ∨ valuation q 475 = false ∨ valuation q 478 = true := counterClause905 (baseVal q)

theorem counterClause906 (q : Nat → Bool) : valuationOf q 477 = false ∨ valuationOf q 479 = true := by
  have hs : count479 q = (countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) + (countLit q [229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) := List.countP_append (p := literal q) (l₁ := [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) (l₂ := [229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244])
  have hm := merge_right (literal (valuationOf q) (477)) (literal (valuationOf q) (479)) (countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) (countLit q [229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) (count479 q) 1 (meaning477 q) (meaning479 q) hs
  change valuationOf q 477 = false ∨ valuationOf q 479 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause906 (q : Snake 81) (h : Conditions q) : valuation q 477 = false ∨ valuation q 479 = true := counterClause906 (baseVal q)

theorem counterClause907 (q : Nat → Bool) : valuationOf q 478 = false ∨ valuationOf q 480 = true := by
  have hs : count479 q = (countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) + (countLit q [229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) := List.countP_append (p := literal q) (l₁ := [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) (l₂ := [229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244])
  have hm := merge_right (literal (valuationOf q) (478)) (literal (valuationOf q) (480)) (countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) (countLit q [229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) (count479 q) 2 (meaning478 q) (meaning480 q) hs
  change valuationOf q 478 = false ∨ valuationOf q 480 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause907 (q : Snake 81) (h : Conditions q) : valuation q 478 = false ∨ valuation q 480 = true := counterClause907 (baseVal q)

theorem counterClause908 (q : Nat → Bool) : valuationOf q 447 = false ∨ valuationOf q 479 = true := by
  have hs : count479 q = (countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) + (countLit q [229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) := List.countP_append (p := literal q) (l₁ := [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) (l₂ := [229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244])
  have hm := merge_left (literal (valuationOf q) (447)) (literal (valuationOf q) (479)) (countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) (countLit q [229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) (count479 q) 1 (meaning447 q) (meaning479 q) hs
  change valuationOf q 447 = false ∨ valuationOf q 479 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause908 (q : Snake 81) (h : Conditions q) : valuation q 447 = false ∨ valuation q 479 = true := counterClause908 (baseVal q)

theorem counterClause909 (q : Nat → Bool) : valuationOf q 447 = false ∨ valuationOf q 477 = false ∨ valuationOf q 480 = true := by
  have hs : count479 q = (countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) + (countLit q [229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) := List.countP_append (p := literal q) (l₁ := [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) (l₂ := [229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244])
  have hm := merge_two (literal (valuationOf q) (447)) (literal (valuationOf q) (477)) (literal (valuationOf q) (480)) (countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) (countLit q [229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) (count479 q) 1 1 (meaning447 q) (meaning477 q) (meaning480 q) hs
  change valuationOf q 447 = false ∨ valuationOf q 477 = false ∨ valuationOf q 480 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause909 (q : Snake 81) (h : Conditions q) : valuation q 447 = false ∨ valuation q 477 = false ∨ valuation q 480 = true := counterClause909 (baseVal q)

theorem counterClause910 (q : Nat → Bool) : valuationOf q 448 = false ∨ valuationOf q 480 = true := by
  have hs : count479 q = (countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) + (countLit q [229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) := List.countP_append (p := literal q) (l₁ := [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) (l₂ := [229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244])
  have hm := merge_left (literal (valuationOf q) (448)) (literal (valuationOf q) (480)) (countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) (countLit q [229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) (count479 q) 2 (meaning448 q) (meaning480 q) hs
  change valuationOf q 448 = false ∨ valuationOf q 480 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause910 (q : Snake 81) (h : Conditions q) : valuation q 448 = false ∨ valuation q 480 = true := counterClause910 (baseVal q)

theorem counterClause911 (q : Nat → Bool) : valuationOf q 479 = false ∨ valuationOf q 481 = true := by
  have hs : count481 q = (countLit q [184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) + (countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) := List.countP_append (p := literal q) (l₁ := [184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) (l₂ := [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244])
  have hm := merge_right (literal (valuationOf q) (479)) (literal (valuationOf q) (481)) (countLit q [184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) (countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) (count481 q) 1 (meaning479 q) (meaning481 q) hs
  change valuationOf q 479 = false ∨ valuationOf q 481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause911 (q : Snake 81) (h : Conditions q) : valuation q 479 = false ∨ valuation q 481 = true := counterClause911 (baseVal q)

theorem counterClause912 (q : Nat → Bool) : valuationOf q 480 = false ∨ valuationOf q 482 = true := by
  have hs : count481 q = (countLit q [184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) + (countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) := List.countP_append (p := literal q) (l₁ := [184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) (l₂ := [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244])
  have hm := merge_right (literal (valuationOf q) (480)) (literal (valuationOf q) (482)) (countLit q [184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) (countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) (count481 q) 2 (meaning480 q) (meaning482 q) hs
  change valuationOf q 480 = false ∨ valuationOf q 482 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause912 (q : Snake 81) (h : Conditions q) : valuation q 480 = false ∨ valuation q 482 = true := counterClause912 (baseVal q)

theorem counterClause913 (q : Nat → Bool) : valuationOf q 419 = false ∨ valuationOf q 481 = true := by
  have hs : count481 q = (countLit q [184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) + (countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) := List.countP_append (p := literal q) (l₁ := [184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) (l₂ := [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244])
  have hm := merge_left (literal (valuationOf q) (419)) (literal (valuationOf q) (481)) (countLit q [184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) (countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) (count481 q) 1 (meaning419 q) (meaning481 q) hs
  change valuationOf q 419 = false ∨ valuationOf q 481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause913 (q : Snake 81) (h : Conditions q) : valuation q 419 = false ∨ valuation q 481 = true := counterClause913 (baseVal q)

theorem counterClause914 (q : Nat → Bool) : valuationOf q 419 = false ∨ valuationOf q 479 = false ∨ valuationOf q 482 = true := by
  have hs : count481 q = (countLit q [184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) + (countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) := List.countP_append (p := literal q) (l₁ := [184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) (l₂ := [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244])
  have hm := merge_two (literal (valuationOf q) (419)) (literal (valuationOf q) (479)) (literal (valuationOf q) (482)) (countLit q [184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) (countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) (count481 q) 1 1 (meaning419 q) (meaning479 q) (meaning482 q) hs
  change valuationOf q 419 = false ∨ valuationOf q 479 = false ∨ valuationOf q 482 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause914 (q : Snake 81) (h : Conditions q) : valuation q 419 = false ∨ valuation q 479 = false ∨ valuation q 482 = true := counterClause914 (baseVal q)

theorem counterClause915 (q : Nat → Bool) : valuationOf q 420 = false ∨ valuationOf q 482 = true := by
  have hs : count481 q = (countLit q [184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) + (countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) := List.countP_append (p := literal q) (l₁ := [184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) (l₂ := [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244])
  have hm := merge_left (literal (valuationOf q) (420)) (literal (valuationOf q) (482)) (countLit q [184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) (countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) (count481 q) 2 (meaning420 q) (meaning482 q) hs
  change valuationOf q 420 = false ∨ valuationOf q 482 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause915 (q : Snake 81) (h : Conditions q) : valuation q 420 = false ∨ valuation q 482 = true := counterClause915 (baseVal q)

theorem counterClause916 (q : Nat → Bool) : valuationOf q 482 = false ∨ valuationOf q 484 = true := by
  have hs : count483 q = (countLit q [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183]) + (countLit q [184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) := List.countP_append (p := literal q) (l₁ := [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183]) (l₂ := [184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244])
  have hm := merge_right (literal (valuationOf q) (482)) (literal (valuationOf q) (484)) (countLit q [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183]) (countLit q [184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) (count483 q) 2 (meaning482 q) (meaning484 q) hs
  change valuationOf q 482 = false ∨ valuationOf q 484 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause916 (q : Snake 81) (h : Conditions q) : valuation q 482 = false ∨ valuation q 484 = true := counterClause916 (baseVal q)

theorem counterClause917 (q : Nat → Bool) : valuationOf q 361 = false ∨ valuationOf q 481 = false ∨ valuationOf q 484 = true := by
  have hs : count483 q = (countLit q [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183]) + (countLit q [184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) := List.countP_append (p := literal q) (l₁ := [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183]) (l₂ := [184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244])
  have hm := merge_two (literal (valuationOf q) (361)) (literal (valuationOf q) (481)) (literal (valuationOf q) (484)) (countLit q [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183]) (countLit q [184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) (count483 q) 1 1 (meaning361 q) (meaning481 q) (meaning484 q) hs
  change valuationOf q 361 = false ∨ valuationOf q 481 = false ∨ valuationOf q 484 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause917 (q : Snake 81) (h : Conditions q) : valuation q 361 = false ∨ valuation q 481 = false ∨ valuation q 484 = true := counterClause917 (baseVal q)

theorem counterClause918 (q : Nat → Bool) : valuationOf q 362 = false ∨ valuationOf q 484 = true := by
  have hs : count483 q = (countLit q [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183]) + (countLit q [184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) := List.countP_append (p := literal q) (l₁ := [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183]) (l₂ := [184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244])
  have hm := merge_left (literal (valuationOf q) (362)) (literal (valuationOf q) (484)) (countLit q [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183]) (countLit q [184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) (count483 q) 2 (meaning362 q) (meaning484 q) hs
  change valuationOf q 362 = false ∨ valuationOf q 484 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause918 (q : Snake 81) (h : Conditions q) : valuation q 362 = false ∨ valuation q 484 = true := counterClause918 (baseVal q)

theorem clause919 (q : Snake 81) (h : Conditions q) : valuation q 484 = false := by
  rw [value484]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count483 (baseVal q) = (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := other_count_bound q h
  rw [he]
  omega

theorem clause920 (q : Snake 81) (h : Conditions q) : valuation q 123 = true ∨ valuation q 124 = true ∨ valuation q 125 = true ∨ valuation q 126 = true ∨ valuation q 127 = true ∨ valuation q 128 = true ∨ valuation q 129 = true ∨ valuation q 130 = true ∨ valuation q 131 = true ∨ valuation q 132 = true ∨ valuation q 133 = true ∨ valuation q 134 = true ∨ valuation q 135 = true ∨ valuation q 136 = true ∨ valuation q 137 = true ∨ valuation q 138 = true ∨ valuation q 139 = true ∨ valuation q 140 = true ∨ valuation q 141 = true ∨ valuation q 142 = true ∨ valuation q 143 = true ∨ valuation q 144 = true ∨ valuation q 145 = true ∨ valuation q 146 = true ∨ valuation q 147 = true ∨ valuation q 148 = true ∨ valuation q 149 = true ∨ valuation q 150 = true ∨ valuation q 151 = true ∨ valuation q 152 = true ∨ valuation q 153 = true ∨ valuation q 154 = true ∨ valuation q 155 = true ∨ valuation q 156 = true ∨ valuation q 157 = true ∨ valuation q 158 = true ∨ valuation q 159 = true ∨ valuation q 160 = true ∨ valuation q 161 = true ∨ valuation q 162 = true ∨ valuation q 163 = true ∨ valuation q 164 = true ∨ valuation q 165 = true ∨ valuation q 166 = true ∨ valuation q 167 = true ∨ valuation q 168 = true ∨ valuation q 170 = true ∨ valuation q 171 = true ∨ valuation q 172 = true ∨ valuation q 173 = true ∨ valuation q 174 = true ∨ valuation q 175 = true ∨ valuation q 176 = true ∨ valuation q 177 = true ∨ valuation q 178 = true ∨ valuation q 179 = true ∨ valuation q 180 = true ∨ valuation q 181 = true ∨ valuation q 182 = true ∨ valuation q 183 = true ∨ valuation q 184 = true ∨ valuation q 185 = true ∨ valuation q 186 = true ∨ valuation q 187 = true ∨ valuation q 188 = true ∨ valuation q 189 = true ∨ valuation q 190 = true ∨ valuation q 191 = true ∨ valuation q 192 = true ∨ valuation q 193 = true ∨ valuation q 194 = true ∨ valuation q 195 = true ∨ valuation q 196 = true ∨ valuation q 197 = true ∨ valuation q 198 = true ∨ valuation q 199 = true ∨ valuation q 200 = true ∨ valuation q 201 = true ∨ valuation q 202 = true ∨ valuation q 203 = true ∨ valuation q 204 = true ∨ valuation q 205 = true ∨ valuation q 206 = true ∨ valuation q 207 = true ∨ valuation q 208 = true ∨ valuation q 209 = true ∨ valuation q 210 = true ∨ valuation q 211 = true ∨ valuation q 212 = true ∨ valuation q 213 = true ∨ valuation q 214 = true ∨ valuation q 215 = true ∨ valuation q 216 = true ∨ valuation q 217 = true ∨ valuation q 218 = true ∨ valuation q 219 = true ∨ valuation q 220 = true ∨ valuation q 221 = true ∨ valuation q 222 = true ∨ valuation q 223 = true ∨ valuation q 224 = true ∨ valuation q 225 = true ∨ valuation q 226 = true ∨ valuation q 227 = true ∨ valuation q 228 = true ∨ valuation q 229 = true ∨ valuation q 230 = true ∨ valuation q 231 = true ∨ valuation q 232 = true ∨ valuation q 233 = true ∨ valuation q 234 = true ∨ valuation q 235 = true ∨ valuation q 236 = true ∨ valuation q 237 = true ∨ valuation q 238 = true ∨ valuation q 239 = true ∨ valuation q 240 = true ∨ valuation q 241 = true ∨ valuation q 242 = true ∨ valuation q 243 = true ∨ valuation q 244 = true := by
  rw [value123, value124, value125, value126, value127, value128, value129, value130, value131, value132, value133, value134, value135, value136, value137, value138, value139, value140, value141, value142, value143, value144, value145, value146, value147, value148, value149, value150, value151, value152, value153, value154, value155, value156, value157, value158, value159, value160, value161, value162, value163, value164, value165, value166, value167, value168, value170, value171, value172, value173, value174, value175, value176, value177, value178, value179, value180, value181, value182, value183, value184, value185, value186, value187, value188, value189, value190, value191, value192, value193, value194, value195, value196, value197, value198, value199, value200, value201, value202, value203, value204, value205, value206, value207, value208, value209, value210, value211, value212, value213, value214, value215, value216, value217, value218, value219, value220, value221, value222, value223, value224, value225, value226, value227, value228, value229, value230, value231, value232, value233, value234, value235, value236, value237, value238, value239, value240, value241, value242, value243, value244]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hg := other_endpoint q others (fun v hv hn => others_mem v (h.covered v hv) (by simpa only [h.head_fixed] using hn))
  simpa only [others, List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem counterClause921 (q : Nat → Bool) : valuationOf q 5 = true ∨ valuationOf q 1501 = true := by
  have hs : count1501 q = (countLit q [-5]) + (countLit q [-8]) := List.countP_append (p := literal q) (l₁ := [-5]) (l₂ := [-8])
  have hm := merge_left (literal (valuationOf q) (-5)) (literal (valuationOf q) (1501)) (countLit q [-5]) (countLit q [-8]) (count1501 q) 1 (meaningNeg5 q) (meaning1501 q) hs
  change (! (valuationOf q 5)) = false ∨ valuationOf q 1501 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause921 (q : Snake 81) (h : Conditions q) : valuation q 5 = true ∨ valuation q 1501 = true := counterClause921 (baseVal q)

theorem counterClause922 (q : Nat → Bool) : valuationOf q 5 = true ∨ valuationOf q 8 = true ∨ valuationOf q 1502 = true := by
  have hs : count1501 q = (countLit q [-5]) + (countLit q [-8]) := List.countP_append (p := literal q) (l₁ := [-5]) (l₂ := [-8])
  have hm := merge_two (literal (valuationOf q) (-5)) (literal (valuationOf q) (-8)) (literal (valuationOf q) (1502)) (countLit q [-5]) (countLit q [-8]) (count1501 q) 1 1 (meaningNeg5 q) (meaningNeg8 q) (meaning1502 q) hs
  change (! (valuationOf q 5)) = false ∨ (! (valuationOf q 8)) = false ∨ valuationOf q 1502 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause922 (q : Snake 81) (h : Conditions q) : valuation q 5 = true ∨ valuation q 8 = true ∨ valuation q 1502 = true := counterClause922 (baseVal q)

theorem counterClause923 (q : Nat → Bool) : valuationOf q 1501 = false ∨ valuationOf q 1503 = true := by
  have hs : count1503 q = (countLit q [-2]) + (countLit q [-5, -8]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-5, -8])
  have hm := merge_right (literal (valuationOf q) (1501)) (literal (valuationOf q) (1503)) (countLit q [-2]) (countLit q [-5, -8]) (count1503 q) 1 (meaning1501 q) (meaning1503 q) hs
  change valuationOf q 1501 = false ∨ valuationOf q 1503 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause923 (q : Snake 81) (h : Conditions q) : valuation q 1501 = false ∨ valuation q 1503 = true := counterClause923 (baseVal q)

theorem counterClause924 (q : Nat → Bool) : valuationOf q 1502 = false ∨ valuationOf q 1504 = true := by
  have hs : count1503 q = (countLit q [-2]) + (countLit q [-5, -8]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-5, -8])
  have hm := merge_right (literal (valuationOf q) (1502)) (literal (valuationOf q) (1504)) (countLit q [-2]) (countLit q [-5, -8]) (count1503 q) 2 (meaning1502 q) (meaning1504 q) hs
  change valuationOf q 1502 = false ∨ valuationOf q 1504 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause924 (q : Snake 81) (h : Conditions q) : valuation q 1502 = false ∨ valuation q 1504 = true := counterClause924 (baseVal q)

theorem counterClause925 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1501 = false ∨ valuationOf q 1504 = true := by
  have hs : count1503 q = (countLit q [-2]) + (countLit q [-5, -8]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-5, -8])
  have hm := merge_two (literal (valuationOf q) (-2)) (literal (valuationOf q) (1501)) (literal (valuationOf q) (1504)) (countLit q [-2]) (countLit q [-5, -8]) (count1503 q) 1 1 (meaningNeg2 q) (meaning1501 q) (meaning1504 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1501 = false ∨ valuationOf q 1504 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause925 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1501 = false ∨ valuation q 1504 = true := counterClause925 (baseVal q)

theorem counterClause926 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1502 = false ∨ valuationOf q 1505 = true := by
  have hs : count1503 q = (countLit q [-2]) + (countLit q [-5, -8]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-5, -8])
  have hm := merge_two (literal (valuationOf q) (-2)) (literal (valuationOf q) (1502)) (literal (valuationOf q) (1505)) (countLit q [-2]) (countLit q [-5, -8]) (count1503 q) 1 2 (meaningNeg2 q) (meaning1502 q) (meaning1505 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1502 = false ∨ valuationOf q 1505 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause926 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1502 = false ∨ valuation q 1505 = true := counterClause926 (baseVal q)

theorem counterClause927 (q : Nat → Bool) : valuationOf q 13 = true ∨ valuationOf q 1506 = true := by
  have hs : count1506 q = (countLit q [-12]) + (countLit q [-13]) := List.countP_append (p := literal q) (l₁ := [-12]) (l₂ := [-13])
  have hm := merge_right (literal (valuationOf q) (-13)) (literal (valuationOf q) (1506)) (countLit q [-12]) (countLit q [-13]) (count1506 q) 1 (meaningNeg13 q) (meaning1506 q) hs
  change (! (valuationOf q 13)) = false ∨ valuationOf q 1506 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause927 (q : Snake 81) (h : Conditions q) : valuation q 13 = true ∨ valuation q 1506 = true := counterClause927 (baseVal q)

theorem counterClause928 (q : Nat → Bool) : valuationOf q 12 = true ∨ valuationOf q 1506 = true := by
  have hs : count1506 q = (countLit q [-12]) + (countLit q [-13]) := List.countP_append (p := literal q) (l₁ := [-12]) (l₂ := [-13])
  have hm := merge_left (literal (valuationOf q) (-12)) (literal (valuationOf q) (1506)) (countLit q [-12]) (countLit q [-13]) (count1506 q) 1 (meaningNeg12 q) (meaning1506 q) hs
  change (! (valuationOf q 12)) = false ∨ valuationOf q 1506 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause928 (q : Snake 81) (h : Conditions q) : valuation q 12 = true ∨ valuation q 1506 = true := counterClause928 (baseVal q)

theorem block28 (q : Snake 81) (h : Conditions q) : B112E258.Block28 (valuation q) :=
  ⟨clause897 q h, clause898 q h, clause899 q h, clause900 q h, clause901 q h, clause902 q h, clause903 q h, clause904 q h, clause905 q h, clause906 q h, clause907 q h, clause908 q h, clause909 q h, clause910 q h, clause911 q h, clause912 q h, clause913 q h, clause914 q h, clause915 q h, clause916 q h, clause917 q h, clause918 q h, clause919 q h, clause920 q h, clause921 q h, clause922 q h, clause923 q h, clause924 q h, clause925 q h, clause926 q h, clause927 q h, clause928 q h⟩

end
end Snake9.Regrowth.E112258
