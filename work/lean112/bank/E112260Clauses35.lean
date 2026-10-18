import E112260Semantics
import B112E260Inputs
namespace Snake9.Regrowth.E112260
noncomputable section
local instance blockDec35 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1121 (q : Nat → Bool) : valuationOf q 494 = false ∨ valuationOf q 496 = true := by
  have hs : count495 q = (countLit q [247, 248, 249, 250]) + (countLit q [251, 252, 253, 254]) := List.countP_append (p := literal q) (l₁ := [247, 248, 249, 250]) (l₂ := [251, 252, 253, 254])
  have hm := merge_right (literal (valuationOf q) (494)) (literal (valuationOf q) (496)) (countLit q [247, 248, 249, 250]) (countLit q [251, 252, 253, 254]) (count495 q) 2 (meaning494 q) (meaning496 q) hs
  change valuationOf q 494 = false ∨ valuationOf q 496 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1121 (q : Snake 81) (h : Conditions q) : valuation q 494 = false ∨ valuation q 496 = true := counterClause1121 (baseVal q)

theorem counterClause1122 (q : Nat → Bool) : valuationOf q 487 = false ∨ valuationOf q 495 = true := by
  have hs : count495 q = (countLit q [247, 248, 249, 250]) + (countLit q [251, 252, 253, 254]) := List.countP_append (p := literal q) (l₁ := [247, 248, 249, 250]) (l₂ := [251, 252, 253, 254])
  have hm := merge_left (literal (valuationOf q) (487)) (literal (valuationOf q) (495)) (countLit q [247, 248, 249, 250]) (countLit q [251, 252, 253, 254]) (count495 q) 1 (meaning487 q) (meaning495 q) hs
  change valuationOf q 487 = false ∨ valuationOf q 495 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1122 (q : Snake 81) (h : Conditions q) : valuation q 487 = false ∨ valuation q 495 = true := counterClause1122 (baseVal q)

theorem counterClause1123 (q : Nat → Bool) : valuationOf q 487 = false ∨ valuationOf q 493 = false ∨ valuationOf q 496 = true := by
  have hs : count495 q = (countLit q [247, 248, 249, 250]) + (countLit q [251, 252, 253, 254]) := List.countP_append (p := literal q) (l₁ := [247, 248, 249, 250]) (l₂ := [251, 252, 253, 254])
  have hm := merge_two (literal (valuationOf q) (487)) (literal (valuationOf q) (493)) (literal (valuationOf q) (496)) (countLit q [247, 248, 249, 250]) (countLit q [251, 252, 253, 254]) (count495 q) 1 1 (meaning487 q) (meaning493 q) (meaning496 q) hs
  change valuationOf q 487 = false ∨ valuationOf q 493 = false ∨ valuationOf q 496 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1123 (q : Snake 81) (h : Conditions q) : valuation q 487 = false ∨ valuation q 493 = false ∨ valuation q 496 = true := counterClause1123 (baseVal q)

theorem counterClause1124 (q : Nat → Bool) : valuationOf q 495 = false ∨ valuationOf q 497 = true := by
  have hs : count497 q = (countLit q [239, 240, 241, 242, 243, 244, 245, 246]) + (countLit q [247, 248, 249, 250, 251, 252, 253, 254]) := List.countP_append (p := literal q) (l₁ := [239, 240, 241, 242, 243, 244, 245, 246]) (l₂ := [247, 248, 249, 250, 251, 252, 253, 254])
  have hm := merge_right (literal (valuationOf q) (495)) (literal (valuationOf q) (497)) (countLit q [239, 240, 241, 242, 243, 244, 245, 246]) (countLit q [247, 248, 249, 250, 251, 252, 253, 254]) (count497 q) 1 (meaning495 q) (meaning497 q) hs
  change valuationOf q 495 = false ∨ valuationOf q 497 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1124 (q : Snake 81) (h : Conditions q) : valuation q 495 = false ∨ valuation q 497 = true := counterClause1124 (baseVal q)

theorem counterClause1125 (q : Nat → Bool) : valuationOf q 496 = false ∨ valuationOf q 498 = true := by
  have hs : count497 q = (countLit q [239, 240, 241, 242, 243, 244, 245, 246]) + (countLit q [247, 248, 249, 250, 251, 252, 253, 254]) := List.countP_append (p := literal q) (l₁ := [239, 240, 241, 242, 243, 244, 245, 246]) (l₂ := [247, 248, 249, 250, 251, 252, 253, 254])
  have hm := merge_right (literal (valuationOf q) (496)) (literal (valuationOf q) (498)) (countLit q [239, 240, 241, 242, 243, 244, 245, 246]) (countLit q [247, 248, 249, 250, 251, 252, 253, 254]) (count497 q) 2 (meaning496 q) (meaning498 q) hs
  change valuationOf q 496 = false ∨ valuationOf q 498 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1125 (q : Snake 81) (h : Conditions q) : valuation q 496 = false ∨ valuation q 498 = true := counterClause1125 (baseVal q)

theorem counterClause1126 (q : Nat → Bool) : valuationOf q 481 = false ∨ valuationOf q 497 = true := by
  have hs : count497 q = (countLit q [239, 240, 241, 242, 243, 244, 245, 246]) + (countLit q [247, 248, 249, 250, 251, 252, 253, 254]) := List.countP_append (p := literal q) (l₁ := [239, 240, 241, 242, 243, 244, 245, 246]) (l₂ := [247, 248, 249, 250, 251, 252, 253, 254])
  have hm := merge_left (literal (valuationOf q) (481)) (literal (valuationOf q) (497)) (countLit q [239, 240, 241, 242, 243, 244, 245, 246]) (countLit q [247, 248, 249, 250, 251, 252, 253, 254]) (count497 q) 1 (meaning481 q) (meaning497 q) hs
  change valuationOf q 481 = false ∨ valuationOf q 497 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1126 (q : Snake 81) (h : Conditions q) : valuation q 481 = false ∨ valuation q 497 = true := counterClause1126 (baseVal q)

theorem counterClause1127 (q : Nat → Bool) : valuationOf q 481 = false ∨ valuationOf q 495 = false ∨ valuationOf q 498 = true := by
  have hs : count497 q = (countLit q [239, 240, 241, 242, 243, 244, 245, 246]) + (countLit q [247, 248, 249, 250, 251, 252, 253, 254]) := List.countP_append (p := literal q) (l₁ := [239, 240, 241, 242, 243, 244, 245, 246]) (l₂ := [247, 248, 249, 250, 251, 252, 253, 254])
  have hm := merge_two (literal (valuationOf q) (481)) (literal (valuationOf q) (495)) (literal (valuationOf q) (498)) (countLit q [239, 240, 241, 242, 243, 244, 245, 246]) (countLit q [247, 248, 249, 250, 251, 252, 253, 254]) (count497 q) 1 1 (meaning481 q) (meaning495 q) (meaning498 q) hs
  change valuationOf q 481 = false ∨ valuationOf q 495 = false ∨ valuationOf q 498 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1127 (q : Snake 81) (h : Conditions q) : valuation q 481 = false ∨ valuation q 495 = false ∨ valuation q 498 = true := counterClause1127 (baseVal q)

theorem counterClause1128 (q : Nat → Bool) : valuationOf q 482 = false ∨ valuationOf q 498 = true := by
  have hs : count497 q = (countLit q [239, 240, 241, 242, 243, 244, 245, 246]) + (countLit q [247, 248, 249, 250, 251, 252, 253, 254]) := List.countP_append (p := literal q) (l₁ := [239, 240, 241, 242, 243, 244, 245, 246]) (l₂ := [247, 248, 249, 250, 251, 252, 253, 254])
  have hm := merge_left (literal (valuationOf q) (482)) (literal (valuationOf q) (498)) (countLit q [239, 240, 241, 242, 243, 244, 245, 246]) (countLit q [247, 248, 249, 250, 251, 252, 253, 254]) (count497 q) 2 (meaning482 q) (meaning498 q) hs
  change valuationOf q 482 = false ∨ valuationOf q 498 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1128 (q : Snake 81) (h : Conditions q) : valuation q 482 = false ∨ valuation q 498 = true := counterClause1128 (baseVal q)

theorem counterClause1129 (q : Nat → Bool) : valuationOf q 497 = false ∨ valuationOf q 499 = true := by
  have hs : count499 q = (countLit q [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]) + (countLit q [239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]) := List.countP_append (p := literal q) (l₁ := [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]) (l₂ := [239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254])
  have hm := merge_right (literal (valuationOf q) (497)) (literal (valuationOf q) (499)) (countLit q [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]) (countLit q [239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]) (count499 q) 1 (meaning497 q) (meaning499 q) hs
  change valuationOf q 497 = false ∨ valuationOf q 499 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1129 (q : Snake 81) (h : Conditions q) : valuation q 497 = false ∨ valuation q 499 = true := counterClause1129 (baseVal q)

theorem counterClause1130 (q : Nat → Bool) : valuationOf q 498 = false ∨ valuationOf q 500 = true := by
  have hs : count499 q = (countLit q [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]) + (countLit q [239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]) := List.countP_append (p := literal q) (l₁ := [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]) (l₂ := [239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254])
  have hm := merge_right (literal (valuationOf q) (498)) (literal (valuationOf q) (500)) (countLit q [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]) (countLit q [239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]) (count499 q) 2 (meaning498 q) (meaning500 q) hs
  change valuationOf q 498 = false ∨ valuationOf q 500 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1130 (q : Snake 81) (h : Conditions q) : valuation q 498 = false ∨ valuation q 500 = true := counterClause1130 (baseVal q)

theorem counterClause1131 (q : Nat → Bool) : valuationOf q 467 = false ∨ valuationOf q 499 = true := by
  have hs : count499 q = (countLit q [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]) + (countLit q [239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]) := List.countP_append (p := literal q) (l₁ := [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]) (l₂ := [239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254])
  have hm := merge_left (literal (valuationOf q) (467)) (literal (valuationOf q) (499)) (countLit q [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]) (countLit q [239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]) (count499 q) 1 (meaning467 q) (meaning499 q) hs
  change valuationOf q 467 = false ∨ valuationOf q 499 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1131 (q : Snake 81) (h : Conditions q) : valuation q 467 = false ∨ valuation q 499 = true := counterClause1131 (baseVal q)

theorem counterClause1132 (q : Nat → Bool) : valuationOf q 467 = false ∨ valuationOf q 497 = false ∨ valuationOf q 500 = true := by
  have hs : count499 q = (countLit q [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]) + (countLit q [239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]) := List.countP_append (p := literal q) (l₁ := [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]) (l₂ := [239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254])
  have hm := merge_two (literal (valuationOf q) (467)) (literal (valuationOf q) (497)) (literal (valuationOf q) (500)) (countLit q [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]) (countLit q [239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]) (count499 q) 1 1 (meaning467 q) (meaning497 q) (meaning500 q) hs
  change valuationOf q 467 = false ∨ valuationOf q 497 = false ∨ valuationOf q 500 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1132 (q : Snake 81) (h : Conditions q) : valuation q 467 = false ∨ valuation q 497 = false ∨ valuation q 500 = true := counterClause1132 (baseVal q)

theorem counterClause1133 (q : Nat → Bool) : valuationOf q 468 = false ∨ valuationOf q 500 = true := by
  have hs : count499 q = (countLit q [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]) + (countLit q [239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]) := List.countP_append (p := literal q) (l₁ := [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]) (l₂ := [239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254])
  have hm := merge_left (literal (valuationOf q) (468)) (literal (valuationOf q) (500)) (countLit q [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]) (countLit q [239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]) (count499 q) 2 (meaning468 q) (meaning500 q) hs
  change valuationOf q 468 = false ∨ valuationOf q 500 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1133 (q : Snake 81) (h : Conditions q) : valuation q 468 = false ∨ valuation q 500 = true := counterClause1133 (baseVal q)

theorem counterClause1134 (q : Nat → Bool) : valuationOf q 499 = false ∨ valuationOf q 501 = true := by
  have hs : count501 q = (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) + (countLit q [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]) := List.countP_append (p := literal q) (l₁ := [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) (l₂ := [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254])
  have hm := merge_right (literal (valuationOf q) (499)) (literal (valuationOf q) (501)) (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) (countLit q [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]) (count501 q) 1 (meaning499 q) (meaning501 q) hs
  change valuationOf q 499 = false ∨ valuationOf q 501 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1134 (q : Snake 81) (h : Conditions q) : valuation q 499 = false ∨ valuation q 501 = true := counterClause1134 (baseVal q)

theorem counterClause1135 (q : Nat → Bool) : valuationOf q 500 = false ∨ valuationOf q 502 = true := by
  have hs : count501 q = (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) + (countLit q [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]) := List.countP_append (p := literal q) (l₁ := [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) (l₂ := [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254])
  have hm := merge_right (literal (valuationOf q) (500)) (literal (valuationOf q) (502)) (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) (countLit q [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]) (count501 q) 2 (meaning500 q) (meaning502 q) hs
  change valuationOf q 500 = false ∨ valuationOf q 502 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1135 (q : Snake 81) (h : Conditions q) : valuation q 500 = false ∨ valuation q 502 = true := counterClause1135 (baseVal q)

theorem counterClause1136 (q : Nat → Bool) : valuationOf q 437 = false ∨ valuationOf q 501 = true := by
  have hs : count501 q = (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) + (countLit q [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]) := List.countP_append (p := literal q) (l₁ := [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) (l₂ := [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254])
  have hm := merge_left (literal (valuationOf q) (437)) (literal (valuationOf q) (501)) (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) (countLit q [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]) (count501 q) 1 (meaning437 q) (meaning501 q) hs
  change valuationOf q 437 = false ∨ valuationOf q 501 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1136 (q : Snake 81) (h : Conditions q) : valuation q 437 = false ∨ valuation q 501 = true := counterClause1136 (baseVal q)

theorem counterClause1137 (q : Nat → Bool) : valuationOf q 437 = false ∨ valuationOf q 499 = false ∨ valuationOf q 502 = true := by
  have hs : count501 q = (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) + (countLit q [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]) := List.countP_append (p := literal q) (l₁ := [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) (l₂ := [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254])
  have hm := merge_two (literal (valuationOf q) (437)) (literal (valuationOf q) (499)) (literal (valuationOf q) (502)) (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) (countLit q [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]) (count501 q) 1 1 (meaning437 q) (meaning499 q) (meaning502 q) hs
  change valuationOf q 437 = false ∨ valuationOf q 499 = false ∨ valuationOf q 502 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1137 (q : Snake 81) (h : Conditions q) : valuation q 437 = false ∨ valuation q 499 = false ∨ valuation q 502 = true := counterClause1137 (baseVal q)

theorem counterClause1138 (q : Nat → Bool) : valuationOf q 438 = false ∨ valuationOf q 502 = true := by
  have hs : count501 q = (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) + (countLit q [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]) := List.countP_append (p := literal q) (l₁ := [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) (l₂ := [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254])
  have hm := merge_left (literal (valuationOf q) (438)) (literal (valuationOf q) (502)) (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) (countLit q [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]) (count501 q) 2 (meaning438 q) (meaning502 q) hs
  change valuationOf q 438 = false ∨ valuationOf q 502 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1138 (q : Snake 81) (h : Conditions q) : valuation q 438 = false ∨ valuation q 502 = true := counterClause1138 (baseVal q)

theorem counterClause1139 (q : Nat → Bool) : valuationOf q 502 = false ∨ valuationOf q 504 = true := by
  have hs : count503 q = (countLit q [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) + (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]) := List.countP_append (p := literal q) (l₁ := [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) (l₂ := [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254])
  have hm := merge_right (literal (valuationOf q) (502)) (literal (valuationOf q) (504)) (countLit q [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]) (count503 q) 2 (meaning502 q) (meaning504 q) hs
  change valuationOf q 502 = false ∨ valuationOf q 504 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1139 (q : Snake 81) (h : Conditions q) : valuation q 502 = false ∨ valuation q 504 = true := counterClause1139 (baseVal q)

theorem counterClause1140 (q : Nat → Bool) : valuationOf q 377 = false ∨ valuationOf q 501 = false ∨ valuationOf q 504 = true := by
  have hs : count503 q = (countLit q [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) + (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]) := List.countP_append (p := literal q) (l₁ := [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) (l₂ := [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254])
  have hm := merge_two (literal (valuationOf q) (377)) (literal (valuationOf q) (501)) (literal (valuationOf q) (504)) (countLit q [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]) (count503 q) 1 1 (meaning377 q) (meaning501 q) (meaning504 q) hs
  change valuationOf q 377 = false ∨ valuationOf q 501 = false ∨ valuationOf q 504 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1140 (q : Snake 81) (h : Conditions q) : valuation q 377 = false ∨ valuation q 501 = false ∨ valuation q 504 = true := counterClause1140 (baseVal q)

theorem counterClause1141 (q : Nat → Bool) : valuationOf q 378 = false ∨ valuationOf q 504 = true := by
  have hs : count503 q = (countLit q [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) + (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]) := List.countP_append (p := literal q) (l₁ := [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) (l₂ := [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254])
  have hm := merge_left (literal (valuationOf q) (378)) (literal (valuationOf q) (504)) (countLit q [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]) (count503 q) 2 (meaning378 q) (meaning504 q) hs
  change valuationOf q 378 = false ∨ valuationOf q 504 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1141 (q : Snake 81) (h : Conditions q) : valuation q 378 = false ∨ valuation q 504 = true := counterClause1141 (baseVal q)

theorem clause1142 (q : Snake 81) (h : Conditions q) : valuation q 504 = false := by
  rw [value504]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count503 (baseVal q) = (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := other_count_bound q h
  rw [he]
  omega

theorem clause1143 (q : Snake 81) (h : Conditions q) : valuation q 128 = true ∨ valuation q 129 = true ∨ valuation q 130 = true ∨ valuation q 131 = true ∨ valuation q 132 = true ∨ valuation q 133 = true ∨ valuation q 134 = true ∨ valuation q 135 = true ∨ valuation q 136 = true ∨ valuation q 137 = true ∨ valuation q 138 = true ∨ valuation q 139 = true ∨ valuation q 140 = true ∨ valuation q 141 = true ∨ valuation q 142 = true ∨ valuation q 143 = true ∨ valuation q 144 = true ∨ valuation q 145 = true ∨ valuation q 146 = true ∨ valuation q 147 = true ∨ valuation q 148 = true ∨ valuation q 149 = true ∨ valuation q 150 = true ∨ valuation q 151 = true ∨ valuation q 152 = true ∨ valuation q 153 = true ∨ valuation q 154 = true ∨ valuation q 155 = true ∨ valuation q 156 = true ∨ valuation q 157 = true ∨ valuation q 158 = true ∨ valuation q 159 = true ∨ valuation q 160 = true ∨ valuation q 161 = true ∨ valuation q 162 = true ∨ valuation q 163 = true ∨ valuation q 164 = true ∨ valuation q 165 = true ∨ valuation q 166 = true ∨ valuation q 167 = true ∨ valuation q 168 = true ∨ valuation q 169 = true ∨ valuation q 170 = true ∨ valuation q 171 = true ∨ valuation q 172 = true ∨ valuation q 173 = true ∨ valuation q 174 = true ∨ valuation q 175 = true ∨ valuation q 176 = true ∨ valuation q 177 = true ∨ valuation q 178 = true ∨ valuation q 179 = true ∨ valuation q 180 = true ∨ valuation q 181 = true ∨ valuation q 182 = true ∨ valuation q 183 = true ∨ valuation q 184 = true ∨ valuation q 185 = true ∨ valuation q 186 = true ∨ valuation q 187 = true ∨ valuation q 188 = true ∨ valuation q 189 = true ∨ valuation q 190 = true ∨ valuation q 191 = true ∨ valuation q 192 = true ∨ valuation q 193 = true ∨ valuation q 194 = true ∨ valuation q 195 = true ∨ valuation q 196 = true ∨ valuation q 197 = true ∨ valuation q 198 = true ∨ valuation q 199 = true ∨ valuation q 200 = true ∨ valuation q 201 = true ∨ valuation q 202 = true ∨ valuation q 203 = true ∨ valuation q 204 = true ∨ valuation q 205 = true ∨ valuation q 206 = true ∨ valuation q 207 = true ∨ valuation q 208 = true ∨ valuation q 209 = true ∨ valuation q 210 = true ∨ valuation q 212 = true ∨ valuation q 213 = true ∨ valuation q 214 = true ∨ valuation q 215 = true ∨ valuation q 216 = true ∨ valuation q 217 = true ∨ valuation q 218 = true ∨ valuation q 219 = true ∨ valuation q 220 = true ∨ valuation q 221 = true ∨ valuation q 222 = true ∨ valuation q 223 = true ∨ valuation q 224 = true ∨ valuation q 225 = true ∨ valuation q 226 = true ∨ valuation q 227 = true ∨ valuation q 228 = true ∨ valuation q 229 = true ∨ valuation q 230 = true ∨ valuation q 231 = true ∨ valuation q 232 = true ∨ valuation q 233 = true ∨ valuation q 234 = true ∨ valuation q 235 = true ∨ valuation q 236 = true ∨ valuation q 237 = true ∨ valuation q 238 = true ∨ valuation q 239 = true ∨ valuation q 240 = true ∨ valuation q 241 = true ∨ valuation q 242 = true ∨ valuation q 243 = true ∨ valuation q 244 = true ∨ valuation q 245 = true ∨ valuation q 246 = true ∨ valuation q 247 = true ∨ valuation q 248 = true ∨ valuation q 249 = true ∨ valuation q 250 = true ∨ valuation q 251 = true ∨ valuation q 252 = true ∨ valuation q 253 = true ∨ valuation q 254 = true := by
  rw [value128, value129, value130, value131, value132, value133, value134, value135, value136, value137, value138, value139, value140, value141, value142, value143, value144, value145, value146, value147, value148, value149, value150, value151, value152, value153, value154, value155, value156, value157, value158, value159, value160, value161, value162, value163, value164, value165, value166, value167, value168, value169, value170, value171, value172, value173, value174, value175, value176, value177, value178, value179, value180, value181, value182, value183, value184, value185, value186, value187, value188, value189, value190, value191, value192, value193, value194, value195, value196, value197, value198, value199, value200, value201, value202, value203, value204, value205, value206, value207, value208, value209, value210, value212, value213, value214, value215, value216, value217, value218, value219, value220, value221, value222, value223, value224, value225, value226, value227, value228, value229, value230, value231, value232, value233, value234, value235, value236, value237, value238, value239, value240, value241, value242, value243, value244, value245, value246, value247, value248, value249, value250, value251, value252, value253, value254]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hg := other_endpoint q others (fun v hv hn => others_mem v (h.covered v hv) (by simpa only [h.head_fixed] using hn))
  simpa only [others, List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem counterClause1144 (q : Nat → Bool) : valuationOf q 5 = true ∨ valuationOf q 849 = true := by
  have hs : count849 q = (countLit q [-2]) + (countLit q [-5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-5])
  have hm := merge_right (literal (valuationOf q) (-5)) (literal (valuationOf q) (849)) (countLit q [-2]) (countLit q [-5]) (count849 q) 1 (meaningNeg5 q) (meaning849 q) hs
  change (! (valuationOf q 5)) = false ∨ valuationOf q 849 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1144 (q : Snake 81) (h : Conditions q) : valuation q 5 = true ∨ valuation q 849 = true := counterClause1144 (baseVal q)

theorem counterClause1145 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 849 = true := by
  have hs : count849 q = (countLit q [-2]) + (countLit q [-5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-5])
  have hm := merge_left (literal (valuationOf q) (-2)) (literal (valuationOf q) (849)) (countLit q [-2]) (countLit q [-5]) (count849 q) 1 (meaningNeg2 q) (meaning849 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 849 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1145 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 849 = true := counterClause1145 (baseVal q)

theorem counterClause1146 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 5 = true ∨ valuationOf q 850 = true := by
  have hs : count849 q = (countLit q [-2]) + (countLit q [-5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-5])
  have hm := merge_two (literal (valuationOf q) (-2)) (literal (valuationOf q) (-5)) (literal (valuationOf q) (850)) (countLit q [-2]) (countLit q [-5]) (count849 q) 1 1 (meaningNeg2 q) (meaningNeg5 q) (meaning850 q) hs
  change (! (valuationOf q 2)) = false ∨ (! (valuationOf q 5)) = false ∨ valuationOf q 850 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1146 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 5 = true ∨ valuation q 850 = true := counterClause1146 (baseVal q)

theorem counterClause1147 (q : Nat → Bool) : valuationOf q 849 = false ∨ valuationOf q 851 = true := by
  have hs : count851 q = (countLit q [-1]) + (countLit q [-2, -5]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-2, -5])
  have hm := merge_right (literal (valuationOf q) (849)) (literal (valuationOf q) (851)) (countLit q [-1]) (countLit q [-2, -5]) (count851 q) 1 (meaning849 q) (meaning851 q) hs
  change valuationOf q 849 = false ∨ valuationOf q 851 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1147 (q : Snake 81) (h : Conditions q) : valuation q 849 = false ∨ valuation q 851 = true := counterClause1147 (baseVal q)

theorem counterClause1148 (q : Nat → Bool) : valuationOf q 850 = false ∨ valuationOf q 852 = true := by
  have hs : count851 q = (countLit q [-1]) + (countLit q [-2, -5]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-2, -5])
  have hm := merge_right (literal (valuationOf q) (850)) (literal (valuationOf q) (852)) (countLit q [-1]) (countLit q [-2, -5]) (count851 q) 2 (meaning850 q) (meaning852 q) hs
  change valuationOf q 850 = false ∨ valuationOf q 852 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1148 (q : Snake 81) (h : Conditions q) : valuation q 850 = false ∨ valuation q 852 = true := counterClause1148 (baseVal q)

theorem counterClause1149 (q : Nat → Bool) : valuationOf q 1 = true ∨ valuationOf q 851 = true := by
  have hs : count851 q = (countLit q [-1]) + (countLit q [-2, -5]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-2, -5])
  have hm := merge_left (literal (valuationOf q) (-1)) (literal (valuationOf q) (851)) (countLit q [-1]) (countLit q [-2, -5]) (count851 q) 1 (meaningNeg1 q) (meaning851 q) hs
  change (! (valuationOf q 1)) = false ∨ valuationOf q 851 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1149 (q : Snake 81) (h : Conditions q) : valuation q 1 = true ∨ valuation q 851 = true := counterClause1149 (baseVal q)

theorem counterClause1150 (q : Nat → Bool) : valuationOf q 1 = true ∨ valuationOf q 849 = false ∨ valuationOf q 852 = true := by
  have hs : count851 q = (countLit q [-1]) + (countLit q [-2, -5]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-2, -5])
  have hm := merge_two (literal (valuationOf q) (-1)) (literal (valuationOf q) (849)) (literal (valuationOf q) (852)) (countLit q [-1]) (countLit q [-2, -5]) (count851 q) 1 1 (meaningNeg1 q) (meaning849 q) (meaning852 q) hs
  change (! (valuationOf q 1)) = false ∨ valuationOf q 849 = false ∨ valuationOf q 852 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1150 (q : Snake 81) (h : Conditions q) : valuation q 1 = true ∨ valuation q 849 = false ∨ valuation q 852 = true := counterClause1150 (baseVal q)

theorem counterClause1151 (q : Nat → Bool) : valuationOf q 1 = true ∨ valuationOf q 850 = false ∨ valuationOf q 853 = true := by
  have hs : count851 q = (countLit q [-1]) + (countLit q [-2, -5]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-2, -5])
  have hm := merge_two (literal (valuationOf q) (-1)) (literal (valuationOf q) (850)) (literal (valuationOf q) (853)) (countLit q [-1]) (countLit q [-2, -5]) (count851 q) 1 2 (meaningNeg1 q) (meaning850 q) (meaning853 q) hs
  change (! (valuationOf q 1)) = false ∨ valuationOf q 850 = false ∨ valuationOf q 853 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1151 (q : Snake 81) (h : Conditions q) : valuation q 1 = true ∨ valuation q 850 = false ∨ valuation q 853 = true := counterClause1151 (baseVal q)

theorem counterClause1152 (q : Nat → Bool) : valuationOf q 7 = true ∨ valuationOf q 854 = true := by
  have hs : count854 q = (countLit q [-6]) + (countLit q [-7]) := List.countP_append (p := literal q) (l₁ := [-6]) (l₂ := [-7])
  have hm := merge_right (literal (valuationOf q) (-7)) (literal (valuationOf q) (854)) (countLit q [-6]) (countLit q [-7]) (count854 q) 1 (meaningNeg7 q) (meaning854 q) hs
  change (! (valuationOf q 7)) = false ∨ valuationOf q 854 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1152 (q : Snake 81) (h : Conditions q) : valuation q 7 = true ∨ valuation q 854 = true := counterClause1152 (baseVal q)

theorem block35 (q : Snake 81) (h : Conditions q) : B112E260.Block35 (valuation q) :=
  ⟨clause1121 q h, clause1122 q h, clause1123 q h, clause1124 q h, clause1125 q h, clause1126 q h, clause1127 q h, clause1128 q h, clause1129 q h, clause1130 q h, clause1131 q h, clause1132 q h, clause1133 q h, clause1134 q h, clause1135 q h, clause1136 q h, clause1137 q h, clause1138 q h, clause1139 q h, clause1140 q h, clause1141 q h, clause1142 q h, clause1143 q h, clause1144 q h, clause1145 q h, clause1146 q h, clause1147 q h, clause1148 q h, clause1149 q h, clause1150 q h, clause1151 q h, clause1152 q h⟩

end
end Snake9.Regrowth.E112260
