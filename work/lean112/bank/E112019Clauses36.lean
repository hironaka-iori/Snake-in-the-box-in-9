import E112019Semantics
import B112E019Inputs
namespace Snake9.Regrowth.E112019
noncomputable section
local instance blockDec36 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1153 (q : Nat → Bool) : valuationOf q 469 = false ∨ valuationOf q 471 = true := by
  have hs : count471 q = (countLit q [235, 236, 237, 238]) + (countLit q [239, 240, 241, 242]) := List.countP_append (p := literal q) (l₁ := [235, 236, 237, 238]) (l₂ := [239, 240, 241, 242])
  have hm := merge_right (literal (valuationOf q) (469)) (literal (valuationOf q) (471)) (countLit q [235, 236, 237, 238]) (countLit q [239, 240, 241, 242]) (count471 q) 1 (meaning469 q) (meaning471 q) hs
  change valuationOf q 469 = false ∨ valuationOf q 471 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1153 (q : Snake 81) (h : Conditions q) : valuation q 469 = false ∨ valuation q 471 = true := counterClause1153 (baseVal q)

theorem counterClause1154 (q : Nat → Bool) : valuationOf q 463 = false ∨ valuationOf q 471 = true := by
  have hs : count471 q = (countLit q [235, 236, 237, 238]) + (countLit q [239, 240, 241, 242]) := List.countP_append (p := literal q) (l₁ := [235, 236, 237, 238]) (l₂ := [239, 240, 241, 242])
  have hm := merge_left (literal (valuationOf q) (463)) (literal (valuationOf q) (471)) (countLit q [235, 236, 237, 238]) (countLit q [239, 240, 241, 242]) (count471 q) 1 (meaning463 q) (meaning471 q) hs
  change valuationOf q 463 = false ∨ valuationOf q 471 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1154 (q : Snake 81) (h : Conditions q) : valuation q 463 = false ∨ valuation q 471 = true := counterClause1154 (baseVal q)

theorem counterClause1155 (q : Nat → Bool) : valuationOf q 463 = false ∨ valuationOf q 469 = false ∨ valuationOf q 472 = true := by
  have hs : count471 q = (countLit q [235, 236, 237, 238]) + (countLit q [239, 240, 241, 242]) := List.countP_append (p := literal q) (l₁ := [235, 236, 237, 238]) (l₂ := [239, 240, 241, 242])
  have hm := merge_two (literal (valuationOf q) (463)) (literal (valuationOf q) (469)) (literal (valuationOf q) (472)) (countLit q [235, 236, 237, 238]) (countLit q [239, 240, 241, 242]) (count471 q) 1 1 (meaning463 q) (meaning469 q) (meaning472 q) hs
  change valuationOf q 463 = false ∨ valuationOf q 469 = false ∨ valuationOf q 472 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1155 (q : Snake 81) (h : Conditions q) : valuation q 463 = false ∨ valuation q 469 = false ∨ valuation q 472 = true := counterClause1155 (baseVal q)

theorem counterClause1156 (q : Nat → Bool) : valuationOf q 464 = false ∨ valuationOf q 472 = true := by
  have hs : count471 q = (countLit q [235, 236, 237, 238]) + (countLit q [239, 240, 241, 242]) := List.countP_append (p := literal q) (l₁ := [235, 236, 237, 238]) (l₂ := [239, 240, 241, 242])
  have hm := merge_left (literal (valuationOf q) (464)) (literal (valuationOf q) (472)) (countLit q [235, 236, 237, 238]) (countLit q [239, 240, 241, 242]) (count471 q) 2 (meaning464 q) (meaning472 q) hs
  change valuationOf q 464 = false ∨ valuationOf q 472 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1156 (q : Snake 81) (h : Conditions q) : valuation q 464 = false ∨ valuation q 472 = true := counterClause1156 (baseVal q)

theorem counterClause1157 (q : Nat → Bool) : valuationOf q 471 = false ∨ valuationOf q 473 = true := by
  have hs : count473 q = (countLit q [228, 229, 230, 231, 232, 233, 234]) + (countLit q [235, 236, 237, 238, 239, 240, 241, 242]) := List.countP_append (p := literal q) (l₁ := [228, 229, 230, 231, 232, 233, 234]) (l₂ := [235, 236, 237, 238, 239, 240, 241, 242])
  have hm := merge_right (literal (valuationOf q) (471)) (literal (valuationOf q) (473)) (countLit q [228, 229, 230, 231, 232, 233, 234]) (countLit q [235, 236, 237, 238, 239, 240, 241, 242]) (count473 q) 1 (meaning471 q) (meaning473 q) hs
  change valuationOf q 471 = false ∨ valuationOf q 473 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1157 (q : Snake 81) (h : Conditions q) : valuation q 471 = false ∨ valuation q 473 = true := counterClause1157 (baseVal q)

theorem counterClause1158 (q : Nat → Bool) : valuationOf q 472 = false ∨ valuationOf q 474 = true := by
  have hs : count473 q = (countLit q [228, 229, 230, 231, 232, 233, 234]) + (countLit q [235, 236, 237, 238, 239, 240, 241, 242]) := List.countP_append (p := literal q) (l₁ := [228, 229, 230, 231, 232, 233, 234]) (l₂ := [235, 236, 237, 238, 239, 240, 241, 242])
  have hm := merge_right (literal (valuationOf q) (472)) (literal (valuationOf q) (474)) (countLit q [228, 229, 230, 231, 232, 233, 234]) (countLit q [235, 236, 237, 238, 239, 240, 241, 242]) (count473 q) 2 (meaning472 q) (meaning474 q) hs
  change valuationOf q 472 = false ∨ valuationOf q 474 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1158 (q : Snake 81) (h : Conditions q) : valuation q 472 = false ∨ valuation q 474 = true := counterClause1158 (baseVal q)

theorem counterClause1159 (q : Nat → Bool) : valuationOf q 457 = false ∨ valuationOf q 473 = true := by
  have hs : count473 q = (countLit q [228, 229, 230, 231, 232, 233, 234]) + (countLit q [235, 236, 237, 238, 239, 240, 241, 242]) := List.countP_append (p := literal q) (l₁ := [228, 229, 230, 231, 232, 233, 234]) (l₂ := [235, 236, 237, 238, 239, 240, 241, 242])
  have hm := merge_left (literal (valuationOf q) (457)) (literal (valuationOf q) (473)) (countLit q [228, 229, 230, 231, 232, 233, 234]) (countLit q [235, 236, 237, 238, 239, 240, 241, 242]) (count473 q) 1 (meaning457 q) (meaning473 q) hs
  change valuationOf q 457 = false ∨ valuationOf q 473 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1159 (q : Snake 81) (h : Conditions q) : valuation q 457 = false ∨ valuation q 473 = true := counterClause1159 (baseVal q)

theorem counterClause1160 (q : Nat → Bool) : valuationOf q 457 = false ∨ valuationOf q 471 = false ∨ valuationOf q 474 = true := by
  have hs : count473 q = (countLit q [228, 229, 230, 231, 232, 233, 234]) + (countLit q [235, 236, 237, 238, 239, 240, 241, 242]) := List.countP_append (p := literal q) (l₁ := [228, 229, 230, 231, 232, 233, 234]) (l₂ := [235, 236, 237, 238, 239, 240, 241, 242])
  have hm := merge_two (literal (valuationOf q) (457)) (literal (valuationOf q) (471)) (literal (valuationOf q) (474)) (countLit q [228, 229, 230, 231, 232, 233, 234]) (countLit q [235, 236, 237, 238, 239, 240, 241, 242]) (count473 q) 1 1 (meaning457 q) (meaning471 q) (meaning474 q) hs
  change valuationOf q 457 = false ∨ valuationOf q 471 = false ∨ valuationOf q 474 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1160 (q : Snake 81) (h : Conditions q) : valuation q 457 = false ∨ valuation q 471 = false ∨ valuation q 474 = true := counterClause1160 (baseVal q)

theorem counterClause1161 (q : Nat → Bool) : valuationOf q 458 = false ∨ valuationOf q 474 = true := by
  have hs : count473 q = (countLit q [228, 229, 230, 231, 232, 233, 234]) + (countLit q [235, 236, 237, 238, 239, 240, 241, 242]) := List.countP_append (p := literal q) (l₁ := [228, 229, 230, 231, 232, 233, 234]) (l₂ := [235, 236, 237, 238, 239, 240, 241, 242])
  have hm := merge_left (literal (valuationOf q) (458)) (literal (valuationOf q) (474)) (countLit q [228, 229, 230, 231, 232, 233, 234]) (countLit q [235, 236, 237, 238, 239, 240, 241, 242]) (count473 q) 2 (meaning458 q) (meaning474 q) hs
  change valuationOf q 458 = false ∨ valuationOf q 474 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1161 (q : Snake 81) (h : Conditions q) : valuation q 458 = false ∨ valuation q 474 = true := counterClause1161 (baseVal q)

theorem counterClause1162 (q : Nat → Bool) : valuationOf q 473 = false ∨ valuationOf q 475 = true := by
  have hs : count475 q = (countLit q [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227]) + (countLit q [228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) := List.countP_append (p := literal q) (l₁ := [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227]) (l₂ := [228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242])
  have hm := merge_right (literal (valuationOf q) (473)) (literal (valuationOf q) (475)) (countLit q [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227]) (countLit q [228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) (count475 q) 1 (meaning473 q) (meaning475 q) hs
  change valuationOf q 473 = false ∨ valuationOf q 475 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1162 (q : Snake 81) (h : Conditions q) : valuation q 473 = false ∨ valuation q 475 = true := counterClause1162 (baseVal q)

theorem counterClause1163 (q : Nat → Bool) : valuationOf q 474 = false ∨ valuationOf q 476 = true := by
  have hs : count475 q = (countLit q [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227]) + (countLit q [228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) := List.countP_append (p := literal q) (l₁ := [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227]) (l₂ := [228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242])
  have hm := merge_right (literal (valuationOf q) (474)) (literal (valuationOf q) (476)) (countLit q [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227]) (countLit q [228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) (count475 q) 2 (meaning474 q) (meaning476 q) hs
  change valuationOf q 474 = false ∨ valuationOf q 476 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1163 (q : Snake 81) (h : Conditions q) : valuation q 474 = false ∨ valuation q 476 = true := counterClause1163 (baseVal q)

theorem counterClause1164 (q : Nat → Bool) : valuationOf q 445 = false ∨ valuationOf q 475 = true := by
  have hs : count475 q = (countLit q [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227]) + (countLit q [228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) := List.countP_append (p := literal q) (l₁ := [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227]) (l₂ := [228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242])
  have hm := merge_left (literal (valuationOf q) (445)) (literal (valuationOf q) (475)) (countLit q [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227]) (countLit q [228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) (count475 q) 1 (meaning445 q) (meaning475 q) hs
  change valuationOf q 445 = false ∨ valuationOf q 475 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1164 (q : Snake 81) (h : Conditions q) : valuation q 445 = false ∨ valuation q 475 = true := counterClause1164 (baseVal q)

theorem counterClause1165 (q : Nat → Bool) : valuationOf q 445 = false ∨ valuationOf q 473 = false ∨ valuationOf q 476 = true := by
  have hs : count475 q = (countLit q [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227]) + (countLit q [228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) := List.countP_append (p := literal q) (l₁ := [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227]) (l₂ := [228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242])
  have hm := merge_two (literal (valuationOf q) (445)) (literal (valuationOf q) (473)) (literal (valuationOf q) (476)) (countLit q [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227]) (countLit q [228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) (count475 q) 1 1 (meaning445 q) (meaning473 q) (meaning476 q) hs
  change valuationOf q 445 = false ∨ valuationOf q 473 = false ∨ valuationOf q 476 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1165 (q : Snake 81) (h : Conditions q) : valuation q 445 = false ∨ valuation q 473 = false ∨ valuation q 476 = true := counterClause1165 (baseVal q)

theorem counterClause1166 (q : Nat → Bool) : valuationOf q 446 = false ∨ valuationOf q 476 = true := by
  have hs : count475 q = (countLit q [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227]) + (countLit q [228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) := List.countP_append (p := literal q) (l₁ := [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227]) (l₂ := [228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242])
  have hm := merge_left (literal (valuationOf q) (446)) (literal (valuationOf q) (476)) (countLit q [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227]) (countLit q [228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) (count475 q) 2 (meaning446 q) (meaning476 q) hs
  change valuationOf q 446 = false ∨ valuationOf q 476 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1166 (q : Snake 81) (h : Conditions q) : valuation q 446 = false ∨ valuation q 476 = true := counterClause1166 (baseVal q)

theorem counterClause1167 (q : Nat → Bool) : valuationOf q 475 = false ∨ valuationOf q 477 = true := by
  have hs : count477 q = (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) + (countLit q [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) := List.countP_append (p := literal q) (l₁ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (l₂ := [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242])
  have hm := merge_right (literal (valuationOf q) (475)) (literal (valuationOf q) (477)) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (countLit q [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) (count477 q) 1 (meaning475 q) (meaning477 q) hs
  change valuationOf q 475 = false ∨ valuationOf q 477 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1167 (q : Snake 81) (h : Conditions q) : valuation q 475 = false ∨ valuation q 477 = true := counterClause1167 (baseVal q)

theorem counterClause1168 (q : Nat → Bool) : valuationOf q 476 = false ∨ valuationOf q 478 = true := by
  have hs : count477 q = (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) + (countLit q [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) := List.countP_append (p := literal q) (l₁ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (l₂ := [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242])
  have hm := merge_right (literal (valuationOf q) (476)) (literal (valuationOf q) (478)) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (countLit q [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) (count477 q) 2 (meaning476 q) (meaning478 q) hs
  change valuationOf q 476 = false ∨ valuationOf q 478 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1168 (q : Snake 81) (h : Conditions q) : valuation q 476 = false ∨ valuation q 478 = true := counterClause1168 (baseVal q)

theorem counterClause1169 (q : Nat → Bool) : valuationOf q 417 = false ∨ valuationOf q 477 = true := by
  have hs : count477 q = (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) + (countLit q [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) := List.countP_append (p := literal q) (l₁ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (l₂ := [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242])
  have hm := merge_left (literal (valuationOf q) (417)) (literal (valuationOf q) (477)) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (countLit q [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) (count477 q) 1 (meaning417 q) (meaning477 q) hs
  change valuationOf q 417 = false ∨ valuationOf q 477 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1169 (q : Snake 81) (h : Conditions q) : valuation q 417 = false ∨ valuation q 477 = true := counterClause1169 (baseVal q)

theorem counterClause1170 (q : Nat → Bool) : valuationOf q 417 = false ∨ valuationOf q 475 = false ∨ valuationOf q 478 = true := by
  have hs : count477 q = (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) + (countLit q [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) := List.countP_append (p := literal q) (l₁ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (l₂ := [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242])
  have hm := merge_two (literal (valuationOf q) (417)) (literal (valuationOf q) (475)) (literal (valuationOf q) (478)) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (countLit q [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) (count477 q) 1 1 (meaning417 q) (meaning475 q) (meaning478 q) hs
  change valuationOf q 417 = false ∨ valuationOf q 475 = false ∨ valuationOf q 478 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1170 (q : Snake 81) (h : Conditions q) : valuation q 417 = false ∨ valuation q 475 = false ∨ valuation q 478 = true := counterClause1170 (baseVal q)

theorem counterClause1171 (q : Nat → Bool) : valuationOf q 418 = false ∨ valuationOf q 478 = true := by
  have hs : count477 q = (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) + (countLit q [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) := List.countP_append (p := literal q) (l₁ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (l₂ := [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242])
  have hm := merge_left (literal (valuationOf q) (418)) (literal (valuationOf q) (478)) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (countLit q [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) (count477 q) 2 (meaning418 q) (meaning478 q) hs
  change valuationOf q 418 = false ∨ valuationOf q 478 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1171 (q : Snake 81) (h : Conditions q) : valuation q 418 = false ∨ valuation q 478 = true := counterClause1171 (baseVal q)

theorem counterClause1172 (q : Nat → Bool) : valuationOf q 478 = false ∨ valuationOf q 480 = true := by
  have hs : count479 q = (countLit q [122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 182]) + (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) := List.countP_append (p := literal q) (l₁ := [122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 182]) (l₂ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242])
  have hm := merge_right (literal (valuationOf q) (478)) (literal (valuationOf q) (480)) (countLit q [122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 182]) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) (count479 q) 2 (meaning478 q) (meaning480 q) hs
  change valuationOf q 478 = false ∨ valuationOf q 480 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1172 (q : Snake 81) (h : Conditions q) : valuation q 478 = false ∨ valuation q 480 = true := counterClause1172 (baseVal q)

theorem counterClause1173 (q : Nat → Bool) : valuationOf q 359 = false ∨ valuationOf q 477 = false ∨ valuationOf q 480 = true := by
  have hs : count479 q = (countLit q [122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 182]) + (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) := List.countP_append (p := literal q) (l₁ := [122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 182]) (l₂ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242])
  have hm := merge_two (literal (valuationOf q) (359)) (literal (valuationOf q) (477)) (literal (valuationOf q) (480)) (countLit q [122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 182]) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) (count479 q) 1 1 (meaning359 q) (meaning477 q) (meaning480 q) hs
  change valuationOf q 359 = false ∨ valuationOf q 477 = false ∨ valuationOf q 480 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1173 (q : Snake 81) (h : Conditions q) : valuation q 359 = false ∨ valuation q 477 = false ∨ valuation q 480 = true := counterClause1173 (baseVal q)

theorem counterClause1174 (q : Nat → Bool) : valuationOf q 360 = false ∨ valuationOf q 480 = true := by
  have hs : count479 q = (countLit q [122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 182]) + (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) := List.countP_append (p := literal q) (l₁ := [122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 182]) (l₂ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242])
  have hm := merge_left (literal (valuationOf q) (360)) (literal (valuationOf q) (480)) (countLit q [122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 182]) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) (count479 q) 2 (meaning360 q) (meaning480 q) hs
  change valuationOf q 360 = false ∨ valuationOf q 480 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1174 (q : Snake 81) (h : Conditions q) : valuation q 360 = false ∨ valuation q 480 = true := counterClause1174 (baseVal q)

theorem clause1175 (q : Snake 81) (h : Conditions q) : valuation q 480 = false := by
  rw [value480]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count479 (baseVal q) = (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := other_count_bound q h
  rw [he]
  omega

theorem clause1176 (q : Snake 81) (h : Conditions q) : valuation q 122 = true ∨ valuation q 123 = true ∨ valuation q 124 = true ∨ valuation q 125 = true ∨ valuation q 126 = true ∨ valuation q 127 = true ∨ valuation q 128 = true ∨ valuation q 129 = true ∨ valuation q 130 = true ∨ valuation q 131 = true ∨ valuation q 132 = true ∨ valuation q 133 = true ∨ valuation q 134 = true ∨ valuation q 135 = true ∨ valuation q 136 = true ∨ valuation q 137 = true ∨ valuation q 138 = true ∨ valuation q 139 = true ∨ valuation q 140 = true ∨ valuation q 141 = true ∨ valuation q 142 = true ∨ valuation q 143 = true ∨ valuation q 144 = true ∨ valuation q 145 = true ∨ valuation q 146 = true ∨ valuation q 147 = true ∨ valuation q 148 = true ∨ valuation q 149 = true ∨ valuation q 150 = true ∨ valuation q 151 = true ∨ valuation q 152 = true ∨ valuation q 153 = true ∨ valuation q 154 = true ∨ valuation q 155 = true ∨ valuation q 156 = true ∨ valuation q 157 = true ∨ valuation q 158 = true ∨ valuation q 159 = true ∨ valuation q 160 = true ∨ valuation q 161 = true ∨ valuation q 162 = true ∨ valuation q 163 = true ∨ valuation q 164 = true ∨ valuation q 165 = true ∨ valuation q 166 = true ∨ valuation q 167 = true ∨ valuation q 168 = true ∨ valuation q 169 = true ∨ valuation q 170 = true ∨ valuation q 171 = true ∨ valuation q 172 = true ∨ valuation q 173 = true ∨ valuation q 174 = true ∨ valuation q 175 = true ∨ valuation q 176 = true ∨ valuation q 177 = true ∨ valuation q 178 = true ∨ valuation q 179 = true ∨ valuation q 180 = true ∨ valuation q 182 = true ∨ valuation q 183 = true ∨ valuation q 184 = true ∨ valuation q 185 = true ∨ valuation q 186 = true ∨ valuation q 187 = true ∨ valuation q 188 = true ∨ valuation q 189 = true ∨ valuation q 190 = true ∨ valuation q 191 = true ∨ valuation q 192 = true ∨ valuation q 193 = true ∨ valuation q 194 = true ∨ valuation q 195 = true ∨ valuation q 196 = true ∨ valuation q 197 = true ∨ valuation q 198 = true ∨ valuation q 199 = true ∨ valuation q 200 = true ∨ valuation q 201 = true ∨ valuation q 202 = true ∨ valuation q 203 = true ∨ valuation q 204 = true ∨ valuation q 205 = true ∨ valuation q 206 = true ∨ valuation q 207 = true ∨ valuation q 208 = true ∨ valuation q 209 = true ∨ valuation q 210 = true ∨ valuation q 211 = true ∨ valuation q 212 = true ∨ valuation q 213 = true ∨ valuation q 214 = true ∨ valuation q 215 = true ∨ valuation q 216 = true ∨ valuation q 217 = true ∨ valuation q 218 = true ∨ valuation q 219 = true ∨ valuation q 220 = true ∨ valuation q 221 = true ∨ valuation q 222 = true ∨ valuation q 223 = true ∨ valuation q 224 = true ∨ valuation q 225 = true ∨ valuation q 226 = true ∨ valuation q 227 = true ∨ valuation q 228 = true ∨ valuation q 229 = true ∨ valuation q 230 = true ∨ valuation q 231 = true ∨ valuation q 232 = true ∨ valuation q 233 = true ∨ valuation q 234 = true ∨ valuation q 235 = true ∨ valuation q 236 = true ∨ valuation q 237 = true ∨ valuation q 238 = true ∨ valuation q 239 = true ∨ valuation q 240 = true ∨ valuation q 241 = true ∨ valuation q 242 = true := by
  rw [value122, value123, value124, value125, value126, value127, value128, value129, value130, value131, value132, value133, value134, value135, value136, value137, value138, value139, value140, value141, value142, value143, value144, value145, value146, value147, value148, value149, value150, value151, value152, value153, value154, value155, value156, value157, value158, value159, value160, value161, value162, value163, value164, value165, value166, value167, value168, value169, value170, value171, value172, value173, value174, value175, value176, value177, value178, value179, value180, value182, value183, value184, value185, value186, value187, value188, value189, value190, value191, value192, value193, value194, value195, value196, value197, value198, value199, value200, value201, value202, value203, value204, value205, value206, value207, value208, value209, value210, value211, value212, value213, value214, value215, value216, value217, value218, value219, value220, value221, value222, value223, value224, value225, value226, value227, value228, value229, value230, value231, value232, value233, value234, value235, value236, value237, value238, value239, value240, value241, value242]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hg := other_endpoint q others (fun v hv hn => others_mem v (h.covered v hv) (by simpa only [h.head_fixed] using hn))
  simpa only [others, List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem counterClause1177 (q : Nat → Bool) : valuationOf q 7 = true ∨ valuationOf q 1475 = true := by
  have hs : count1475 q = (countLit q [-5]) + (countLit q [-7]) := List.countP_append (p := literal q) (l₁ := [-5]) (l₂ := [-7])
  have hm := merge_right (literal (valuationOf q) (-7)) (literal (valuationOf q) (1475)) (countLit q [-5]) (countLit q [-7]) (count1475 q) 1 (meaningNeg7 q) (meaning1475 q) hs
  change (! (valuationOf q 7)) = false ∨ valuationOf q 1475 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1177 (q : Snake 81) (h : Conditions q) : valuation q 7 = true ∨ valuation q 1475 = true := counterClause1177 (baseVal q)

theorem counterClause1178 (q : Nat → Bool) : valuationOf q 5 = true ∨ valuationOf q 1475 = true := by
  have hs : count1475 q = (countLit q [-5]) + (countLit q [-7]) := List.countP_append (p := literal q) (l₁ := [-5]) (l₂ := [-7])
  have hm := merge_left (literal (valuationOf q) (-5)) (literal (valuationOf q) (1475)) (countLit q [-5]) (countLit q [-7]) (count1475 q) 1 (meaningNeg5 q) (meaning1475 q) hs
  change (! (valuationOf q 5)) = false ∨ valuationOf q 1475 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1178 (q : Snake 81) (h : Conditions q) : valuation q 5 = true ∨ valuation q 1475 = true := counterClause1178 (baseVal q)

theorem counterClause1179 (q : Nat → Bool) : valuationOf q 5 = true ∨ valuationOf q 7 = true ∨ valuationOf q 1476 = true := by
  have hs : count1475 q = (countLit q [-5]) + (countLit q [-7]) := List.countP_append (p := literal q) (l₁ := [-5]) (l₂ := [-7])
  have hm := merge_two (literal (valuationOf q) (-5)) (literal (valuationOf q) (-7)) (literal (valuationOf q) (1476)) (countLit q [-5]) (countLit q [-7]) (count1475 q) 1 1 (meaningNeg5 q) (meaningNeg7 q) (meaning1476 q) hs
  change (! (valuationOf q 5)) = false ∨ (! (valuationOf q 7)) = false ∨ valuationOf q 1476 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1179 (q : Snake 81) (h : Conditions q) : valuation q 5 = true ∨ valuation q 7 = true ∨ valuation q 1476 = true := counterClause1179 (baseVal q)

theorem counterClause1180 (q : Nat → Bool) : valuationOf q 1475 = false ∨ valuationOf q 1477 = true := by
  have hs : count1477 q = (countLit q [-2]) + (countLit q [-5, -7]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-5, -7])
  have hm := merge_right (literal (valuationOf q) (1475)) (literal (valuationOf q) (1477)) (countLit q [-2]) (countLit q [-5, -7]) (count1477 q) 1 (meaning1475 q) (meaning1477 q) hs
  change valuationOf q 1475 = false ∨ valuationOf q 1477 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1180 (q : Snake 81) (h : Conditions q) : valuation q 1475 = false ∨ valuation q 1477 = true := counterClause1180 (baseVal q)

theorem counterClause1181 (q : Nat → Bool) : valuationOf q 1476 = false ∨ valuationOf q 1478 = true := by
  have hs : count1477 q = (countLit q [-2]) + (countLit q [-5, -7]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-5, -7])
  have hm := merge_right (literal (valuationOf q) (1476)) (literal (valuationOf q) (1478)) (countLit q [-2]) (countLit q [-5, -7]) (count1477 q) 2 (meaning1476 q) (meaning1478 q) hs
  change valuationOf q 1476 = false ∨ valuationOf q 1478 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1181 (q : Snake 81) (h : Conditions q) : valuation q 1476 = false ∨ valuation q 1478 = true := counterClause1181 (baseVal q)

theorem counterClause1182 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1477 = true := by
  have hs : count1477 q = (countLit q [-2]) + (countLit q [-5, -7]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-5, -7])
  have hm := merge_left (literal (valuationOf q) (-2)) (literal (valuationOf q) (1477)) (countLit q [-2]) (countLit q [-5, -7]) (count1477 q) 1 (meaningNeg2 q) (meaning1477 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1477 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1182 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1477 = true := counterClause1182 (baseVal q)

theorem counterClause1183 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1475 = false ∨ valuationOf q 1478 = true := by
  have hs : count1477 q = (countLit q [-2]) + (countLit q [-5, -7]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-5, -7])
  have hm := merge_two (literal (valuationOf q) (-2)) (literal (valuationOf q) (1475)) (literal (valuationOf q) (1478)) (countLit q [-2]) (countLit q [-5, -7]) (count1477 q) 1 1 (meaningNeg2 q) (meaning1475 q) (meaning1478 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1475 = false ∨ valuationOf q 1478 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1183 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1475 = false ∨ valuation q 1478 = true := counterClause1183 (baseVal q)

theorem counterClause1184 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1476 = false ∨ valuationOf q 1479 = true := by
  have hs : count1477 q = (countLit q [-2]) + (countLit q [-5, -7]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-5, -7])
  have hm := merge_two (literal (valuationOf q) (-2)) (literal (valuationOf q) (1476)) (literal (valuationOf q) (1479)) (countLit q [-2]) (countLit q [-5, -7]) (count1477 q) 1 2 (meaningNeg2 q) (meaning1476 q) (meaning1479 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1476 = false ∨ valuationOf q 1479 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1184 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1476 = false ∨ valuation q 1479 = true := counterClause1184 (baseVal q)

theorem block36 (q : Snake 81) (h : Conditions q) : B112E019.Block36 (valuation q) :=
  ⟨clause1153 q h, clause1154 q h, clause1155 q h, clause1156 q h, clause1157 q h, clause1158 q h, clause1159 q h, clause1160 q h, clause1161 q h, clause1162 q h, clause1163 q h, clause1164 q h, clause1165 q h, clause1166 q h, clause1167 q h, clause1168 q h, clause1169 q h, clause1170 q h, clause1171 q h, clause1172 q h, clause1173 q h, clause1174 q h, clause1175 q h, clause1176 q h, clause1177 q h, clause1178 q h, clause1179 q h, clause1180 q h, clause1181 q h, clause1182 q h, clause1183 q h, clause1184 q h⟩

end
end Snake9.Regrowth.E112019
