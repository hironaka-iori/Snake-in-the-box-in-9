import E112019Semantics
import B112E019Inputs
namespace Snake9.Regrowth.E112019
noncomputable section
local instance blockDec35 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1121 (q : Nat → Bool) : valuationOf q 431 = false ∨ valuationOf q 435 = true := by
  have hs : count435 q = (countLit q [220, 221]) + (countLit q [222, 223]) := List.countP_append (p := literal q) (l₁ := [220, 221]) (l₂ := [222, 223])
  have hm := merge_left (literal (valuationOf q) (431)) (literal (valuationOf q) (435)) (countLit q [220, 221]) (countLit q [222, 223]) (count435 q) 1 (meaning431 q) (meaning435 q) hs
  change valuationOf q 431 = false ∨ valuationOf q 435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1121 (q : Snake 81) (h : Conditions q) : valuation q 431 = false ∨ valuation q 435 = true := counterClause1121 (baseVal q)

theorem counterClause1122 (q : Nat → Bool) : valuationOf q 431 = false ∨ valuationOf q 433 = false ∨ valuationOf q 436 = true := by
  have hs : count435 q = (countLit q [220, 221]) + (countLit q [222, 223]) := List.countP_append (p := literal q) (l₁ := [220, 221]) (l₂ := [222, 223])
  have hm := merge_two (literal (valuationOf q) (431)) (literal (valuationOf q) (433)) (literal (valuationOf q) (436)) (countLit q [220, 221]) (countLit q [222, 223]) (count435 q) 1 1 (meaning431 q) (meaning433 q) (meaning436 q) hs
  change valuationOf q 431 = false ∨ valuationOf q 433 = false ∨ valuationOf q 436 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1122 (q : Snake 81) (h : Conditions q) : valuation q 431 = false ∨ valuation q 433 = false ∨ valuation q 436 = true := counterClause1122 (baseVal q)

theorem counterClause1123 (q : Nat → Bool) : valuationOf q 224 = false ∨ valuationOf q 437 = true := by
  have hs : count437 q = (countLit q [224]) + (countLit q [225]) := List.countP_append (p := literal q) (l₁ := [224]) (l₂ := [225])
  have hm := merge_left (literal (valuationOf q) (224)) (literal (valuationOf q) (437)) (countLit q [224]) (countLit q [225]) (count437 q) 1 (meaning224 q) (meaning437 q) hs
  change valuationOf q 224 = false ∨ valuationOf q 437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1123 (q : Snake 81) (h : Conditions q) : valuation q 224 = false ∨ valuation q 437 = true := counterClause1123 (baseVal q)

theorem counterClause1124 (q : Nat → Bool) : valuationOf q 437 = false ∨ valuationOf q 441 = true := by
  have hs : count441 q = (countLit q [224, 225]) + (countLit q [226, 227]) := List.countP_append (p := literal q) (l₁ := [224, 225]) (l₂ := [226, 227])
  have hm := merge_left (literal (valuationOf q) (437)) (literal (valuationOf q) (441)) (countLit q [224, 225]) (countLit q [226, 227]) (count441 q) 1 (meaning437 q) (meaning441 q) hs
  change valuationOf q 437 = false ∨ valuationOf q 441 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1124 (q : Snake 81) (h : Conditions q) : valuation q 437 = false ∨ valuation q 441 = true := counterClause1124 (baseVal q)

theorem counterClause1125 (q : Nat → Bool) : valuationOf q 441 = false ∨ valuationOf q 443 = true := by
  have hs : count443 q = (countLit q [220, 221, 222, 223]) + (countLit q [224, 225, 226, 227]) := List.countP_append (p := literal q) (l₁ := [220, 221, 222, 223]) (l₂ := [224, 225, 226, 227])
  have hm := merge_right (literal (valuationOf q) (441)) (literal (valuationOf q) (443)) (countLit q [220, 221, 222, 223]) (countLit q [224, 225, 226, 227]) (count443 q) 1 (meaning441 q) (meaning443 q) hs
  change valuationOf q 441 = false ∨ valuationOf q 443 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1125 (q : Snake 81) (h : Conditions q) : valuation q 441 = false ∨ valuation q 443 = true := counterClause1125 (baseVal q)

theorem counterClause1126 (q : Nat → Bool) : valuationOf q 435 = false ∨ valuationOf q 443 = true := by
  have hs : count443 q = (countLit q [220, 221, 222, 223]) + (countLit q [224, 225, 226, 227]) := List.countP_append (p := literal q) (l₁ := [220, 221, 222, 223]) (l₂ := [224, 225, 226, 227])
  have hm := merge_left (literal (valuationOf q) (435)) (literal (valuationOf q) (443)) (countLit q [220, 221, 222, 223]) (countLit q [224, 225, 226, 227]) (count443 q) 1 (meaning435 q) (meaning443 q) hs
  change valuationOf q 435 = false ∨ valuationOf q 443 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1126 (q : Snake 81) (h : Conditions q) : valuation q 435 = false ∨ valuation q 443 = true := counterClause1126 (baseVal q)

theorem counterClause1127 (q : Nat → Bool) : valuationOf q 435 = false ∨ valuationOf q 441 = false ∨ valuationOf q 444 = true := by
  have hs : count443 q = (countLit q [220, 221, 222, 223]) + (countLit q [224, 225, 226, 227]) := List.countP_append (p := literal q) (l₁ := [220, 221, 222, 223]) (l₂ := [224, 225, 226, 227])
  have hm := merge_two (literal (valuationOf q) (435)) (literal (valuationOf q) (441)) (literal (valuationOf q) (444)) (countLit q [220, 221, 222, 223]) (countLit q [224, 225, 226, 227]) (count443 q) 1 1 (meaning435 q) (meaning441 q) (meaning444 q) hs
  change valuationOf q 435 = false ∨ valuationOf q 441 = false ∨ valuationOf q 444 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1127 (q : Snake 81) (h : Conditions q) : valuation q 435 = false ∨ valuation q 441 = false ∨ valuation q 444 = true := counterClause1127 (baseVal q)

theorem counterClause1128 (q : Nat → Bool) : valuationOf q 436 = false ∨ valuationOf q 444 = true := by
  have hs : count443 q = (countLit q [220, 221, 222, 223]) + (countLit q [224, 225, 226, 227]) := List.countP_append (p := literal q) (l₁ := [220, 221, 222, 223]) (l₂ := [224, 225, 226, 227])
  have hm := merge_left (literal (valuationOf q) (436)) (literal (valuationOf q) (444)) (countLit q [220, 221, 222, 223]) (countLit q [224, 225, 226, 227]) (count443 q) 2 (meaning436 q) (meaning444 q) hs
  change valuationOf q 436 = false ∨ valuationOf q 444 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1128 (q : Snake 81) (h : Conditions q) : valuation q 436 = false ∨ valuation q 444 = true := counterClause1128 (baseVal q)

theorem counterClause1129 (q : Nat → Bool) : valuationOf q 443 = false ∨ valuationOf q 445 = true := by
  have hs : count445 q = (countLit q [213, 214, 215, 216, 217, 218, 219]) + (countLit q [220, 221, 222, 223, 224, 225, 226, 227]) := List.countP_append (p := literal q) (l₁ := [213, 214, 215, 216, 217, 218, 219]) (l₂ := [220, 221, 222, 223, 224, 225, 226, 227])
  have hm := merge_right (literal (valuationOf q) (443)) (literal (valuationOf q) (445)) (countLit q [213, 214, 215, 216, 217, 218, 219]) (countLit q [220, 221, 222, 223, 224, 225, 226, 227]) (count445 q) 1 (meaning443 q) (meaning445 q) hs
  change valuationOf q 443 = false ∨ valuationOf q 445 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1129 (q : Snake 81) (h : Conditions q) : valuation q 443 = false ∨ valuation q 445 = true := counterClause1129 (baseVal q)

theorem counterClause1130 (q : Nat → Bool) : valuationOf q 444 = false ∨ valuationOf q 446 = true := by
  have hs : count445 q = (countLit q [213, 214, 215, 216, 217, 218, 219]) + (countLit q [220, 221, 222, 223, 224, 225, 226, 227]) := List.countP_append (p := literal q) (l₁ := [213, 214, 215, 216, 217, 218, 219]) (l₂ := [220, 221, 222, 223, 224, 225, 226, 227])
  have hm := merge_right (literal (valuationOf q) (444)) (literal (valuationOf q) (446)) (countLit q [213, 214, 215, 216, 217, 218, 219]) (countLit q [220, 221, 222, 223, 224, 225, 226, 227]) (count445 q) 2 (meaning444 q) (meaning446 q) hs
  change valuationOf q 444 = false ∨ valuationOf q 446 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1130 (q : Snake 81) (h : Conditions q) : valuation q 444 = false ∨ valuation q 446 = true := counterClause1130 (baseVal q)

theorem counterClause1131 (q : Nat → Bool) : valuationOf q 429 = false ∨ valuationOf q 445 = true := by
  have hs : count445 q = (countLit q [213, 214, 215, 216, 217, 218, 219]) + (countLit q [220, 221, 222, 223, 224, 225, 226, 227]) := List.countP_append (p := literal q) (l₁ := [213, 214, 215, 216, 217, 218, 219]) (l₂ := [220, 221, 222, 223, 224, 225, 226, 227])
  have hm := merge_left (literal (valuationOf q) (429)) (literal (valuationOf q) (445)) (countLit q [213, 214, 215, 216, 217, 218, 219]) (countLit q [220, 221, 222, 223, 224, 225, 226, 227]) (count445 q) 1 (meaning429 q) (meaning445 q) hs
  change valuationOf q 429 = false ∨ valuationOf q 445 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1131 (q : Snake 81) (h : Conditions q) : valuation q 429 = false ∨ valuation q 445 = true := counterClause1131 (baseVal q)

theorem counterClause1132 (q : Nat → Bool) : valuationOf q 429 = false ∨ valuationOf q 443 = false ∨ valuationOf q 446 = true := by
  have hs : count445 q = (countLit q [213, 214, 215, 216, 217, 218, 219]) + (countLit q [220, 221, 222, 223, 224, 225, 226, 227]) := List.countP_append (p := literal q) (l₁ := [213, 214, 215, 216, 217, 218, 219]) (l₂ := [220, 221, 222, 223, 224, 225, 226, 227])
  have hm := merge_two (literal (valuationOf q) (429)) (literal (valuationOf q) (443)) (literal (valuationOf q) (446)) (countLit q [213, 214, 215, 216, 217, 218, 219]) (countLit q [220, 221, 222, 223, 224, 225, 226, 227]) (count445 q) 1 1 (meaning429 q) (meaning443 q) (meaning446 q) hs
  change valuationOf q 429 = false ∨ valuationOf q 443 = false ∨ valuationOf q 446 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1132 (q : Snake 81) (h : Conditions q) : valuation q 429 = false ∨ valuation q 443 = false ∨ valuation q 446 = true := counterClause1132 (baseVal q)

theorem counterClause1133 (q : Nat → Bool) : valuationOf q 430 = false ∨ valuationOf q 446 = true := by
  have hs : count445 q = (countLit q [213, 214, 215, 216, 217, 218, 219]) + (countLit q [220, 221, 222, 223, 224, 225, 226, 227]) := List.countP_append (p := literal q) (l₁ := [213, 214, 215, 216, 217, 218, 219]) (l₂ := [220, 221, 222, 223, 224, 225, 226, 227])
  have hm := merge_left (literal (valuationOf q) (430)) (literal (valuationOf q) (446)) (countLit q [213, 214, 215, 216, 217, 218, 219]) (countLit q [220, 221, 222, 223, 224, 225, 226, 227]) (count445 q) 2 (meaning430 q) (meaning446 q) hs
  change valuationOf q 430 = false ∨ valuationOf q 446 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1133 (q : Snake 81) (h : Conditions q) : valuation q 430 = false ∨ valuation q 446 = true := counterClause1133 (baseVal q)

theorem counterClause1134 (q : Nat → Bool) : valuationOf q 228 = false ∨ valuationOf q 449 = true := by
  have hs : count449 q = (countLit q [228]) + (countLit q [229, 230]) := List.countP_append (p := literal q) (l₁ := [228]) (l₂ := [229, 230])
  have hm := merge_left (literal (valuationOf q) (228)) (literal (valuationOf q) (449)) (countLit q [228]) (countLit q [229, 230]) (count449 q) 1 (meaning228 q) (meaning449 q) hs
  change valuationOf q 228 = false ∨ valuationOf q 449 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1134 (q : Snake 81) (h : Conditions q) : valuation q 228 = false ∨ valuation q 449 = true := counterClause1134 (baseVal q)

theorem counterClause1135 (q : Nat → Bool) : valuationOf q 231 = false ∨ valuationOf q 451 = true := by
  have hs : count451 q = (countLit q [231]) + (countLit q [232]) := List.countP_append (p := literal q) (l₁ := [231]) (l₂ := [232])
  have hm := merge_left (literal (valuationOf q) (231)) (literal (valuationOf q) (451)) (countLit q [231]) (countLit q [232]) (count451 q) 1 (meaning231 q) (meaning451 q) hs
  change valuationOf q 231 = false ∨ valuationOf q 451 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1135 (q : Snake 81) (h : Conditions q) : valuation q 231 = false ∨ valuation q 451 = true := counterClause1135 (baseVal q)

theorem counterClause1136 (q : Nat → Bool) : valuationOf q 234 = false ∨ valuationOf q 453 = true := by
  have hs : count453 q = (countLit q [233]) + (countLit q [234]) := List.countP_append (p := literal q) (l₁ := [233]) (l₂ := [234])
  have hm := merge_right (literal (valuationOf q) (234)) (literal (valuationOf q) (453)) (countLit q [233]) (countLit q [234]) (count453 q) 1 (meaning234 q) (meaning453 q) hs
  change valuationOf q 234 = false ∨ valuationOf q 453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1136 (q : Snake 81) (h : Conditions q) : valuation q 234 = false ∨ valuation q 453 = true := counterClause1136 (baseVal q)

theorem counterClause1137 (q : Nat → Bool) : valuationOf q 233 = false ∨ valuationOf q 453 = true := by
  have hs : count453 q = (countLit q [233]) + (countLit q [234]) := List.countP_append (p := literal q) (l₁ := [233]) (l₂ := [234])
  have hm := merge_left (literal (valuationOf q) (233)) (literal (valuationOf q) (453)) (countLit q [233]) (countLit q [234]) (count453 q) 1 (meaning233 q) (meaning453 q) hs
  change valuationOf q 233 = false ∨ valuationOf q 453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1137 (q : Snake 81) (h : Conditions q) : valuation q 233 = false ∨ valuation q 453 = true := counterClause1137 (baseVal q)

theorem counterClause1138 (q : Nat → Bool) : valuationOf q 453 = false ∨ valuationOf q 455 = true := by
  have hs : count455 q = (countLit q [231, 232]) + (countLit q [233, 234]) := List.countP_append (p := literal q) (l₁ := [231, 232]) (l₂ := [233, 234])
  have hm := merge_right (literal (valuationOf q) (453)) (literal (valuationOf q) (455)) (countLit q [231, 232]) (countLit q [233, 234]) (count455 q) 1 (meaning453 q) (meaning455 q) hs
  change valuationOf q 453 = false ∨ valuationOf q 455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1138 (q : Snake 81) (h : Conditions q) : valuation q 453 = false ∨ valuation q 455 = true := counterClause1138 (baseVal q)

theorem counterClause1139 (q : Nat → Bool) : valuationOf q 451 = false ∨ valuationOf q 455 = true := by
  have hs : count455 q = (countLit q [231, 232]) + (countLit q [233, 234]) := List.countP_append (p := literal q) (l₁ := [231, 232]) (l₂ := [233, 234])
  have hm := merge_left (literal (valuationOf q) (451)) (literal (valuationOf q) (455)) (countLit q [231, 232]) (countLit q [233, 234]) (count455 q) 1 (meaning451 q) (meaning455 q) hs
  change valuationOf q 451 = false ∨ valuationOf q 455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1139 (q : Snake 81) (h : Conditions q) : valuation q 451 = false ∨ valuation q 455 = true := counterClause1139 (baseVal q)

theorem counterClause1140 (q : Nat → Bool) : valuationOf q 451 = false ∨ valuationOf q 453 = false ∨ valuationOf q 456 = true := by
  have hs : count455 q = (countLit q [231, 232]) + (countLit q [233, 234]) := List.countP_append (p := literal q) (l₁ := [231, 232]) (l₂ := [233, 234])
  have hm := merge_two (literal (valuationOf q) (451)) (literal (valuationOf q) (453)) (literal (valuationOf q) (456)) (countLit q [231, 232]) (countLit q [233, 234]) (count455 q) 1 1 (meaning451 q) (meaning453 q) (meaning456 q) hs
  change valuationOf q 451 = false ∨ valuationOf q 453 = false ∨ valuationOf q 456 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1140 (q : Snake 81) (h : Conditions q) : valuation q 451 = false ∨ valuation q 453 = false ∨ valuation q 456 = true := counterClause1140 (baseVal q)

theorem counterClause1141 (q : Nat → Bool) : valuationOf q 455 = false ∨ valuationOf q 457 = true := by
  have hs : count457 q = (countLit q [228, 229, 230]) + (countLit q [231, 232, 233, 234]) := List.countP_append (p := literal q) (l₁ := [228, 229, 230]) (l₂ := [231, 232, 233, 234])
  have hm := merge_right (literal (valuationOf q) (455)) (literal (valuationOf q) (457)) (countLit q [228, 229, 230]) (countLit q [231, 232, 233, 234]) (count457 q) 1 (meaning455 q) (meaning457 q) hs
  change valuationOf q 455 = false ∨ valuationOf q 457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1141 (q : Snake 81) (h : Conditions q) : valuation q 455 = false ∨ valuation q 457 = true := counterClause1141 (baseVal q)

theorem counterClause1142 (q : Nat → Bool) : valuationOf q 456 = false ∨ valuationOf q 458 = true := by
  have hs : count457 q = (countLit q [228, 229, 230]) + (countLit q [231, 232, 233, 234]) := List.countP_append (p := literal q) (l₁ := [228, 229, 230]) (l₂ := [231, 232, 233, 234])
  have hm := merge_right (literal (valuationOf q) (456)) (literal (valuationOf q) (458)) (countLit q [228, 229, 230]) (countLit q [231, 232, 233, 234]) (count457 q) 2 (meaning456 q) (meaning458 q) hs
  change valuationOf q 456 = false ∨ valuationOf q 458 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1142 (q : Snake 81) (h : Conditions q) : valuation q 456 = false ∨ valuation q 458 = true := counterClause1142 (baseVal q)

theorem counterClause1143 (q : Nat → Bool) : valuationOf q 449 = false ∨ valuationOf q 457 = true := by
  have hs : count457 q = (countLit q [228, 229, 230]) + (countLit q [231, 232, 233, 234]) := List.countP_append (p := literal q) (l₁ := [228, 229, 230]) (l₂ := [231, 232, 233, 234])
  have hm := merge_left (literal (valuationOf q) (449)) (literal (valuationOf q) (457)) (countLit q [228, 229, 230]) (countLit q [231, 232, 233, 234]) (count457 q) 1 (meaning449 q) (meaning457 q) hs
  change valuationOf q 449 = false ∨ valuationOf q 457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1143 (q : Snake 81) (h : Conditions q) : valuation q 449 = false ∨ valuation q 457 = true := counterClause1143 (baseVal q)

theorem counterClause1144 (q : Nat → Bool) : valuationOf q 236 = false ∨ valuationOf q 459 = true := by
  have hs : count459 q = (countLit q [235]) + (countLit q [236]) := List.countP_append (p := literal q) (l₁ := [235]) (l₂ := [236])
  have hm := merge_right (literal (valuationOf q) (236)) (literal (valuationOf q) (459)) (countLit q [235]) (countLit q [236]) (count459 q) 1 (meaning236 q) (meaning459 q) hs
  change valuationOf q 236 = false ∨ valuationOf q 459 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1144 (q : Snake 81) (h : Conditions q) : valuation q 236 = false ∨ valuation q 459 = true := counterClause1144 (baseVal q)

theorem counterClause1145 (q : Nat → Bool) : valuationOf q 237 = false ∨ valuationOf q 461 = true := by
  have hs : count461 q = (countLit q [237]) + (countLit q [238]) := List.countP_append (p := literal q) (l₁ := [237]) (l₂ := [238])
  have hm := merge_left (literal (valuationOf q) (237)) (literal (valuationOf q) (461)) (countLit q [237]) (countLit q [238]) (count461 q) 1 (meaning237 q) (meaning461 q) hs
  change valuationOf q 237 = false ∨ valuationOf q 461 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1145 (q : Snake 81) (h : Conditions q) : valuation q 237 = false ∨ valuation q 461 = true := counterClause1145 (baseVal q)

theorem counterClause1146 (q : Nat → Bool) : valuationOf q 461 = false ∨ valuationOf q 463 = true := by
  have hs : count463 q = (countLit q [235, 236]) + (countLit q [237, 238]) := List.countP_append (p := literal q) (l₁ := [235, 236]) (l₂ := [237, 238])
  have hm := merge_right (literal (valuationOf q) (461)) (literal (valuationOf q) (463)) (countLit q [235, 236]) (countLit q [237, 238]) (count463 q) 1 (meaning461 q) (meaning463 q) hs
  change valuationOf q 461 = false ∨ valuationOf q 463 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1146 (q : Snake 81) (h : Conditions q) : valuation q 461 = false ∨ valuation q 463 = true := counterClause1146 (baseVal q)

theorem counterClause1147 (q : Nat → Bool) : valuationOf q 459 = false ∨ valuationOf q 463 = true := by
  have hs : count463 q = (countLit q [235, 236]) + (countLit q [237, 238]) := List.countP_append (p := literal q) (l₁ := [235, 236]) (l₂ := [237, 238])
  have hm := merge_left (literal (valuationOf q) (459)) (literal (valuationOf q) (463)) (countLit q [235, 236]) (countLit q [237, 238]) (count463 q) 1 (meaning459 q) (meaning463 q) hs
  change valuationOf q 459 = false ∨ valuationOf q 463 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1147 (q : Snake 81) (h : Conditions q) : valuation q 459 = false ∨ valuation q 463 = true := counterClause1147 (baseVal q)

theorem counterClause1148 (q : Nat → Bool) : valuationOf q 459 = false ∨ valuationOf q 461 = false ∨ valuationOf q 464 = true := by
  have hs : count463 q = (countLit q [235, 236]) + (countLit q [237, 238]) := List.countP_append (p := literal q) (l₁ := [235, 236]) (l₂ := [237, 238])
  have hm := merge_two (literal (valuationOf q) (459)) (literal (valuationOf q) (461)) (literal (valuationOf q) (464)) (countLit q [235, 236]) (countLit q [237, 238]) (count463 q) 1 1 (meaning459 q) (meaning461 q) (meaning464 q) hs
  change valuationOf q 459 = false ∨ valuationOf q 461 = false ∨ valuationOf q 464 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1148 (q : Snake 81) (h : Conditions q) : valuation q 459 = false ∨ valuation q 461 = false ∨ valuation q 464 = true := counterClause1148 (baseVal q)

theorem counterClause1149 (q : Nat → Bool) : valuationOf q 239 = false ∨ valuationOf q 465 = true := by
  have hs : count465 q = (countLit q [239]) + (countLit q [240]) := List.countP_append (p := literal q) (l₁ := [239]) (l₂ := [240])
  have hm := merge_left (literal (valuationOf q) (239)) (literal (valuationOf q) (465)) (countLit q [239]) (countLit q [240]) (count465 q) 1 (meaning239 q) (meaning465 q) hs
  change valuationOf q 239 = false ∨ valuationOf q 465 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1149 (q : Snake 81) (h : Conditions q) : valuation q 239 = false ∨ valuation q 465 = true := counterClause1149 (baseVal q)

theorem counterClause1150 (q : Nat → Bool) : valuationOf q 241 = false ∨ valuationOf q 467 = true := by
  have hs : count467 q = (countLit q [241]) + (countLit q [242]) := List.countP_append (p := literal q) (l₁ := [241]) (l₂ := [242])
  have hm := merge_left (literal (valuationOf q) (241)) (literal (valuationOf q) (467)) (countLit q [241]) (countLit q [242]) (count467 q) 1 (meaning241 q) (meaning467 q) hs
  change valuationOf q 241 = false ∨ valuationOf q 467 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1150 (q : Snake 81) (h : Conditions q) : valuation q 241 = false ∨ valuation q 467 = true := counterClause1150 (baseVal q)

theorem counterClause1151 (q : Nat → Bool) : valuationOf q 467 = false ∨ valuationOf q 469 = true := by
  have hs : count469 q = (countLit q [239, 240]) + (countLit q [241, 242]) := List.countP_append (p := literal q) (l₁ := [239, 240]) (l₂ := [241, 242])
  have hm := merge_right (literal (valuationOf q) (467)) (literal (valuationOf q) (469)) (countLit q [239, 240]) (countLit q [241, 242]) (count469 q) 1 (meaning467 q) (meaning469 q) hs
  change valuationOf q 467 = false ∨ valuationOf q 469 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1151 (q : Snake 81) (h : Conditions q) : valuation q 467 = false ∨ valuation q 469 = true := counterClause1151 (baseVal q)

theorem counterClause1152 (q : Nat → Bool) : valuationOf q 465 = false ∨ valuationOf q 469 = true := by
  have hs : count469 q = (countLit q [239, 240]) + (countLit q [241, 242]) := List.countP_append (p := literal q) (l₁ := [239, 240]) (l₂ := [241, 242])
  have hm := merge_left (literal (valuationOf q) (465)) (literal (valuationOf q) (469)) (countLit q [239, 240]) (countLit q [241, 242]) (count469 q) 1 (meaning465 q) (meaning469 q) hs
  change valuationOf q 465 = false ∨ valuationOf q 469 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1152 (q : Snake 81) (h : Conditions q) : valuation q 465 = false ∨ valuation q 469 = true := counterClause1152 (baseVal q)

theorem block35 (q : Snake 81) (h : Conditions q) : B112E019.Block35 (valuation q) :=
  ⟨clause1121 q h, clause1122 q h, clause1123 q h, clause1124 q h, clause1125 q h, clause1126 q h, clause1127 q h, clause1128 q h, clause1129 q h, clause1130 q h, clause1131 q h, clause1132 q h, clause1133 q h, clause1134 q h, clause1135 q h, clause1136 q h, clause1137 q h, clause1138 q h, clause1139 q h, clause1140 q h, clause1141 q h, clause1142 q h, clause1143 q h, clause1144 q h, clause1145 q h, clause1146 q h, clause1147 q h, clause1148 q h, clause1149 q h, clause1150 q h, clause1151 q h, clause1152 q h⟩

end
end Snake9.Regrowth.E112019
