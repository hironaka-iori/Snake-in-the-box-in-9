import E112260Semantics
import B112E260Inputs
namespace Snake9.Regrowth.E112260
noncomputable section
local instance blockDec33 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1057 (q : Nat → Bool) : valuationOf q 425 = false ∨ valuationOf q 433 = true := by
  have hs : count433 q = (countLit q [215, 216, 217, 218]) + (countLit q [219, 220, 221, 222]) := List.countP_append (p := literal q) (l₁ := [215, 216, 217, 218]) (l₂ := [219, 220, 221, 222])
  have hm := merge_left (literal (valuationOf q) (425)) (literal (valuationOf q) (433)) (countLit q [215, 216, 217, 218]) (countLit q [219, 220, 221, 222]) (count433 q) 1 (meaning425 q) (meaning433 q) hs
  change valuationOf q 425 = false ∨ valuationOf q 433 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1057 (q : Snake 81) (h : Conditions q) : valuation q 425 = false ∨ valuation q 433 = true := counterClause1057 (baseVal q)

theorem counterClause1058 (q : Nat → Bool) : valuationOf q 426 = false ∨ valuationOf q 434 = true := by
  have hs : count433 q = (countLit q [215, 216, 217, 218]) + (countLit q [219, 220, 221, 222]) := List.countP_append (p := literal q) (l₁ := [215, 216, 217, 218]) (l₂ := [219, 220, 221, 222])
  have hm := merge_left (literal (valuationOf q) (426)) (literal (valuationOf q) (434)) (countLit q [215, 216, 217, 218]) (countLit q [219, 220, 221, 222]) (count433 q) 2 (meaning426 q) (meaning434 q) hs
  change valuationOf q 426 = false ∨ valuationOf q 434 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1058 (q : Snake 81) (h : Conditions q) : valuation q 426 = false ∨ valuation q 434 = true := counterClause1058 (baseVal q)

theorem counterClause1059 (q : Nat → Bool) : valuationOf q 433 = false ∨ valuationOf q 435 = true := by
  have hs : count435 q = (countLit q [206, 207, 208, 209, 210, 212, 213, 214]) + (countLit q [215, 216, 217, 218, 219, 220, 221, 222]) := List.countP_append (p := literal q) (l₁ := [206, 207, 208, 209, 210, 212, 213, 214]) (l₂ := [215, 216, 217, 218, 219, 220, 221, 222])
  have hm := merge_right (literal (valuationOf q) (433)) (literal (valuationOf q) (435)) (countLit q [206, 207, 208, 209, 210, 212, 213, 214]) (countLit q [215, 216, 217, 218, 219, 220, 221, 222]) (count435 q) 1 (meaning433 q) (meaning435 q) hs
  change valuationOf q 433 = false ∨ valuationOf q 435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1059 (q : Snake 81) (h : Conditions q) : valuation q 433 = false ∨ valuation q 435 = true := counterClause1059 (baseVal q)

theorem counterClause1060 (q : Nat → Bool) : valuationOf q 434 = false ∨ valuationOf q 436 = true := by
  have hs : count435 q = (countLit q [206, 207, 208, 209, 210, 212, 213, 214]) + (countLit q [215, 216, 217, 218, 219, 220, 221, 222]) := List.countP_append (p := literal q) (l₁ := [206, 207, 208, 209, 210, 212, 213, 214]) (l₂ := [215, 216, 217, 218, 219, 220, 221, 222])
  have hm := merge_right (literal (valuationOf q) (434)) (literal (valuationOf q) (436)) (countLit q [206, 207, 208, 209, 210, 212, 213, 214]) (countLit q [215, 216, 217, 218, 219, 220, 221, 222]) (count435 q) 2 (meaning434 q) (meaning436 q) hs
  change valuationOf q 434 = false ∨ valuationOf q 436 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1060 (q : Snake 81) (h : Conditions q) : valuation q 434 = false ∨ valuation q 436 = true := counterClause1060 (baseVal q)

theorem counterClause1061 (q : Nat → Bool) : valuationOf q 419 = false ∨ valuationOf q 435 = true := by
  have hs : count435 q = (countLit q [206, 207, 208, 209, 210, 212, 213, 214]) + (countLit q [215, 216, 217, 218, 219, 220, 221, 222]) := List.countP_append (p := literal q) (l₁ := [206, 207, 208, 209, 210, 212, 213, 214]) (l₂ := [215, 216, 217, 218, 219, 220, 221, 222])
  have hm := merge_left (literal (valuationOf q) (419)) (literal (valuationOf q) (435)) (countLit q [206, 207, 208, 209, 210, 212, 213, 214]) (countLit q [215, 216, 217, 218, 219, 220, 221, 222]) (count435 q) 1 (meaning419 q) (meaning435 q) hs
  change valuationOf q 419 = false ∨ valuationOf q 435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1061 (q : Snake 81) (h : Conditions q) : valuation q 419 = false ∨ valuation q 435 = true := counterClause1061 (baseVal q)

theorem counterClause1062 (q : Nat → Bool) : valuationOf q 419 = false ∨ valuationOf q 433 = false ∨ valuationOf q 436 = true := by
  have hs : count435 q = (countLit q [206, 207, 208, 209, 210, 212, 213, 214]) + (countLit q [215, 216, 217, 218, 219, 220, 221, 222]) := List.countP_append (p := literal q) (l₁ := [206, 207, 208, 209, 210, 212, 213, 214]) (l₂ := [215, 216, 217, 218, 219, 220, 221, 222])
  have hm := merge_two (literal (valuationOf q) (419)) (literal (valuationOf q) (433)) (literal (valuationOf q) (436)) (countLit q [206, 207, 208, 209, 210, 212, 213, 214]) (countLit q [215, 216, 217, 218, 219, 220, 221, 222]) (count435 q) 1 1 (meaning419 q) (meaning433 q) (meaning436 q) hs
  change valuationOf q 419 = false ∨ valuationOf q 433 = false ∨ valuationOf q 436 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1062 (q : Snake 81) (h : Conditions q) : valuation q 419 = false ∨ valuation q 433 = false ∨ valuation q 436 = true := counterClause1062 (baseVal q)

theorem counterClause1063 (q : Nat → Bool) : valuationOf q 435 = false ∨ valuationOf q 437 = true := by
  have hs : count437 q = (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205]) + (countLit q [206, 207, 208, 209, 210, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) := List.countP_append (p := literal q) (l₁ := [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205]) (l₂ := [206, 207, 208, 209, 210, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222])
  have hm := merge_right (literal (valuationOf q) (435)) (literal (valuationOf q) (437)) (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205]) (countLit q [206, 207, 208, 209, 210, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) (count437 q) 1 (meaning435 q) (meaning437 q) hs
  change valuationOf q 435 = false ∨ valuationOf q 437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1063 (q : Snake 81) (h : Conditions q) : valuation q 435 = false ∨ valuation q 437 = true := counterClause1063 (baseVal q)

theorem counterClause1064 (q : Nat → Bool) : valuationOf q 436 = false ∨ valuationOf q 438 = true := by
  have hs : count437 q = (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205]) + (countLit q [206, 207, 208, 209, 210, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) := List.countP_append (p := literal q) (l₁ := [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205]) (l₂ := [206, 207, 208, 209, 210, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222])
  have hm := merge_right (literal (valuationOf q) (436)) (literal (valuationOf q) (438)) (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205]) (countLit q [206, 207, 208, 209, 210, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) (count437 q) 2 (meaning436 q) (meaning438 q) hs
  change valuationOf q 436 = false ∨ valuationOf q 438 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1064 (q : Snake 81) (h : Conditions q) : valuation q 436 = false ∨ valuation q 438 = true := counterClause1064 (baseVal q)

theorem counterClause1065 (q : Nat → Bool) : valuationOf q 405 = false ∨ valuationOf q 437 = true := by
  have hs : count437 q = (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205]) + (countLit q [206, 207, 208, 209, 210, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) := List.countP_append (p := literal q) (l₁ := [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205]) (l₂ := [206, 207, 208, 209, 210, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222])
  have hm := merge_left (literal (valuationOf q) (405)) (literal (valuationOf q) (437)) (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205]) (countLit q [206, 207, 208, 209, 210, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) (count437 q) 1 (meaning405 q) (meaning437 q) hs
  change valuationOf q 405 = false ∨ valuationOf q 437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1065 (q : Snake 81) (h : Conditions q) : valuation q 405 = false ∨ valuation q 437 = true := counterClause1065 (baseVal q)

theorem counterClause1066 (q : Nat → Bool) : valuationOf q 405 = false ∨ valuationOf q 435 = false ∨ valuationOf q 438 = true := by
  have hs : count437 q = (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205]) + (countLit q [206, 207, 208, 209, 210, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) := List.countP_append (p := literal q) (l₁ := [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205]) (l₂ := [206, 207, 208, 209, 210, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222])
  have hm := merge_two (literal (valuationOf q) (405)) (literal (valuationOf q) (435)) (literal (valuationOf q) (438)) (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205]) (countLit q [206, 207, 208, 209, 210, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) (count437 q) 1 1 (meaning405 q) (meaning435 q) (meaning438 q) hs
  change valuationOf q 405 = false ∨ valuationOf q 435 = false ∨ valuationOf q 438 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1066 (q : Snake 81) (h : Conditions q) : valuation q 405 = false ∨ valuation q 435 = false ∨ valuation q 438 = true := counterClause1066 (baseVal q)

theorem counterClause1067 (q : Nat → Bool) : valuationOf q 406 = false ∨ valuationOf q 438 = true := by
  have hs : count437 q = (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205]) + (countLit q [206, 207, 208, 209, 210, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) := List.countP_append (p := literal q) (l₁ := [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205]) (l₂ := [206, 207, 208, 209, 210, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222])
  have hm := merge_left (literal (valuationOf q) (406)) (literal (valuationOf q) (438)) (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205]) (countLit q [206, 207, 208, 209, 210, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) (count437 q) 2 (meaning406 q) (meaning438 q) hs
  change valuationOf q 406 = false ∨ valuationOf q 438 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1067 (q : Snake 81) (h : Conditions q) : valuation q 406 = false ∨ valuation q 438 = true := counterClause1067 (baseVal q)

theorem counterClause1068 (q : Nat → Bool) : valuationOf q 223 = false ∨ valuationOf q 439 = true := by
  have hs : count439 q = (countLit q [223]) + (countLit q [224]) := List.countP_append (p := literal q) (l₁ := [223]) (l₂ := [224])
  have hm := merge_left (literal (valuationOf q) (223)) (literal (valuationOf q) (439)) (countLit q [223]) (countLit q [224]) (count439 q) 1 (meaning223 q) (meaning439 q) hs
  change valuationOf q 223 = false ∨ valuationOf q 439 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1068 (q : Snake 81) (h : Conditions q) : valuation q 223 = false ∨ valuation q 439 = true := counterClause1068 (baseVal q)

theorem counterClause1069 (q : Nat → Bool) : valuationOf q 225 = false ∨ valuationOf q 441 = true := by
  have hs : count441 q = (countLit q [225]) + (countLit q [226]) := List.countP_append (p := literal q) (l₁ := [225]) (l₂ := [226])
  have hm := merge_left (literal (valuationOf q) (225)) (literal (valuationOf q) (441)) (countLit q [225]) (countLit q [226]) (count441 q) 1 (meaning225 q) (meaning441 q) hs
  change valuationOf q 225 = false ∨ valuationOf q 441 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1069 (q : Snake 81) (h : Conditions q) : valuation q 225 = false ∨ valuation q 441 = true := counterClause1069 (baseVal q)

theorem counterClause1070 (q : Nat → Bool) : valuationOf q 441 = false ∨ valuationOf q 443 = true := by
  have hs : count443 q = (countLit q [223, 224]) + (countLit q [225, 226]) := List.countP_append (p := literal q) (l₁ := [223, 224]) (l₂ := [225, 226])
  have hm := merge_right (literal (valuationOf q) (441)) (literal (valuationOf q) (443)) (countLit q [223, 224]) (countLit q [225, 226]) (count443 q) 1 (meaning441 q) (meaning443 q) hs
  change valuationOf q 441 = false ∨ valuationOf q 443 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1070 (q : Snake 81) (h : Conditions q) : valuation q 441 = false ∨ valuation q 443 = true := counterClause1070 (baseVal q)

theorem counterClause1071 (q : Nat → Bool) : valuationOf q 439 = false ∨ valuationOf q 443 = true := by
  have hs : count443 q = (countLit q [223, 224]) + (countLit q [225, 226]) := List.countP_append (p := literal q) (l₁ := [223, 224]) (l₂ := [225, 226])
  have hm := merge_left (literal (valuationOf q) (439)) (literal (valuationOf q) (443)) (countLit q [223, 224]) (countLit q [225, 226]) (count443 q) 1 (meaning439 q) (meaning443 q) hs
  change valuationOf q 439 = false ∨ valuationOf q 443 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1071 (q : Snake 81) (h : Conditions q) : valuation q 439 = false ∨ valuation q 443 = true := counterClause1071 (baseVal q)

theorem counterClause1072 (q : Nat → Bool) : valuationOf q 227 = false ∨ valuationOf q 445 = true := by
  have hs : count445 q = (countLit q [227]) + (countLit q [228]) := List.countP_append (p := literal q) (l₁ := [227]) (l₂ := [228])
  have hm := merge_left (literal (valuationOf q) (227)) (literal (valuationOf q) (445)) (countLit q [227]) (countLit q [228]) (count445 q) 1 (meaning227 q) (meaning445 q) hs
  change valuationOf q 227 = false ∨ valuationOf q 445 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1072 (q : Snake 81) (h : Conditions q) : valuation q 227 = false ∨ valuation q 445 = true := counterClause1072 (baseVal q)

theorem counterClause1073 (q : Nat → Bool) : valuationOf q 230 = false ∨ valuationOf q 447 = true := by
  have hs : count447 q = (countLit q [229]) + (countLit q [230]) := List.countP_append (p := literal q) (l₁ := [229]) (l₂ := [230])
  have hm := merge_right (literal (valuationOf q) (230)) (literal (valuationOf q) (447)) (countLit q [229]) (countLit q [230]) (count447 q) 1 (meaning230 q) (meaning447 q) hs
  change valuationOf q 230 = false ∨ valuationOf q 447 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1073 (q : Snake 81) (h : Conditions q) : valuation q 230 = false ∨ valuation q 447 = true := counterClause1073 (baseVal q)

theorem counterClause1074 (q : Nat → Bool) : valuationOf q 447 = false ∨ valuationOf q 449 = true := by
  have hs : count449 q = (countLit q [227, 228]) + (countLit q [229, 230]) := List.countP_append (p := literal q) (l₁ := [227, 228]) (l₂ := [229, 230])
  have hm := merge_right (literal (valuationOf q) (447)) (literal (valuationOf q) (449)) (countLit q [227, 228]) (countLit q [229, 230]) (count449 q) 1 (meaning447 q) (meaning449 q) hs
  change valuationOf q 447 = false ∨ valuationOf q 449 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1074 (q : Snake 81) (h : Conditions q) : valuation q 447 = false ∨ valuation q 449 = true := counterClause1074 (baseVal q)

theorem counterClause1075 (q : Nat → Bool) : valuationOf q 445 = false ∨ valuationOf q 449 = true := by
  have hs : count449 q = (countLit q [227, 228]) + (countLit q [229, 230]) := List.countP_append (p := literal q) (l₁ := [227, 228]) (l₂ := [229, 230])
  have hm := merge_left (literal (valuationOf q) (445)) (literal (valuationOf q) (449)) (countLit q [227, 228]) (countLit q [229, 230]) (count449 q) 1 (meaning445 q) (meaning449 q) hs
  change valuationOf q 445 = false ∨ valuationOf q 449 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1075 (q : Snake 81) (h : Conditions q) : valuation q 445 = false ∨ valuation q 449 = true := counterClause1075 (baseVal q)

theorem counterClause1076 (q : Nat → Bool) : valuationOf q 449 = false ∨ valuationOf q 451 = true := by
  have hs : count451 q = (countLit q [223, 224, 225, 226]) + (countLit q [227, 228, 229, 230]) := List.countP_append (p := literal q) (l₁ := [223, 224, 225, 226]) (l₂ := [227, 228, 229, 230])
  have hm := merge_right (literal (valuationOf q) (449)) (literal (valuationOf q) (451)) (countLit q [223, 224, 225, 226]) (countLit q [227, 228, 229, 230]) (count451 q) 1 (meaning449 q) (meaning451 q) hs
  change valuationOf q 449 = false ∨ valuationOf q 451 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1076 (q : Snake 81) (h : Conditions q) : valuation q 449 = false ∨ valuation q 451 = true := counterClause1076 (baseVal q)

theorem counterClause1077 (q : Nat → Bool) : valuationOf q 443 = false ∨ valuationOf q 451 = true := by
  have hs : count451 q = (countLit q [223, 224, 225, 226]) + (countLit q [227, 228, 229, 230]) := List.countP_append (p := literal q) (l₁ := [223, 224, 225, 226]) (l₂ := [227, 228, 229, 230])
  have hm := merge_left (literal (valuationOf q) (443)) (literal (valuationOf q) (451)) (countLit q [223, 224, 225, 226]) (countLit q [227, 228, 229, 230]) (count451 q) 1 (meaning443 q) (meaning451 q) hs
  change valuationOf q 443 = false ∨ valuationOf q 451 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1077 (q : Snake 81) (h : Conditions q) : valuation q 443 = false ∨ valuation q 451 = true := counterClause1077 (baseVal q)

theorem counterClause1078 (q : Nat → Bool) : valuationOf q 443 = false ∨ valuationOf q 449 = false ∨ valuationOf q 452 = true := by
  have hs : count451 q = (countLit q [223, 224, 225, 226]) + (countLit q [227, 228, 229, 230]) := List.countP_append (p := literal q) (l₁ := [223, 224, 225, 226]) (l₂ := [227, 228, 229, 230])
  have hm := merge_two (literal (valuationOf q) (443)) (literal (valuationOf q) (449)) (literal (valuationOf q) (452)) (countLit q [223, 224, 225, 226]) (countLit q [227, 228, 229, 230]) (count451 q) 1 1 (meaning443 q) (meaning449 q) (meaning452 q) hs
  change valuationOf q 443 = false ∨ valuationOf q 449 = false ∨ valuationOf q 452 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1078 (q : Snake 81) (h : Conditions q) : valuation q 443 = false ∨ valuation q 449 = false ∨ valuation q 452 = true := counterClause1078 (baseVal q)

theorem counterClause1079 (q : Nat → Bool) : valuationOf q 232 = false ∨ valuationOf q 453 = true := by
  have hs : count453 q = (countLit q [231]) + (countLit q [232]) := List.countP_append (p := literal q) (l₁ := [231]) (l₂ := [232])
  have hm := merge_right (literal (valuationOf q) (232)) (literal (valuationOf q) (453)) (countLit q [231]) (countLit q [232]) (count453 q) 1 (meaning232 q) (meaning453 q) hs
  change valuationOf q 232 = false ∨ valuationOf q 453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1079 (q : Snake 81) (h : Conditions q) : valuation q 232 = false ∨ valuation q 453 = true := counterClause1079 (baseVal q)

theorem counterClause1080 (q : Nat → Bool) : valuationOf q 453 = false ∨ valuationOf q 457 = true := by
  have hs : count457 q = (countLit q [231, 232]) + (countLit q [233, 234]) := List.countP_append (p := literal q) (l₁ := [231, 232]) (l₂ := [233, 234])
  have hm := merge_left (literal (valuationOf q) (453)) (literal (valuationOf q) (457)) (countLit q [231, 232]) (countLit q [233, 234]) (count457 q) 1 (meaning453 q) (meaning457 q) hs
  change valuationOf q 453 = false ∨ valuationOf q 457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1080 (q : Snake 81) (h : Conditions q) : valuation q 453 = false ∨ valuation q 457 = true := counterClause1080 (baseVal q)

theorem counterClause1081 (q : Nat → Bool) : valuationOf q 235 = false ∨ valuationOf q 459 = true := by
  have hs : count459 q = (countLit q [235]) + (countLit q [236]) := List.countP_append (p := literal q) (l₁ := [235]) (l₂ := [236])
  have hm := merge_left (literal (valuationOf q) (235)) (literal (valuationOf q) (459)) (countLit q [235]) (countLit q [236]) (count459 q) 1 (meaning235 q) (meaning459 q) hs
  change valuationOf q 235 = false ∨ valuationOf q 459 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1081 (q : Snake 81) (h : Conditions q) : valuation q 235 = false ∨ valuation q 459 = true := counterClause1081 (baseVal q)

theorem counterClause1082 (q : Nat → Bool) : valuationOf q 238 = false ∨ valuationOf q 461 = true := by
  have hs : count461 q = (countLit q [237]) + (countLit q [238]) := List.countP_append (p := literal q) (l₁ := [237]) (l₂ := [238])
  have hm := merge_right (literal (valuationOf q) (238)) (literal (valuationOf q) (461)) (countLit q [237]) (countLit q [238]) (count461 q) 1 (meaning238 q) (meaning461 q) hs
  change valuationOf q 238 = false ∨ valuationOf q 461 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1082 (q : Snake 81) (h : Conditions q) : valuation q 238 = false ∨ valuation q 461 = true := counterClause1082 (baseVal q)

theorem counterClause1083 (q : Nat → Bool) : valuationOf q 237 = false ∨ valuationOf q 461 = true := by
  have hs : count461 q = (countLit q [237]) + (countLit q [238]) := List.countP_append (p := literal q) (l₁ := [237]) (l₂ := [238])
  have hm := merge_left (literal (valuationOf q) (237)) (literal (valuationOf q) (461)) (countLit q [237]) (countLit q [238]) (count461 q) 1 (meaning237 q) (meaning461 q) hs
  change valuationOf q 237 = false ∨ valuationOf q 461 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1083 (q : Snake 81) (h : Conditions q) : valuation q 237 = false ∨ valuation q 461 = true := counterClause1083 (baseVal q)

theorem counterClause1084 (q : Nat → Bool) : valuationOf q 237 = false ∨ valuationOf q 238 = false ∨ valuationOf q 462 = true := by
  have hs : count461 q = (countLit q [237]) + (countLit q [238]) := List.countP_append (p := literal q) (l₁ := [237]) (l₂ := [238])
  have hm := merge_two (literal (valuationOf q) (237)) (literal (valuationOf q) (238)) (literal (valuationOf q) (462)) (countLit q [237]) (countLit q [238]) (count461 q) 1 1 (meaning237 q) (meaning238 q) (meaning462 q) hs
  change valuationOf q 237 = false ∨ valuationOf q 238 = false ∨ valuationOf q 462 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1084 (q : Snake 81) (h : Conditions q) : valuation q 237 = false ∨ valuation q 238 = false ∨ valuation q 462 = true := counterClause1084 (baseVal q)

theorem counterClause1085 (q : Nat → Bool) : valuationOf q 461 = false ∨ valuationOf q 463 = true := by
  have hs : count463 q = (countLit q [235, 236]) + (countLit q [237, 238]) := List.countP_append (p := literal q) (l₁ := [235, 236]) (l₂ := [237, 238])
  have hm := merge_right (literal (valuationOf q) (461)) (literal (valuationOf q) (463)) (countLit q [235, 236]) (countLit q [237, 238]) (count463 q) 1 (meaning461 q) (meaning463 q) hs
  change valuationOf q 461 = false ∨ valuationOf q 463 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1085 (q : Snake 81) (h : Conditions q) : valuation q 461 = false ∨ valuation q 463 = true := counterClause1085 (baseVal q)

theorem counterClause1086 (q : Nat → Bool) : valuationOf q 462 = false ∨ valuationOf q 464 = true := by
  have hs : count463 q = (countLit q [235, 236]) + (countLit q [237, 238]) := List.countP_append (p := literal q) (l₁ := [235, 236]) (l₂ := [237, 238])
  have hm := merge_right (literal (valuationOf q) (462)) (literal (valuationOf q) (464)) (countLit q [235, 236]) (countLit q [237, 238]) (count463 q) 2 (meaning462 q) (meaning464 q) hs
  change valuationOf q 462 = false ∨ valuationOf q 464 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1086 (q : Snake 81) (h : Conditions q) : valuation q 462 = false ∨ valuation q 464 = true := counterClause1086 (baseVal q)

theorem counterClause1087 (q : Nat → Bool) : valuationOf q 459 = false ∨ valuationOf q 463 = true := by
  have hs : count463 q = (countLit q [235, 236]) + (countLit q [237, 238]) := List.countP_append (p := literal q) (l₁ := [235, 236]) (l₂ := [237, 238])
  have hm := merge_left (literal (valuationOf q) (459)) (literal (valuationOf q) (463)) (countLit q [235, 236]) (countLit q [237, 238]) (count463 q) 1 (meaning459 q) (meaning463 q) hs
  change valuationOf q 459 = false ∨ valuationOf q 463 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1087 (q : Snake 81) (h : Conditions q) : valuation q 459 = false ∨ valuation q 463 = true := counterClause1087 (baseVal q)

theorem counterClause1088 (q : Nat → Bool) : valuationOf q 459 = false ∨ valuationOf q 461 = false ∨ valuationOf q 464 = true := by
  have hs : count463 q = (countLit q [235, 236]) + (countLit q [237, 238]) := List.countP_append (p := literal q) (l₁ := [235, 236]) (l₂ := [237, 238])
  have hm := merge_two (literal (valuationOf q) (459)) (literal (valuationOf q) (461)) (literal (valuationOf q) (464)) (countLit q [235, 236]) (countLit q [237, 238]) (count463 q) 1 1 (meaning459 q) (meaning461 q) (meaning464 q) hs
  change valuationOf q 459 = false ∨ valuationOf q 461 = false ∨ valuationOf q 464 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1088 (q : Snake 81) (h : Conditions q) : valuation q 459 = false ∨ valuation q 461 = false ∨ valuation q 464 = true := counterClause1088 (baseVal q)

theorem block33 (q : Snake 81) (h : Conditions q) : B112E260.Block33 (valuation q) :=
  ⟨clause1057 q h, clause1058 q h, clause1059 q h, clause1060 q h, clause1061 q h, clause1062 q h, clause1063 q h, clause1064 q h, clause1065 q h, clause1066 q h, clause1067 q h, clause1068 q h, clause1069 q h, clause1070 q h, clause1071 q h, clause1072 q h, clause1073 q h, clause1074 q h, clause1075 q h, clause1076 q h, clause1077 q h, clause1078 q h, clause1079 q h, clause1080 q h, clause1081 q h, clause1082 q h, clause1083 q h, clause1084 q h, clause1085 q h, clause1086 q h, clause1087 q h, clause1088 q h⟩

end
end Snake9.Regrowth.E112260
