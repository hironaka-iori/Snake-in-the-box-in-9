import E112260Semantics
import B112E260Inputs
namespace Snake9.Regrowth.E112260
noncomputable section
local instance blockDec34 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1089 (q : Nat → Bool) : valuationOf q 463 = false ∨ valuationOf q 465 = true := by
  have hs : count465 q = (countLit q [231, 232, 233, 234]) + (countLit q [235, 236, 237, 238]) := List.countP_append (p := literal q) (l₁ := [231, 232, 233, 234]) (l₂ := [235, 236, 237, 238])
  have hm := merge_right (literal (valuationOf q) (463)) (literal (valuationOf q) (465)) (countLit q [231, 232, 233, 234]) (countLit q [235, 236, 237, 238]) (count465 q) 1 (meaning463 q) (meaning465 q) hs
  change valuationOf q 463 = false ∨ valuationOf q 465 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1089 (q : Snake 81) (h : Conditions q) : valuation q 463 = false ∨ valuation q 465 = true := counterClause1089 (baseVal q)

theorem counterClause1090 (q : Nat → Bool) : valuationOf q 464 = false ∨ valuationOf q 466 = true := by
  have hs : count465 q = (countLit q [231, 232, 233, 234]) + (countLit q [235, 236, 237, 238]) := List.countP_append (p := literal q) (l₁ := [231, 232, 233, 234]) (l₂ := [235, 236, 237, 238])
  have hm := merge_right (literal (valuationOf q) (464)) (literal (valuationOf q) (466)) (countLit q [231, 232, 233, 234]) (countLit q [235, 236, 237, 238]) (count465 q) 2 (meaning464 q) (meaning466 q) hs
  change valuationOf q 464 = false ∨ valuationOf q 466 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1090 (q : Snake 81) (h : Conditions q) : valuation q 464 = false ∨ valuation q 466 = true := counterClause1090 (baseVal q)

theorem counterClause1091 (q : Nat → Bool) : valuationOf q 457 = false ∨ valuationOf q 465 = true := by
  have hs : count465 q = (countLit q [231, 232, 233, 234]) + (countLit q [235, 236, 237, 238]) := List.countP_append (p := literal q) (l₁ := [231, 232, 233, 234]) (l₂ := [235, 236, 237, 238])
  have hm := merge_left (literal (valuationOf q) (457)) (literal (valuationOf q) (465)) (countLit q [231, 232, 233, 234]) (countLit q [235, 236, 237, 238]) (count465 q) 1 (meaning457 q) (meaning465 q) hs
  change valuationOf q 457 = false ∨ valuationOf q 465 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1091 (q : Snake 81) (h : Conditions q) : valuation q 457 = false ∨ valuation q 465 = true := counterClause1091 (baseVal q)

theorem counterClause1092 (q : Nat → Bool) : valuationOf q 465 = false ∨ valuationOf q 467 = true := by
  have hs : count467 q = (countLit q [223, 224, 225, 226, 227, 228, 229, 230]) + (countLit q [231, 232, 233, 234, 235, 236, 237, 238]) := List.countP_append (p := literal q) (l₁ := [223, 224, 225, 226, 227, 228, 229, 230]) (l₂ := [231, 232, 233, 234, 235, 236, 237, 238])
  have hm := merge_right (literal (valuationOf q) (465)) (literal (valuationOf q) (467)) (countLit q [223, 224, 225, 226, 227, 228, 229, 230]) (countLit q [231, 232, 233, 234, 235, 236, 237, 238]) (count467 q) 1 (meaning465 q) (meaning467 q) hs
  change valuationOf q 465 = false ∨ valuationOf q 467 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1092 (q : Snake 81) (h : Conditions q) : valuation q 465 = false ∨ valuation q 467 = true := counterClause1092 (baseVal q)

theorem counterClause1093 (q : Nat → Bool) : valuationOf q 466 = false ∨ valuationOf q 468 = true := by
  have hs : count467 q = (countLit q [223, 224, 225, 226, 227, 228, 229, 230]) + (countLit q [231, 232, 233, 234, 235, 236, 237, 238]) := List.countP_append (p := literal q) (l₁ := [223, 224, 225, 226, 227, 228, 229, 230]) (l₂ := [231, 232, 233, 234, 235, 236, 237, 238])
  have hm := merge_right (literal (valuationOf q) (466)) (literal (valuationOf q) (468)) (countLit q [223, 224, 225, 226, 227, 228, 229, 230]) (countLit q [231, 232, 233, 234, 235, 236, 237, 238]) (count467 q) 2 (meaning466 q) (meaning468 q) hs
  change valuationOf q 466 = false ∨ valuationOf q 468 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1093 (q : Snake 81) (h : Conditions q) : valuation q 466 = false ∨ valuation q 468 = true := counterClause1093 (baseVal q)

theorem counterClause1094 (q : Nat → Bool) : valuationOf q 451 = false ∨ valuationOf q 467 = true := by
  have hs : count467 q = (countLit q [223, 224, 225, 226, 227, 228, 229, 230]) + (countLit q [231, 232, 233, 234, 235, 236, 237, 238]) := List.countP_append (p := literal q) (l₁ := [223, 224, 225, 226, 227, 228, 229, 230]) (l₂ := [231, 232, 233, 234, 235, 236, 237, 238])
  have hm := merge_left (literal (valuationOf q) (451)) (literal (valuationOf q) (467)) (countLit q [223, 224, 225, 226, 227, 228, 229, 230]) (countLit q [231, 232, 233, 234, 235, 236, 237, 238]) (count467 q) 1 (meaning451 q) (meaning467 q) hs
  change valuationOf q 451 = false ∨ valuationOf q 467 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1094 (q : Snake 81) (h : Conditions q) : valuation q 451 = false ∨ valuation q 467 = true := counterClause1094 (baseVal q)

theorem counterClause1095 (q : Nat → Bool) : valuationOf q 451 = false ∨ valuationOf q 465 = false ∨ valuationOf q 468 = true := by
  have hs : count467 q = (countLit q [223, 224, 225, 226, 227, 228, 229, 230]) + (countLit q [231, 232, 233, 234, 235, 236, 237, 238]) := List.countP_append (p := literal q) (l₁ := [223, 224, 225, 226, 227, 228, 229, 230]) (l₂ := [231, 232, 233, 234, 235, 236, 237, 238])
  have hm := merge_two (literal (valuationOf q) (451)) (literal (valuationOf q) (465)) (literal (valuationOf q) (468)) (countLit q [223, 224, 225, 226, 227, 228, 229, 230]) (countLit q [231, 232, 233, 234, 235, 236, 237, 238]) (count467 q) 1 1 (meaning451 q) (meaning465 q) (meaning468 q) hs
  change valuationOf q 451 = false ∨ valuationOf q 465 = false ∨ valuationOf q 468 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1095 (q : Snake 81) (h : Conditions q) : valuation q 451 = false ∨ valuation q 465 = false ∨ valuation q 468 = true := counterClause1095 (baseVal q)

theorem counterClause1096 (q : Nat → Bool) : valuationOf q 452 = false ∨ valuationOf q 468 = true := by
  have hs : count467 q = (countLit q [223, 224, 225, 226, 227, 228, 229, 230]) + (countLit q [231, 232, 233, 234, 235, 236, 237, 238]) := List.countP_append (p := literal q) (l₁ := [223, 224, 225, 226, 227, 228, 229, 230]) (l₂ := [231, 232, 233, 234, 235, 236, 237, 238])
  have hm := merge_left (literal (valuationOf q) (452)) (literal (valuationOf q) (468)) (countLit q [223, 224, 225, 226, 227, 228, 229, 230]) (countLit q [231, 232, 233, 234, 235, 236, 237, 238]) (count467 q) 2 (meaning452 q) (meaning468 q) hs
  change valuationOf q 452 = false ∨ valuationOf q 468 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1096 (q : Snake 81) (h : Conditions q) : valuation q 452 = false ∨ valuation q 468 = true := counterClause1096 (baseVal q)

theorem counterClause1097 (q : Nat → Bool) : valuationOf q 240 = false ∨ valuationOf q 469 = true := by
  have hs : count469 q = (countLit q [239]) + (countLit q [240]) := List.countP_append (p := literal q) (l₁ := [239]) (l₂ := [240])
  have hm := merge_right (literal (valuationOf q) (240)) (literal (valuationOf q) (469)) (countLit q [239]) (countLit q [240]) (count469 q) 1 (meaning240 q) (meaning469 q) hs
  change valuationOf q 240 = false ∨ valuationOf q 469 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1097 (q : Snake 81) (h : Conditions q) : valuation q 240 = false ∨ valuation q 469 = true := counterClause1097 (baseVal q)

theorem counterClause1098 (q : Nat → Bool) : valuationOf q 242 = false ∨ valuationOf q 471 = true := by
  have hs : count471 q = (countLit q [241]) + (countLit q [242]) := List.countP_append (p := literal q) (l₁ := [241]) (l₂ := [242])
  have hm := merge_right (literal (valuationOf q) (242)) (literal (valuationOf q) (471)) (countLit q [241]) (countLit q [242]) (count471 q) 1 (meaning242 q) (meaning471 q) hs
  change valuationOf q 242 = false ∨ valuationOf q 471 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1098 (q : Snake 81) (h : Conditions q) : valuation q 242 = false ∨ valuation q 471 = true := counterClause1098 (baseVal q)

theorem counterClause1099 (q : Nat → Bool) : valuationOf q 471 = false ∨ valuationOf q 473 = true := by
  have hs : count473 q = (countLit q [239, 240]) + (countLit q [241, 242]) := List.countP_append (p := literal q) (l₁ := [239, 240]) (l₂ := [241, 242])
  have hm := merge_right (literal (valuationOf q) (471)) (literal (valuationOf q) (473)) (countLit q [239, 240]) (countLit q [241, 242]) (count473 q) 1 (meaning471 q) (meaning473 q) hs
  change valuationOf q 471 = false ∨ valuationOf q 473 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1099 (q : Snake 81) (h : Conditions q) : valuation q 471 = false ∨ valuation q 473 = true := counterClause1099 (baseVal q)

theorem counterClause1100 (q : Nat → Bool) : valuationOf q 469 = false ∨ valuationOf q 473 = true := by
  have hs : count473 q = (countLit q [239, 240]) + (countLit q [241, 242]) := List.countP_append (p := literal q) (l₁ := [239, 240]) (l₂ := [241, 242])
  have hm := merge_left (literal (valuationOf q) (469)) (literal (valuationOf q) (473)) (countLit q [239, 240]) (countLit q [241, 242]) (count473 q) 1 (meaning469 q) (meaning473 q) hs
  change valuationOf q 469 = false ∨ valuationOf q 473 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1100 (q : Snake 81) (h : Conditions q) : valuation q 469 = false ∨ valuation q 473 = true := counterClause1100 (baseVal q)

theorem counterClause1101 (q : Nat → Bool) : valuationOf q 469 = false ∨ valuationOf q 471 = false ∨ valuationOf q 474 = true := by
  have hs : count473 q = (countLit q [239, 240]) + (countLit q [241, 242]) := List.countP_append (p := literal q) (l₁ := [239, 240]) (l₂ := [241, 242])
  have hm := merge_two (literal (valuationOf q) (469)) (literal (valuationOf q) (471)) (literal (valuationOf q) (474)) (countLit q [239, 240]) (countLit q [241, 242]) (count473 q) 1 1 (meaning469 q) (meaning471 q) (meaning474 q) hs
  change valuationOf q 469 = false ∨ valuationOf q 471 = false ∨ valuationOf q 474 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1101 (q : Snake 81) (h : Conditions q) : valuation q 469 = false ∨ valuation q 471 = false ∨ valuation q 474 = true := counterClause1101 (baseVal q)

theorem counterClause1102 (q : Nat → Bool) : valuationOf q 244 = false ∨ valuationOf q 475 = true := by
  have hs : count475 q = (countLit q [243]) + (countLit q [244]) := List.countP_append (p := literal q) (l₁ := [243]) (l₂ := [244])
  have hm := merge_right (literal (valuationOf q) (244)) (literal (valuationOf q) (475)) (countLit q [243]) (countLit q [244]) (count475 q) 1 (meaning244 q) (meaning475 q) hs
  change valuationOf q 244 = false ∨ valuationOf q 475 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1102 (q : Snake 81) (h : Conditions q) : valuation q 244 = false ∨ valuation q 475 = true := counterClause1102 (baseVal q)

theorem counterClause1103 (q : Nat → Bool) : valuationOf q 246 = false ∨ valuationOf q 477 = true := by
  have hs : count477 q = (countLit q [245]) + (countLit q [246]) := List.countP_append (p := literal q) (l₁ := [245]) (l₂ := [246])
  have hm := merge_right (literal (valuationOf q) (246)) (literal (valuationOf q) (477)) (countLit q [245]) (countLit q [246]) (count477 q) 1 (meaning246 q) (meaning477 q) hs
  change valuationOf q 246 = false ∨ valuationOf q 477 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1103 (q : Snake 81) (h : Conditions q) : valuation q 246 = false ∨ valuation q 477 = true := counterClause1103 (baseVal q)

theorem counterClause1104 (q : Nat → Bool) : valuationOf q 477 = false ∨ valuationOf q 479 = true := by
  have hs : count479 q = (countLit q [243, 244]) + (countLit q [245, 246]) := List.countP_append (p := literal q) (l₁ := [243, 244]) (l₂ := [245, 246])
  have hm := merge_right (literal (valuationOf q) (477)) (literal (valuationOf q) (479)) (countLit q [243, 244]) (countLit q [245, 246]) (count479 q) 1 (meaning477 q) (meaning479 q) hs
  change valuationOf q 477 = false ∨ valuationOf q 479 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1104 (q : Snake 81) (h : Conditions q) : valuation q 477 = false ∨ valuation q 479 = true := counterClause1104 (baseVal q)

theorem counterClause1105 (q : Nat → Bool) : valuationOf q 475 = false ∨ valuationOf q 479 = true := by
  have hs : count479 q = (countLit q [243, 244]) + (countLit q [245, 246]) := List.countP_append (p := literal q) (l₁ := [243, 244]) (l₂ := [245, 246])
  have hm := merge_left (literal (valuationOf q) (475)) (literal (valuationOf q) (479)) (countLit q [243, 244]) (countLit q [245, 246]) (count479 q) 1 (meaning475 q) (meaning479 q) hs
  change valuationOf q 475 = false ∨ valuationOf q 479 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1105 (q : Snake 81) (h : Conditions q) : valuation q 475 = false ∨ valuation q 479 = true := counterClause1105 (baseVal q)

theorem counterClause1106 (q : Nat → Bool) : valuationOf q 479 = false ∨ valuationOf q 481 = true := by
  have hs : count481 q = (countLit q [239, 240, 241, 242]) + (countLit q [243, 244, 245, 246]) := List.countP_append (p := literal q) (l₁ := [239, 240, 241, 242]) (l₂ := [243, 244, 245, 246])
  have hm := merge_right (literal (valuationOf q) (479)) (literal (valuationOf q) (481)) (countLit q [239, 240, 241, 242]) (countLit q [243, 244, 245, 246]) (count481 q) 1 (meaning479 q) (meaning481 q) hs
  change valuationOf q 479 = false ∨ valuationOf q 481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1106 (q : Snake 81) (h : Conditions q) : valuation q 479 = false ∨ valuation q 481 = true := counterClause1106 (baseVal q)

theorem counterClause1107 (q : Nat → Bool) : valuationOf q 473 = false ∨ valuationOf q 481 = true := by
  have hs : count481 q = (countLit q [239, 240, 241, 242]) + (countLit q [243, 244, 245, 246]) := List.countP_append (p := literal q) (l₁ := [239, 240, 241, 242]) (l₂ := [243, 244, 245, 246])
  have hm := merge_left (literal (valuationOf q) (473)) (literal (valuationOf q) (481)) (countLit q [239, 240, 241, 242]) (countLit q [243, 244, 245, 246]) (count481 q) 1 (meaning473 q) (meaning481 q) hs
  change valuationOf q 473 = false ∨ valuationOf q 481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1107 (q : Snake 81) (h : Conditions q) : valuation q 473 = false ∨ valuation q 481 = true := counterClause1107 (baseVal q)

theorem counterClause1108 (q : Nat → Bool) : valuationOf q 473 = false ∨ valuationOf q 479 = false ∨ valuationOf q 482 = true := by
  have hs : count481 q = (countLit q [239, 240, 241, 242]) + (countLit q [243, 244, 245, 246]) := List.countP_append (p := literal q) (l₁ := [239, 240, 241, 242]) (l₂ := [243, 244, 245, 246])
  have hm := merge_two (literal (valuationOf q) (473)) (literal (valuationOf q) (479)) (literal (valuationOf q) (482)) (countLit q [239, 240, 241, 242]) (countLit q [243, 244, 245, 246]) (count481 q) 1 1 (meaning473 q) (meaning479 q) (meaning482 q) hs
  change valuationOf q 473 = false ∨ valuationOf q 479 = false ∨ valuationOf q 482 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1108 (q : Snake 81) (h : Conditions q) : valuation q 473 = false ∨ valuation q 479 = false ∨ valuation q 482 = true := counterClause1108 (baseVal q)

theorem counterClause1109 (q : Nat → Bool) : valuationOf q 474 = false ∨ valuationOf q 482 = true := by
  have hs : count481 q = (countLit q [239, 240, 241, 242]) + (countLit q [243, 244, 245, 246]) := List.countP_append (p := literal q) (l₁ := [239, 240, 241, 242]) (l₂ := [243, 244, 245, 246])
  have hm := merge_left (literal (valuationOf q) (474)) (literal (valuationOf q) (482)) (countLit q [239, 240, 241, 242]) (countLit q [243, 244, 245, 246]) (count481 q) 2 (meaning474 q) (meaning482 q) hs
  change valuationOf q 474 = false ∨ valuationOf q 482 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1109 (q : Snake 81) (h : Conditions q) : valuation q 474 = false ∨ valuation q 482 = true := counterClause1109 (baseVal q)

theorem counterClause1110 (q : Nat → Bool) : valuationOf q 249 = false ∨ valuationOf q 485 = true := by
  have hs : count485 q = (countLit q [249]) + (countLit q [250]) := List.countP_append (p := literal q) (l₁ := [249]) (l₂ := [250])
  have hm := merge_left (literal (valuationOf q) (249)) (literal (valuationOf q) (485)) (countLit q [249]) (countLit q [250]) (count485 q) 1 (meaning249 q) (meaning485 q) hs
  change valuationOf q 249 = false ∨ valuationOf q 485 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1110 (q : Snake 81) (h : Conditions q) : valuation q 249 = false ∨ valuation q 485 = true := counterClause1110 (baseVal q)

theorem counterClause1111 (q : Nat → Bool) : valuationOf q 485 = false ∨ valuationOf q 487 = true := by
  have hs : count487 q = (countLit q [247, 248]) + (countLit q [249, 250]) := List.countP_append (p := literal q) (l₁ := [247, 248]) (l₂ := [249, 250])
  have hm := merge_right (literal (valuationOf q) (485)) (literal (valuationOf q) (487)) (countLit q [247, 248]) (countLit q [249, 250]) (count487 q) 1 (meaning485 q) (meaning487 q) hs
  change valuationOf q 485 = false ∨ valuationOf q 487 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1111 (q : Snake 81) (h : Conditions q) : valuation q 485 = false ∨ valuation q 487 = true := counterClause1111 (baseVal q)

theorem counterClause1112 (q : Nat → Bool) : valuationOf q 251 = false ∨ valuationOf q 489 = true := by
  have hs : count489 q = (countLit q [251]) + (countLit q [252]) := List.countP_append (p := literal q) (l₁ := [251]) (l₂ := [252])
  have hm := merge_left (literal (valuationOf q) (251)) (literal (valuationOf q) (489)) (countLit q [251]) (countLit q [252]) (count489 q) 1 (meaning251 q) (meaning489 q) hs
  change valuationOf q 251 = false ∨ valuationOf q 489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1112 (q : Snake 81) (h : Conditions q) : valuation q 251 = false ∨ valuation q 489 = true := counterClause1112 (baseVal q)

theorem counterClause1113 (q : Nat → Bool) : valuationOf q 254 = false ∨ valuationOf q 491 = true := by
  have hs : count491 q = (countLit q [253]) + (countLit q [254]) := List.countP_append (p := literal q) (l₁ := [253]) (l₂ := [254])
  have hm := merge_right (literal (valuationOf q) (254)) (literal (valuationOf q) (491)) (countLit q [253]) (countLit q [254]) (count491 q) 1 (meaning254 q) (meaning491 q) hs
  change valuationOf q 254 = false ∨ valuationOf q 491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1113 (q : Snake 81) (h : Conditions q) : valuation q 254 = false ∨ valuation q 491 = true := counterClause1113 (baseVal q)

theorem counterClause1114 (q : Nat → Bool) : valuationOf q 253 = false ∨ valuationOf q 491 = true := by
  have hs : count491 q = (countLit q [253]) + (countLit q [254]) := List.countP_append (p := literal q) (l₁ := [253]) (l₂ := [254])
  have hm := merge_left (literal (valuationOf q) (253)) (literal (valuationOf q) (491)) (countLit q [253]) (countLit q [254]) (count491 q) 1 (meaning253 q) (meaning491 q) hs
  change valuationOf q 253 = false ∨ valuationOf q 491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1114 (q : Snake 81) (h : Conditions q) : valuation q 253 = false ∨ valuation q 491 = true := counterClause1114 (baseVal q)

theorem counterClause1115 (q : Nat → Bool) : valuationOf q 253 = false ∨ valuationOf q 254 = false ∨ valuationOf q 492 = true := by
  have hs : count491 q = (countLit q [253]) + (countLit q [254]) := List.countP_append (p := literal q) (l₁ := [253]) (l₂ := [254])
  have hm := merge_two (literal (valuationOf q) (253)) (literal (valuationOf q) (254)) (literal (valuationOf q) (492)) (countLit q [253]) (countLit q [254]) (count491 q) 1 1 (meaning253 q) (meaning254 q) (meaning492 q) hs
  change valuationOf q 253 = false ∨ valuationOf q 254 = false ∨ valuationOf q 492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1115 (q : Snake 81) (h : Conditions q) : valuation q 253 = false ∨ valuation q 254 = false ∨ valuation q 492 = true := counterClause1115 (baseVal q)

theorem counterClause1116 (q : Nat → Bool) : valuationOf q 491 = false ∨ valuationOf q 493 = true := by
  have hs : count493 q = (countLit q [251, 252]) + (countLit q [253, 254]) := List.countP_append (p := literal q) (l₁ := [251, 252]) (l₂ := [253, 254])
  have hm := merge_right (literal (valuationOf q) (491)) (literal (valuationOf q) (493)) (countLit q [251, 252]) (countLit q [253, 254]) (count493 q) 1 (meaning491 q) (meaning493 q) hs
  change valuationOf q 491 = false ∨ valuationOf q 493 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1116 (q : Snake 81) (h : Conditions q) : valuation q 491 = false ∨ valuation q 493 = true := counterClause1116 (baseVal q)

theorem counterClause1117 (q : Nat → Bool) : valuationOf q 492 = false ∨ valuationOf q 494 = true := by
  have hs : count493 q = (countLit q [251, 252]) + (countLit q [253, 254]) := List.countP_append (p := literal q) (l₁ := [251, 252]) (l₂ := [253, 254])
  have hm := merge_right (literal (valuationOf q) (492)) (literal (valuationOf q) (494)) (countLit q [251, 252]) (countLit q [253, 254]) (count493 q) 2 (meaning492 q) (meaning494 q) hs
  change valuationOf q 492 = false ∨ valuationOf q 494 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1117 (q : Snake 81) (h : Conditions q) : valuation q 492 = false ∨ valuation q 494 = true := counterClause1117 (baseVal q)

theorem counterClause1118 (q : Nat → Bool) : valuationOf q 489 = false ∨ valuationOf q 493 = true := by
  have hs : count493 q = (countLit q [251, 252]) + (countLit q [253, 254]) := List.countP_append (p := literal q) (l₁ := [251, 252]) (l₂ := [253, 254])
  have hm := merge_left (literal (valuationOf q) (489)) (literal (valuationOf q) (493)) (countLit q [251, 252]) (countLit q [253, 254]) (count493 q) 1 (meaning489 q) (meaning493 q) hs
  change valuationOf q 489 = false ∨ valuationOf q 493 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1118 (q : Snake 81) (h : Conditions q) : valuation q 489 = false ∨ valuation q 493 = true := counterClause1118 (baseVal q)

theorem counterClause1119 (q : Nat → Bool) : valuationOf q 489 = false ∨ valuationOf q 491 = false ∨ valuationOf q 494 = true := by
  have hs : count493 q = (countLit q [251, 252]) + (countLit q [253, 254]) := List.countP_append (p := literal q) (l₁ := [251, 252]) (l₂ := [253, 254])
  have hm := merge_two (literal (valuationOf q) (489)) (literal (valuationOf q) (491)) (literal (valuationOf q) (494)) (countLit q [251, 252]) (countLit q [253, 254]) (count493 q) 1 1 (meaning489 q) (meaning491 q) (meaning494 q) hs
  change valuationOf q 489 = false ∨ valuationOf q 491 = false ∨ valuationOf q 494 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1119 (q : Snake 81) (h : Conditions q) : valuation q 489 = false ∨ valuation q 491 = false ∨ valuation q 494 = true := counterClause1119 (baseVal q)

theorem counterClause1120 (q : Nat → Bool) : valuationOf q 493 = false ∨ valuationOf q 495 = true := by
  have hs : count495 q = (countLit q [247, 248, 249, 250]) + (countLit q [251, 252, 253, 254]) := List.countP_append (p := literal q) (l₁ := [247, 248, 249, 250]) (l₂ := [251, 252, 253, 254])
  have hm := merge_right (literal (valuationOf q) (493)) (literal (valuationOf q) (495)) (countLit q [247, 248, 249, 250]) (countLit q [251, 252, 253, 254]) (count495 q) 1 (meaning493 q) (meaning495 q) hs
  change valuationOf q 493 = false ∨ valuationOf q 495 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1120 (q : Snake 81) (h : Conditions q) : valuation q 493 = false ∨ valuation q 495 = true := counterClause1120 (baseVal q)

theorem block34 (q : Snake 81) (h : Conditions q) : B112E260.Block34 (valuation q) :=
  ⟨clause1089 q h, clause1090 q h, clause1091 q h, clause1092 q h, clause1093 q h, clause1094 q h, clause1095 q h, clause1096 q h, clause1097 q h, clause1098 q h, clause1099 q h, clause1100 q h, clause1101 q h, clause1102 q h, clause1103 q h, clause1104 q h, clause1105 q h, clause1106 q h, clause1107 q h, clause1108 q h, clause1109 q h, clause1110 q h, clause1111 q h, clause1112 q h, clause1113 q h, clause1114 q h, clause1115 q h, clause1116 q h, clause1117 q h, clause1118 q h, clause1119 q h, clause1120 q h⟩

end
end Snake9.Regrowth.E112260
