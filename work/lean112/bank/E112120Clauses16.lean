import E112120Semantics
import B112E120Inputs
namespace Snake9.Regrowth.E112120
noncomputable section
local instance blockDec16 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause513 (q : Nat → Bool) : valuationOf q 1414 = false ∨ valuationOf q 1441 = true := by
  have hs : count1441 q = (countLit q [-1, -2, -5, -8, -10, -14, -15]) + (countLit q [-16, -19, -21, -24, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -8, -10, -14, -15]) (l₂ := [-16, -19, -21, -24, -25, -28, -30])
  have hm := merge_left (literal (valuationOf q) (1414)) (literal (valuationOf q) (1441)) (countLit q [-1, -2, -5, -8, -10, -14, -15]) (countLit q [-16, -19, -21, -24, -25, -28, -30]) (count1441 q) 1 (meaning1414 q) (meaning1441 q) hs
  change valuationOf q 1414 = false ∨ valuationOf q 1441 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause513 (q : Snake 81) (h : Conditions q) : valuation q 1414 = false ∨ valuation q 1441 = true := counterClause513 (baseVal q)

theorem counterClause514 (q : Nat → Bool) : valuationOf q 1414 = false ∨ valuationOf q 1434 = false ∨ valuationOf q 1442 = true := by
  have hs : count1441 q = (countLit q [-1, -2, -5, -8, -10, -14, -15]) + (countLit q [-16, -19, -21, -24, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -8, -10, -14, -15]) (l₂ := [-16, -19, -21, -24, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1414)) (literal (valuationOf q) (1434)) (literal (valuationOf q) (1442)) (countLit q [-1, -2, -5, -8, -10, -14, -15]) (countLit q [-16, -19, -21, -24, -25, -28, -30]) (count1441 q) 1 1 (meaning1414 q) (meaning1434 q) (meaning1442 q) hs
  change valuationOf q 1414 = false ∨ valuationOf q 1434 = false ∨ valuationOf q 1442 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause514 (q : Snake 81) (h : Conditions q) : valuation q 1414 = false ∨ valuation q 1434 = false ∨ valuation q 1442 = true := counterClause514 (baseVal q)

theorem counterClause515 (q : Nat → Bool) : valuationOf q 1414 = false ∨ valuationOf q 1435 = false ∨ valuationOf q 1443 = true := by
  have hs : count1441 q = (countLit q [-1, -2, -5, -8, -10, -14, -15]) + (countLit q [-16, -19, -21, -24, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -8, -10, -14, -15]) (l₂ := [-16, -19, -21, -24, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1414)) (literal (valuationOf q) (1435)) (literal (valuationOf q) (1443)) (countLit q [-1, -2, -5, -8, -10, -14, -15]) (countLit q [-16, -19, -21, -24, -25, -28, -30]) (count1441 q) 1 2 (meaning1414 q) (meaning1435 q) (meaning1443 q) hs
  change valuationOf q 1414 = false ∨ valuationOf q 1435 = false ∨ valuationOf q 1443 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause515 (q : Snake 81) (h : Conditions q) : valuation q 1414 = false ∨ valuation q 1435 = false ∨ valuation q 1443 = true := counterClause515 (baseVal q)

theorem counterClause516 (q : Nat → Bool) : valuationOf q 1414 = false ∨ valuationOf q 1436 = false ∨ valuationOf q 1444 = true := by
  have hs : count1441 q = (countLit q [-1, -2, -5, -8, -10, -14, -15]) + (countLit q [-16, -19, -21, -24, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -8, -10, -14, -15]) (l₂ := [-16, -19, -21, -24, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1414)) (literal (valuationOf q) (1436)) (literal (valuationOf q) (1444)) (countLit q [-1, -2, -5, -8, -10, -14, -15]) (countLit q [-16, -19, -21, -24, -25, -28, -30]) (count1441 q) 1 3 (meaning1414 q) (meaning1436 q) (meaning1444 q) hs
  change valuationOf q 1414 = false ∨ valuationOf q 1436 = false ∨ valuationOf q 1444 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause516 (q : Snake 81) (h : Conditions q) : valuation q 1414 = false ∨ valuation q 1436 = false ∨ valuation q 1444 = true := counterClause516 (baseVal q)

theorem counterClause517 (q : Nat → Bool) : valuationOf q 1414 = false ∨ valuationOf q 1437 = false ∨ valuationOf q 1445 = true := by
  have hs : count1441 q = (countLit q [-1, -2, -5, -8, -10, -14, -15]) + (countLit q [-16, -19, -21, -24, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -8, -10, -14, -15]) (l₂ := [-16, -19, -21, -24, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1414)) (literal (valuationOf q) (1437)) (literal (valuationOf q) (1445)) (countLit q [-1, -2, -5, -8, -10, -14, -15]) (countLit q [-16, -19, -21, -24, -25, -28, -30]) (count1441 q) 1 4 (meaning1414 q) (meaning1437 q) (meaning1445 q) hs
  change valuationOf q 1414 = false ∨ valuationOf q 1437 = false ∨ valuationOf q 1445 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause517 (q : Snake 81) (h : Conditions q) : valuation q 1414 = false ∨ valuation q 1437 = false ∨ valuation q 1445 = true := counterClause517 (baseVal q)

theorem counterClause518 (q : Nat → Bool) : valuationOf q 1415 = false ∨ valuationOf q 1442 = true := by
  have hs : count1441 q = (countLit q [-1, -2, -5, -8, -10, -14, -15]) + (countLit q [-16, -19, -21, -24, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -8, -10, -14, -15]) (l₂ := [-16, -19, -21, -24, -25, -28, -30])
  have hm := merge_left (literal (valuationOf q) (1415)) (literal (valuationOf q) (1442)) (countLit q [-1, -2, -5, -8, -10, -14, -15]) (countLit q [-16, -19, -21, -24, -25, -28, -30]) (count1441 q) 2 (meaning1415 q) (meaning1442 q) hs
  change valuationOf q 1415 = false ∨ valuationOf q 1442 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause518 (q : Snake 81) (h : Conditions q) : valuation q 1415 = false ∨ valuation q 1442 = true := counterClause518 (baseVal q)

theorem counterClause519 (q : Nat → Bool) : valuationOf q 1415 = false ∨ valuationOf q 1434 = false ∨ valuationOf q 1443 = true := by
  have hs : count1441 q = (countLit q [-1, -2, -5, -8, -10, -14, -15]) + (countLit q [-16, -19, -21, -24, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -8, -10, -14, -15]) (l₂ := [-16, -19, -21, -24, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1415)) (literal (valuationOf q) (1434)) (literal (valuationOf q) (1443)) (countLit q [-1, -2, -5, -8, -10, -14, -15]) (countLit q [-16, -19, -21, -24, -25, -28, -30]) (count1441 q) 2 1 (meaning1415 q) (meaning1434 q) (meaning1443 q) hs
  change valuationOf q 1415 = false ∨ valuationOf q 1434 = false ∨ valuationOf q 1443 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause519 (q : Snake 81) (h : Conditions q) : valuation q 1415 = false ∨ valuation q 1434 = false ∨ valuation q 1443 = true := counterClause519 (baseVal q)

theorem counterClause520 (q : Nat → Bool) : valuationOf q 1415 = false ∨ valuationOf q 1435 = false ∨ valuationOf q 1444 = true := by
  have hs : count1441 q = (countLit q [-1, -2, -5, -8, -10, -14, -15]) + (countLit q [-16, -19, -21, -24, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -8, -10, -14, -15]) (l₂ := [-16, -19, -21, -24, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1415)) (literal (valuationOf q) (1435)) (literal (valuationOf q) (1444)) (countLit q [-1, -2, -5, -8, -10, -14, -15]) (countLit q [-16, -19, -21, -24, -25, -28, -30]) (count1441 q) 2 2 (meaning1415 q) (meaning1435 q) (meaning1444 q) hs
  change valuationOf q 1415 = false ∨ valuationOf q 1435 = false ∨ valuationOf q 1444 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause520 (q : Snake 81) (h : Conditions q) : valuation q 1415 = false ∨ valuation q 1435 = false ∨ valuation q 1444 = true := counterClause520 (baseVal q)

theorem counterClause521 (q : Nat → Bool) : valuationOf q 1415 = false ∨ valuationOf q 1436 = false ∨ valuationOf q 1445 = true := by
  have hs : count1441 q = (countLit q [-1, -2, -5, -8, -10, -14, -15]) + (countLit q [-16, -19, -21, -24, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -8, -10, -14, -15]) (l₂ := [-16, -19, -21, -24, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1415)) (literal (valuationOf q) (1436)) (literal (valuationOf q) (1445)) (countLit q [-1, -2, -5, -8, -10, -14, -15]) (countLit q [-16, -19, -21, -24, -25, -28, -30]) (count1441 q) 2 3 (meaning1415 q) (meaning1436 q) (meaning1445 q) hs
  change valuationOf q 1415 = false ∨ valuationOf q 1436 = false ∨ valuationOf q 1445 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause521 (q : Snake 81) (h : Conditions q) : valuation q 1415 = false ∨ valuation q 1436 = false ∨ valuation q 1445 = true := counterClause521 (baseVal q)

theorem counterClause522 (q : Nat → Bool) : valuationOf q 1416 = false ∨ valuationOf q 1434 = false ∨ valuationOf q 1444 = true := by
  have hs : count1441 q = (countLit q [-1, -2, -5, -8, -10, -14, -15]) + (countLit q [-16, -19, -21, -24, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -8, -10, -14, -15]) (l₂ := [-16, -19, -21, -24, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1416)) (literal (valuationOf q) (1434)) (literal (valuationOf q) (1444)) (countLit q [-1, -2, -5, -8, -10, -14, -15]) (countLit q [-16, -19, -21, -24, -25, -28, -30]) (count1441 q) 3 1 (meaning1416 q) (meaning1434 q) (meaning1444 q) hs
  change valuationOf q 1416 = false ∨ valuationOf q 1434 = false ∨ valuationOf q 1444 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause522 (q : Snake 81) (h : Conditions q) : valuation q 1416 = false ∨ valuation q 1434 = false ∨ valuation q 1444 = true := counterClause522 (baseVal q)

theorem counterClause523 (q : Nat → Bool) : valuationOf q 1416 = false ∨ valuationOf q 1435 = false ∨ valuationOf q 1445 = true := by
  have hs : count1441 q = (countLit q [-1, -2, -5, -8, -10, -14, -15]) + (countLit q [-16, -19, -21, -24, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -8, -10, -14, -15]) (l₂ := [-16, -19, -21, -24, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1416)) (literal (valuationOf q) (1435)) (literal (valuationOf q) (1445)) (countLit q [-1, -2, -5, -8, -10, -14, -15]) (countLit q [-16, -19, -21, -24, -25, -28, -30]) (count1441 q) 3 2 (meaning1416 q) (meaning1435 q) (meaning1445 q) hs
  change valuationOf q 1416 = false ∨ valuationOf q 1435 = false ∨ valuationOf q 1445 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause523 (q : Snake 81) (h : Conditions q) : valuation q 1416 = false ∨ valuation q 1435 = false ∨ valuation q 1445 = true := counterClause523 (baseVal q)

theorem counterClause524 (q : Nat → Bool) : valuationOf q 1417 = false ∨ valuationOf q 1434 = false ∨ valuationOf q 1445 = true := by
  have hs : count1441 q = (countLit q [-1, -2, -5, -8, -10, -14, -15]) + (countLit q [-16, -19, -21, -24, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -8, -10, -14, -15]) (l₂ := [-16, -19, -21, -24, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1417)) (literal (valuationOf q) (1434)) (literal (valuationOf q) (1445)) (countLit q [-1, -2, -5, -8, -10, -14, -15]) (countLit q [-16, -19, -21, -24, -25, -28, -30]) (count1441 q) 4 1 (meaning1417 q) (meaning1434 q) (meaning1445 q) hs
  change valuationOf q 1417 = false ∨ valuationOf q 1434 = false ∨ valuationOf q 1445 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause524 (q : Snake 81) (h : Conditions q) : valuation q 1417 = false ∨ valuation q 1434 = false ∨ valuation q 1445 = true := counterClause524 (baseVal q)

theorem counterClause525 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 1455 = true := by
  have hs : count1455 q = (countLit q [-33]) + (countLit q [-37]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-37])
  have hm := merge_left (literal (valuationOf q) (-33)) (literal (valuationOf q) (1455)) (countLit q [-33]) (countLit q [-37]) (count1455 q) 1 (meaningNeg33 q) (meaning1455 q) hs
  change (! (valuationOf q 33)) = false ∨ valuationOf q 1455 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause525 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 1455 = true := counterClause525 (baseVal q)

theorem counterClause526 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 37 = true ∨ valuationOf q 1456 = true := by
  have hs : count1455 q = (countLit q [-33]) + (countLit q [-37]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-37])
  have hm := merge_two (literal (valuationOf q) (-33)) (literal (valuationOf q) (-37)) (literal (valuationOf q) (1456)) (countLit q [-33]) (countLit q [-37]) (count1455 q) 1 1 (meaningNeg33 q) (meaningNeg37 q) (meaning1456 q) hs
  change (! (valuationOf q 33)) = false ∨ (! (valuationOf q 37)) = false ∨ valuationOf q 1456 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause526 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 37 = true ∨ valuation q 1456 = true := counterClause526 (baseVal q)

theorem counterClause527 (q : Nat → Bool) : valuationOf q 1455 = false ∨ valuationOf q 1457 = true := by
  have hs : count1457 q = (countLit q [-31]) + (countLit q [-33, -37]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-33, -37])
  have hm := merge_right (literal (valuationOf q) (1455)) (literal (valuationOf q) (1457)) (countLit q [-31]) (countLit q [-33, -37]) (count1457 q) 1 (meaning1455 q) (meaning1457 q) hs
  change valuationOf q 1455 = false ∨ valuationOf q 1457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause527 (q : Snake 81) (h : Conditions q) : valuation q 1455 = false ∨ valuation q 1457 = true := counterClause527 (baseVal q)

theorem counterClause528 (q : Nat → Bool) : valuationOf q 1456 = false ∨ valuationOf q 1458 = true := by
  have hs : count1457 q = (countLit q [-31]) + (countLit q [-33, -37]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-33, -37])
  have hm := merge_right (literal (valuationOf q) (1456)) (literal (valuationOf q) (1458)) (countLit q [-31]) (countLit q [-33, -37]) (count1457 q) 2 (meaning1456 q) (meaning1458 q) hs
  change valuationOf q 1456 = false ∨ valuationOf q 1458 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause528 (q : Snake 81) (h : Conditions q) : valuation q 1456 = false ∨ valuation q 1458 = true := counterClause528 (baseVal q)

theorem counterClause529 (q : Nat → Bool) : valuationOf q 31 = true ∨ valuationOf q 1457 = true := by
  have hs : count1457 q = (countLit q [-31]) + (countLit q [-33, -37]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-33, -37])
  have hm := merge_left (literal (valuationOf q) (-31)) (literal (valuationOf q) (1457)) (countLit q [-31]) (countLit q [-33, -37]) (count1457 q) 1 (meaningNeg31 q) (meaning1457 q) hs
  change (! (valuationOf q 31)) = false ∨ valuationOf q 1457 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause529 (q : Snake 81) (h : Conditions q) : valuation q 31 = true ∨ valuation q 1457 = true := counterClause529 (baseVal q)

theorem counterClause530 (q : Nat → Bool) : valuationOf q 31 = true ∨ valuationOf q 1455 = false ∨ valuationOf q 1458 = true := by
  have hs : count1457 q = (countLit q [-31]) + (countLit q [-33, -37]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-33, -37])
  have hm := merge_two (literal (valuationOf q) (-31)) (literal (valuationOf q) (1455)) (literal (valuationOf q) (1458)) (countLit q [-31]) (countLit q [-33, -37]) (count1457 q) 1 1 (meaningNeg31 q) (meaning1455 q) (meaning1458 q) hs
  change (! (valuationOf q 31)) = false ∨ valuationOf q 1455 = false ∨ valuationOf q 1458 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause530 (q : Snake 81) (h : Conditions q) : valuation q 31 = true ∨ valuation q 1455 = false ∨ valuation q 1458 = true := counterClause530 (baseVal q)

theorem counterClause531 (q : Nat → Bool) : valuationOf q 39 = true ∨ valuationOf q 1460 = true := by
  have hs : count1460 q = (countLit q [-38]) + (countLit q [-39]) := List.countP_append (p := literal q) (l₁ := [-38]) (l₂ := [-39])
  have hm := merge_right (literal (valuationOf q) (-39)) (literal (valuationOf q) (1460)) (countLit q [-38]) (countLit q [-39]) (count1460 q) 1 (meaningNeg39 q) (meaning1460 q) hs
  change (! (valuationOf q 39)) = false ∨ valuationOf q 1460 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause531 (q : Snake 81) (h : Conditions q) : valuation q 39 = true ∨ valuation q 1460 = true := counterClause531 (baseVal q)

theorem counterClause532 (q : Nat → Bool) : valuationOf q 38 = true ∨ valuationOf q 1460 = true := by
  have hs : count1460 q = (countLit q [-38]) + (countLit q [-39]) := List.countP_append (p := literal q) (l₁ := [-38]) (l₂ := [-39])
  have hm := merge_left (literal (valuationOf q) (-38)) (literal (valuationOf q) (1460)) (countLit q [-38]) (countLit q [-39]) (count1460 q) 1 (meaningNeg38 q) (meaning1460 q) hs
  change (! (valuationOf q 38)) = false ∨ valuationOf q 1460 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause532 (q : Snake 81) (h : Conditions q) : valuation q 38 = true ∨ valuation q 1460 = true := counterClause532 (baseVal q)

theorem counterClause533 (q : Nat → Bool) : valuationOf q 44 = true ∨ valuationOf q 1462 = true := by
  have hs : count1462 q = (countLit q [-40]) + (countLit q [-44]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-44])
  have hm := merge_right (literal (valuationOf q) (-44)) (literal (valuationOf q) (1462)) (countLit q [-40]) (countLit q [-44]) (count1462 q) 1 (meaningNeg44 q) (meaning1462 q) hs
  change (! (valuationOf q 44)) = false ∨ valuationOf q 1462 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause533 (q : Snake 81) (h : Conditions q) : valuation q 44 = true ∨ valuation q 1462 = true := counterClause533 (baseVal q)

theorem counterClause534 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 1462 = true := by
  have hs : count1462 q = (countLit q [-40]) + (countLit q [-44]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-44])
  have hm := merge_left (literal (valuationOf q) (-40)) (literal (valuationOf q) (1462)) (countLit q [-40]) (countLit q [-44]) (count1462 q) 1 (meaningNeg40 q) (meaning1462 q) hs
  change (! (valuationOf q 40)) = false ∨ valuationOf q 1462 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause534 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 1462 = true := counterClause534 (baseVal q)

theorem counterClause535 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 44 = true ∨ valuationOf q 1463 = true := by
  have hs : count1462 q = (countLit q [-40]) + (countLit q [-44]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-44])
  have hm := merge_two (literal (valuationOf q) (-40)) (literal (valuationOf q) (-44)) (literal (valuationOf q) (1463)) (countLit q [-40]) (countLit q [-44]) (count1462 q) 1 1 (meaningNeg40 q) (meaningNeg44 q) (meaning1463 q) hs
  change (! (valuationOf q 40)) = false ∨ (! (valuationOf q 44)) = false ∨ valuationOf q 1463 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause535 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 44 = true ∨ valuation q 1463 = true := counterClause535 (baseVal q)

theorem counterClause536 (q : Nat → Bool) : valuationOf q 1462 = false ∨ valuationOf q 1464 = true := by
  have hs : count1464 q = (countLit q [-38, -39]) + (countLit q [-40, -44]) := List.countP_append (p := literal q) (l₁ := [-38, -39]) (l₂ := [-40, -44])
  have hm := merge_right (literal (valuationOf q) (1462)) (literal (valuationOf q) (1464)) (countLit q [-38, -39]) (countLit q [-40, -44]) (count1464 q) 1 (meaning1462 q) (meaning1464 q) hs
  change valuationOf q 1462 = false ∨ valuationOf q 1464 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause536 (q : Snake 81) (h : Conditions q) : valuation q 1462 = false ∨ valuation q 1464 = true := counterClause536 (baseVal q)

theorem counterClause537 (q : Nat → Bool) : valuationOf q 1463 = false ∨ valuationOf q 1465 = true := by
  have hs : count1464 q = (countLit q [-38, -39]) + (countLit q [-40, -44]) := List.countP_append (p := literal q) (l₁ := [-38, -39]) (l₂ := [-40, -44])
  have hm := merge_right (literal (valuationOf q) (1463)) (literal (valuationOf q) (1465)) (countLit q [-38, -39]) (countLit q [-40, -44]) (count1464 q) 2 (meaning1463 q) (meaning1465 q) hs
  change valuationOf q 1463 = false ∨ valuationOf q 1465 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause537 (q : Snake 81) (h : Conditions q) : valuation q 1463 = false ∨ valuation q 1465 = true := counterClause537 (baseVal q)

theorem counterClause538 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1464 = true := by
  have hs : count1464 q = (countLit q [-38, -39]) + (countLit q [-40, -44]) := List.countP_append (p := literal q) (l₁ := [-38, -39]) (l₂ := [-40, -44])
  have hm := merge_left (literal (valuationOf q) (1460)) (literal (valuationOf q) (1464)) (countLit q [-38, -39]) (countLit q [-40, -44]) (count1464 q) 1 (meaning1460 q) (meaning1464 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1464 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause538 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1464 = true := counterClause538 (baseVal q)

theorem counterClause539 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1462 = false ∨ valuationOf q 1465 = true := by
  have hs : count1464 q = (countLit q [-38, -39]) + (countLit q [-40, -44]) := List.countP_append (p := literal q) (l₁ := [-38, -39]) (l₂ := [-40, -44])
  have hm := merge_two (literal (valuationOf q) (1460)) (literal (valuationOf q) (1462)) (literal (valuationOf q) (1465)) (countLit q [-38, -39]) (countLit q [-40, -44]) (count1464 q) 1 1 (meaning1460 q) (meaning1462 q) (meaning1465 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1462 = false ∨ valuationOf q 1465 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause539 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1462 = false ∨ valuation q 1465 = true := counterClause539 (baseVal q)

theorem counterClause540 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1463 = false ∨ valuationOf q 1466 = true := by
  have hs : count1464 q = (countLit q [-38, -39]) + (countLit q [-40, -44]) := List.countP_append (p := literal q) (l₁ := [-38, -39]) (l₂ := [-40, -44])
  have hm := merge_two (literal (valuationOf q) (1460)) (literal (valuationOf q) (1463)) (literal (valuationOf q) (1466)) (countLit q [-38, -39]) (countLit q [-40, -44]) (count1464 q) 1 2 (meaning1460 q) (meaning1463 q) (meaning1466 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1463 = false ∨ valuationOf q 1466 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause540 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1463 = false ∨ valuation q 1466 = true := counterClause540 (baseVal q)

theorem counterClause541 (q : Nat → Bool) : valuationOf q 1464 = false ∨ valuationOf q 1468 = true := by
  have hs : count1468 q = (countLit q [-31, -33, -37]) + (countLit q [-38, -39, -40, -44]) := List.countP_append (p := literal q) (l₁ := [-31, -33, -37]) (l₂ := [-38, -39, -40, -44])
  have hm := merge_right (literal (valuationOf q) (1464)) (literal (valuationOf q) (1468)) (countLit q [-31, -33, -37]) (countLit q [-38, -39, -40, -44]) (count1468 q) 1 (meaning1464 q) (meaning1468 q) hs
  change valuationOf q 1464 = false ∨ valuationOf q 1468 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause541 (q : Snake 81) (h : Conditions q) : valuation q 1464 = false ∨ valuation q 1468 = true := counterClause541 (baseVal q)

theorem counterClause542 (q : Nat → Bool) : valuationOf q 1465 = false ∨ valuationOf q 1469 = true := by
  have hs : count1468 q = (countLit q [-31, -33, -37]) + (countLit q [-38, -39, -40, -44]) := List.countP_append (p := literal q) (l₁ := [-31, -33, -37]) (l₂ := [-38, -39, -40, -44])
  have hm := merge_right (literal (valuationOf q) (1465)) (literal (valuationOf q) (1469)) (countLit q [-31, -33, -37]) (countLit q [-38, -39, -40, -44]) (count1468 q) 2 (meaning1465 q) (meaning1469 q) hs
  change valuationOf q 1465 = false ∨ valuationOf q 1469 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause542 (q : Snake 81) (h : Conditions q) : valuation q 1465 = false ∨ valuation q 1469 = true := counterClause542 (baseVal q)

theorem counterClause543 (q : Nat → Bool) : valuationOf q 1457 = false ∨ valuationOf q 1464 = false ∨ valuationOf q 1469 = true := by
  have hs : count1468 q = (countLit q [-31, -33, -37]) + (countLit q [-38, -39, -40, -44]) := List.countP_append (p := literal q) (l₁ := [-31, -33, -37]) (l₂ := [-38, -39, -40, -44])
  have hm := merge_two (literal (valuationOf q) (1457)) (literal (valuationOf q) (1464)) (literal (valuationOf q) (1469)) (countLit q [-31, -33, -37]) (countLit q [-38, -39, -40, -44]) (count1468 q) 1 1 (meaning1457 q) (meaning1464 q) (meaning1469 q) hs
  change valuationOf q 1457 = false ∨ valuationOf q 1464 = false ∨ valuationOf q 1469 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause543 (q : Snake 81) (h : Conditions q) : valuation q 1457 = false ∨ valuation q 1464 = false ∨ valuation q 1469 = true := counterClause543 (baseVal q)

theorem counterClause544 (q : Nat → Bool) : valuationOf q 1457 = false ∨ valuationOf q 1465 = false ∨ valuationOf q 1470 = true := by
  have hs : count1468 q = (countLit q [-31, -33, -37]) + (countLit q [-38, -39, -40, -44]) := List.countP_append (p := literal q) (l₁ := [-31, -33, -37]) (l₂ := [-38, -39, -40, -44])
  have hm := merge_two (literal (valuationOf q) (1457)) (literal (valuationOf q) (1465)) (literal (valuationOf q) (1470)) (countLit q [-31, -33, -37]) (countLit q [-38, -39, -40, -44]) (count1468 q) 1 2 (meaning1457 q) (meaning1465 q) (meaning1470 q) hs
  change valuationOf q 1457 = false ∨ valuationOf q 1465 = false ∨ valuationOf q 1470 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause544 (q : Snake 81) (h : Conditions q) : valuation q 1457 = false ∨ valuation q 1465 = false ∨ valuation q 1470 = true := counterClause544 (baseVal q)

theorem block16 (q : Snake 81) (h : Conditions q) : B112E120.Block16 (valuation q) :=
  ⟨clause513 q h, clause514 q h, clause515 q h, clause516 q h, clause517 q h, clause518 q h, clause519 q h, clause520 q h, clause521 q h, clause522 q h, clause523 q h, clause524 q h, clause525 q h, clause526 q h, clause527 q h, clause528 q h, clause529 q h, clause530 q h, clause531 q h, clause532 q h, clause533 q h, clause534 q h, clause535 q h, clause536 q h, clause537 q h, clause538 q h, clause539 q h, clause540 q h, clause541 q h, clause542 q h, clause543 q h, clause544 q h⟩

end
end Snake9.Regrowth.E112120
