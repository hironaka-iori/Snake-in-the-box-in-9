import E112152Semantics
import B112E152Inputs
namespace Snake9.Regrowth.E112152
noncomputable section
local instance blockDec18 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause577 (q : Nat → Bool) : valuationOf q 1478 = false ∨ valuationOf q 1480 = true := by
  have hs : count1479 q = (countLit q [-16]) + (countLit q [-20, -21]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-20, -21])
  have hm := merge_right (literal (valuationOf q) (1478)) (literal (valuationOf q) (1480)) (countLit q [-16]) (countLit q [-20, -21]) (count1479 q) 2 (meaning1478 q) (meaning1480 q) hs
  change valuationOf q 1478 = false ∨ valuationOf q 1480 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause577 (q : Snake 81) (h : Conditions q) : valuation q 1478 = false ∨ valuation q 1480 = true := counterClause577 (baseVal q)

theorem counterClause578 (q : Nat → Bool) : valuationOf q 16 = true ∨ valuationOf q 1479 = true := by
  have hs : count1479 q = (countLit q [-16]) + (countLit q [-20, -21]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-20, -21])
  have hm := merge_left (literal (valuationOf q) (-16)) (literal (valuationOf q) (1479)) (countLit q [-16]) (countLit q [-20, -21]) (count1479 q) 1 (meaningNeg16 q) (meaning1479 q) hs
  change (! (valuationOf q 16)) = false ∨ valuationOf q 1479 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause578 (q : Snake 81) (h : Conditions q) : valuation q 16 = true ∨ valuation q 1479 = true := counterClause578 (baseVal q)

theorem counterClause579 (q : Nat → Bool) : valuationOf q 16 = true ∨ valuationOf q 1477 = false ∨ valuationOf q 1480 = true := by
  have hs : count1479 q = (countLit q [-16]) + (countLit q [-20, -21]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-20, -21])
  have hm := merge_two (literal (valuationOf q) (-16)) (literal (valuationOf q) (1477)) (literal (valuationOf q) (1480)) (countLit q [-16]) (countLit q [-20, -21]) (count1479 q) 1 1 (meaningNeg16 q) (meaning1477 q) (meaning1480 q) hs
  change (! (valuationOf q 16)) = false ∨ valuationOf q 1477 = false ∨ valuationOf q 1480 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause579 (q : Snake 81) (h : Conditions q) : valuation q 16 = true ∨ valuation q 1477 = false ∨ valuation q 1480 = true := counterClause579 (baseVal q)

theorem counterClause580 (q : Nat → Bool) : valuationOf q 23 = true ∨ valuationOf q 1482 = true := by
  have hs : count1482 q = (countLit q [-22]) + (countLit q [-23]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-23])
  have hm := merge_right (literal (valuationOf q) (-23)) (literal (valuationOf q) (1482)) (countLit q [-22]) (countLit q [-23]) (count1482 q) 1 (meaningNeg23 q) (meaning1482 q) hs
  change (! (valuationOf q 23)) = false ∨ valuationOf q 1482 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause580 (q : Snake 81) (h : Conditions q) : valuation q 23 = true ∨ valuation q 1482 = true := counterClause580 (baseVal q)

theorem counterClause581 (q : Nat → Bool) : valuationOf q 22 = true ∨ valuationOf q 1482 = true := by
  have hs : count1482 q = (countLit q [-22]) + (countLit q [-23]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-23])
  have hm := merge_left (literal (valuationOf q) (-22)) (literal (valuationOf q) (1482)) (countLit q [-22]) (countLit q [-23]) (count1482 q) 1 (meaningNeg22 q) (meaning1482 q) hs
  change (! (valuationOf q 22)) = false ∨ valuationOf q 1482 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause581 (q : Snake 81) (h : Conditions q) : valuation q 22 = true ∨ valuation q 1482 = true := counterClause581 (baseVal q)

theorem counterClause582 (q : Nat → Bool) : valuationOf q 22 = true ∨ valuationOf q 23 = true ∨ valuationOf q 1483 = true := by
  have hs : count1482 q = (countLit q [-22]) + (countLit q [-23]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-23])
  have hm := merge_two (literal (valuationOf q) (-22)) (literal (valuationOf q) (-23)) (literal (valuationOf q) (1483)) (countLit q [-22]) (countLit q [-23]) (count1482 q) 1 1 (meaningNeg22 q) (meaningNeg23 q) (meaning1483 q) hs
  change (! (valuationOf q 22)) = false ∨ (! (valuationOf q 23)) = false ∨ valuationOf q 1483 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause582 (q : Snake 81) (h : Conditions q) : valuation q 22 = true ∨ valuation q 23 = true ∨ valuation q 1483 = true := counterClause582 (baseVal q)

theorem counterClause583 (q : Nat → Bool) : valuationOf q 29 = true ∨ valuationOf q 1484 = true := by
  have hs : count1484 q = (countLit q [-27]) + (countLit q [-29]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-29])
  have hm := merge_right (literal (valuationOf q) (-29)) (literal (valuationOf q) (1484)) (countLit q [-27]) (countLit q [-29]) (count1484 q) 1 (meaningNeg29 q) (meaning1484 q) hs
  change (! (valuationOf q 29)) = false ∨ valuationOf q 1484 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause583 (q : Snake 81) (h : Conditions q) : valuation q 29 = true ∨ valuation q 1484 = true := counterClause583 (baseVal q)

theorem counterClause584 (q : Nat → Bool) : valuationOf q 27 = true ∨ valuationOf q 1484 = true := by
  have hs : count1484 q = (countLit q [-27]) + (countLit q [-29]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-29])
  have hm := merge_left (literal (valuationOf q) (-27)) (literal (valuationOf q) (1484)) (countLit q [-27]) (countLit q [-29]) (count1484 q) 1 (meaningNeg27 q) (meaning1484 q) hs
  change (! (valuationOf q 27)) = false ∨ valuationOf q 1484 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause584 (q : Snake 81) (h : Conditions q) : valuation q 27 = true ∨ valuation q 1484 = true := counterClause584 (baseVal q)

theorem counterClause585 (q : Nat → Bool) : valuationOf q 1484 = false ∨ valuationOf q 1486 = true := by
  have hs : count1486 q = (countLit q [-22, -23]) + (countLit q [-27, -29]) := List.countP_append (p := literal q) (l₁ := [-22, -23]) (l₂ := [-27, -29])
  have hm := merge_right (literal (valuationOf q) (1484)) (literal (valuationOf q) (1486)) (countLit q [-22, -23]) (countLit q [-27, -29]) (count1486 q) 1 (meaning1484 q) (meaning1486 q) hs
  change valuationOf q 1484 = false ∨ valuationOf q 1486 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause585 (q : Snake 81) (h : Conditions q) : valuation q 1484 = false ∨ valuation q 1486 = true := counterClause585 (baseVal q)

theorem counterClause586 (q : Nat → Bool) : valuationOf q 1482 = false ∨ valuationOf q 1486 = true := by
  have hs : count1486 q = (countLit q [-22, -23]) + (countLit q [-27, -29]) := List.countP_append (p := literal q) (l₁ := [-22, -23]) (l₂ := [-27, -29])
  have hm := merge_left (literal (valuationOf q) (1482)) (literal (valuationOf q) (1486)) (countLit q [-22, -23]) (countLit q [-27, -29]) (count1486 q) 1 (meaning1482 q) (meaning1486 q) hs
  change valuationOf q 1482 = false ∨ valuationOf q 1486 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause586 (q : Snake 81) (h : Conditions q) : valuation q 1482 = false ∨ valuation q 1486 = true := counterClause586 (baseVal q)

theorem counterClause587 (q : Nat → Bool) : valuationOf q 1482 = false ∨ valuationOf q 1484 = false ∨ valuationOf q 1487 = true := by
  have hs : count1486 q = (countLit q [-22, -23]) + (countLit q [-27, -29]) := List.countP_append (p := literal q) (l₁ := [-22, -23]) (l₂ := [-27, -29])
  have hm := merge_two (literal (valuationOf q) (1482)) (literal (valuationOf q) (1484)) (literal (valuationOf q) (1487)) (countLit q [-22, -23]) (countLit q [-27, -29]) (count1486 q) 1 1 (meaning1482 q) (meaning1484 q) (meaning1487 q) hs
  change valuationOf q 1482 = false ∨ valuationOf q 1484 = false ∨ valuationOf q 1487 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause587 (q : Snake 81) (h : Conditions q) : valuation q 1482 = false ∨ valuation q 1484 = false ∨ valuation q 1487 = true := counterClause587 (baseVal q)

theorem counterClause588 (q : Nat → Bool) : valuationOf q 1483 = false ∨ valuationOf q 1487 = true := by
  have hs : count1486 q = (countLit q [-22, -23]) + (countLit q [-27, -29]) := List.countP_append (p := literal q) (l₁ := [-22, -23]) (l₂ := [-27, -29])
  have hm := merge_left (literal (valuationOf q) (1483)) (literal (valuationOf q) (1487)) (countLit q [-22, -23]) (countLit q [-27, -29]) (count1486 q) 2 (meaning1483 q) (meaning1487 q) hs
  change valuationOf q 1483 = false ∨ valuationOf q 1487 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause588 (q : Snake 81) (h : Conditions q) : valuation q 1483 = false ∨ valuation q 1487 = true := counterClause588 (baseVal q)

theorem counterClause589 (q : Nat → Bool) : valuationOf q 1483 = false ∨ valuationOf q 1484 = false ∨ valuationOf q 1488 = true := by
  have hs : count1486 q = (countLit q [-22, -23]) + (countLit q [-27, -29]) := List.countP_append (p := literal q) (l₁ := [-22, -23]) (l₂ := [-27, -29])
  have hm := merge_two (literal (valuationOf q) (1483)) (literal (valuationOf q) (1484)) (literal (valuationOf q) (1488)) (countLit q [-22, -23]) (countLit q [-27, -29]) (count1486 q) 2 1 (meaning1483 q) (meaning1484 q) (meaning1488 q) hs
  change valuationOf q 1483 = false ∨ valuationOf q 1484 = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause589 (q : Snake 81) (h : Conditions q) : valuation q 1483 = false ∨ valuation q 1484 = false ∨ valuation q 1488 = true := counterClause589 (baseVal q)

theorem counterClause590 (q : Nat → Bool) : valuationOf q 1486 = false ∨ valuationOf q 1490 = true := by
  have hs : count1490 q = (countLit q [-16, -20, -21]) + (countLit q [-22, -23, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-16, -20, -21]) (l₂ := [-22, -23, -27, -29])
  have hm := merge_right (literal (valuationOf q) (1486)) (literal (valuationOf q) (1490)) (countLit q [-16, -20, -21]) (countLit q [-22, -23, -27, -29]) (count1490 q) 1 (meaning1486 q) (meaning1490 q) hs
  change valuationOf q 1486 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause590 (q : Snake 81) (h : Conditions q) : valuation q 1486 = false ∨ valuation q 1490 = true := counterClause590 (baseVal q)

theorem counterClause591 (q : Nat → Bool) : valuationOf q 1487 = false ∨ valuationOf q 1491 = true := by
  have hs : count1490 q = (countLit q [-16, -20, -21]) + (countLit q [-22, -23, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-16, -20, -21]) (l₂ := [-22, -23, -27, -29])
  have hm := merge_right (literal (valuationOf q) (1487)) (literal (valuationOf q) (1491)) (countLit q [-16, -20, -21]) (countLit q [-22, -23, -27, -29]) (count1490 q) 2 (meaning1487 q) (meaning1491 q) hs
  change valuationOf q 1487 = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause591 (q : Snake 81) (h : Conditions q) : valuation q 1487 = false ∨ valuation q 1491 = true := counterClause591 (baseVal q)

theorem counterClause592 (q : Nat → Bool) : valuationOf q 1479 = false ∨ valuationOf q 1490 = true := by
  have hs : count1490 q = (countLit q [-16, -20, -21]) + (countLit q [-22, -23, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-16, -20, -21]) (l₂ := [-22, -23, -27, -29])
  have hm := merge_left (literal (valuationOf q) (1479)) (literal (valuationOf q) (1490)) (countLit q [-16, -20, -21]) (countLit q [-22, -23, -27, -29]) (count1490 q) 1 (meaning1479 q) (meaning1490 q) hs
  change valuationOf q 1479 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause592 (q : Snake 81) (h : Conditions q) : valuation q 1479 = false ∨ valuation q 1490 = true := counterClause592 (baseVal q)

theorem counterClause593 (q : Nat → Bool) : valuationOf q 1479 = false ∨ valuationOf q 1486 = false ∨ valuationOf q 1491 = true := by
  have hs : count1490 q = (countLit q [-16, -20, -21]) + (countLit q [-22, -23, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-16, -20, -21]) (l₂ := [-22, -23, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1479)) (literal (valuationOf q) (1486)) (literal (valuationOf q) (1491)) (countLit q [-16, -20, -21]) (countLit q [-22, -23, -27, -29]) (count1490 q) 1 1 (meaning1479 q) (meaning1486 q) (meaning1491 q) hs
  change valuationOf q 1479 = false ∨ valuationOf q 1486 = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause593 (q : Snake 81) (h : Conditions q) : valuation q 1479 = false ∨ valuation q 1486 = false ∨ valuation q 1491 = true := counterClause593 (baseVal q)

theorem counterClause594 (q : Nat → Bool) : valuationOf q 1479 = false ∨ valuationOf q 1487 = false ∨ valuationOf q 1492 = true := by
  have hs : count1490 q = (countLit q [-16, -20, -21]) + (countLit q [-22, -23, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-16, -20, -21]) (l₂ := [-22, -23, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1479)) (literal (valuationOf q) (1487)) (literal (valuationOf q) (1492)) (countLit q [-16, -20, -21]) (countLit q [-22, -23, -27, -29]) (count1490 q) 1 2 (meaning1479 q) (meaning1487 q) (meaning1492 q) hs
  change valuationOf q 1479 = false ∨ valuationOf q 1487 = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause594 (q : Snake 81) (h : Conditions q) : valuation q 1479 = false ∨ valuation q 1487 = false ∨ valuation q 1492 = true := counterClause594 (baseVal q)

theorem counterClause595 (q : Nat → Bool) : valuationOf q 1479 = false ∨ valuationOf q 1488 = false ∨ valuationOf q 1493 = true := by
  have hs : count1490 q = (countLit q [-16, -20, -21]) + (countLit q [-22, -23, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-16, -20, -21]) (l₂ := [-22, -23, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1479)) (literal (valuationOf q) (1488)) (literal (valuationOf q) (1493)) (countLit q [-16, -20, -21]) (countLit q [-22, -23, -27, -29]) (count1490 q) 1 3 (meaning1479 q) (meaning1488 q) (meaning1493 q) hs
  change valuationOf q 1479 = false ∨ valuationOf q 1488 = false ∨ valuationOf q 1493 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause595 (q : Snake 81) (h : Conditions q) : valuation q 1479 = false ∨ valuation q 1488 = false ∨ valuation q 1493 = true := counterClause595 (baseVal q)

theorem counterClause596 (q : Nat → Bool) : valuationOf q 1480 = false ∨ valuationOf q 1491 = true := by
  have hs : count1490 q = (countLit q [-16, -20, -21]) + (countLit q [-22, -23, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-16, -20, -21]) (l₂ := [-22, -23, -27, -29])
  have hm := merge_left (literal (valuationOf q) (1480)) (literal (valuationOf q) (1491)) (countLit q [-16, -20, -21]) (countLit q [-22, -23, -27, -29]) (count1490 q) 2 (meaning1480 q) (meaning1491 q) hs
  change valuationOf q 1480 = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause596 (q : Snake 81) (h : Conditions q) : valuation q 1480 = false ∨ valuation q 1491 = true := counterClause596 (baseVal q)

theorem counterClause597 (q : Nat → Bool) : valuationOf q 1480 = false ∨ valuationOf q 1486 = false ∨ valuationOf q 1492 = true := by
  have hs : count1490 q = (countLit q [-16, -20, -21]) + (countLit q [-22, -23, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-16, -20, -21]) (l₂ := [-22, -23, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1480)) (literal (valuationOf q) (1486)) (literal (valuationOf q) (1492)) (countLit q [-16, -20, -21]) (countLit q [-22, -23, -27, -29]) (count1490 q) 2 1 (meaning1480 q) (meaning1486 q) (meaning1492 q) hs
  change valuationOf q 1480 = false ∨ valuationOf q 1486 = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause597 (q : Snake 81) (h : Conditions q) : valuation q 1480 = false ∨ valuation q 1486 = false ∨ valuation q 1492 = true := counterClause597 (baseVal q)

theorem counterClause598 (q : Nat → Bool) : valuationOf q 1480 = false ∨ valuationOf q 1487 = false ∨ valuationOf q 1493 = true := by
  have hs : count1490 q = (countLit q [-16, -20, -21]) + (countLit q [-22, -23, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-16, -20, -21]) (l₂ := [-22, -23, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1480)) (literal (valuationOf q) (1487)) (literal (valuationOf q) (1493)) (countLit q [-16, -20, -21]) (countLit q [-22, -23, -27, -29]) (count1490 q) 2 2 (meaning1480 q) (meaning1487 q) (meaning1493 q) hs
  change valuationOf q 1480 = false ∨ valuationOf q 1487 = false ∨ valuationOf q 1493 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause598 (q : Snake 81) (h : Conditions q) : valuation q 1480 = false ∨ valuation q 1487 = false ∨ valuation q 1493 = true := counterClause598 (baseVal q)

theorem counterClause599 (q : Nat → Bool) : valuationOf q 1471 = false ∨ valuationOf q 1490 = false ∨ valuationOf q 1499 = true := by
  have hs : count1497 q = (countLit q [-3, -4, -6, -8, -11, -13, -14]) + (countLit q [-16, -20, -21, -22, -23, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -8, -11, -13, -14]) (l₂ := [-16, -20, -21, -22, -23, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1471)) (literal (valuationOf q) (1490)) (literal (valuationOf q) (1499)) (countLit q [-3, -4, -6, -8, -11, -13, -14]) (countLit q [-16, -20, -21, -22, -23, -27, -29]) (count1497 q) 2 1 (meaning1471 q) (meaning1490 q) (meaning1499 q) hs
  change valuationOf q 1471 = false ∨ valuationOf q 1490 = false ∨ valuationOf q 1499 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause599 (q : Snake 81) (h : Conditions q) : valuation q 1471 = false ∨ valuation q 1490 = false ∨ valuation q 1499 = true := counterClause599 (baseVal q)

theorem counterClause600 (q : Nat → Bool) : valuationOf q 1471 = false ∨ valuationOf q 1491 = false ∨ valuationOf q 1500 = true := by
  have hs : count1497 q = (countLit q [-3, -4, -6, -8, -11, -13, -14]) + (countLit q [-16, -20, -21, -22, -23, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -8, -11, -13, -14]) (l₂ := [-16, -20, -21, -22, -23, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1471)) (literal (valuationOf q) (1491)) (literal (valuationOf q) (1500)) (countLit q [-3, -4, -6, -8, -11, -13, -14]) (countLit q [-16, -20, -21, -22, -23, -27, -29]) (count1497 q) 2 2 (meaning1471 q) (meaning1491 q) (meaning1500 q) hs
  change valuationOf q 1471 = false ∨ valuationOf q 1491 = false ∨ valuationOf q 1500 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause600 (q : Snake 81) (h : Conditions q) : valuation q 1471 = false ∨ valuation q 1491 = false ∨ valuation q 1500 = true := counterClause600 (baseVal q)

theorem counterClause601 (q : Nat → Bool) : valuationOf q 1471 = false ∨ valuationOf q 1492 = false ∨ valuationOf q 1501 = true := by
  have hs : count1497 q = (countLit q [-3, -4, -6, -8, -11, -13, -14]) + (countLit q [-16, -20, -21, -22, -23, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -8, -11, -13, -14]) (l₂ := [-16, -20, -21, -22, -23, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1471)) (literal (valuationOf q) (1492)) (literal (valuationOf q) (1501)) (countLit q [-3, -4, -6, -8, -11, -13, -14]) (countLit q [-16, -20, -21, -22, -23, -27, -29]) (count1497 q) 2 3 (meaning1471 q) (meaning1492 q) (meaning1501 q) hs
  change valuationOf q 1471 = false ∨ valuationOf q 1492 = false ∨ valuationOf q 1501 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause601 (q : Snake 81) (h : Conditions q) : valuation q 1471 = false ∨ valuation q 1492 = false ∨ valuation q 1501 = true := counterClause601 (baseVal q)

theorem counterClause602 (q : Nat → Bool) : valuationOf q 1471 = false ∨ valuationOf q 1493 = false ∨ valuationOf q 1502 = true := by
  have hs : count1497 q = (countLit q [-3, -4, -6, -8, -11, -13, -14]) + (countLit q [-16, -20, -21, -22, -23, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -8, -11, -13, -14]) (l₂ := [-16, -20, -21, -22, -23, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1471)) (literal (valuationOf q) (1493)) (literal (valuationOf q) (1502)) (countLit q [-3, -4, -6, -8, -11, -13, -14]) (countLit q [-16, -20, -21, -22, -23, -27, -29]) (count1497 q) 2 4 (meaning1471 q) (meaning1493 q) (meaning1502 q) hs
  change valuationOf q 1471 = false ∨ valuationOf q 1493 = false ∨ valuationOf q 1502 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause602 (q : Snake 81) (h : Conditions q) : valuation q 1471 = false ∨ valuation q 1493 = false ∨ valuation q 1502 = true := counterClause602 (baseVal q)

theorem counterClause603 (q : Nat → Bool) : valuationOf q 1472 = false ∨ valuationOf q 1490 = false ∨ valuationOf q 1500 = true := by
  have hs : count1497 q = (countLit q [-3, -4, -6, -8, -11, -13, -14]) + (countLit q [-16, -20, -21, -22, -23, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -8, -11, -13, -14]) (l₂ := [-16, -20, -21, -22, -23, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1472)) (literal (valuationOf q) (1490)) (literal (valuationOf q) (1500)) (countLit q [-3, -4, -6, -8, -11, -13, -14]) (countLit q [-16, -20, -21, -22, -23, -27, -29]) (count1497 q) 3 1 (meaning1472 q) (meaning1490 q) (meaning1500 q) hs
  change valuationOf q 1472 = false ∨ valuationOf q 1490 = false ∨ valuationOf q 1500 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause603 (q : Snake 81) (h : Conditions q) : valuation q 1472 = false ∨ valuation q 1490 = false ∨ valuation q 1500 = true := counterClause603 (baseVal q)

theorem counterClause604 (q : Nat → Bool) : valuationOf q 1472 = false ∨ valuationOf q 1491 = false ∨ valuationOf q 1501 = true := by
  have hs : count1497 q = (countLit q [-3, -4, -6, -8, -11, -13, -14]) + (countLit q [-16, -20, -21, -22, -23, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -8, -11, -13, -14]) (l₂ := [-16, -20, -21, -22, -23, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1472)) (literal (valuationOf q) (1491)) (literal (valuationOf q) (1501)) (countLit q [-3, -4, -6, -8, -11, -13, -14]) (countLit q [-16, -20, -21, -22, -23, -27, -29]) (count1497 q) 3 2 (meaning1472 q) (meaning1491 q) (meaning1501 q) hs
  change valuationOf q 1472 = false ∨ valuationOf q 1491 = false ∨ valuationOf q 1501 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause604 (q : Snake 81) (h : Conditions q) : valuation q 1472 = false ∨ valuation q 1491 = false ∨ valuation q 1501 = true := counterClause604 (baseVal q)

theorem counterClause605 (q : Nat → Bool) : valuationOf q 1472 = false ∨ valuationOf q 1492 = false ∨ valuationOf q 1502 = true := by
  have hs : count1497 q = (countLit q [-3, -4, -6, -8, -11, -13, -14]) + (countLit q [-16, -20, -21, -22, -23, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -8, -11, -13, -14]) (l₂ := [-16, -20, -21, -22, -23, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1472)) (literal (valuationOf q) (1492)) (literal (valuationOf q) (1502)) (countLit q [-3, -4, -6, -8, -11, -13, -14]) (countLit q [-16, -20, -21, -22, -23, -27, -29]) (count1497 q) 3 3 (meaning1472 q) (meaning1492 q) (meaning1502 q) hs
  change valuationOf q 1472 = false ∨ valuationOf q 1492 = false ∨ valuationOf q 1502 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause605 (q : Snake 81) (h : Conditions q) : valuation q 1472 = false ∨ valuation q 1492 = false ∨ valuation q 1502 = true := counterClause605 (baseVal q)

theorem counterClause606 (q : Nat → Bool) : valuationOf q 1473 = false ∨ valuationOf q 1490 = false ∨ valuationOf q 1501 = true := by
  have hs : count1497 q = (countLit q [-3, -4, -6, -8, -11, -13, -14]) + (countLit q [-16, -20, -21, -22, -23, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -8, -11, -13, -14]) (l₂ := [-16, -20, -21, -22, -23, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1473)) (literal (valuationOf q) (1490)) (literal (valuationOf q) (1501)) (countLit q [-3, -4, -6, -8, -11, -13, -14]) (countLit q [-16, -20, -21, -22, -23, -27, -29]) (count1497 q) 4 1 (meaning1473 q) (meaning1490 q) (meaning1501 q) hs
  change valuationOf q 1473 = false ∨ valuationOf q 1490 = false ∨ valuationOf q 1501 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause606 (q : Snake 81) (h : Conditions q) : valuation q 1473 = false ∨ valuation q 1490 = false ∨ valuation q 1501 = true := counterClause606 (baseVal q)

theorem counterClause607 (q : Nat → Bool) : valuationOf q 37 = true ∨ valuationOf q 1511 = true := by
  have hs : count1511 q = (countLit q [-33]) + (countLit q [-37]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-37])
  have hm := merge_right (literal (valuationOf q) (-37)) (literal (valuationOf q) (1511)) (countLit q [-33]) (countLit q [-37]) (count1511 q) 1 (meaningNeg37 q) (meaning1511 q) hs
  change (! (valuationOf q 37)) = false ∨ valuationOf q 1511 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause607 (q : Snake 81) (h : Conditions q) : valuation q 37 = true ∨ valuation q 1511 = true := counterClause607 (baseVal q)

theorem counterClause608 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 1511 = true := by
  have hs : count1511 q = (countLit q [-33]) + (countLit q [-37]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-37])
  have hm := merge_left (literal (valuationOf q) (-33)) (literal (valuationOf q) (1511)) (countLit q [-33]) (countLit q [-37]) (count1511 q) 1 (meaningNeg33 q) (meaning1511 q) hs
  change (! (valuationOf q 33)) = false ∨ valuationOf q 1511 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause608 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 1511 = true := counterClause608 (baseVal q)

theorem block18 (q : Snake 81) (h : Conditions q) : B112E152.Block18 (valuation q) :=
  ⟨clause577 q h, clause578 q h, clause579 q h, clause580 q h, clause581 q h, clause582 q h, clause583 q h, clause584 q h, clause585 q h, clause586 q h, clause587 q h, clause588 q h, clause589 q h, clause590 q h, clause591 q h, clause592 q h, clause593 q h, clause594 q h, clause595 q h, clause596 q h, clause597 q h, clause598 q h, clause599 q h, clause600 q h, clause601 q h, clause602 q h, clause603 q h, clause604 q h, clause605 q h, clause606 q h, clause607 q h, clause608 q h⟩

end
end Snake9.Regrowth.E112152
