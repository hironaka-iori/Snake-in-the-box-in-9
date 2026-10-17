import E112166Semantics
import B112E166Inputs
namespace Snake9.Regrowth.E112166
noncomputable section
local instance blockDec18 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause577 (q : Nat → Bool) : valuationOf q 98 = true ∨ valuationOf q 101 = true ∨ valuationOf q 1484 = true := by
  have hs : count1483 q = (countLit q [-98]) + (countLit q [-101]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-101])
  have hm := merge_two (literal (valuationOf q) (-98)) (literal (valuationOf q) (-101)) (literal (valuationOf q) (1484)) (countLit q [-98]) (countLit q [-101]) (count1483 q) 1 1 (meaningNeg98 q) (meaningNeg101 q) (meaning1484 q) hs
  change (! (valuationOf q 98)) = false ∨ (! (valuationOf q 101)) = false ∨ valuationOf q 1484 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause577 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 101 = true ∨ valuation q 1484 = true := counterClause577 (baseVal q)

theorem counterClause578 (q : Nat → Bool) : valuationOf q 1483 = false ∨ valuationOf q 1485 = true := by
  have hs : count1485 q = (countLit q [-97]) + (countLit q [-98, -101]) := List.countP_append (p := literal q) (l₁ := [-97]) (l₂ := [-98, -101])
  have hm := merge_right (literal (valuationOf q) (1483)) (literal (valuationOf q) (1485)) (countLit q [-97]) (countLit q [-98, -101]) (count1485 q) 1 (meaning1483 q) (meaning1485 q) hs
  change valuationOf q 1483 = false ∨ valuationOf q 1485 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause578 (q : Snake 81) (h : Conditions q) : valuation q 1483 = false ∨ valuation q 1485 = true := counterClause578 (baseVal q)

theorem counterClause579 (q : Nat → Bool) : valuationOf q 1484 = false ∨ valuationOf q 1486 = true := by
  have hs : count1485 q = (countLit q [-97]) + (countLit q [-98, -101]) := List.countP_append (p := literal q) (l₁ := [-97]) (l₂ := [-98, -101])
  have hm := merge_right (literal (valuationOf q) (1484)) (literal (valuationOf q) (1486)) (countLit q [-97]) (countLit q [-98, -101]) (count1485 q) 2 (meaning1484 q) (meaning1486 q) hs
  change valuationOf q 1484 = false ∨ valuationOf q 1486 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause579 (q : Snake 81) (h : Conditions q) : valuation q 1484 = false ∨ valuation q 1486 = true := counterClause579 (baseVal q)

theorem counterClause580 (q : Nat → Bool) : valuationOf q 97 = true ∨ valuationOf q 1485 = true := by
  have hs : count1485 q = (countLit q [-97]) + (countLit q [-98, -101]) := List.countP_append (p := literal q) (l₁ := [-97]) (l₂ := [-98, -101])
  have hm := merge_left (literal (valuationOf q) (-97)) (literal (valuationOf q) (1485)) (countLit q [-97]) (countLit q [-98, -101]) (count1485 q) 1 (meaningNeg97 q) (meaning1485 q) hs
  change (! (valuationOf q 97)) = false ∨ valuationOf q 1485 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause580 (q : Snake 81) (h : Conditions q) : valuation q 97 = true ∨ valuation q 1485 = true := counterClause580 (baseVal q)

theorem counterClause581 (q : Nat → Bool) : valuationOf q 97 = true ∨ valuationOf q 1483 = false ∨ valuationOf q 1486 = true := by
  have hs : count1485 q = (countLit q [-97]) + (countLit q [-98, -101]) := List.countP_append (p := literal q) (l₁ := [-97]) (l₂ := [-98, -101])
  have hm := merge_two (literal (valuationOf q) (-97)) (literal (valuationOf q) (1483)) (literal (valuationOf q) (1486)) (countLit q [-97]) (countLit q [-98, -101]) (count1485 q) 1 1 (meaningNeg97 q) (meaning1483 q) (meaning1486 q) hs
  change (! (valuationOf q 97)) = false ∨ valuationOf q 1483 = false ∨ valuationOf q 1486 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause581 (q : Snake 81) (h : Conditions q) : valuation q 97 = true ∨ valuation q 1483 = false ∨ valuation q 1486 = true := counterClause581 (baseVal q)

theorem counterClause582 (q : Nat → Bool) : valuationOf q 104 = true ∨ valuationOf q 1488 = true := by
  have hs : count1488 q = (countLit q [-102]) + (countLit q [-104]) := List.countP_append (p := literal q) (l₁ := [-102]) (l₂ := [-104])
  have hm := merge_right (literal (valuationOf q) (-104)) (literal (valuationOf q) (1488)) (countLit q [-102]) (countLit q [-104]) (count1488 q) 1 (meaningNeg104 q) (meaning1488 q) hs
  change (! (valuationOf q 104)) = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause582 (q : Snake 81) (h : Conditions q) : valuation q 104 = true ∨ valuation q 1488 = true := counterClause582 (baseVal q)

theorem counterClause583 (q : Nat → Bool) : valuationOf q 102 = true ∨ valuationOf q 1488 = true := by
  have hs : count1488 q = (countLit q [-102]) + (countLit q [-104]) := List.countP_append (p := literal q) (l₁ := [-102]) (l₂ := [-104])
  have hm := merge_left (literal (valuationOf q) (-102)) (literal (valuationOf q) (1488)) (countLit q [-102]) (countLit q [-104]) (count1488 q) 1 (meaningNeg102 q) (meaning1488 q) hs
  change (! (valuationOf q 102)) = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause583 (q : Snake 81) (h : Conditions q) : valuation q 102 = true ∨ valuation q 1488 = true := counterClause583 (baseVal q)

theorem counterClause584 (q : Nat → Bool) : valuationOf q 107 = true ∨ valuationOf q 1490 = true := by
  have hs : count1490 q = (countLit q [-106]) + (countLit q [-107]) := List.countP_append (p := literal q) (l₁ := [-106]) (l₂ := [-107])
  have hm := merge_right (literal (valuationOf q) (-107)) (literal (valuationOf q) (1490)) (countLit q [-106]) (countLit q [-107]) (count1490 q) 1 (meaningNeg107 q) (meaning1490 q) hs
  change (! (valuationOf q 107)) = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause584 (q : Snake 81) (h : Conditions q) : valuation q 107 = true ∨ valuation q 1490 = true := counterClause584 (baseVal q)

theorem counterClause585 (q : Nat → Bool) : valuationOf q 106 = true ∨ valuationOf q 1490 = true := by
  have hs : count1490 q = (countLit q [-106]) + (countLit q [-107]) := List.countP_append (p := literal q) (l₁ := [-106]) (l₂ := [-107])
  have hm := merge_left (literal (valuationOf q) (-106)) (literal (valuationOf q) (1490)) (countLit q [-106]) (countLit q [-107]) (count1490 q) 1 (meaningNeg106 q) (meaning1490 q) hs
  change (! (valuationOf q 106)) = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause585 (q : Snake 81) (h : Conditions q) : valuation q 106 = true ∨ valuation q 1490 = true := counterClause585 (baseVal q)

theorem counterClause586 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1492 = true := by
  have hs : count1492 q = (countLit q [-102, -104]) + (countLit q [-106, -107]) := List.countP_append (p := literal q) (l₁ := [-102, -104]) (l₂ := [-106, -107])
  have hm := merge_right (literal (valuationOf q) (1490)) (literal (valuationOf q) (1492)) (countLit q [-102, -104]) (countLit q [-106, -107]) (count1492 q) 1 (meaning1490 q) (meaning1492 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause586 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1492 = true := counterClause586 (baseVal q)

theorem counterClause587 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1492 = true := by
  have hs : count1492 q = (countLit q [-102, -104]) + (countLit q [-106, -107]) := List.countP_append (p := literal q) (l₁ := [-102, -104]) (l₂ := [-106, -107])
  have hm := merge_left (literal (valuationOf q) (1488)) (literal (valuationOf q) (1492)) (countLit q [-102, -104]) (countLit q [-106, -107]) (count1492 q) 1 (meaning1488 q) (meaning1492 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause587 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1492 = true := counterClause587 (baseVal q)

theorem counterClause588 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1490 = false ∨ valuationOf q 1493 = true := by
  have hs : count1492 q = (countLit q [-102, -104]) + (countLit q [-106, -107]) := List.countP_append (p := literal q) (l₁ := [-102, -104]) (l₂ := [-106, -107])
  have hm := merge_two (literal (valuationOf q) (1488)) (literal (valuationOf q) (1490)) (literal (valuationOf q) (1493)) (countLit q [-102, -104]) (countLit q [-106, -107]) (count1492 q) 1 1 (meaning1488 q) (meaning1490 q) (meaning1493 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1490 = false ∨ valuationOf q 1493 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause588 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1490 = false ∨ valuation q 1493 = true := counterClause588 (baseVal q)

theorem counterClause589 (q : Nat → Bool) : valuationOf q 1492 = false ∨ valuationOf q 1496 = true := by
  have hs : count1496 q = (countLit q [-97, -98, -101]) + (countLit q [-102, -104, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-97, -98, -101]) (l₂ := [-102, -104, -106, -107])
  have hm := merge_right (literal (valuationOf q) (1492)) (literal (valuationOf q) (1496)) (countLit q [-97, -98, -101]) (countLit q [-102, -104, -106, -107]) (count1496 q) 1 (meaning1492 q) (meaning1496 q) hs
  change valuationOf q 1492 = false ∨ valuationOf q 1496 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause589 (q : Snake 81) (h : Conditions q) : valuation q 1492 = false ∨ valuation q 1496 = true := counterClause589 (baseVal q)

theorem counterClause590 (q : Nat → Bool) : valuationOf q 1493 = false ∨ valuationOf q 1497 = true := by
  have hs : count1496 q = (countLit q [-97, -98, -101]) + (countLit q [-102, -104, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-97, -98, -101]) (l₂ := [-102, -104, -106, -107])
  have hm := merge_right (literal (valuationOf q) (1493)) (literal (valuationOf q) (1497)) (countLit q [-97, -98, -101]) (countLit q [-102, -104, -106, -107]) (count1496 q) 2 (meaning1493 q) (meaning1497 q) hs
  change valuationOf q 1493 = false ∨ valuationOf q 1497 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause590 (q : Snake 81) (h : Conditions q) : valuation q 1493 = false ∨ valuation q 1497 = true := counterClause590 (baseVal q)

theorem counterClause591 (q : Nat → Bool) : valuationOf q 1485 = false ∨ valuationOf q 1496 = true := by
  have hs : count1496 q = (countLit q [-97, -98, -101]) + (countLit q [-102, -104, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-97, -98, -101]) (l₂ := [-102, -104, -106, -107])
  have hm := merge_left (literal (valuationOf q) (1485)) (literal (valuationOf q) (1496)) (countLit q [-97, -98, -101]) (countLit q [-102, -104, -106, -107]) (count1496 q) 1 (meaning1485 q) (meaning1496 q) hs
  change valuationOf q 1485 = false ∨ valuationOf q 1496 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause591 (q : Snake 81) (h : Conditions q) : valuation q 1485 = false ∨ valuation q 1496 = true := counterClause591 (baseVal q)

theorem counterClause592 (q : Nat → Bool) : valuationOf q 1485 = false ∨ valuationOf q 1492 = false ∨ valuationOf q 1497 = true := by
  have hs : count1496 q = (countLit q [-97, -98, -101]) + (countLit q [-102, -104, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-97, -98, -101]) (l₂ := [-102, -104, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1485)) (literal (valuationOf q) (1492)) (literal (valuationOf q) (1497)) (countLit q [-97, -98, -101]) (countLit q [-102, -104, -106, -107]) (count1496 q) 1 1 (meaning1485 q) (meaning1492 q) (meaning1497 q) hs
  change valuationOf q 1485 = false ∨ valuationOf q 1492 = false ∨ valuationOf q 1497 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause592 (q : Snake 81) (h : Conditions q) : valuation q 1485 = false ∨ valuation q 1492 = false ∨ valuation q 1497 = true := counterClause592 (baseVal q)

theorem counterClause593 (q : Nat → Bool) : valuationOf q 1485 = false ∨ valuationOf q 1493 = false ∨ valuationOf q 1498 = true := by
  have hs : count1496 q = (countLit q [-97, -98, -101]) + (countLit q [-102, -104, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-97, -98, -101]) (l₂ := [-102, -104, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1485)) (literal (valuationOf q) (1493)) (literal (valuationOf q) (1498)) (countLit q [-97, -98, -101]) (countLit q [-102, -104, -106, -107]) (count1496 q) 1 2 (meaning1485 q) (meaning1493 q) (meaning1498 q) hs
  change valuationOf q 1485 = false ∨ valuationOf q 1493 = false ∨ valuationOf q 1498 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause593 (q : Snake 81) (h : Conditions q) : valuation q 1485 = false ∨ valuation q 1493 = false ∨ valuation q 1498 = true := counterClause593 (baseVal q)

theorem counterClause594 (q : Nat → Bool) : valuationOf q 1486 = false ∨ valuationOf q 1497 = true := by
  have hs : count1496 q = (countLit q [-97, -98, -101]) + (countLit q [-102, -104, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-97, -98, -101]) (l₂ := [-102, -104, -106, -107])
  have hm := merge_left (literal (valuationOf q) (1486)) (literal (valuationOf q) (1497)) (countLit q [-97, -98, -101]) (countLit q [-102, -104, -106, -107]) (count1496 q) 2 (meaning1486 q) (meaning1497 q) hs
  change valuationOf q 1486 = false ∨ valuationOf q 1497 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause594 (q : Snake 81) (h : Conditions q) : valuation q 1486 = false ∨ valuation q 1497 = true := counterClause594 (baseVal q)

theorem counterClause595 (q : Nat → Bool) : valuationOf q 1486 = false ∨ valuationOf q 1492 = false ∨ valuationOf q 1498 = true := by
  have hs : count1496 q = (countLit q [-97, -98, -101]) + (countLit q [-102, -104, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-97, -98, -101]) (l₂ := [-102, -104, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1486)) (literal (valuationOf q) (1492)) (literal (valuationOf q) (1498)) (countLit q [-97, -98, -101]) (countLit q [-102, -104, -106, -107]) (count1496 q) 2 1 (meaning1486 q) (meaning1492 q) (meaning1498 q) hs
  change valuationOf q 1486 = false ∨ valuationOf q 1492 = false ∨ valuationOf q 1498 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause595 (q : Snake 81) (h : Conditions q) : valuation q 1486 = false ∨ valuation q 1492 = false ∨ valuation q 1498 = true := counterClause595 (baseVal q)

theorem counterClause596 (q : Nat → Bool) : valuationOf q 1496 = false ∨ valuationOf q 1503 = true := by
  have hs : count1503 q = (countLit q [-81, -84, -86, -87, -90, -92, -93]) + (countLit q [-97, -98, -101, -102, -104, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-81, -84, -86, -87, -90, -92, -93]) (l₂ := [-97, -98, -101, -102, -104, -106, -107])
  have hm := merge_right (literal (valuationOf q) (1496)) (literal (valuationOf q) (1503)) (countLit q [-81, -84, -86, -87, -90, -92, -93]) (countLit q [-97, -98, -101, -102, -104, -106, -107]) (count1503 q) 1 (meaning1496 q) (meaning1503 q) hs
  change valuationOf q 1496 = false ∨ valuationOf q 1503 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause596 (q : Snake 81) (h : Conditions q) : valuation q 1496 = false ∨ valuation q 1503 = true := counterClause596 (baseVal q)

theorem counterClause597 (q : Nat → Bool) : valuationOf q 1476 = false ∨ valuationOf q 1496 = false ∨ valuationOf q 1504 = true := by
  have hs : count1503 q = (countLit q [-81, -84, -86, -87, -90, -92, -93]) + (countLit q [-97, -98, -101, -102, -104, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-81, -84, -86, -87, -90, -92, -93]) (l₂ := [-97, -98, -101, -102, -104, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1476)) (literal (valuationOf q) (1496)) (literal (valuationOf q) (1504)) (countLit q [-81, -84, -86, -87, -90, -92, -93]) (countLit q [-97, -98, -101, -102, -104, -106, -107]) (count1503 q) 1 1 (meaning1476 q) (meaning1496 q) (meaning1504 q) hs
  change valuationOf q 1476 = false ∨ valuationOf q 1496 = false ∨ valuationOf q 1504 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause597 (q : Snake 81) (h : Conditions q) : valuation q 1476 = false ∨ valuation q 1496 = false ∨ valuation q 1504 = true := counterClause597 (baseVal q)

theorem counterClause598 (q : Nat → Bool) : valuationOf q 1476 = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1505 = true := by
  have hs : count1503 q = (countLit q [-81, -84, -86, -87, -90, -92, -93]) + (countLit q [-97, -98, -101, -102, -104, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-81, -84, -86, -87, -90, -92, -93]) (l₂ := [-97, -98, -101, -102, -104, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1476)) (literal (valuationOf q) (1497)) (literal (valuationOf q) (1505)) (countLit q [-81, -84, -86, -87, -90, -92, -93]) (countLit q [-97, -98, -101, -102, -104, -106, -107]) (count1503 q) 1 2 (meaning1476 q) (meaning1497 q) (meaning1505 q) hs
  change valuationOf q 1476 = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1505 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause598 (q : Snake 81) (h : Conditions q) : valuation q 1476 = false ∨ valuation q 1497 = false ∨ valuation q 1505 = true := counterClause598 (baseVal q)

theorem counterClause599 (q : Nat → Bool) : valuationOf q 1477 = false ∨ valuationOf q 1496 = false ∨ valuationOf q 1505 = true := by
  have hs : count1503 q = (countLit q [-81, -84, -86, -87, -90, -92, -93]) + (countLit q [-97, -98, -101, -102, -104, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-81, -84, -86, -87, -90, -92, -93]) (l₂ := [-97, -98, -101, -102, -104, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1477)) (literal (valuationOf q) (1496)) (literal (valuationOf q) (1505)) (countLit q [-81, -84, -86, -87, -90, -92, -93]) (countLit q [-97, -98, -101, -102, -104, -106, -107]) (count1503 q) 2 1 (meaning1477 q) (meaning1496 q) (meaning1505 q) hs
  change valuationOf q 1477 = false ∨ valuationOf q 1496 = false ∨ valuationOf q 1505 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause599 (q : Snake 81) (h : Conditions q) : valuation q 1477 = false ∨ valuation q 1496 = false ∨ valuation q 1505 = true := counterClause599 (baseVal q)

theorem counterClause600 (q : Nat → Bool) : valuationOf q 1477 = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1506 = true := by
  have hs : count1503 q = (countLit q [-81, -84, -86, -87, -90, -92, -93]) + (countLit q [-97, -98, -101, -102, -104, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-81, -84, -86, -87, -90, -92, -93]) (l₂ := [-97, -98, -101, -102, -104, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1477)) (literal (valuationOf q) (1497)) (literal (valuationOf q) (1506)) (countLit q [-81, -84, -86, -87, -90, -92, -93]) (countLit q [-97, -98, -101, -102, -104, -106, -107]) (count1503 q) 2 2 (meaning1477 q) (meaning1497 q) (meaning1506 q) hs
  change valuationOf q 1477 = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1506 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause600 (q : Snake 81) (h : Conditions q) : valuation q 1477 = false ∨ valuation q 1497 = false ∨ valuation q 1506 = true := counterClause600 (baseVal q)

theorem counterClause601 (q : Nat → Bool) : valuationOf q 1477 = false ∨ valuationOf q 1498 = false ∨ valuationOf q 1507 = true := by
  have hs : count1503 q = (countLit q [-81, -84, -86, -87, -90, -92, -93]) + (countLit q [-97, -98, -101, -102, -104, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-81, -84, -86, -87, -90, -92, -93]) (l₂ := [-97, -98, -101, -102, -104, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1477)) (literal (valuationOf q) (1498)) (literal (valuationOf q) (1507)) (countLit q [-81, -84, -86, -87, -90, -92, -93]) (countLit q [-97, -98, -101, -102, -104, -106, -107]) (count1503 q) 2 3 (meaning1477 q) (meaning1498 q) (meaning1507 q) hs
  change valuationOf q 1477 = false ∨ valuationOf q 1498 = false ∨ valuationOf q 1507 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause601 (q : Snake 81) (h : Conditions q) : valuation q 1477 = false ∨ valuation q 1498 = false ∨ valuation q 1507 = true := counterClause601 (baseVal q)

theorem counterClause602 (q : Nat → Bool) : valuationOf q 1478 = false ∨ valuationOf q 1496 = false ∨ valuationOf q 1506 = true := by
  have hs : count1503 q = (countLit q [-81, -84, -86, -87, -90, -92, -93]) + (countLit q [-97, -98, -101, -102, -104, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-81, -84, -86, -87, -90, -92, -93]) (l₂ := [-97, -98, -101, -102, -104, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1478)) (literal (valuationOf q) (1496)) (literal (valuationOf q) (1506)) (countLit q [-81, -84, -86, -87, -90, -92, -93]) (countLit q [-97, -98, -101, -102, -104, -106, -107]) (count1503 q) 3 1 (meaning1478 q) (meaning1496 q) (meaning1506 q) hs
  change valuationOf q 1478 = false ∨ valuationOf q 1496 = false ∨ valuationOf q 1506 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause602 (q : Snake 81) (h : Conditions q) : valuation q 1478 = false ∨ valuation q 1496 = false ∨ valuation q 1506 = true := counterClause602 (baseVal q)

theorem counterClause603 (q : Nat → Bool) : valuationOf q 1478 = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1507 = true := by
  have hs : count1503 q = (countLit q [-81, -84, -86, -87, -90, -92, -93]) + (countLit q [-97, -98, -101, -102, -104, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-81, -84, -86, -87, -90, -92, -93]) (l₂ := [-97, -98, -101, -102, -104, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1478)) (literal (valuationOf q) (1497)) (literal (valuationOf q) (1507)) (countLit q [-81, -84, -86, -87, -90, -92, -93]) (countLit q [-97, -98, -101, -102, -104, -106, -107]) (count1503 q) 3 2 (meaning1478 q) (meaning1497 q) (meaning1507 q) hs
  change valuationOf q 1478 = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1507 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause603 (q : Snake 81) (h : Conditions q) : valuation q 1478 = false ∨ valuation q 1497 = false ∨ valuation q 1507 = true := counterClause603 (baseVal q)

theorem counterClause604 (q : Nat → Bool) : valuationOf q 1478 = false ∨ valuationOf q 1498 = false ∨ valuationOf q 1508 = true := by
  have hs : count1503 q = (countLit q [-81, -84, -86, -87, -90, -92, -93]) + (countLit q [-97, -98, -101, -102, -104, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-81, -84, -86, -87, -90, -92, -93]) (l₂ := [-97, -98, -101, -102, -104, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1478)) (literal (valuationOf q) (1498)) (literal (valuationOf q) (1508)) (countLit q [-81, -84, -86, -87, -90, -92, -93]) (countLit q [-97, -98, -101, -102, -104, -106, -107]) (count1503 q) 3 3 (meaning1478 q) (meaning1498 q) (meaning1508 q) hs
  change valuationOf q 1478 = false ∨ valuationOf q 1498 = false ∨ valuationOf q 1508 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause604 (q : Snake 81) (h : Conditions q) : valuation q 1478 = false ∨ valuation q 1498 = false ∨ valuation q 1508 = true := counterClause604 (baseVal q)

theorem counterClause605 (q : Nat → Bool) : valuationOf q 1479 = false ∨ valuationOf q 1496 = false ∨ valuationOf q 1507 = true := by
  have hs : count1503 q = (countLit q [-81, -84, -86, -87, -90, -92, -93]) + (countLit q [-97, -98, -101, -102, -104, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-81, -84, -86, -87, -90, -92, -93]) (l₂ := [-97, -98, -101, -102, -104, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1479)) (literal (valuationOf q) (1496)) (literal (valuationOf q) (1507)) (countLit q [-81, -84, -86, -87, -90, -92, -93]) (countLit q [-97, -98, -101, -102, -104, -106, -107]) (count1503 q) 4 1 (meaning1479 q) (meaning1496 q) (meaning1507 q) hs
  change valuationOf q 1479 = false ∨ valuationOf q 1496 = false ∨ valuationOf q 1507 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause605 (q : Snake 81) (h : Conditions q) : valuation q 1479 = false ∨ valuation q 1496 = false ∨ valuation q 1507 = true := counterClause605 (baseVal q)

theorem counterClause606 (q : Nat → Bool) : valuationOf q 1479 = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1508 = true := by
  have hs : count1503 q = (countLit q [-81, -84, -86, -87, -90, -92, -93]) + (countLit q [-97, -98, -101, -102, -104, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-81, -84, -86, -87, -90, -92, -93]) (l₂ := [-97, -98, -101, -102, -104, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1479)) (literal (valuationOf q) (1497)) (literal (valuationOf q) (1508)) (countLit q [-81, -84, -86, -87, -90, -92, -93]) (countLit q [-97, -98, -101, -102, -104, -106, -107]) (count1503 q) 4 2 (meaning1479 q) (meaning1497 q) (meaning1508 q) hs
  change valuationOf q 1479 = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1508 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause606 (q : Snake 81) (h : Conditions q) : valuation q 1479 = false ∨ valuation q 1497 = false ∨ valuation q 1508 = true := counterClause606 (baseVal q)

theorem counterClause607 (q : Nat → Bool) : valuationOf q 1480 = false ∨ valuationOf q 1496 = false ∨ valuationOf q 1508 = true := by
  have hs : count1503 q = (countLit q [-81, -84, -86, -87, -90, -92, -93]) + (countLit q [-97, -98, -101, -102, -104, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-81, -84, -86, -87, -90, -92, -93]) (l₂ := [-97, -98, -101, -102, -104, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1480)) (literal (valuationOf q) (1496)) (literal (valuationOf q) (1508)) (countLit q [-81, -84, -86, -87, -90, -92, -93]) (countLit q [-97, -98, -101, -102, -104, -106, -107]) (count1503 q) 5 1 (meaning1480 q) (meaning1496 q) (meaning1508 q) hs
  change valuationOf q 1480 = false ∨ valuationOf q 1496 = false ∨ valuationOf q 1508 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause607 (q : Snake 81) (h : Conditions q) : valuation q 1480 = false ∨ valuation q 1496 = false ∨ valuation q 1508 = true := counterClause607 (baseVal q)

theorem counterClause608 (q : Nat → Bool) : valuationOf q 1480 = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1509 = true := by
  have hs : count1503 q = (countLit q [-81, -84, -86, -87, -90, -92, -93]) + (countLit q [-97, -98, -101, -102, -104, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-81, -84, -86, -87, -90, -92, -93]) (l₂ := [-97, -98, -101, -102, -104, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1480)) (literal (valuationOf q) (1497)) (literal (valuationOf q) (1509)) (countLit q [-81, -84, -86, -87, -90, -92, -93]) (countLit q [-97, -98, -101, -102, -104, -106, -107]) (count1503 q) 5 2 (meaning1480 q) (meaning1497 q) (meaning1509 q) hs
  change valuationOf q 1480 = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1509 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause608 (q : Snake 81) (h : Conditions q) : valuation q 1480 = false ∨ valuation q 1497 = false ∨ valuation q 1509 = true := counterClause608 (baseVal q)

theorem block18 (q : Snake 81) (h : Conditions q) : B112E166.Block18 (valuation q) :=
  ⟨clause577 q h, clause578 q h, clause579 q h, clause580 q h, clause581 q h, clause582 q h, clause583 q h, clause584 q h, clause585 q h, clause586 q h, clause587 q h, clause588 q h, clause589 q h, clause590 q h, clause591 q h, clause592 q h, clause593 q h, clause594 q h, clause595 q h, clause596 q h, clause597 q h, clause598 q h, clause599 q h, clause600 q h, clause601 q h, clause602 q h, clause603 q h, clause604 q h, clause605 q h, clause606 q h, clause607 q h, clause608 q h⟩

end
end Snake9.Regrowth.E112166
