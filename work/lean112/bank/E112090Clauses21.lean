import E112090Semantics
import B112E090Inputs
namespace Snake9.Regrowth.E112090
noncomputable section
local instance blockDec21 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause673 (q : Nat → Bool) : valuationOf q 1466 = false ∨ valuationOf q 1473 = false ∨ valuationOf q 1479 = true := by
  have hs : count1476 q = (countLit q [-83, -85, -87]) + (countLit q [-88, -91, -92, -94]) := List.countP_append (p := literal q) (l₁ := [-83, -85, -87]) (l₂ := [-88, -91, -92, -94])
  have hm := merge_two (literal (valuationOf q) (1466)) (literal (valuationOf q) (1473)) (literal (valuationOf q) (1479)) (countLit q [-83, -85, -87]) (countLit q [-88, -91, -92, -94]) (count1476 q) 2 2 (meaning1466 q) (meaning1473 q) (meaning1479 q) hs
  change valuationOf q 1466 = false ∨ valuationOf q 1473 = false ∨ valuationOf q 1479 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause673 (q : Snake 81) (h : Conditions q) : valuation q 1466 = false ∨ valuation q 1473 = false ∨ valuation q 1479 = true := counterClause673 (baseVal q)

theorem counterClause674 (q : Nat → Bool) : valuationOf q 1466 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1480 = true := by
  have hs : count1476 q = (countLit q [-83, -85, -87]) + (countLit q [-88, -91, -92, -94]) := List.countP_append (p := literal q) (l₁ := [-83, -85, -87]) (l₂ := [-88, -91, -92, -94])
  have hm := merge_two (literal (valuationOf q) (1466)) (literal (valuationOf q) (1474)) (literal (valuationOf q) (1480)) (countLit q [-83, -85, -87]) (countLit q [-88, -91, -92, -94]) (count1476 q) 2 3 (meaning1466 q) (meaning1474 q) (meaning1480 q) hs
  change valuationOf q 1466 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1480 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause674 (q : Snake 81) (h : Conditions q) : valuation q 1466 = false ∨ valuation q 1474 = false ∨ valuation q 1480 = true := counterClause674 (baseVal q)

theorem counterClause675 (q : Nat → Bool) : valuationOf q 1466 = false ∨ valuationOf q 1475 = false ∨ valuationOf q 1481 = true := by
  have hs : count1476 q = (countLit q [-83, -85, -87]) + (countLit q [-88, -91, -92, -94]) := List.countP_append (p := literal q) (l₁ := [-83, -85, -87]) (l₂ := [-88, -91, -92, -94])
  have hm := merge_two (literal (valuationOf q) (1466)) (literal (valuationOf q) (1475)) (literal (valuationOf q) (1481)) (countLit q [-83, -85, -87]) (countLit q [-88, -91, -92, -94]) (count1476 q) 2 4 (meaning1466 q) (meaning1475 q) (meaning1481 q) hs
  change valuationOf q 1466 = false ∨ valuationOf q 1475 = false ∨ valuationOf q 1481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause675 (q : Snake 81) (h : Conditions q) : valuation q 1466 = false ∨ valuation q 1475 = false ∨ valuation q 1481 = true := counterClause675 (baseVal q)

theorem counterClause676 (q : Nat → Bool) : valuationOf q 1467 = false ∨ valuationOf q 1472 = false ∨ valuationOf q 1479 = true := by
  have hs : count1476 q = (countLit q [-83, -85, -87]) + (countLit q [-88, -91, -92, -94]) := List.countP_append (p := literal q) (l₁ := [-83, -85, -87]) (l₂ := [-88, -91, -92, -94])
  have hm := merge_two (literal (valuationOf q) (1467)) (literal (valuationOf q) (1472)) (literal (valuationOf q) (1479)) (countLit q [-83, -85, -87]) (countLit q [-88, -91, -92, -94]) (count1476 q) 3 1 (meaning1467 q) (meaning1472 q) (meaning1479 q) hs
  change valuationOf q 1467 = false ∨ valuationOf q 1472 = false ∨ valuationOf q 1479 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause676 (q : Snake 81) (h : Conditions q) : valuation q 1467 = false ∨ valuation q 1472 = false ∨ valuation q 1479 = true := counterClause676 (baseVal q)

theorem counterClause677 (q : Nat → Bool) : valuationOf q 1467 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1481 = true := by
  have hs : count1476 q = (countLit q [-83, -85, -87]) + (countLit q [-88, -91, -92, -94]) := List.countP_append (p := literal q) (l₁ := [-83, -85, -87]) (l₂ := [-88, -91, -92, -94])
  have hm := merge_two (literal (valuationOf q) (1467)) (literal (valuationOf q) (1474)) (literal (valuationOf q) (1481)) (countLit q [-83, -85, -87]) (countLit q [-88, -91, -92, -94]) (count1476 q) 3 3 (meaning1467 q) (meaning1474 q) (meaning1481 q) hs
  change valuationOf q 1467 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause677 (q : Snake 81) (h : Conditions q) : valuation q 1467 = false ∨ valuation q 1474 = false ∨ valuation q 1481 = true := counterClause677 (baseVal q)

theorem counterClause678 (q : Nat → Bool) : valuationOf q 101 = true ∨ valuationOf q 1483 = true := by
  have hs : count1483 q = (countLit q [-99]) + (countLit q [-101]) := List.countP_append (p := literal q) (l₁ := [-99]) (l₂ := [-101])
  have hm := merge_right (literal (valuationOf q) (-101)) (literal (valuationOf q) (1483)) (countLit q [-99]) (countLit q [-101]) (count1483 q) 1 (meaningNeg101 q) (meaning1483 q) hs
  change (! (valuationOf q 101)) = false ∨ valuationOf q 1483 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause678 (q : Snake 81) (h : Conditions q) : valuation q 101 = true ∨ valuation q 1483 = true := counterClause678 (baseVal q)

theorem counterClause679 (q : Nat → Bool) : valuationOf q 99 = true ∨ valuationOf q 1483 = true := by
  have hs : count1483 q = (countLit q [-99]) + (countLit q [-101]) := List.countP_append (p := literal q) (l₁ := [-99]) (l₂ := [-101])
  have hm := merge_left (literal (valuationOf q) (-99)) (literal (valuationOf q) (1483)) (countLit q [-99]) (countLit q [-101]) (count1483 q) 1 (meaningNeg99 q) (meaning1483 q) hs
  change (! (valuationOf q 99)) = false ∨ valuationOf q 1483 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause679 (q : Snake 81) (h : Conditions q) : valuation q 99 = true ∨ valuation q 1483 = true := counterClause679 (baseVal q)

theorem counterClause680 (q : Nat → Bool) : valuationOf q 99 = true ∨ valuationOf q 101 = true ∨ valuationOf q 1484 = true := by
  have hs : count1483 q = (countLit q [-99]) + (countLit q [-101]) := List.countP_append (p := literal q) (l₁ := [-99]) (l₂ := [-101])
  have hm := merge_two (literal (valuationOf q) (-99)) (literal (valuationOf q) (-101)) (literal (valuationOf q) (1484)) (countLit q [-99]) (countLit q [-101]) (count1483 q) 1 1 (meaningNeg99 q) (meaningNeg101 q) (meaning1484 q) hs
  change (! (valuationOf q 99)) = false ∨ (! (valuationOf q 101)) = false ∨ valuationOf q 1484 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause680 (q : Snake 81) (h : Conditions q) : valuation q 99 = true ∨ valuation q 101 = true ∨ valuation q 1484 = true := counterClause680 (baseVal q)

theorem counterClause681 (q : Nat → Bool) : valuationOf q 1483 = false ∨ valuationOf q 1485 = true := by
  have hs : count1485 q = (countLit q [-96]) + (countLit q [-99, -101]) := List.countP_append (p := literal q) (l₁ := [-96]) (l₂ := [-99, -101])
  have hm := merge_right (literal (valuationOf q) (1483)) (literal (valuationOf q) (1485)) (countLit q [-96]) (countLit q [-99, -101]) (count1485 q) 1 (meaning1483 q) (meaning1485 q) hs
  change valuationOf q 1483 = false ∨ valuationOf q 1485 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause681 (q : Snake 81) (h : Conditions q) : valuation q 1483 = false ∨ valuation q 1485 = true := counterClause681 (baseVal q)

theorem counterClause682 (q : Nat → Bool) : valuationOf q 1484 = false ∨ valuationOf q 1486 = true := by
  have hs : count1485 q = (countLit q [-96]) + (countLit q [-99, -101]) := List.countP_append (p := literal q) (l₁ := [-96]) (l₂ := [-99, -101])
  have hm := merge_right (literal (valuationOf q) (1484)) (literal (valuationOf q) (1486)) (countLit q [-96]) (countLit q [-99, -101]) (count1485 q) 2 (meaning1484 q) (meaning1486 q) hs
  change valuationOf q 1484 = false ∨ valuationOf q 1486 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause682 (q : Snake 81) (h : Conditions q) : valuation q 1484 = false ∨ valuation q 1486 = true := counterClause682 (baseVal q)

theorem counterClause683 (q : Nat → Bool) : valuationOf q 96 = true ∨ valuationOf q 1485 = true := by
  have hs : count1485 q = (countLit q [-96]) + (countLit q [-99, -101]) := List.countP_append (p := literal q) (l₁ := [-96]) (l₂ := [-99, -101])
  have hm := merge_left (literal (valuationOf q) (-96)) (literal (valuationOf q) (1485)) (countLit q [-96]) (countLit q [-99, -101]) (count1485 q) 1 (meaningNeg96 q) (meaning1485 q) hs
  change (! (valuationOf q 96)) = false ∨ valuationOf q 1485 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause683 (q : Snake 81) (h : Conditions q) : valuation q 96 = true ∨ valuation q 1485 = true := counterClause683 (baseVal q)

theorem counterClause684 (q : Nat → Bool) : valuationOf q 96 = true ∨ valuationOf q 1483 = false ∨ valuationOf q 1486 = true := by
  have hs : count1485 q = (countLit q [-96]) + (countLit q [-99, -101]) := List.countP_append (p := literal q) (l₁ := [-96]) (l₂ := [-99, -101])
  have hm := merge_two (literal (valuationOf q) (-96)) (literal (valuationOf q) (1483)) (literal (valuationOf q) (1486)) (countLit q [-96]) (countLit q [-99, -101]) (count1485 q) 1 1 (meaningNeg96 q) (meaning1483 q) (meaning1486 q) hs
  change (! (valuationOf q 96)) = false ∨ valuationOf q 1483 = false ∨ valuationOf q 1486 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause684 (q : Snake 81) (h : Conditions q) : valuation q 96 = true ∨ valuation q 1483 = false ∨ valuation q 1486 = true := counterClause684 (baseVal q)

theorem counterClause685 (q : Nat → Bool) : valuationOf q 96 = true ∨ valuationOf q 1484 = false ∨ valuationOf q 1487 = true := by
  have hs : count1485 q = (countLit q [-96]) + (countLit q [-99, -101]) := List.countP_append (p := literal q) (l₁ := [-96]) (l₂ := [-99, -101])
  have hm := merge_two (literal (valuationOf q) (-96)) (literal (valuationOf q) (1484)) (literal (valuationOf q) (1487)) (countLit q [-96]) (countLit q [-99, -101]) (count1485 q) 1 2 (meaningNeg96 q) (meaning1484 q) (meaning1487 q) hs
  change (! (valuationOf q 96)) = false ∨ valuationOf q 1484 = false ∨ valuationOf q 1487 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause685 (q : Snake 81) (h : Conditions q) : valuation q 96 = true ∨ valuation q 1484 = false ∨ valuation q 1487 = true := counterClause685 (baseVal q)

theorem counterClause686 (q : Nat → Bool) : valuationOf q 104 = true ∨ valuationOf q 1488 = true := by
  have hs : count1488 q = (countLit q [-103]) + (countLit q [-104]) := List.countP_append (p := literal q) (l₁ := [-103]) (l₂ := [-104])
  have hm := merge_right (literal (valuationOf q) (-104)) (literal (valuationOf q) (1488)) (countLit q [-103]) (countLit q [-104]) (count1488 q) 1 (meaningNeg104 q) (meaning1488 q) hs
  change (! (valuationOf q 104)) = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause686 (q : Snake 81) (h : Conditions q) : valuation q 104 = true ∨ valuation q 1488 = true := counterClause686 (baseVal q)

theorem counterClause687 (q : Nat → Bool) : valuationOf q 103 = true ∨ valuationOf q 1488 = true := by
  have hs : count1488 q = (countLit q [-103]) + (countLit q [-104]) := List.countP_append (p := literal q) (l₁ := [-103]) (l₂ := [-104])
  have hm := merge_left (literal (valuationOf q) (-103)) (literal (valuationOf q) (1488)) (countLit q [-103]) (countLit q [-104]) (count1488 q) 1 (meaningNeg103 q) (meaning1488 q) hs
  change (! (valuationOf q 103)) = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause687 (q : Snake 81) (h : Conditions q) : valuation q 103 = true ∨ valuation q 1488 = true := counterClause687 (baseVal q)

theorem counterClause688 (q : Nat → Bool) : valuationOf q 108 = true ∨ valuationOf q 1490 = true := by
  have hs : count1490 q = (countLit q [-107]) + (countLit q [-108]) := List.countP_append (p := literal q) (l₁ := [-107]) (l₂ := [-108])
  have hm := merge_right (literal (valuationOf q) (-108)) (literal (valuationOf q) (1490)) (countLit q [-107]) (countLit q [-108]) (count1490 q) 1 (meaningNeg108 q) (meaning1490 q) hs
  change (! (valuationOf q 108)) = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause688 (q : Snake 81) (h : Conditions q) : valuation q 108 = true ∨ valuation q 1490 = true := counterClause688 (baseVal q)

theorem counterClause689 (q : Nat → Bool) : valuationOf q 107 = true ∨ valuationOf q 1490 = true := by
  have hs : count1490 q = (countLit q [-107]) + (countLit q [-108]) := List.countP_append (p := literal q) (l₁ := [-107]) (l₂ := [-108])
  have hm := merge_left (literal (valuationOf q) (-107)) (literal (valuationOf q) (1490)) (countLit q [-107]) (countLit q [-108]) (count1490 q) 1 (meaningNeg107 q) (meaning1490 q) hs
  change (! (valuationOf q 107)) = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause689 (q : Snake 81) (h : Conditions q) : valuation q 107 = true ∨ valuation q 1490 = true := counterClause689 (baseVal q)

theorem counterClause690 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1492 = true := by
  have hs : count1492 q = (countLit q [-103, -104]) + (countLit q [-107, -108]) := List.countP_append (p := literal q) (l₁ := [-103, -104]) (l₂ := [-107, -108])
  have hm := merge_right (literal (valuationOf q) (1490)) (literal (valuationOf q) (1492)) (countLit q [-103, -104]) (countLit q [-107, -108]) (count1492 q) 1 (meaning1490 q) (meaning1492 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause690 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1492 = true := counterClause690 (baseVal q)

theorem counterClause691 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1492 = true := by
  have hs : count1492 q = (countLit q [-103, -104]) + (countLit q [-107, -108]) := List.countP_append (p := literal q) (l₁ := [-103, -104]) (l₂ := [-107, -108])
  have hm := merge_left (literal (valuationOf q) (1488)) (literal (valuationOf q) (1492)) (countLit q [-103, -104]) (countLit q [-107, -108]) (count1492 q) 1 (meaning1488 q) (meaning1492 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause691 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1492 = true := counterClause691 (baseVal q)

theorem counterClause692 (q : Nat → Bool) : valuationOf q 1492 = false ∨ valuationOf q 1496 = true := by
  have hs : count1496 q = (countLit q [-96, -99, -101]) + (countLit q [-103, -104, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -101]) (l₂ := [-103, -104, -107, -108])
  have hm := merge_right (literal (valuationOf q) (1492)) (literal (valuationOf q) (1496)) (countLit q [-96, -99, -101]) (countLit q [-103, -104, -107, -108]) (count1496 q) 1 (meaning1492 q) (meaning1496 q) hs
  change valuationOf q 1492 = false ∨ valuationOf q 1496 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause692 (q : Snake 81) (h : Conditions q) : valuation q 1492 = false ∨ valuation q 1496 = true := counterClause692 (baseVal q)

theorem counterClause693 (q : Nat → Bool) : valuationOf q 1485 = false ∨ valuationOf q 1496 = true := by
  have hs : count1496 q = (countLit q [-96, -99, -101]) + (countLit q [-103, -104, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -101]) (l₂ := [-103, -104, -107, -108])
  have hm := merge_left (literal (valuationOf q) (1485)) (literal (valuationOf q) (1496)) (countLit q [-96, -99, -101]) (countLit q [-103, -104, -107, -108]) (count1496 q) 1 (meaning1485 q) (meaning1496 q) hs
  change valuationOf q 1485 = false ∨ valuationOf q 1496 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause693 (q : Snake 81) (h : Conditions q) : valuation q 1485 = false ∨ valuation q 1496 = true := counterClause693 (baseVal q)

theorem counterClause694 (q : Nat → Bool) : valuationOf q 1485 = false ∨ valuationOf q 1492 = false ∨ valuationOf q 1497 = true := by
  have hs : count1496 q = (countLit q [-96, -99, -101]) + (countLit q [-103, -104, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -101]) (l₂ := [-103, -104, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1485)) (literal (valuationOf q) (1492)) (literal (valuationOf q) (1497)) (countLit q [-96, -99, -101]) (countLit q [-103, -104, -107, -108]) (count1496 q) 1 1 (meaning1485 q) (meaning1492 q) (meaning1497 q) hs
  change valuationOf q 1485 = false ∨ valuationOf q 1492 = false ∨ valuationOf q 1497 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause694 (q : Snake 81) (h : Conditions q) : valuation q 1485 = false ∨ valuation q 1492 = false ∨ valuation q 1497 = true := counterClause694 (baseVal q)

theorem counterClause695 (q : Nat → Bool) : valuationOf q 1486 = false ∨ valuationOf q 1497 = true := by
  have hs : count1496 q = (countLit q [-96, -99, -101]) + (countLit q [-103, -104, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -101]) (l₂ := [-103, -104, -107, -108])
  have hm := merge_left (literal (valuationOf q) (1486)) (literal (valuationOf q) (1497)) (countLit q [-96, -99, -101]) (countLit q [-103, -104, -107, -108]) (count1496 q) 2 (meaning1486 q) (meaning1497 q) hs
  change valuationOf q 1486 = false ∨ valuationOf q 1497 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause695 (q : Snake 81) (h : Conditions q) : valuation q 1486 = false ∨ valuation q 1497 = true := counterClause695 (baseVal q)

theorem counterClause696 (q : Nat → Bool) : valuationOf q 1486 = false ∨ valuationOf q 1492 = false ∨ valuationOf q 1498 = true := by
  have hs : count1496 q = (countLit q [-96, -99, -101]) + (countLit q [-103, -104, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -101]) (l₂ := [-103, -104, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1486)) (literal (valuationOf q) (1492)) (literal (valuationOf q) (1498)) (countLit q [-96, -99, -101]) (countLit q [-103, -104, -107, -108]) (count1496 q) 2 1 (meaning1486 q) (meaning1492 q) (meaning1498 q) hs
  change valuationOf q 1486 = false ∨ valuationOf q 1492 = false ∨ valuationOf q 1498 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause696 (q : Snake 81) (h : Conditions q) : valuation q 1486 = false ∨ valuation q 1492 = false ∨ valuation q 1498 = true := counterClause696 (baseVal q)

theorem counterClause697 (q : Nat → Bool) : valuationOf q 1487 = false ∨ valuationOf q 1498 = true := by
  have hs : count1496 q = (countLit q [-96, -99, -101]) + (countLit q [-103, -104, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -101]) (l₂ := [-103, -104, -107, -108])
  have hm := merge_left (literal (valuationOf q) (1487)) (literal (valuationOf q) (1498)) (countLit q [-96, -99, -101]) (countLit q [-103, -104, -107, -108]) (count1496 q) 3 (meaning1487 q) (meaning1498 q) hs
  change valuationOf q 1487 = false ∨ valuationOf q 1498 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause697 (q : Snake 81) (h : Conditions q) : valuation q 1487 = false ∨ valuation q 1498 = true := counterClause697 (baseVal q)

theorem counterClause698 (q : Nat → Bool) : valuationOf q 1497 = false ∨ valuationOf q 1504 = true := by
  have hs : count1503 q = (countLit q [-83, -85, -87, -88, -91, -92, -94]) + (countLit q [-96, -99, -101, -103, -104, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-83, -85, -87, -88, -91, -92, -94]) (l₂ := [-96, -99, -101, -103, -104, -107, -108])
  have hm := merge_right (literal (valuationOf q) (1497)) (literal (valuationOf q) (1504)) (countLit q [-83, -85, -87, -88, -91, -92, -94]) (countLit q [-96, -99, -101, -103, -104, -107, -108]) (count1503 q) 2 (meaning1497 q) (meaning1504 q) hs
  change valuationOf q 1497 = false ∨ valuationOf q 1504 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause698 (q : Snake 81) (h : Conditions q) : valuation q 1497 = false ∨ valuation q 1504 = true := counterClause698 (baseVal q)

theorem counterClause699 (q : Nat → Bool) : valuationOf q 1476 = false ∨ valuationOf q 1503 = true := by
  have hs : count1503 q = (countLit q [-83, -85, -87, -88, -91, -92, -94]) + (countLit q [-96, -99, -101, -103, -104, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-83, -85, -87, -88, -91, -92, -94]) (l₂ := [-96, -99, -101, -103, -104, -107, -108])
  have hm := merge_left (literal (valuationOf q) (1476)) (literal (valuationOf q) (1503)) (countLit q [-83, -85, -87, -88, -91, -92, -94]) (countLit q [-96, -99, -101, -103, -104, -107, -108]) (count1503 q) 1 (meaning1476 q) (meaning1503 q) hs
  change valuationOf q 1476 = false ∨ valuationOf q 1503 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause699 (q : Snake 81) (h : Conditions q) : valuation q 1476 = false ∨ valuation q 1503 = true := counterClause699 (baseVal q)

theorem counterClause700 (q : Nat → Bool) : valuationOf q 1476 = false ∨ valuationOf q 1496 = false ∨ valuationOf q 1504 = true := by
  have hs : count1503 q = (countLit q [-83, -85, -87, -88, -91, -92, -94]) + (countLit q [-96, -99, -101, -103, -104, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-83, -85, -87, -88, -91, -92, -94]) (l₂ := [-96, -99, -101, -103, -104, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1476)) (literal (valuationOf q) (1496)) (literal (valuationOf q) (1504)) (countLit q [-83, -85, -87, -88, -91, -92, -94]) (countLit q [-96, -99, -101, -103, -104, -107, -108]) (count1503 q) 1 1 (meaning1476 q) (meaning1496 q) (meaning1504 q) hs
  change valuationOf q 1476 = false ∨ valuationOf q 1496 = false ∨ valuationOf q 1504 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause700 (q : Snake 81) (h : Conditions q) : valuation q 1476 = false ∨ valuation q 1496 = false ∨ valuation q 1504 = true := counterClause700 (baseVal q)

theorem counterClause701 (q : Nat → Bool) : valuationOf q 1476 = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1505 = true := by
  have hs : count1503 q = (countLit q [-83, -85, -87, -88, -91, -92, -94]) + (countLit q [-96, -99, -101, -103, -104, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-83, -85, -87, -88, -91, -92, -94]) (l₂ := [-96, -99, -101, -103, -104, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1476)) (literal (valuationOf q) (1497)) (literal (valuationOf q) (1505)) (countLit q [-83, -85, -87, -88, -91, -92, -94]) (countLit q [-96, -99, -101, -103, -104, -107, -108]) (count1503 q) 1 2 (meaning1476 q) (meaning1497 q) (meaning1505 q) hs
  change valuationOf q 1476 = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1505 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause701 (q : Snake 81) (h : Conditions q) : valuation q 1476 = false ∨ valuation q 1497 = false ∨ valuation q 1505 = true := counterClause701 (baseVal q)

theorem counterClause702 (q : Nat → Bool) : valuationOf q 1476 = false ∨ valuationOf q 1498 = false ∨ valuationOf q 1506 = true := by
  have hs : count1503 q = (countLit q [-83, -85, -87, -88, -91, -92, -94]) + (countLit q [-96, -99, -101, -103, -104, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-83, -85, -87, -88, -91, -92, -94]) (l₂ := [-96, -99, -101, -103, -104, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1476)) (literal (valuationOf q) (1498)) (literal (valuationOf q) (1506)) (countLit q [-83, -85, -87, -88, -91, -92, -94]) (countLit q [-96, -99, -101, -103, -104, -107, -108]) (count1503 q) 1 3 (meaning1476 q) (meaning1498 q) (meaning1506 q) hs
  change valuationOf q 1476 = false ∨ valuationOf q 1498 = false ∨ valuationOf q 1506 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause702 (q : Snake 81) (h : Conditions q) : valuation q 1476 = false ∨ valuation q 1498 = false ∨ valuation q 1506 = true := counterClause702 (baseVal q)

theorem counterClause703 (q : Nat → Bool) : valuationOf q 1477 = false ∨ valuationOf q 1504 = true := by
  have hs : count1503 q = (countLit q [-83, -85, -87, -88, -91, -92, -94]) + (countLit q [-96, -99, -101, -103, -104, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-83, -85, -87, -88, -91, -92, -94]) (l₂ := [-96, -99, -101, -103, -104, -107, -108])
  have hm := merge_left (literal (valuationOf q) (1477)) (literal (valuationOf q) (1504)) (countLit q [-83, -85, -87, -88, -91, -92, -94]) (countLit q [-96, -99, -101, -103, -104, -107, -108]) (count1503 q) 2 (meaning1477 q) (meaning1504 q) hs
  change valuationOf q 1477 = false ∨ valuationOf q 1504 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause703 (q : Snake 81) (h : Conditions q) : valuation q 1477 = false ∨ valuation q 1504 = true := counterClause703 (baseVal q)

theorem counterClause704 (q : Nat → Bool) : valuationOf q 1477 = false ∨ valuationOf q 1496 = false ∨ valuationOf q 1505 = true := by
  have hs : count1503 q = (countLit q [-83, -85, -87, -88, -91, -92, -94]) + (countLit q [-96, -99, -101, -103, -104, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-83, -85, -87, -88, -91, -92, -94]) (l₂ := [-96, -99, -101, -103, -104, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1477)) (literal (valuationOf q) (1496)) (literal (valuationOf q) (1505)) (countLit q [-83, -85, -87, -88, -91, -92, -94]) (countLit q [-96, -99, -101, -103, -104, -107, -108]) (count1503 q) 2 1 (meaning1477 q) (meaning1496 q) (meaning1505 q) hs
  change valuationOf q 1477 = false ∨ valuationOf q 1496 = false ∨ valuationOf q 1505 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause704 (q : Snake 81) (h : Conditions q) : valuation q 1477 = false ∨ valuation q 1496 = false ∨ valuation q 1505 = true := counterClause704 (baseVal q)

theorem block21 (q : Snake 81) (h : Conditions q) : B112E090.Block21 (valuation q) :=
  ⟨clause673 q h, clause674 q h, clause675 q h, clause676 q h, clause677 q h, clause678 q h, clause679 q h, clause680 q h, clause681 q h, clause682 q h, clause683 q h, clause684 q h, clause685 q h, clause686 q h, clause687 q h, clause688 q h, clause689 q h, clause690 q h, clause691 q h, clause692 q h, clause693 q h, clause694 q h, clause695 q h, clause696 q h, clause697 q h, clause698 q h, clause699 q h, clause700 q h, clause701 q h, clause702 q h, clause703 q h, clause704 q h⟩

end
end Snake9.Regrowth.E112090
