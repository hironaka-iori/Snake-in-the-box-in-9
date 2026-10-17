import E112110Semantics
import B112E110Inputs
namespace Snake9.Regrowth.E112110
noncomputable section
local instance blockDec28 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause897 (q : Nat → Bool) : valuationOf q 1483 = false ∨ valuationOf q 1487 = true := by
  have hs : count1485 q = (countLit q [-30, -32, -35]) + (countLit q [-37, -38, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -35]) (l₂ := [-37, -38, -40, -42])
  have hm := merge_right (literal (valuationOf q) (1483)) (literal (valuationOf q) (1487)) (countLit q [-30, -32, -35]) (countLit q [-37, -38, -40, -42]) (count1485 q) 3 (meaning1483 q) (meaning1487 q) hs
  change valuationOf q 1483 = false ∨ valuationOf q 1487 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause897 (q : Snake 81) (h : Conditions q) : valuation q 1483 = false ∨ valuation q 1487 = true := counterClause897 (baseVal q)

theorem counterClause898 (q : Nat → Bool) : valuationOf q 1484 = false ∨ valuationOf q 1488 = true := by
  have hs : count1485 q = (countLit q [-30, -32, -35]) + (countLit q [-37, -38, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -35]) (l₂ := [-37, -38, -40, -42])
  have hm := merge_right (literal (valuationOf q) (1484)) (literal (valuationOf q) (1488)) (countLit q [-30, -32, -35]) (countLit q [-37, -38, -40, -42]) (count1485 q) 4 (meaning1484 q) (meaning1488 q) hs
  change valuationOf q 1484 = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause898 (q : Snake 81) (h : Conditions q) : valuation q 1484 = false ∨ valuation q 1488 = true := counterClause898 (baseVal q)

theorem counterClause899 (q : Nat → Bool) : valuationOf q 1474 = false ∨ valuationOf q 1485 = true := by
  have hs : count1485 q = (countLit q [-30, -32, -35]) + (countLit q [-37, -38, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -35]) (l₂ := [-37, -38, -40, -42])
  have hm := merge_left (literal (valuationOf q) (1474)) (literal (valuationOf q) (1485)) (countLit q [-30, -32, -35]) (countLit q [-37, -38, -40, -42]) (count1485 q) 1 (meaning1474 q) (meaning1485 q) hs
  change valuationOf q 1474 = false ∨ valuationOf q 1485 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause899 (q : Snake 81) (h : Conditions q) : valuation q 1474 = false ∨ valuation q 1485 = true := counterClause899 (baseVal q)

theorem counterClause900 (q : Nat → Bool) : valuationOf q 1474 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1486 = true := by
  have hs : count1485 q = (countLit q [-30, -32, -35]) + (countLit q [-37, -38, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -35]) (l₂ := [-37, -38, -40, -42])
  have hm := merge_two (literal (valuationOf q) (1474)) (literal (valuationOf q) (1481)) (literal (valuationOf q) (1486)) (countLit q [-30, -32, -35]) (countLit q [-37, -38, -40, -42]) (count1485 q) 1 1 (meaning1474 q) (meaning1481 q) (meaning1486 q) hs
  change valuationOf q 1474 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1486 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause900 (q : Snake 81) (h : Conditions q) : valuation q 1474 = false ∨ valuation q 1481 = false ∨ valuation q 1486 = true := counterClause900 (baseVal q)

theorem counterClause901 (q : Nat → Bool) : valuationOf q 1474 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1487 = true := by
  have hs : count1485 q = (countLit q [-30, -32, -35]) + (countLit q [-37, -38, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -35]) (l₂ := [-37, -38, -40, -42])
  have hm := merge_two (literal (valuationOf q) (1474)) (literal (valuationOf q) (1482)) (literal (valuationOf q) (1487)) (countLit q [-30, -32, -35]) (countLit q [-37, -38, -40, -42]) (count1485 q) 1 2 (meaning1474 q) (meaning1482 q) (meaning1487 q) hs
  change valuationOf q 1474 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1487 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause901 (q : Snake 81) (h : Conditions q) : valuation q 1474 = false ∨ valuation q 1482 = false ∨ valuation q 1487 = true := counterClause901 (baseVal q)

theorem counterClause902 (q : Nat → Bool) : valuationOf q 1474 = false ∨ valuationOf q 1483 = false ∨ valuationOf q 1488 = true := by
  have hs : count1485 q = (countLit q [-30, -32, -35]) + (countLit q [-37, -38, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -35]) (l₂ := [-37, -38, -40, -42])
  have hm := merge_two (literal (valuationOf q) (1474)) (literal (valuationOf q) (1483)) (literal (valuationOf q) (1488)) (countLit q [-30, -32, -35]) (countLit q [-37, -38, -40, -42]) (count1485 q) 1 3 (meaning1474 q) (meaning1483 q) (meaning1488 q) hs
  change valuationOf q 1474 = false ∨ valuationOf q 1483 = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause902 (q : Snake 81) (h : Conditions q) : valuation q 1474 = false ∨ valuation q 1483 = false ∨ valuation q 1488 = true := counterClause902 (baseVal q)

theorem counterClause903 (q : Nat → Bool) : valuationOf q 1474 = false ∨ valuationOf q 1484 = false ∨ valuationOf q 1489 = true := by
  have hs : count1485 q = (countLit q [-30, -32, -35]) + (countLit q [-37, -38, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -35]) (l₂ := [-37, -38, -40, -42])
  have hm := merge_two (literal (valuationOf q) (1474)) (literal (valuationOf q) (1484)) (literal (valuationOf q) (1489)) (countLit q [-30, -32, -35]) (countLit q [-37, -38, -40, -42]) (count1485 q) 1 4 (meaning1474 q) (meaning1484 q) (meaning1489 q) hs
  change valuationOf q 1474 = false ∨ valuationOf q 1484 = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause903 (q : Snake 81) (h : Conditions q) : valuation q 1474 = false ∨ valuation q 1484 = false ∨ valuation q 1489 = true := counterClause903 (baseVal q)

theorem counterClause904 (q : Nat → Bool) : valuationOf q 1475 = false ∨ valuationOf q 1486 = true := by
  have hs : count1485 q = (countLit q [-30, -32, -35]) + (countLit q [-37, -38, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -35]) (l₂ := [-37, -38, -40, -42])
  have hm := merge_left (literal (valuationOf q) (1475)) (literal (valuationOf q) (1486)) (countLit q [-30, -32, -35]) (countLit q [-37, -38, -40, -42]) (count1485 q) 2 (meaning1475 q) (meaning1486 q) hs
  change valuationOf q 1475 = false ∨ valuationOf q 1486 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause904 (q : Snake 81) (h : Conditions q) : valuation q 1475 = false ∨ valuation q 1486 = true := counterClause904 (baseVal q)

theorem counterClause905 (q : Nat → Bool) : valuationOf q 1475 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1487 = true := by
  have hs : count1485 q = (countLit q [-30, -32, -35]) + (countLit q [-37, -38, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -35]) (l₂ := [-37, -38, -40, -42])
  have hm := merge_two (literal (valuationOf q) (1475)) (literal (valuationOf q) (1481)) (literal (valuationOf q) (1487)) (countLit q [-30, -32, -35]) (countLit q [-37, -38, -40, -42]) (count1485 q) 2 1 (meaning1475 q) (meaning1481 q) (meaning1487 q) hs
  change valuationOf q 1475 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1487 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause905 (q : Snake 81) (h : Conditions q) : valuation q 1475 = false ∨ valuation q 1481 = false ∨ valuation q 1487 = true := counterClause905 (baseVal q)

theorem counterClause906 (q : Nat → Bool) : valuationOf q 1475 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1488 = true := by
  have hs : count1485 q = (countLit q [-30, -32, -35]) + (countLit q [-37, -38, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -35]) (l₂ := [-37, -38, -40, -42])
  have hm := merge_two (literal (valuationOf q) (1475)) (literal (valuationOf q) (1482)) (literal (valuationOf q) (1488)) (countLit q [-30, -32, -35]) (countLit q [-37, -38, -40, -42]) (count1485 q) 2 2 (meaning1475 q) (meaning1482 q) (meaning1488 q) hs
  change valuationOf q 1475 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause906 (q : Snake 81) (h : Conditions q) : valuation q 1475 = false ∨ valuation q 1482 = false ∨ valuation q 1488 = true := counterClause906 (baseVal q)

theorem counterClause907 (q : Nat → Bool) : valuationOf q 1475 = false ∨ valuationOf q 1483 = false ∨ valuationOf q 1489 = true := by
  have hs : count1485 q = (countLit q [-30, -32, -35]) + (countLit q [-37, -38, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -35]) (l₂ := [-37, -38, -40, -42])
  have hm := merge_two (literal (valuationOf q) (1475)) (literal (valuationOf q) (1483)) (literal (valuationOf q) (1489)) (countLit q [-30, -32, -35]) (countLit q [-37, -38, -40, -42]) (count1485 q) 2 3 (meaning1475 q) (meaning1483 q) (meaning1489 q) hs
  change valuationOf q 1475 = false ∨ valuationOf q 1483 = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause907 (q : Snake 81) (h : Conditions q) : valuation q 1475 = false ∨ valuation q 1483 = false ∨ valuation q 1489 = true := counterClause907 (baseVal q)

theorem counterClause908 (q : Nat → Bool) : valuationOf q 1476 = false ∨ valuationOf q 1487 = true := by
  have hs : count1485 q = (countLit q [-30, -32, -35]) + (countLit q [-37, -38, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -35]) (l₂ := [-37, -38, -40, -42])
  have hm := merge_left (literal (valuationOf q) (1476)) (literal (valuationOf q) (1487)) (countLit q [-30, -32, -35]) (countLit q [-37, -38, -40, -42]) (count1485 q) 3 (meaning1476 q) (meaning1487 q) hs
  change valuationOf q 1476 = false ∨ valuationOf q 1487 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause908 (q : Snake 81) (h : Conditions q) : valuation q 1476 = false ∨ valuation q 1487 = true := counterClause908 (baseVal q)

theorem counterClause909 (q : Nat → Bool) : valuationOf q 1476 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1488 = true := by
  have hs : count1485 q = (countLit q [-30, -32, -35]) + (countLit q [-37, -38, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -35]) (l₂ := [-37, -38, -40, -42])
  have hm := merge_two (literal (valuationOf q) (1476)) (literal (valuationOf q) (1481)) (literal (valuationOf q) (1488)) (countLit q [-30, -32, -35]) (countLit q [-37, -38, -40, -42]) (count1485 q) 3 1 (meaning1476 q) (meaning1481 q) (meaning1488 q) hs
  change valuationOf q 1476 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause909 (q : Snake 81) (h : Conditions q) : valuation q 1476 = false ∨ valuation q 1481 = false ∨ valuation q 1488 = true := counterClause909 (baseVal q)

theorem counterClause910 (q : Nat → Bool) : valuationOf q 46 = true ∨ valuationOf q 1492 = true := by
  have hs : count1492 q = (countLit q [-45]) + (countLit q [-46]) := List.countP_append (p := literal q) (l₁ := [-45]) (l₂ := [-46])
  have hm := merge_right (literal (valuationOf q) (-46)) (literal (valuationOf q) (1492)) (countLit q [-45]) (countLit q [-46]) (count1492 q) 1 (meaningNeg46 q) (meaning1492 q) hs
  change (! (valuationOf q 46)) = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause910 (q : Snake 81) (h : Conditions q) : valuation q 46 = true ∨ valuation q 1492 = true := counterClause910 (baseVal q)

theorem counterClause911 (q : Nat → Bool) : valuationOf q 45 = true ∨ valuationOf q 1492 = true := by
  have hs : count1492 q = (countLit q [-45]) + (countLit q [-46]) := List.countP_append (p := literal q) (l₁ := [-45]) (l₂ := [-46])
  have hm := merge_left (literal (valuationOf q) (-45)) (literal (valuationOf q) (1492)) (countLit q [-45]) (countLit q [-46]) (count1492 q) 1 (meaningNeg45 q) (meaning1492 q) hs
  change (! (valuationOf q 45)) = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause911 (q : Snake 81) (h : Conditions q) : valuation q 45 = true ∨ valuation q 1492 = true := counterClause911 (baseVal q)

theorem counterClause912 (q : Nat → Bool) : valuationOf q 45 = true ∨ valuationOf q 46 = true ∨ valuationOf q 1493 = true := by
  have hs : count1492 q = (countLit q [-45]) + (countLit q [-46]) := List.countP_append (p := literal q) (l₁ := [-45]) (l₂ := [-46])
  have hm := merge_two (literal (valuationOf q) (-45)) (literal (valuationOf q) (-46)) (literal (valuationOf q) (1493)) (countLit q [-45]) (countLit q [-46]) (count1492 q) 1 1 (meaningNeg45 q) (meaningNeg46 q) (meaning1493 q) hs
  change (! (valuationOf q 45)) = false ∨ (! (valuationOf q 46)) = false ∨ valuationOf q 1493 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause912 (q : Snake 81) (h : Conditions q) : valuation q 45 = true ∨ valuation q 46 = true ∨ valuation q 1493 = true := counterClause912 (baseVal q)

theorem counterClause913 (q : Nat → Bool) : valuationOf q 49 = true ∨ valuationOf q 1494 = true := by
  have hs : count1494 q = (countLit q [-48]) + (countLit q [-49]) := List.countP_append (p := literal q) (l₁ := [-48]) (l₂ := [-49])
  have hm := merge_right (literal (valuationOf q) (-49)) (literal (valuationOf q) (1494)) (countLit q [-48]) (countLit q [-49]) (count1494 q) 1 (meaningNeg49 q) (meaning1494 q) hs
  change (! (valuationOf q 49)) = false ∨ valuationOf q 1494 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause913 (q : Snake 81) (h : Conditions q) : valuation q 49 = true ∨ valuation q 1494 = true := counterClause913 (baseVal q)

theorem counterClause914 (q : Nat → Bool) : valuationOf q 48 = true ∨ valuationOf q 1494 = true := by
  have hs : count1494 q = (countLit q [-48]) + (countLit q [-49]) := List.countP_append (p := literal q) (l₁ := [-48]) (l₂ := [-49])
  have hm := merge_left (literal (valuationOf q) (-48)) (literal (valuationOf q) (1494)) (countLit q [-48]) (countLit q [-49]) (count1494 q) 1 (meaningNeg48 q) (meaning1494 q) hs
  change (! (valuationOf q 48)) = false ∨ valuationOf q 1494 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause914 (q : Snake 81) (h : Conditions q) : valuation q 48 = true ∨ valuation q 1494 = true := counterClause914 (baseVal q)

theorem counterClause915 (q : Nat → Bool) : valuationOf q 48 = true ∨ valuationOf q 49 = true ∨ valuationOf q 1495 = true := by
  have hs : count1494 q = (countLit q [-48]) + (countLit q [-49]) := List.countP_append (p := literal q) (l₁ := [-48]) (l₂ := [-49])
  have hm := merge_two (literal (valuationOf q) (-48)) (literal (valuationOf q) (-49)) (literal (valuationOf q) (1495)) (countLit q [-48]) (countLit q [-49]) (count1494 q) 1 1 (meaningNeg48 q) (meaningNeg49 q) (meaning1495 q) hs
  change (! (valuationOf q 48)) = false ∨ (! (valuationOf q 49)) = false ∨ valuationOf q 1495 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause915 (q : Snake 81) (h : Conditions q) : valuation q 48 = true ∨ valuation q 49 = true ∨ valuation q 1495 = true := counterClause915 (baseVal q)

theorem counterClause916 (q : Nat → Bool) : valuationOf q 1494 = false ∨ valuationOf q 1496 = true := by
  have hs : count1496 q = (countLit q [-45, -46]) + (countLit q [-48, -49]) := List.countP_append (p := literal q) (l₁ := [-45, -46]) (l₂ := [-48, -49])
  have hm := merge_right (literal (valuationOf q) (1494)) (literal (valuationOf q) (1496)) (countLit q [-45, -46]) (countLit q [-48, -49]) (count1496 q) 1 (meaning1494 q) (meaning1496 q) hs
  change valuationOf q 1494 = false ∨ valuationOf q 1496 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause916 (q : Snake 81) (h : Conditions q) : valuation q 1494 = false ∨ valuation q 1496 = true := counterClause916 (baseVal q)

theorem counterClause917 (q : Nat → Bool) : valuationOf q 1495 = false ∨ valuationOf q 1497 = true := by
  have hs : count1496 q = (countLit q [-45, -46]) + (countLit q [-48, -49]) := List.countP_append (p := literal q) (l₁ := [-45, -46]) (l₂ := [-48, -49])
  have hm := merge_right (literal (valuationOf q) (1495)) (literal (valuationOf q) (1497)) (countLit q [-45, -46]) (countLit q [-48, -49]) (count1496 q) 2 (meaning1495 q) (meaning1497 q) hs
  change valuationOf q 1495 = false ∨ valuationOf q 1497 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause917 (q : Snake 81) (h : Conditions q) : valuation q 1495 = false ∨ valuation q 1497 = true := counterClause917 (baseVal q)

theorem counterClause918 (q : Nat → Bool) : valuationOf q 1492 = false ∨ valuationOf q 1496 = true := by
  have hs : count1496 q = (countLit q [-45, -46]) + (countLit q [-48, -49]) := List.countP_append (p := literal q) (l₁ := [-45, -46]) (l₂ := [-48, -49])
  have hm := merge_left (literal (valuationOf q) (1492)) (literal (valuationOf q) (1496)) (countLit q [-45, -46]) (countLit q [-48, -49]) (count1496 q) 1 (meaning1492 q) (meaning1496 q) hs
  change valuationOf q 1492 = false ∨ valuationOf q 1496 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause918 (q : Snake 81) (h : Conditions q) : valuation q 1492 = false ∨ valuation q 1496 = true := counterClause918 (baseVal q)

theorem counterClause919 (q : Nat → Bool) : valuationOf q 1492 = false ∨ valuationOf q 1494 = false ∨ valuationOf q 1497 = true := by
  have hs : count1496 q = (countLit q [-45, -46]) + (countLit q [-48, -49]) := List.countP_append (p := literal q) (l₁ := [-45, -46]) (l₂ := [-48, -49])
  have hm := merge_two (literal (valuationOf q) (1492)) (literal (valuationOf q) (1494)) (literal (valuationOf q) (1497)) (countLit q [-45, -46]) (countLit q [-48, -49]) (count1496 q) 1 1 (meaning1492 q) (meaning1494 q) (meaning1497 q) hs
  change valuationOf q 1492 = false ∨ valuationOf q 1494 = false ∨ valuationOf q 1497 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause919 (q : Snake 81) (h : Conditions q) : valuation q 1492 = false ∨ valuation q 1494 = false ∨ valuation q 1497 = true := counterClause919 (baseVal q)

theorem counterClause920 (q : Nat → Bool) : valuationOf q 1492 = false ∨ valuationOf q 1495 = false ∨ valuationOf q 1498 = true := by
  have hs : count1496 q = (countLit q [-45, -46]) + (countLit q [-48, -49]) := List.countP_append (p := literal q) (l₁ := [-45, -46]) (l₂ := [-48, -49])
  have hm := merge_two (literal (valuationOf q) (1492)) (literal (valuationOf q) (1495)) (literal (valuationOf q) (1498)) (countLit q [-45, -46]) (countLit q [-48, -49]) (count1496 q) 1 2 (meaning1492 q) (meaning1495 q) (meaning1498 q) hs
  change valuationOf q 1492 = false ∨ valuationOf q 1495 = false ∨ valuationOf q 1498 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause920 (q : Snake 81) (h : Conditions q) : valuation q 1492 = false ∨ valuation q 1495 = false ∨ valuation q 1498 = true := counterClause920 (baseVal q)

theorem counterClause921 (q : Nat → Bool) : valuationOf q 1493 = false ∨ valuationOf q 1497 = true := by
  have hs : count1496 q = (countLit q [-45, -46]) + (countLit q [-48, -49]) := List.countP_append (p := literal q) (l₁ := [-45, -46]) (l₂ := [-48, -49])
  have hm := merge_left (literal (valuationOf q) (1493)) (literal (valuationOf q) (1497)) (countLit q [-45, -46]) (countLit q [-48, -49]) (count1496 q) 2 (meaning1493 q) (meaning1497 q) hs
  change valuationOf q 1493 = false ∨ valuationOf q 1497 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause921 (q : Snake 81) (h : Conditions q) : valuation q 1493 = false ∨ valuation q 1497 = true := counterClause921 (baseVal q)

theorem counterClause922 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 1500 = true := by
  have hs : count1500 q = (countLit q [-52]) + (countLit q [-54]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-54])
  have hm := merge_left (literal (valuationOf q) (-52)) (literal (valuationOf q) (1500)) (countLit q [-52]) (countLit q [-54]) (count1500 q) 1 (meaningNeg52 q) (meaning1500 q) hs
  change (! (valuationOf q 52)) = false ∨ valuationOf q 1500 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause922 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 1500 = true := counterClause922 (baseVal q)

theorem counterClause923 (q : Nat → Bool) : valuationOf q 58 = true ∨ valuationOf q 1502 = true := by
  have hs : count1502 q = (countLit q [-55]) + (countLit q [-58]) := List.countP_append (p := literal q) (l₁ := [-55]) (l₂ := [-58])
  have hm := merge_right (literal (valuationOf q) (-58)) (literal (valuationOf q) (1502)) (countLit q [-55]) (countLit q [-58]) (count1502 q) 1 (meaningNeg58 q) (meaning1502 q) hs
  change (! (valuationOf q 58)) = false ∨ valuationOf q 1502 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause923 (q : Snake 81) (h : Conditions q) : valuation q 58 = true ∨ valuation q 1502 = true := counterClause923 (baseVal q)

theorem counterClause924 (q : Nat → Bool) : valuationOf q 1502 = false ∨ valuationOf q 1504 = true := by
  have hs : count1504 q = (countLit q [-52, -54]) + (countLit q [-55, -58]) := List.countP_append (p := literal q) (l₁ := [-52, -54]) (l₂ := [-55, -58])
  have hm := merge_right (literal (valuationOf q) (1502)) (literal (valuationOf q) (1504)) (countLit q [-52, -54]) (countLit q [-55, -58]) (count1504 q) 1 (meaning1502 q) (meaning1504 q) hs
  change valuationOf q 1502 = false ∨ valuationOf q 1504 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause924 (q : Snake 81) (h : Conditions q) : valuation q 1502 = false ∨ valuation q 1504 = true := counterClause924 (baseVal q)

theorem counterClause925 (q : Nat → Bool) : valuationOf q 1500 = false ∨ valuationOf q 1504 = true := by
  have hs : count1504 q = (countLit q [-52, -54]) + (countLit q [-55, -58]) := List.countP_append (p := literal q) (l₁ := [-52, -54]) (l₂ := [-55, -58])
  have hm := merge_left (literal (valuationOf q) (1500)) (literal (valuationOf q) (1504)) (countLit q [-52, -54]) (countLit q [-55, -58]) (count1504 q) 1 (meaning1500 q) (meaning1504 q) hs
  change valuationOf q 1500 = false ∨ valuationOf q 1504 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause925 (q : Snake 81) (h : Conditions q) : valuation q 1500 = false ∨ valuation q 1504 = true := counterClause925 (baseVal q)

theorem counterClause926 (q : Nat → Bool) : valuationOf q 1500 = false ∨ valuationOf q 1502 = false ∨ valuationOf q 1505 = true := by
  have hs : count1504 q = (countLit q [-52, -54]) + (countLit q [-55, -58]) := List.countP_append (p := literal q) (l₁ := [-52, -54]) (l₂ := [-55, -58])
  have hm := merge_two (literal (valuationOf q) (1500)) (literal (valuationOf q) (1502)) (literal (valuationOf q) (1505)) (countLit q [-52, -54]) (countLit q [-55, -58]) (count1504 q) 1 1 (meaning1500 q) (meaning1502 q) (meaning1505 q) hs
  change valuationOf q 1500 = false ∨ valuationOf q 1502 = false ∨ valuationOf q 1505 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause926 (q : Snake 81) (h : Conditions q) : valuation q 1500 = false ∨ valuation q 1502 = false ∨ valuation q 1505 = true := counterClause926 (baseVal q)

theorem counterClause927 (q : Nat → Bool) : valuationOf q 1504 = false ∨ valuationOf q 1508 = true := by
  have hs : count1508 q = (countLit q [-45, -46, -48, -49]) + (countLit q [-52, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-45, -46, -48, -49]) (l₂ := [-52, -54, -55, -58])
  have hm := merge_right (literal (valuationOf q) (1504)) (literal (valuationOf q) (1508)) (countLit q [-45, -46, -48, -49]) (countLit q [-52, -54, -55, -58]) (count1508 q) 1 (meaning1504 q) (meaning1508 q) hs
  change valuationOf q 1504 = false ∨ valuationOf q 1508 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause927 (q : Snake 81) (h : Conditions q) : valuation q 1504 = false ∨ valuation q 1508 = true := counterClause927 (baseVal q)

theorem counterClause928 (q : Nat → Bool) : valuationOf q 1505 = false ∨ valuationOf q 1509 = true := by
  have hs : count1508 q = (countLit q [-45, -46, -48, -49]) + (countLit q [-52, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-45, -46, -48, -49]) (l₂ := [-52, -54, -55, -58])
  have hm := merge_right (literal (valuationOf q) (1505)) (literal (valuationOf q) (1509)) (countLit q [-45, -46, -48, -49]) (countLit q [-52, -54, -55, -58]) (count1508 q) 2 (meaning1505 q) (meaning1509 q) hs
  change valuationOf q 1505 = false ∨ valuationOf q 1509 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause928 (q : Snake 81) (h : Conditions q) : valuation q 1505 = false ∨ valuation q 1509 = true := counterClause928 (baseVal q)

theorem block28 (q : Snake 81) (h : Conditions q) : B112E110.Block28 (valuation q) :=
  ⟨clause897 q h, clause898 q h, clause899 q h, clause900 q h, clause901 q h, clause902 q h, clause903 q h, clause904 q h, clause905 q h, clause906 q h, clause907 q h, clause908 q h, clause909 q h, clause910 q h, clause911 q h, clause912 q h, clause913 q h, clause914 q h, clause915 q h, clause916 q h, clause917 q h, clause918 q h, clause919 q h, clause920 q h, clause921 q h, clause922 q h, clause923 q h, clause924 q h, clause925 q h, clause926 q h, clause927 q h, clause928 q h⟩

end
end Snake9.Regrowth.E112110
