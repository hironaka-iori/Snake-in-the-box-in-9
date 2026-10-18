import E112104Semantics
import B112E104Inputs
namespace Snake9.Regrowth.E112104
noncomputable section
local instance blockDec27 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause865 (q : Nat → Bool) : valuationOf q 1505 = false ∨ valuationOf q 1509 = true := by
  have hs : count1508 q = (countLit q [-44, -45, -48, -49]) + (countLit q [-50, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-44, -45, -48, -49]) (l₂ := [-50, -52, -55, -56])
  have hm := merge_right (literal (valuationOf q) (1505)) (literal (valuationOf q) (1509)) (countLit q [-44, -45, -48, -49]) (countLit q [-50, -52, -55, -56]) (count1508 q) 2 (meaning1505 q) (meaning1509 q) hs
  change valuationOf q 1505 = false ∨ valuationOf q 1509 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause865 (q : Snake 81) (h : Conditions q) : valuation q 1505 = false ∨ valuation q 1509 = true := counterClause865 (baseVal q)

theorem counterClause866 (q : Nat → Bool) : valuationOf q 1496 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1509 = true := by
  have hs : count1508 q = (countLit q [-44, -45, -48, -49]) + (countLit q [-50, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-44, -45, -48, -49]) (l₂ := [-50, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1496)) (literal (valuationOf q) (1504)) (literal (valuationOf q) (1509)) (countLit q [-44, -45, -48, -49]) (countLit q [-50, -52, -55, -56]) (count1508 q) 1 1 (meaning1496 q) (meaning1504 q) (meaning1509 q) hs
  change valuationOf q 1496 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1509 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause866 (q : Snake 81) (h : Conditions q) : valuation q 1496 = false ∨ valuation q 1504 = false ∨ valuation q 1509 = true := counterClause866 (baseVal q)

theorem counterClause867 (q : Nat → Bool) : valuationOf q 1496 = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1510 = true := by
  have hs : count1508 q = (countLit q [-44, -45, -48, -49]) + (countLit q [-50, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-44, -45, -48, -49]) (l₂ := [-50, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1496)) (literal (valuationOf q) (1505)) (literal (valuationOf q) (1510)) (countLit q [-44, -45, -48, -49]) (countLit q [-50, -52, -55, -56]) (count1508 q) 1 2 (meaning1496 q) (meaning1505 q) (meaning1510 q) hs
  change valuationOf q 1496 = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1510 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause867 (q : Snake 81) (h : Conditions q) : valuation q 1496 = false ∨ valuation q 1505 = false ∨ valuation q 1510 = true := counterClause867 (baseVal q)

theorem counterClause868 (q : Nat → Bool) : valuationOf q 1497 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1510 = true := by
  have hs : count1508 q = (countLit q [-44, -45, -48, -49]) + (countLit q [-50, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-44, -45, -48, -49]) (l₂ := [-50, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1497)) (literal (valuationOf q) (1504)) (literal (valuationOf q) (1510)) (countLit q [-44, -45, -48, -49]) (countLit q [-50, -52, -55, -56]) (count1508 q) 2 1 (meaning1497 q) (meaning1504 q) (meaning1510 q) hs
  change valuationOf q 1497 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1510 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause868 (q : Snake 81) (h : Conditions q) : valuation q 1497 = false ∨ valuation q 1504 = false ∨ valuation q 1510 = true := counterClause868 (baseVal q)

theorem counterClause869 (q : Nat → Bool) : valuationOf q 1497 = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1511 = true := by
  have hs : count1508 q = (countLit q [-44, -45, -48, -49]) + (countLit q [-50, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-44, -45, -48, -49]) (l₂ := [-50, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1497)) (literal (valuationOf q) (1505)) (literal (valuationOf q) (1511)) (countLit q [-44, -45, -48, -49]) (countLit q [-50, -52, -55, -56]) (count1508 q) 2 2 (meaning1497 q) (meaning1505 q) (meaning1511 q) hs
  change valuationOf q 1497 = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1511 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause869 (q : Snake 81) (h : Conditions q) : valuation q 1497 = false ∨ valuation q 1505 = false ∨ valuation q 1511 = true := counterClause869 (baseVal q)

theorem counterClause870 (q : Nat → Bool) : valuationOf q 1498 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1511 = true := by
  have hs : count1508 q = (countLit q [-44, -45, -48, -49]) + (countLit q [-50, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-44, -45, -48, -49]) (l₂ := [-50, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1498)) (literal (valuationOf q) (1504)) (literal (valuationOf q) (1511)) (countLit q [-44, -45, -48, -49]) (countLit q [-50, -52, -55, -56]) (count1508 q) 3 1 (meaning1498 q) (meaning1504 q) (meaning1511 q) hs
  change valuationOf q 1498 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1511 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause870 (q : Snake 81) (h : Conditions q) : valuation q 1498 = false ∨ valuation q 1504 = false ∨ valuation q 1511 = true := counterClause870 (baseVal q)

theorem counterClause871 (q : Nat → Bool) : valuationOf q 1509 = false ∨ valuationOf q 1517 = true := by
  have hs : count1516 q = (countLit q [-31, -34, -35, -36, -39, -40, -41]) + (countLit q [-44, -45, -48, -49, -50, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-31, -34, -35, -36, -39, -40, -41]) (l₂ := [-44, -45, -48, -49, -50, -52, -55, -56])
  have hm := merge_right (literal (valuationOf q) (1509)) (literal (valuationOf q) (1517)) (countLit q [-31, -34, -35, -36, -39, -40, -41]) (countLit q [-44, -45, -48, -49, -50, -52, -55, -56]) (count1516 q) 2 (meaning1509 q) (meaning1517 q) hs
  change valuationOf q 1509 = false ∨ valuationOf q 1517 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause871 (q : Snake 81) (h : Conditions q) : valuation q 1509 = false ∨ valuation q 1517 = true := counterClause871 (baseVal q)

theorem counterClause872 (q : Nat → Bool) : valuationOf q 1485 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1518 = true := by
  have hs : count1516 q = (countLit q [-31, -34, -35, -36, -39, -40, -41]) + (countLit q [-44, -45, -48, -49, -50, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-31, -34, -35, -36, -39, -40, -41]) (l₂ := [-44, -45, -48, -49, -50, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1485)) (literal (valuationOf q) (1509)) (literal (valuationOf q) (1518)) (countLit q [-31, -34, -35, -36, -39, -40, -41]) (countLit q [-44, -45, -48, -49, -50, -52, -55, -56]) (count1516 q) 1 2 (meaning1485 q) (meaning1509 q) (meaning1518 q) hs
  change valuationOf q 1485 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1518 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause872 (q : Snake 81) (h : Conditions q) : valuation q 1485 = false ∨ valuation q 1509 = false ∨ valuation q 1518 = true := counterClause872 (baseVal q)

theorem counterClause873 (q : Nat → Bool) : valuationOf q 1485 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1519 = true := by
  have hs : count1516 q = (countLit q [-31, -34, -35, -36, -39, -40, -41]) + (countLit q [-44, -45, -48, -49, -50, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-31, -34, -35, -36, -39, -40, -41]) (l₂ := [-44, -45, -48, -49, -50, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1485)) (literal (valuationOf q) (1510)) (literal (valuationOf q) (1519)) (countLit q [-31, -34, -35, -36, -39, -40, -41]) (countLit q [-44, -45, -48, -49, -50, -52, -55, -56]) (count1516 q) 1 3 (meaning1485 q) (meaning1510 q) (meaning1519 q) hs
  change valuationOf q 1485 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1519 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause873 (q : Snake 81) (h : Conditions q) : valuation q 1485 = false ∨ valuation q 1510 = false ∨ valuation q 1519 = true := counterClause873 (baseVal q)

theorem counterClause874 (q : Nat → Bool) : valuationOf q 1485 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1520 = true := by
  have hs : count1516 q = (countLit q [-31, -34, -35, -36, -39, -40, -41]) + (countLit q [-44, -45, -48, -49, -50, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-31, -34, -35, -36, -39, -40, -41]) (l₂ := [-44, -45, -48, -49, -50, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1485)) (literal (valuationOf q) (1511)) (literal (valuationOf q) (1520)) (countLit q [-31, -34, -35, -36, -39, -40, -41]) (countLit q [-44, -45, -48, -49, -50, -52, -55, -56]) (count1516 q) 1 4 (meaning1485 q) (meaning1511 q) (meaning1520 q) hs
  change valuationOf q 1485 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause874 (q : Snake 81) (h : Conditions q) : valuation q 1485 = false ∨ valuation q 1511 = false ∨ valuation q 1520 = true := counterClause874 (baseVal q)

theorem counterClause875 (q : Nat → Bool) : valuationOf q 1486 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1519 = true := by
  have hs : count1516 q = (countLit q [-31, -34, -35, -36, -39, -40, -41]) + (countLit q [-44, -45, -48, -49, -50, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-31, -34, -35, -36, -39, -40, -41]) (l₂ := [-44, -45, -48, -49, -50, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1486)) (literal (valuationOf q) (1509)) (literal (valuationOf q) (1519)) (countLit q [-31, -34, -35, -36, -39, -40, -41]) (countLit q [-44, -45, -48, -49, -50, -52, -55, -56]) (count1516 q) 2 2 (meaning1486 q) (meaning1509 q) (meaning1519 q) hs
  change valuationOf q 1486 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1519 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause875 (q : Snake 81) (h : Conditions q) : valuation q 1486 = false ∨ valuation q 1509 = false ∨ valuation q 1519 = true := counterClause875 (baseVal q)

theorem counterClause876 (q : Nat → Bool) : valuationOf q 1486 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1520 = true := by
  have hs : count1516 q = (countLit q [-31, -34, -35, -36, -39, -40, -41]) + (countLit q [-44, -45, -48, -49, -50, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-31, -34, -35, -36, -39, -40, -41]) (l₂ := [-44, -45, -48, -49, -50, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1486)) (literal (valuationOf q) (1510)) (literal (valuationOf q) (1520)) (countLit q [-31, -34, -35, -36, -39, -40, -41]) (countLit q [-44, -45, -48, -49, -50, -52, -55, -56]) (count1516 q) 2 3 (meaning1486 q) (meaning1510 q) (meaning1520 q) hs
  change valuationOf q 1486 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause876 (q : Snake 81) (h : Conditions q) : valuation q 1486 = false ∨ valuation q 1510 = false ∨ valuation q 1520 = true := counterClause876 (baseVal q)

theorem counterClause877 (q : Nat → Bool) : valuationOf q 1486 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1521 = true := by
  have hs : count1516 q = (countLit q [-31, -34, -35, -36, -39, -40, -41]) + (countLit q [-44, -45, -48, -49, -50, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-31, -34, -35, -36, -39, -40, -41]) (l₂ := [-44, -45, -48, -49, -50, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1486)) (literal (valuationOf q) (1511)) (literal (valuationOf q) (1521)) (countLit q [-31, -34, -35, -36, -39, -40, -41]) (countLit q [-44, -45, -48, -49, -50, -52, -55, -56]) (count1516 q) 2 4 (meaning1486 q) (meaning1511 q) (meaning1521 q) hs
  change valuationOf q 1486 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1521 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause877 (q : Snake 81) (h : Conditions q) : valuation q 1486 = false ∨ valuation q 1511 = false ∨ valuation q 1521 = true := counterClause877 (baseVal q)

theorem counterClause878 (q : Nat → Bool) : valuationOf q 1487 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1520 = true := by
  have hs : count1516 q = (countLit q [-31, -34, -35, -36, -39, -40, -41]) + (countLit q [-44, -45, -48, -49, -50, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-31, -34, -35, -36, -39, -40, -41]) (l₂ := [-44, -45, -48, -49, -50, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1487)) (literal (valuationOf q) (1509)) (literal (valuationOf q) (1520)) (countLit q [-31, -34, -35, -36, -39, -40, -41]) (countLit q [-44, -45, -48, -49, -50, -52, -55, -56]) (count1516 q) 3 2 (meaning1487 q) (meaning1509 q) (meaning1520 q) hs
  change valuationOf q 1487 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause878 (q : Snake 81) (h : Conditions q) : valuation q 1487 = false ∨ valuation q 1509 = false ∨ valuation q 1520 = true := counterClause878 (baseVal q)

theorem counterClause879 (q : Nat → Bool) : valuationOf q 1487 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1521 = true := by
  have hs : count1516 q = (countLit q [-31, -34, -35, -36, -39, -40, -41]) + (countLit q [-44, -45, -48, -49, -50, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-31, -34, -35, -36, -39, -40, -41]) (l₂ := [-44, -45, -48, -49, -50, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1487)) (literal (valuationOf q) (1510)) (literal (valuationOf q) (1521)) (countLit q [-31, -34, -35, -36, -39, -40, -41]) (countLit q [-44, -45, -48, -49, -50, -52, -55, -56]) (count1516 q) 3 3 (meaning1487 q) (meaning1510 q) (meaning1521 q) hs
  change valuationOf q 1487 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1521 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause879 (q : Snake 81) (h : Conditions q) : valuation q 1487 = false ∨ valuation q 1510 = false ∨ valuation q 1521 = true := counterClause879 (baseVal q)

theorem counterClause880 (q : Nat → Bool) : valuationOf q 1487 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1522 = true := by
  have hs : count1516 q = (countLit q [-31, -34, -35, -36, -39, -40, -41]) + (countLit q [-44, -45, -48, -49, -50, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-31, -34, -35, -36, -39, -40, -41]) (l₂ := [-44, -45, -48, -49, -50, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1487)) (literal (valuationOf q) (1511)) (literal (valuationOf q) (1522)) (countLit q [-31, -34, -35, -36, -39, -40, -41]) (countLit q [-44, -45, -48, -49, -50, -52, -55, -56]) (count1516 q) 3 4 (meaning1487 q) (meaning1511 q) (meaning1522 q) hs
  change valuationOf q 1487 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1522 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause880 (q : Snake 81) (h : Conditions q) : valuation q 1487 = false ∨ valuation q 1511 = false ∨ valuation q 1522 = true := counterClause880 (baseVal q)

theorem counterClause881 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1521 = true := by
  have hs : count1516 q = (countLit q [-31, -34, -35, -36, -39, -40, -41]) + (countLit q [-44, -45, -48, -49, -50, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-31, -34, -35, -36, -39, -40, -41]) (l₂ := [-44, -45, -48, -49, -50, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1488)) (literal (valuationOf q) (1509)) (literal (valuationOf q) (1521)) (countLit q [-31, -34, -35, -36, -39, -40, -41]) (countLit q [-44, -45, -48, -49, -50, -52, -55, -56]) (count1516 q) 4 2 (meaning1488 q) (meaning1509 q) (meaning1521 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1521 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause881 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1509 = false ∨ valuation q 1521 = true := counterClause881 (baseVal q)

theorem counterClause882 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1522 = true := by
  have hs : count1516 q = (countLit q [-31, -34, -35, -36, -39, -40, -41]) + (countLit q [-44, -45, -48, -49, -50, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-31, -34, -35, -36, -39, -40, -41]) (l₂ := [-44, -45, -48, -49, -50, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1488)) (literal (valuationOf q) (1510)) (literal (valuationOf q) (1522)) (countLit q [-31, -34, -35, -36, -39, -40, -41]) (countLit q [-44, -45, -48, -49, -50, -52, -55, -56]) (count1516 q) 4 3 (meaning1488 q) (meaning1510 q) (meaning1522 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1522 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause882 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1510 = false ∨ valuation q 1522 = true := counterClause882 (baseVal q)

theorem counterClause883 (q : Nat → Bool) : valuationOf q 1489 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1522 = true := by
  have hs : count1516 q = (countLit q [-31, -34, -35, -36, -39, -40, -41]) + (countLit q [-44, -45, -48, -49, -50, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-31, -34, -35, -36, -39, -40, -41]) (l₂ := [-44, -45, -48, -49, -50, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1489)) (literal (valuationOf q) (1509)) (literal (valuationOf q) (1522)) (countLit q [-31, -34, -35, -36, -39, -40, -41]) (countLit q [-44, -45, -48, -49, -50, -52, -55, -56]) (count1516 q) 5 2 (meaning1489 q) (meaning1509 q) (meaning1522 q) hs
  change valuationOf q 1489 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1522 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause883 (q : Snake 81) (h : Conditions q) : valuation q 1489 = false ∨ valuation q 1509 = false ∨ valuation q 1522 = true := counterClause883 (baseVal q)

theorem counterClause884 (q : Nat → Bool) : valuationOf q 1461 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1538 = true := by
  have hs : count1531 q = (countLit q [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28]) + (countLit q [-31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28]) (l₂ := [-31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1461)) (literal (valuationOf q) (1518)) (literal (valuationOf q) (1538)) (countLit q [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28]) (countLit q [-31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56]) (count1531 q) 5 3 (meaning1461 q) (meaning1518 q) (meaning1538 q) hs
  change valuationOf q 1461 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1538 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause884 (q : Snake 81) (h : Conditions q) : valuation q 1461 = false ∨ valuation q 1518 = false ∨ valuation q 1538 = true := counterClause884 (baseVal q)

theorem counterClause885 (q : Nat → Bool) : valuationOf q 1461 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1539 = true := by
  have hs : count1531 q = (countLit q [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28]) + (countLit q [-31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28]) (l₂ := [-31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1461)) (literal (valuationOf q) (1519)) (literal (valuationOf q) (1539)) (countLit q [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28]) (countLit q [-31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56]) (count1531 q) 5 4 (meaning1461 q) (meaning1519 q) (meaning1539 q) hs
  change valuationOf q 1461 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1539 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause885 (q : Snake 81) (h : Conditions q) : valuation q 1461 = false ∨ valuation q 1519 = false ∨ valuation q 1539 = true := counterClause885 (baseVal q)

theorem counterClause886 (q : Nat → Bool) : valuationOf q 1461 = false ∨ valuationOf q 1520 = false ∨ valuationOf q 1540 = true := by
  have hs : count1531 q = (countLit q [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28]) + (countLit q [-31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28]) (l₂ := [-31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1461)) (literal (valuationOf q) (1520)) (literal (valuationOf q) (1540)) (countLit q [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28]) (countLit q [-31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56]) (count1531 q) 5 5 (meaning1461 q) (meaning1520 q) (meaning1540 q) hs
  change valuationOf q 1461 = false ∨ valuationOf q 1520 = false ∨ valuationOf q 1540 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause886 (q : Snake 81) (h : Conditions q) : valuation q 1461 = false ∨ valuation q 1520 = false ∨ valuation q 1540 = true := counterClause886 (baseVal q)

theorem counterClause887 (q : Nat → Bool) : valuationOf q 1461 = false ∨ valuationOf q 1521 = false ∨ valuationOf q 1541 = true := by
  have hs : count1531 q = (countLit q [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28]) + (countLit q [-31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28]) (l₂ := [-31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1461)) (literal (valuationOf q) (1521)) (literal (valuationOf q) (1541)) (countLit q [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28]) (countLit q [-31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56]) (count1531 q) 5 6 (meaning1461 q) (meaning1521 q) (meaning1541 q) hs
  change valuationOf q 1461 = false ∨ valuationOf q 1521 = false ∨ valuationOf q 1541 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause887 (q : Snake 81) (h : Conditions q) : valuation q 1461 = false ∨ valuation q 1521 = false ∨ valuation q 1541 = true := counterClause887 (baseVal q)

theorem counterClause888 (q : Nat → Bool) : valuationOf q 1461 = false ∨ valuationOf q 1522 = false ∨ valuationOf q 1542 = true := by
  have hs : count1531 q = (countLit q [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28]) + (countLit q [-31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28]) (l₂ := [-31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1461)) (literal (valuationOf q) (1522)) (literal (valuationOf q) (1542)) (countLit q [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28]) (countLit q [-31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56]) (count1531 q) 5 7 (meaning1461 q) (meaning1522 q) (meaning1542 q) hs
  change valuationOf q 1461 = false ∨ valuationOf q 1522 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause888 (q : Snake 81) (h : Conditions q) : valuation q 1461 = false ∨ valuation q 1522 = false ∨ valuation q 1542 = true := counterClause888 (baseVal q)

theorem counterClause889 (q : Nat → Bool) : valuationOf q 1462 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1539 = true := by
  have hs : count1531 q = (countLit q [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28]) + (countLit q [-31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28]) (l₂ := [-31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1462)) (literal (valuationOf q) (1518)) (literal (valuationOf q) (1539)) (countLit q [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28]) (countLit q [-31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56]) (count1531 q) 6 3 (meaning1462 q) (meaning1518 q) (meaning1539 q) hs
  change valuationOf q 1462 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1539 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause889 (q : Snake 81) (h : Conditions q) : valuation q 1462 = false ∨ valuation q 1518 = false ∨ valuation q 1539 = true := counterClause889 (baseVal q)

theorem counterClause890 (q : Nat → Bool) : valuationOf q 1462 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1540 = true := by
  have hs : count1531 q = (countLit q [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28]) + (countLit q [-31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28]) (l₂ := [-31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1462)) (literal (valuationOf q) (1519)) (literal (valuationOf q) (1540)) (countLit q [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28]) (countLit q [-31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56]) (count1531 q) 6 4 (meaning1462 q) (meaning1519 q) (meaning1540 q) hs
  change valuationOf q 1462 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1540 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause890 (q : Snake 81) (h : Conditions q) : valuation q 1462 = false ∨ valuation q 1519 = false ∨ valuation q 1540 = true := counterClause890 (baseVal q)

theorem counterClause891 (q : Nat → Bool) : valuationOf q 1462 = false ∨ valuationOf q 1520 = false ∨ valuationOf q 1541 = true := by
  have hs : count1531 q = (countLit q [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28]) + (countLit q [-31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28]) (l₂ := [-31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1462)) (literal (valuationOf q) (1520)) (literal (valuationOf q) (1541)) (countLit q [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28]) (countLit q [-31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56]) (count1531 q) 6 5 (meaning1462 q) (meaning1520 q) (meaning1541 q) hs
  change valuationOf q 1462 = false ∨ valuationOf q 1520 = false ∨ valuationOf q 1541 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause891 (q : Snake 81) (h : Conditions q) : valuation q 1462 = false ∨ valuation q 1520 = false ∨ valuation q 1541 = true := counterClause891 (baseVal q)

theorem counterClause892 (q : Nat → Bool) : valuationOf q 1462 = false ∨ valuationOf q 1521 = false ∨ valuationOf q 1542 = true := by
  have hs : count1531 q = (countLit q [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28]) + (countLit q [-31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28]) (l₂ := [-31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1462)) (literal (valuationOf q) (1521)) (literal (valuationOf q) (1542)) (countLit q [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28]) (countLit q [-31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56]) (count1531 q) 6 6 (meaning1462 q) (meaning1521 q) (meaning1542 q) hs
  change valuationOf q 1462 = false ∨ valuationOf q 1521 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause892 (q : Snake 81) (h : Conditions q) : valuation q 1462 = false ∨ valuation q 1521 = false ∨ valuation q 1542 = true := counterClause892 (baseVal q)

theorem counterClause893 (q : Nat → Bool) : valuationOf q 1462 = false ∨ valuationOf q 1522 = false ∨ valuationOf q 1543 = true := by
  have hs : count1531 q = (countLit q [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28]) + (countLit q [-31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28]) (l₂ := [-31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1462)) (literal (valuationOf q) (1522)) (literal (valuationOf q) (1543)) (countLit q [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28]) (countLit q [-31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56]) (count1531 q) 6 7 (meaning1462 q) (meaning1522 q) (meaning1543 q) hs
  change valuationOf q 1462 = false ∨ valuationOf q 1522 = false ∨ valuationOf q 1543 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause893 (q : Snake 81) (h : Conditions q) : valuation q 1462 = false ∨ valuation q 1522 = false ∨ valuation q 1543 = true := counterClause893 (baseVal q)

theorem counterClause894 (q : Nat → Bool) : valuationOf q 1463 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1540 = true := by
  have hs : count1531 q = (countLit q [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28]) + (countLit q [-31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28]) (l₂ := [-31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1463)) (literal (valuationOf q) (1518)) (literal (valuationOf q) (1540)) (countLit q [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28]) (countLit q [-31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56]) (count1531 q) 7 3 (meaning1463 q) (meaning1518 q) (meaning1540 q) hs
  change valuationOf q 1463 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1540 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause894 (q : Snake 81) (h : Conditions q) : valuation q 1463 = false ∨ valuation q 1518 = false ∨ valuation q 1540 = true := counterClause894 (baseVal q)

theorem counterClause895 (q : Nat → Bool) : valuationOf q 1463 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1541 = true := by
  have hs : count1531 q = (countLit q [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28]) + (countLit q [-31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28]) (l₂ := [-31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1463)) (literal (valuationOf q) (1519)) (literal (valuationOf q) (1541)) (countLit q [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28]) (countLit q [-31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56]) (count1531 q) 7 4 (meaning1463 q) (meaning1519 q) (meaning1541 q) hs
  change valuationOf q 1463 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1541 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause895 (q : Snake 81) (h : Conditions q) : valuation q 1463 = false ∨ valuation q 1519 = false ∨ valuation q 1541 = true := counterClause895 (baseVal q)

theorem counterClause896 (q : Nat → Bool) : valuationOf q 1463 = false ∨ valuationOf q 1520 = false ∨ valuationOf q 1542 = true := by
  have hs : count1531 q = (countLit q [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28]) + (countLit q [-31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28]) (l₂ := [-31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1463)) (literal (valuationOf q) (1520)) (literal (valuationOf q) (1542)) (countLit q [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28]) (countLit q [-31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56]) (count1531 q) 7 5 (meaning1463 q) (meaning1520 q) (meaning1542 q) hs
  change valuationOf q 1463 = false ∨ valuationOf q 1520 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause896 (q : Snake 81) (h : Conditions q) : valuation q 1463 = false ∨ valuation q 1520 = false ∨ valuation q 1542 = true := counterClause896 (baseVal q)

theorem block27 (q : Snake 81) (h : Conditions q) : B112E104.Block27 (valuation q) :=
  ⟨clause865 q h, clause866 q h, clause867 q h, clause868 q h, clause869 q h, clause870 q h, clause871 q h, clause872 q h, clause873 q h, clause874 q h, clause875 q h, clause876 q h, clause877 q h, clause878 q h, clause879 q h, clause880 q h, clause881 q h, clause882 q h, clause883 q h, clause884 q h, clause885 q h, clause886 q h, clause887 q h, clause888 q h, clause889 q h, clause890 q h, clause891 q h, clause892 q h, clause893 q h, clause894 q h, clause895 q h, clause896 q h⟩

end
end Snake9.Regrowth.E112104
