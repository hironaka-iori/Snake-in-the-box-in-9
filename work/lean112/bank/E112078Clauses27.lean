import E112078Semantics
import B112E078Inputs
namespace Snake9.Regrowth.E112078
noncomputable section
local instance blockDec27 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause865 (q : Nat → Bool) : valuationOf q 1503 = false ∨ valuationOf q 1514 = true := by
  have hs : count1514 q = (countLit q [-27, -30, -32]) + (countLit q [-35, -38, -39, -42]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -32]) (l₂ := [-35, -38, -39, -42])
  have hm := merge_left (literal (valuationOf q) (1503)) (literal (valuationOf q) (1514)) (countLit q [-27, -30, -32]) (countLit q [-35, -38, -39, -42]) (count1514 q) 1 (meaning1503 q) (meaning1514 q) hs
  change valuationOf q 1503 = false ∨ valuationOf q 1514 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause865 (q : Snake 81) (h : Conditions q) : valuation q 1503 = false ∨ valuation q 1514 = true := counterClause865 (baseVal q)

theorem counterClause866 (q : Nat → Bool) : valuationOf q 1503 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1515 = true := by
  have hs : count1514 q = (countLit q [-27, -30, -32]) + (countLit q [-35, -38, -39, -42]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -32]) (l₂ := [-35, -38, -39, -42])
  have hm := merge_two (literal (valuationOf q) (1503)) (literal (valuationOf q) (1510)) (literal (valuationOf q) (1515)) (countLit q [-27, -30, -32]) (countLit q [-35, -38, -39, -42]) (count1514 q) 1 1 (meaning1503 q) (meaning1510 q) (meaning1515 q) hs
  change valuationOf q 1503 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1515 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause866 (q : Snake 81) (h : Conditions q) : valuation q 1503 = false ∨ valuation q 1510 = false ∨ valuation q 1515 = true := counterClause866 (baseVal q)

theorem counterClause867 (q : Nat → Bool) : valuationOf q 1503 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1516 = true := by
  have hs : count1514 q = (countLit q [-27, -30, -32]) + (countLit q [-35, -38, -39, -42]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -32]) (l₂ := [-35, -38, -39, -42])
  have hm := merge_two (literal (valuationOf q) (1503)) (literal (valuationOf q) (1511)) (literal (valuationOf q) (1516)) (countLit q [-27, -30, -32]) (countLit q [-35, -38, -39, -42]) (count1514 q) 1 2 (meaning1503 q) (meaning1511 q) (meaning1516 q) hs
  change valuationOf q 1503 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1516 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause867 (q : Snake 81) (h : Conditions q) : valuation q 1503 = false ∨ valuation q 1511 = false ∨ valuation q 1516 = true := counterClause867 (baseVal q)

theorem counterClause868 (q : Nat → Bool) : valuationOf q 1503 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1517 = true := by
  have hs : count1514 q = (countLit q [-27, -30, -32]) + (countLit q [-35, -38, -39, -42]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -32]) (l₂ := [-35, -38, -39, -42])
  have hm := merge_two (literal (valuationOf q) (1503)) (literal (valuationOf q) (1512)) (literal (valuationOf q) (1517)) (countLit q [-27, -30, -32]) (countLit q [-35, -38, -39, -42]) (count1514 q) 1 3 (meaning1503 q) (meaning1512 q) (meaning1517 q) hs
  change valuationOf q 1503 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1517 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause868 (q : Snake 81) (h : Conditions q) : valuation q 1503 = false ∨ valuation q 1512 = false ∨ valuation q 1517 = true := counterClause868 (baseVal q)

theorem counterClause869 (q : Nat → Bool) : valuationOf q 1503 = false ∨ valuationOf q 1513 = false ∨ valuationOf q 1518 = true := by
  have hs : count1514 q = (countLit q [-27, -30, -32]) + (countLit q [-35, -38, -39, -42]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -32]) (l₂ := [-35, -38, -39, -42])
  have hm := merge_two (literal (valuationOf q) (1503)) (literal (valuationOf q) (1513)) (literal (valuationOf q) (1518)) (countLit q [-27, -30, -32]) (countLit q [-35, -38, -39, -42]) (count1514 q) 1 4 (meaning1503 q) (meaning1513 q) (meaning1518 q) hs
  change valuationOf q 1503 = false ∨ valuationOf q 1513 = false ∨ valuationOf q 1518 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause869 (q : Snake 81) (h : Conditions q) : valuation q 1503 = false ∨ valuation q 1513 = false ∨ valuation q 1518 = true := counterClause869 (baseVal q)

theorem counterClause870 (q : Nat → Bool) : valuationOf q 1504 = false ∨ valuationOf q 1515 = true := by
  have hs : count1514 q = (countLit q [-27, -30, -32]) + (countLit q [-35, -38, -39, -42]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -32]) (l₂ := [-35, -38, -39, -42])
  have hm := merge_left (literal (valuationOf q) (1504)) (literal (valuationOf q) (1515)) (countLit q [-27, -30, -32]) (countLit q [-35, -38, -39, -42]) (count1514 q) 2 (meaning1504 q) (meaning1515 q) hs
  change valuationOf q 1504 = false ∨ valuationOf q 1515 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause870 (q : Snake 81) (h : Conditions q) : valuation q 1504 = false ∨ valuation q 1515 = true := counterClause870 (baseVal q)

theorem counterClause871 (q : Nat → Bool) : valuationOf q 1504 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1516 = true := by
  have hs : count1514 q = (countLit q [-27, -30, -32]) + (countLit q [-35, -38, -39, -42]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -32]) (l₂ := [-35, -38, -39, -42])
  have hm := merge_two (literal (valuationOf q) (1504)) (literal (valuationOf q) (1510)) (literal (valuationOf q) (1516)) (countLit q [-27, -30, -32]) (countLit q [-35, -38, -39, -42]) (count1514 q) 2 1 (meaning1504 q) (meaning1510 q) (meaning1516 q) hs
  change valuationOf q 1504 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1516 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause871 (q : Snake 81) (h : Conditions q) : valuation q 1504 = false ∨ valuation q 1510 = false ∨ valuation q 1516 = true := counterClause871 (baseVal q)

theorem counterClause872 (q : Nat → Bool) : valuationOf q 1504 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1517 = true := by
  have hs : count1514 q = (countLit q [-27, -30, -32]) + (countLit q [-35, -38, -39, -42]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -32]) (l₂ := [-35, -38, -39, -42])
  have hm := merge_two (literal (valuationOf q) (1504)) (literal (valuationOf q) (1511)) (literal (valuationOf q) (1517)) (countLit q [-27, -30, -32]) (countLit q [-35, -38, -39, -42]) (count1514 q) 2 2 (meaning1504 q) (meaning1511 q) (meaning1517 q) hs
  change valuationOf q 1504 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1517 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause872 (q : Snake 81) (h : Conditions q) : valuation q 1504 = false ∨ valuation q 1511 = false ∨ valuation q 1517 = true := counterClause872 (baseVal q)

theorem counterClause873 (q : Nat → Bool) : valuationOf q 1504 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1518 = true := by
  have hs : count1514 q = (countLit q [-27, -30, -32]) + (countLit q [-35, -38, -39, -42]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -32]) (l₂ := [-35, -38, -39, -42])
  have hm := merge_two (literal (valuationOf q) (1504)) (literal (valuationOf q) (1512)) (literal (valuationOf q) (1518)) (countLit q [-27, -30, -32]) (countLit q [-35, -38, -39, -42]) (count1514 q) 2 3 (meaning1504 q) (meaning1512 q) (meaning1518 q) hs
  change valuationOf q 1504 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1518 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause873 (q : Snake 81) (h : Conditions q) : valuation q 1504 = false ∨ valuation q 1512 = false ∨ valuation q 1518 = true := counterClause873 (baseVal q)

theorem counterClause874 (q : Nat → Bool) : valuationOf q 1504 = false ∨ valuationOf q 1513 = false ∨ valuationOf q 1519 = true := by
  have hs : count1514 q = (countLit q [-27, -30, -32]) + (countLit q [-35, -38, -39, -42]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -32]) (l₂ := [-35, -38, -39, -42])
  have hm := merge_two (literal (valuationOf q) (1504)) (literal (valuationOf q) (1513)) (literal (valuationOf q) (1519)) (countLit q [-27, -30, -32]) (countLit q [-35, -38, -39, -42]) (count1514 q) 2 4 (meaning1504 q) (meaning1513 q) (meaning1519 q) hs
  change valuationOf q 1504 = false ∨ valuationOf q 1513 = false ∨ valuationOf q 1519 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause874 (q : Snake 81) (h : Conditions q) : valuation q 1504 = false ∨ valuation q 1513 = false ∨ valuation q 1519 = true := counterClause874 (baseVal q)

theorem counterClause875 (q : Nat → Bool) : valuationOf q 1505 = false ∨ valuationOf q 1516 = true := by
  have hs : count1514 q = (countLit q [-27, -30, -32]) + (countLit q [-35, -38, -39, -42]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -32]) (l₂ := [-35, -38, -39, -42])
  have hm := merge_left (literal (valuationOf q) (1505)) (literal (valuationOf q) (1516)) (countLit q [-27, -30, -32]) (countLit q [-35, -38, -39, -42]) (count1514 q) 3 (meaning1505 q) (meaning1516 q) hs
  change valuationOf q 1505 = false ∨ valuationOf q 1516 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause875 (q : Snake 81) (h : Conditions q) : valuation q 1505 = false ∨ valuation q 1516 = true := counterClause875 (baseVal q)

theorem counterClause876 (q : Nat → Bool) : valuationOf q 1505 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1517 = true := by
  have hs : count1514 q = (countLit q [-27, -30, -32]) + (countLit q [-35, -38, -39, -42]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -32]) (l₂ := [-35, -38, -39, -42])
  have hm := merge_two (literal (valuationOf q) (1505)) (literal (valuationOf q) (1510)) (literal (valuationOf q) (1517)) (countLit q [-27, -30, -32]) (countLit q [-35, -38, -39, -42]) (count1514 q) 3 1 (meaning1505 q) (meaning1510 q) (meaning1517 q) hs
  change valuationOf q 1505 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1517 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause876 (q : Snake 81) (h : Conditions q) : valuation q 1505 = false ∨ valuation q 1510 = false ∨ valuation q 1517 = true := counterClause876 (baseVal q)

theorem counterClause877 (q : Nat → Bool) : valuationOf q 1505 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1518 = true := by
  have hs : count1514 q = (countLit q [-27, -30, -32]) + (countLit q [-35, -38, -39, -42]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -32]) (l₂ := [-35, -38, -39, -42])
  have hm := merge_two (literal (valuationOf q) (1505)) (literal (valuationOf q) (1511)) (literal (valuationOf q) (1518)) (countLit q [-27, -30, -32]) (countLit q [-35, -38, -39, -42]) (count1514 q) 3 2 (meaning1505 q) (meaning1511 q) (meaning1518 q) hs
  change valuationOf q 1505 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1518 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause877 (q : Snake 81) (h : Conditions q) : valuation q 1505 = false ∨ valuation q 1511 = false ∨ valuation q 1518 = true := counterClause877 (baseVal q)

theorem counterClause878 (q : Nat → Bool) : valuationOf q 47 = true ∨ valuationOf q 1521 = true := by
  have hs : count1521 q = (countLit q [-46]) + (countLit q [-47]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-47])
  have hm := merge_right (literal (valuationOf q) (-47)) (literal (valuationOf q) (1521)) (countLit q [-46]) (countLit q [-47]) (count1521 q) 1 (meaningNeg47 q) (meaning1521 q) hs
  change (! (valuationOf q 47)) = false ∨ valuationOf q 1521 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause878 (q : Snake 81) (h : Conditions q) : valuation q 47 = true ∨ valuation q 1521 = true := counterClause878 (baseVal q)

theorem counterClause879 (q : Nat → Bool) : valuationOf q 46 = true ∨ valuationOf q 1521 = true := by
  have hs : count1521 q = (countLit q [-46]) + (countLit q [-47]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-47])
  have hm := merge_left (literal (valuationOf q) (-46)) (literal (valuationOf q) (1521)) (countLit q [-46]) (countLit q [-47]) (count1521 q) 1 (meaningNeg46 q) (meaning1521 q) hs
  change (! (valuationOf q 46)) = false ∨ valuationOf q 1521 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause879 (q : Snake 81) (h : Conditions q) : valuation q 46 = true ∨ valuation q 1521 = true := counterClause879 (baseVal q)

theorem counterClause880 (q : Nat → Bool) : valuationOf q 46 = true ∨ valuationOf q 47 = true ∨ valuationOf q 1522 = true := by
  have hs : count1521 q = (countLit q [-46]) + (countLit q [-47]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-47])
  have hm := merge_two (literal (valuationOf q) (-46)) (literal (valuationOf q) (-47)) (literal (valuationOf q) (1522)) (countLit q [-46]) (countLit q [-47]) (count1521 q) 1 1 (meaningNeg46 q) (meaningNeg47 q) (meaning1522 q) hs
  change (! (valuationOf q 46)) = false ∨ (! (valuationOf q 47)) = false ∨ valuationOf q 1522 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause880 (q : Snake 81) (h : Conditions q) : valuation q 46 = true ∨ valuation q 47 = true ∨ valuation q 1522 = true := counterClause880 (baseVal q)

theorem counterClause881 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 1523 = true := by
  have hs : count1523 q = (countLit q [-49]) + (countLit q [-52]) := List.countP_append (p := literal q) (l₁ := [-49]) (l₂ := [-52])
  have hm := merge_right (literal (valuationOf q) (-52)) (literal (valuationOf q) (1523)) (countLit q [-49]) (countLit q [-52]) (count1523 q) 1 (meaningNeg52 q) (meaning1523 q) hs
  change (! (valuationOf q 52)) = false ∨ valuationOf q 1523 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause881 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 1523 = true := counterClause881 (baseVal q)

theorem counterClause882 (q : Nat → Bool) : valuationOf q 49 = true ∨ valuationOf q 1523 = true := by
  have hs : count1523 q = (countLit q [-49]) + (countLit q [-52]) := List.countP_append (p := literal q) (l₁ := [-49]) (l₂ := [-52])
  have hm := merge_left (literal (valuationOf q) (-49)) (literal (valuationOf q) (1523)) (countLit q [-49]) (countLit q [-52]) (count1523 q) 1 (meaningNeg49 q) (meaning1523 q) hs
  change (! (valuationOf q 49)) = false ∨ valuationOf q 1523 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause882 (q : Snake 81) (h : Conditions q) : valuation q 49 = true ∨ valuation q 1523 = true := counterClause882 (baseVal q)

theorem counterClause883 (q : Nat → Bool) : valuationOf q 49 = true ∨ valuationOf q 52 = true ∨ valuationOf q 1524 = true := by
  have hs : count1523 q = (countLit q [-49]) + (countLit q [-52]) := List.countP_append (p := literal q) (l₁ := [-49]) (l₂ := [-52])
  have hm := merge_two (literal (valuationOf q) (-49)) (literal (valuationOf q) (-52)) (literal (valuationOf q) (1524)) (countLit q [-49]) (countLit q [-52]) (count1523 q) 1 1 (meaningNeg49 q) (meaningNeg52 q) (meaning1524 q) hs
  change (! (valuationOf q 49)) = false ∨ (! (valuationOf q 52)) = false ∨ valuationOf q 1524 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause883 (q : Snake 81) (h : Conditions q) : valuation q 49 = true ∨ valuation q 52 = true ∨ valuation q 1524 = true := counterClause883 (baseVal q)

theorem counterClause884 (q : Nat → Bool) : valuationOf q 1523 = false ∨ valuationOf q 1525 = true := by
  have hs : count1525 q = (countLit q [-46, -47]) + (countLit q [-49, -52]) := List.countP_append (p := literal q) (l₁ := [-46, -47]) (l₂ := [-49, -52])
  have hm := merge_right (literal (valuationOf q) (1523)) (literal (valuationOf q) (1525)) (countLit q [-46, -47]) (countLit q [-49, -52]) (count1525 q) 1 (meaning1523 q) (meaning1525 q) hs
  change valuationOf q 1523 = false ∨ valuationOf q 1525 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause884 (q : Snake 81) (h : Conditions q) : valuation q 1523 = false ∨ valuation q 1525 = true := counterClause884 (baseVal q)

theorem counterClause885 (q : Nat → Bool) : valuationOf q 1524 = false ∨ valuationOf q 1526 = true := by
  have hs : count1525 q = (countLit q [-46, -47]) + (countLit q [-49, -52]) := List.countP_append (p := literal q) (l₁ := [-46, -47]) (l₂ := [-49, -52])
  have hm := merge_right (literal (valuationOf q) (1524)) (literal (valuationOf q) (1526)) (countLit q [-46, -47]) (countLit q [-49, -52]) (count1525 q) 2 (meaning1524 q) (meaning1526 q) hs
  change valuationOf q 1524 = false ∨ valuationOf q 1526 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause885 (q : Snake 81) (h : Conditions q) : valuation q 1524 = false ∨ valuation q 1526 = true := counterClause885 (baseVal q)

theorem counterClause886 (q : Nat → Bool) : valuationOf q 1521 = false ∨ valuationOf q 1525 = true := by
  have hs : count1525 q = (countLit q [-46, -47]) + (countLit q [-49, -52]) := List.countP_append (p := literal q) (l₁ := [-46, -47]) (l₂ := [-49, -52])
  have hm := merge_left (literal (valuationOf q) (1521)) (literal (valuationOf q) (1525)) (countLit q [-46, -47]) (countLit q [-49, -52]) (count1525 q) 1 (meaning1521 q) (meaning1525 q) hs
  change valuationOf q 1521 = false ∨ valuationOf q 1525 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause886 (q : Snake 81) (h : Conditions q) : valuation q 1521 = false ∨ valuation q 1525 = true := counterClause886 (baseVal q)

theorem counterClause887 (q : Nat → Bool) : valuationOf q 1521 = false ∨ valuationOf q 1523 = false ∨ valuationOf q 1526 = true := by
  have hs : count1525 q = (countLit q [-46, -47]) + (countLit q [-49, -52]) := List.countP_append (p := literal q) (l₁ := [-46, -47]) (l₂ := [-49, -52])
  have hm := merge_two (literal (valuationOf q) (1521)) (literal (valuationOf q) (1523)) (literal (valuationOf q) (1526)) (countLit q [-46, -47]) (countLit q [-49, -52]) (count1525 q) 1 1 (meaning1521 q) (meaning1523 q) (meaning1526 q) hs
  change valuationOf q 1521 = false ∨ valuationOf q 1523 = false ∨ valuationOf q 1526 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause887 (q : Snake 81) (h : Conditions q) : valuation q 1521 = false ∨ valuation q 1523 = false ∨ valuation q 1526 = true := counterClause887 (baseVal q)

theorem counterClause888 (q : Nat → Bool) : valuationOf q 1521 = false ∨ valuationOf q 1524 = false ∨ valuationOf q 1527 = true := by
  have hs : count1525 q = (countLit q [-46, -47]) + (countLit q [-49, -52]) := List.countP_append (p := literal q) (l₁ := [-46, -47]) (l₂ := [-49, -52])
  have hm := merge_two (literal (valuationOf q) (1521)) (literal (valuationOf q) (1524)) (literal (valuationOf q) (1527)) (countLit q [-46, -47]) (countLit q [-49, -52]) (count1525 q) 1 2 (meaning1521 q) (meaning1524 q) (meaning1527 q) hs
  change valuationOf q 1521 = false ∨ valuationOf q 1524 = false ∨ valuationOf q 1527 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause888 (q : Snake 81) (h : Conditions q) : valuation q 1521 = false ∨ valuation q 1524 = false ∨ valuation q 1527 = true := counterClause888 (baseVal q)

theorem counterClause889 (q : Nat → Bool) : valuationOf q 1522 = false ∨ valuationOf q 1526 = true := by
  have hs : count1525 q = (countLit q [-46, -47]) + (countLit q [-49, -52]) := List.countP_append (p := literal q) (l₁ := [-46, -47]) (l₂ := [-49, -52])
  have hm := merge_left (literal (valuationOf q) (1522)) (literal (valuationOf q) (1526)) (countLit q [-46, -47]) (countLit q [-49, -52]) (count1525 q) 2 (meaning1522 q) (meaning1526 q) hs
  change valuationOf q 1522 = false ∨ valuationOf q 1526 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause889 (q : Snake 81) (h : Conditions q) : valuation q 1522 = false ∨ valuation q 1526 = true := counterClause889 (baseVal q)

theorem counterClause890 (q : Nat → Bool) : valuationOf q 1522 = false ∨ valuationOf q 1523 = false ∨ valuationOf q 1527 = true := by
  have hs : count1525 q = (countLit q [-46, -47]) + (countLit q [-49, -52]) := List.countP_append (p := literal q) (l₁ := [-46, -47]) (l₂ := [-49, -52])
  have hm := merge_two (literal (valuationOf q) (1522)) (literal (valuationOf q) (1523)) (literal (valuationOf q) (1527)) (countLit q [-46, -47]) (countLit q [-49, -52]) (count1525 q) 2 1 (meaning1522 q) (meaning1523 q) (meaning1527 q) hs
  change valuationOf q 1522 = false ∨ valuationOf q 1523 = false ∨ valuationOf q 1527 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause890 (q : Snake 81) (h : Conditions q) : valuation q 1522 = false ∨ valuation q 1523 = false ∨ valuation q 1527 = true := counterClause890 (baseVal q)

theorem counterClause891 (q : Nat → Bool) : valuationOf q 1522 = false ∨ valuationOf q 1524 = false ∨ valuationOf q 1528 = true := by
  have hs : count1525 q = (countLit q [-46, -47]) + (countLit q [-49, -52]) := List.countP_append (p := literal q) (l₁ := [-46, -47]) (l₂ := [-49, -52])
  have hm := merge_two (literal (valuationOf q) (1522)) (literal (valuationOf q) (1524)) (literal (valuationOf q) (1528)) (countLit q [-46, -47]) (countLit q [-49, -52]) (count1525 q) 2 2 (meaning1522 q) (meaning1524 q) (meaning1528 q) hs
  change valuationOf q 1522 = false ∨ valuationOf q 1524 = false ∨ valuationOf q 1528 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause891 (q : Snake 81) (h : Conditions q) : valuation q 1522 = false ∨ valuation q 1524 = false ∨ valuation q 1528 = true := counterClause891 (baseVal q)

theorem counterClause892 (q : Nat → Bool) : valuationOf q 55 = true ∨ valuationOf q 1529 = true := by
  have hs : count1529 q = (countLit q [-53]) + (countLit q [-55]) := List.countP_append (p := literal q) (l₁ := [-53]) (l₂ := [-55])
  have hm := merge_right (literal (valuationOf q) (-55)) (literal (valuationOf q) (1529)) (countLit q [-53]) (countLit q [-55]) (count1529 q) 1 (meaningNeg55 q) (meaning1529 q) hs
  change (! (valuationOf q 55)) = false ∨ valuationOf q 1529 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause892 (q : Snake 81) (h : Conditions q) : valuation q 55 = true ∨ valuation q 1529 = true := counterClause892 (baseVal q)

theorem counterClause893 (q : Nat → Bool) : valuationOf q 53 = true ∨ valuationOf q 1529 = true := by
  have hs : count1529 q = (countLit q [-53]) + (countLit q [-55]) := List.countP_append (p := literal q) (l₁ := [-53]) (l₂ := [-55])
  have hm := merge_left (literal (valuationOf q) (-53)) (literal (valuationOf q) (1529)) (countLit q [-53]) (countLit q [-55]) (count1529 q) 1 (meaningNeg53 q) (meaning1529 q) hs
  change (! (valuationOf q 53)) = false ∨ valuationOf q 1529 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause893 (q : Snake 81) (h : Conditions q) : valuation q 53 = true ∨ valuation q 1529 = true := counterClause893 (baseVal q)

theorem counterClause894 (q : Nat → Bool) : valuationOf q 53 = true ∨ valuationOf q 55 = true ∨ valuationOf q 1530 = true := by
  have hs : count1529 q = (countLit q [-53]) + (countLit q [-55]) := List.countP_append (p := literal q) (l₁ := [-53]) (l₂ := [-55])
  have hm := merge_two (literal (valuationOf q) (-53)) (literal (valuationOf q) (-55)) (literal (valuationOf q) (1530)) (countLit q [-53]) (countLit q [-55]) (count1529 q) 1 1 (meaningNeg53 q) (meaningNeg55 q) (meaning1530 q) hs
  change (! (valuationOf q 53)) = false ∨ (! (valuationOf q 55)) = false ∨ valuationOf q 1530 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause894 (q : Snake 81) (h : Conditions q) : valuation q 53 = true ∨ valuation q 55 = true ∨ valuation q 1530 = true := counterClause894 (baseVal q)

theorem counterClause895 (q : Nat → Bool) : valuationOf q 57 = true ∨ valuationOf q 1531 = true := by
  have hs : count1531 q = (countLit q [-56]) + (countLit q [-57]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-57])
  have hm := merge_right (literal (valuationOf q) (-57)) (literal (valuationOf q) (1531)) (countLit q [-56]) (countLit q [-57]) (count1531 q) 1 (meaningNeg57 q) (meaning1531 q) hs
  change (! (valuationOf q 57)) = false ∨ valuationOf q 1531 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause895 (q : Snake 81) (h : Conditions q) : valuation q 57 = true ∨ valuation q 1531 = true := counterClause895 (baseVal q)

theorem counterClause896 (q : Nat → Bool) : valuationOf q 56 = true ∨ valuationOf q 1531 = true := by
  have hs : count1531 q = (countLit q [-56]) + (countLit q [-57]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-57])
  have hm := merge_left (literal (valuationOf q) (-56)) (literal (valuationOf q) (1531)) (countLit q [-56]) (countLit q [-57]) (count1531 q) 1 (meaningNeg56 q) (meaning1531 q) hs
  change (! (valuationOf q 56)) = false ∨ valuationOf q 1531 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause896 (q : Snake 81) (h : Conditions q) : valuation q 56 = true ∨ valuation q 1531 = true := counterClause896 (baseVal q)

theorem block27 (q : Snake 81) (h : Conditions q) : B112E078.Block27 (valuation q) :=
  ⟨clause865 q h, clause866 q h, clause867 q h, clause868 q h, clause869 q h, clause870 q h, clause871 q h, clause872 q h, clause873 q h, clause874 q h, clause875 q h, clause876 q h, clause877 q h, clause878 q h, clause879 q h, clause880 q h, clause881 q h, clause882 q h, clause883 q h, clause884 q h, clause885 q h, clause886 q h, clause887 q h, clause888 q h, clause889 q h, clause890 q h, clause891 q h, clause892 q h, clause893 q h, clause894 q h, clause895 q h, clause896 q h⟩

end
end Snake9.Regrowth.E112078
