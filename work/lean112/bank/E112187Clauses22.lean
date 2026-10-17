import E112187Semantics
import B112E187Inputs
namespace Snake9.Regrowth.E112187
noncomputable section
local instance blockDec22 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause705 (q : Nat → Bool) : valuationOf q 1506 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1511 = true := by
  have hs : count1510 q = (countLit q [-39, -40]) + (countLit q [-41, -42]) := List.countP_append (p := literal q) (l₁ := [-39, -40]) (l₂ := [-41, -42])
  have hm := merge_two (literal (valuationOf q) (1506)) (literal (valuationOf q) (1508)) (literal (valuationOf q) (1511)) (countLit q [-39, -40]) (countLit q [-41, -42]) (count1510 q) 1 1 (meaning1506 q) (meaning1508 q) (meaning1511 q) hs
  change valuationOf q 1506 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1511 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause705 (q : Snake 81) (h : Conditions q) : valuation q 1506 = false ∨ valuation q 1508 = false ∨ valuation q 1511 = true := counterClause705 (baseVal q)

theorem counterClause706 (q : Nat → Bool) : valuationOf q 1506 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1512 = true := by
  have hs : count1510 q = (countLit q [-39, -40]) + (countLit q [-41, -42]) := List.countP_append (p := literal q) (l₁ := [-39, -40]) (l₂ := [-41, -42])
  have hm := merge_two (literal (valuationOf q) (1506)) (literal (valuationOf q) (1509)) (literal (valuationOf q) (1512)) (countLit q [-39, -40]) (countLit q [-41, -42]) (count1510 q) 1 2 (meaning1506 q) (meaning1509 q) (meaning1512 q) hs
  change valuationOf q 1506 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1512 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause706 (q : Snake 81) (h : Conditions q) : valuation q 1506 = false ∨ valuation q 1509 = false ∨ valuation q 1512 = true := counterClause706 (baseVal q)

theorem counterClause707 (q : Nat → Bool) : valuationOf q 1507 = false ∨ valuationOf q 1511 = true := by
  have hs : count1510 q = (countLit q [-39, -40]) + (countLit q [-41, -42]) := List.countP_append (p := literal q) (l₁ := [-39, -40]) (l₂ := [-41, -42])
  have hm := merge_left (literal (valuationOf q) (1507)) (literal (valuationOf q) (1511)) (countLit q [-39, -40]) (countLit q [-41, -42]) (count1510 q) 2 (meaning1507 q) (meaning1511 q) hs
  change valuationOf q 1507 = false ∨ valuationOf q 1511 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause707 (q : Snake 81) (h : Conditions q) : valuation q 1507 = false ∨ valuation q 1511 = true := counterClause707 (baseVal q)

theorem counterClause708 (q : Nat → Bool) : valuationOf q 1507 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1512 = true := by
  have hs : count1510 q = (countLit q [-39, -40]) + (countLit q [-41, -42]) := List.countP_append (p := literal q) (l₁ := [-39, -40]) (l₂ := [-41, -42])
  have hm := merge_two (literal (valuationOf q) (1507)) (literal (valuationOf q) (1508)) (literal (valuationOf q) (1512)) (countLit q [-39, -40]) (countLit q [-41, -42]) (count1510 q) 2 1 (meaning1507 q) (meaning1508 q) (meaning1512 q) hs
  change valuationOf q 1507 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1512 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause708 (q : Snake 81) (h : Conditions q) : valuation q 1507 = false ∨ valuation q 1508 = false ∨ valuation q 1512 = true := counterClause708 (baseVal q)

theorem counterClause709 (q : Nat → Bool) : valuationOf q 1510 = false ∨ valuationOf q 1514 = true := by
  have hs : count1514 q = (countLit q [-32, -34, -35]) + (countLit q [-39, -40, -41, -42]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35]) (l₂ := [-39, -40, -41, -42])
  have hm := merge_right (literal (valuationOf q) (1510)) (literal (valuationOf q) (1514)) (countLit q [-32, -34, -35]) (countLit q [-39, -40, -41, -42]) (count1514 q) 1 (meaning1510 q) (meaning1514 q) hs
  change valuationOf q 1510 = false ∨ valuationOf q 1514 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause709 (q : Snake 81) (h : Conditions q) : valuation q 1510 = false ∨ valuation q 1514 = true := counterClause709 (baseVal q)

theorem counterClause710 (q : Nat → Bool) : valuationOf q 1511 = false ∨ valuationOf q 1515 = true := by
  have hs : count1514 q = (countLit q [-32, -34, -35]) + (countLit q [-39, -40, -41, -42]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35]) (l₂ := [-39, -40, -41, -42])
  have hm := merge_right (literal (valuationOf q) (1511)) (literal (valuationOf q) (1515)) (countLit q [-32, -34, -35]) (countLit q [-39, -40, -41, -42]) (count1514 q) 2 (meaning1511 q) (meaning1515 q) hs
  change valuationOf q 1511 = false ∨ valuationOf q 1515 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause710 (q : Snake 81) (h : Conditions q) : valuation q 1511 = false ∨ valuation q 1515 = true := counterClause710 (baseVal q)

theorem counterClause711 (q : Nat → Bool) : valuationOf q 1503 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1515 = true := by
  have hs : count1514 q = (countLit q [-32, -34, -35]) + (countLit q [-39, -40, -41, -42]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35]) (l₂ := [-39, -40, -41, -42])
  have hm := merge_two (literal (valuationOf q) (1503)) (literal (valuationOf q) (1510)) (literal (valuationOf q) (1515)) (countLit q [-32, -34, -35]) (countLit q [-39, -40, -41, -42]) (count1514 q) 1 1 (meaning1503 q) (meaning1510 q) (meaning1515 q) hs
  change valuationOf q 1503 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1515 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause711 (q : Snake 81) (h : Conditions q) : valuation q 1503 = false ∨ valuation q 1510 = false ∨ valuation q 1515 = true := counterClause711 (baseVal q)

theorem counterClause712 (q : Nat → Bool) : valuationOf q 1503 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1516 = true := by
  have hs : count1514 q = (countLit q [-32, -34, -35]) + (countLit q [-39, -40, -41, -42]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35]) (l₂ := [-39, -40, -41, -42])
  have hm := merge_two (literal (valuationOf q) (1503)) (literal (valuationOf q) (1511)) (literal (valuationOf q) (1516)) (countLit q [-32, -34, -35]) (countLit q [-39, -40, -41, -42]) (count1514 q) 1 2 (meaning1503 q) (meaning1511 q) (meaning1516 q) hs
  change valuationOf q 1503 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1516 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause712 (q : Snake 81) (h : Conditions q) : valuation q 1503 = false ∨ valuation q 1511 = false ∨ valuation q 1516 = true := counterClause712 (baseVal q)

theorem counterClause713 (q : Nat → Bool) : valuationOf q 1503 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1517 = true := by
  have hs : count1514 q = (countLit q [-32, -34, -35]) + (countLit q [-39, -40, -41, -42]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35]) (l₂ := [-39, -40, -41, -42])
  have hm := merge_two (literal (valuationOf q) (1503)) (literal (valuationOf q) (1512)) (literal (valuationOf q) (1517)) (countLit q [-32, -34, -35]) (countLit q [-39, -40, -41, -42]) (count1514 q) 1 3 (meaning1503 q) (meaning1512 q) (meaning1517 q) hs
  change valuationOf q 1503 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1517 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause713 (q : Snake 81) (h : Conditions q) : valuation q 1503 = false ∨ valuation q 1512 = false ∨ valuation q 1517 = true := counterClause713 (baseVal q)

theorem counterClause714 (q : Nat → Bool) : valuationOf q 1504 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1516 = true := by
  have hs : count1514 q = (countLit q [-32, -34, -35]) + (countLit q [-39, -40, -41, -42]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35]) (l₂ := [-39, -40, -41, -42])
  have hm := merge_two (literal (valuationOf q) (1504)) (literal (valuationOf q) (1510)) (literal (valuationOf q) (1516)) (countLit q [-32, -34, -35]) (countLit q [-39, -40, -41, -42]) (count1514 q) 2 1 (meaning1504 q) (meaning1510 q) (meaning1516 q) hs
  change valuationOf q 1504 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1516 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause714 (q : Snake 81) (h : Conditions q) : valuation q 1504 = false ∨ valuation q 1510 = false ∨ valuation q 1516 = true := counterClause714 (baseVal q)

theorem counterClause715 (q : Nat → Bool) : valuationOf q 1504 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1517 = true := by
  have hs : count1514 q = (countLit q [-32, -34, -35]) + (countLit q [-39, -40, -41, -42]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35]) (l₂ := [-39, -40, -41, -42])
  have hm := merge_two (literal (valuationOf q) (1504)) (literal (valuationOf q) (1511)) (literal (valuationOf q) (1517)) (countLit q [-32, -34, -35]) (countLit q [-39, -40, -41, -42]) (count1514 q) 2 2 (meaning1504 q) (meaning1511 q) (meaning1517 q) hs
  change valuationOf q 1504 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1517 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause715 (q : Snake 81) (h : Conditions q) : valuation q 1504 = false ∨ valuation q 1511 = false ∨ valuation q 1517 = true := counterClause715 (baseVal q)

theorem counterClause716 (q : Nat → Bool) : valuationOf q 1504 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1518 = true := by
  have hs : count1514 q = (countLit q [-32, -34, -35]) + (countLit q [-39, -40, -41, -42]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35]) (l₂ := [-39, -40, -41, -42])
  have hm := merge_two (literal (valuationOf q) (1504)) (literal (valuationOf q) (1512)) (literal (valuationOf q) (1518)) (countLit q [-32, -34, -35]) (countLit q [-39, -40, -41, -42]) (count1514 q) 2 3 (meaning1504 q) (meaning1512 q) (meaning1518 q) hs
  change valuationOf q 1504 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1518 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause716 (q : Snake 81) (h : Conditions q) : valuation q 1504 = false ∨ valuation q 1512 = false ∨ valuation q 1518 = true := counterClause716 (baseVal q)

theorem counterClause717 (q : Nat → Bool) : valuationOf q 1505 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1517 = true := by
  have hs : count1514 q = (countLit q [-32, -34, -35]) + (countLit q [-39, -40, -41, -42]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35]) (l₂ := [-39, -40, -41, -42])
  have hm := merge_two (literal (valuationOf q) (1505)) (literal (valuationOf q) (1510)) (literal (valuationOf q) (1517)) (countLit q [-32, -34, -35]) (countLit q [-39, -40, -41, -42]) (count1514 q) 3 1 (meaning1505 q) (meaning1510 q) (meaning1517 q) hs
  change valuationOf q 1505 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1517 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause717 (q : Snake 81) (h : Conditions q) : valuation q 1505 = false ∨ valuation q 1510 = false ∨ valuation q 1517 = true := counterClause717 (baseVal q)

theorem counterClause718 (q : Nat → Bool) : valuationOf q 1505 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1518 = true := by
  have hs : count1514 q = (countLit q [-32, -34, -35]) + (countLit q [-39, -40, -41, -42]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35]) (l₂ := [-39, -40, -41, -42])
  have hm := merge_two (literal (valuationOf q) (1505)) (literal (valuationOf q) (1511)) (literal (valuationOf q) (1518)) (countLit q [-32, -34, -35]) (countLit q [-39, -40, -41, -42]) (count1514 q) 3 2 (meaning1505 q) (meaning1511 q) (meaning1518 q) hs
  change valuationOf q 1505 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1518 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause718 (q : Snake 81) (h : Conditions q) : valuation q 1505 = false ∨ valuation q 1511 = false ∨ valuation q 1518 = true := counterClause718 (baseVal q)

theorem counterClause719 (q : Nat → Bool) : valuationOf q 48 = true ∨ valuationOf q 1521 = true := by
  have hs : count1521 q = (countLit q [-46]) + (countLit q [-48]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-48])
  have hm := merge_right (literal (valuationOf q) (-48)) (literal (valuationOf q) (1521)) (countLit q [-46]) (countLit q [-48]) (count1521 q) 1 (meaningNeg48 q) (meaning1521 q) hs
  change (! (valuationOf q 48)) = false ∨ valuationOf q 1521 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause719 (q : Snake 81) (h : Conditions q) : valuation q 48 = true ∨ valuation q 1521 = true := counterClause719 (baseVal q)

theorem counterClause720 (q : Nat → Bool) : valuationOf q 46 = true ∨ valuationOf q 1521 = true := by
  have hs : count1521 q = (countLit q [-46]) + (countLit q [-48]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-48])
  have hm := merge_left (literal (valuationOf q) (-46)) (literal (valuationOf q) (1521)) (countLit q [-46]) (countLit q [-48]) (count1521 q) 1 (meaningNeg46 q) (meaning1521 q) hs
  change (! (valuationOf q 46)) = false ∨ valuationOf q 1521 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause720 (q : Snake 81) (h : Conditions q) : valuation q 46 = true ∨ valuation q 1521 = true := counterClause720 (baseVal q)

theorem counterClause721 (q : Nat → Bool) : valuationOf q 46 = true ∨ valuationOf q 48 = true ∨ valuationOf q 1522 = true := by
  have hs : count1521 q = (countLit q [-46]) + (countLit q [-48]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-48])
  have hm := merge_two (literal (valuationOf q) (-46)) (literal (valuationOf q) (-48)) (literal (valuationOf q) (1522)) (countLit q [-46]) (countLit q [-48]) (count1521 q) 1 1 (meaningNeg46 q) (meaningNeg48 q) (meaning1522 q) hs
  change (! (valuationOf q 46)) = false ∨ (! (valuationOf q 48)) = false ∨ valuationOf q 1522 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause721 (q : Snake 81) (h : Conditions q) : valuation q 46 = true ∨ valuation q 48 = true ∨ valuation q 1522 = true := counterClause721 (baseVal q)

theorem counterClause722 (q : Nat → Bool) : valuationOf q 51 = true ∨ valuationOf q 1523 = true := by
  have hs : count1523 q = (countLit q [-49]) + (countLit q [-51]) := List.countP_append (p := literal q) (l₁ := [-49]) (l₂ := [-51])
  have hm := merge_right (literal (valuationOf q) (-51)) (literal (valuationOf q) (1523)) (countLit q [-49]) (countLit q [-51]) (count1523 q) 1 (meaningNeg51 q) (meaning1523 q) hs
  change (! (valuationOf q 51)) = false ∨ valuationOf q 1523 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause722 (q : Snake 81) (h : Conditions q) : valuation q 51 = true ∨ valuation q 1523 = true := counterClause722 (baseVal q)

theorem counterClause723 (q : Nat → Bool) : valuationOf q 49 = true ∨ valuationOf q 1523 = true := by
  have hs : count1523 q = (countLit q [-49]) + (countLit q [-51]) := List.countP_append (p := literal q) (l₁ := [-49]) (l₂ := [-51])
  have hm := merge_left (literal (valuationOf q) (-49)) (literal (valuationOf q) (1523)) (countLit q [-49]) (countLit q [-51]) (count1523 q) 1 (meaningNeg49 q) (meaning1523 q) hs
  change (! (valuationOf q 49)) = false ∨ valuationOf q 1523 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause723 (q : Snake 81) (h : Conditions q) : valuation q 49 = true ∨ valuation q 1523 = true := counterClause723 (baseVal q)

theorem counterClause724 (q : Nat → Bool) : valuationOf q 49 = true ∨ valuationOf q 51 = true ∨ valuationOf q 1524 = true := by
  have hs : count1523 q = (countLit q [-49]) + (countLit q [-51]) := List.countP_append (p := literal q) (l₁ := [-49]) (l₂ := [-51])
  have hm := merge_two (literal (valuationOf q) (-49)) (literal (valuationOf q) (-51)) (literal (valuationOf q) (1524)) (countLit q [-49]) (countLit q [-51]) (count1523 q) 1 1 (meaningNeg49 q) (meaningNeg51 q) (meaning1524 q) hs
  change (! (valuationOf q 49)) = false ∨ (! (valuationOf q 51)) = false ∨ valuationOf q 1524 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause724 (q : Snake 81) (h : Conditions q) : valuation q 49 = true ∨ valuation q 51 = true ∨ valuation q 1524 = true := counterClause724 (baseVal q)

theorem counterClause725 (q : Nat → Bool) : valuationOf q 1523 = false ∨ valuationOf q 1525 = true := by
  have hs : count1525 q = (countLit q [-46, -48]) + (countLit q [-49, -51]) := List.countP_append (p := literal q) (l₁ := [-46, -48]) (l₂ := [-49, -51])
  have hm := merge_right (literal (valuationOf q) (1523)) (literal (valuationOf q) (1525)) (countLit q [-46, -48]) (countLit q [-49, -51]) (count1525 q) 1 (meaning1523 q) (meaning1525 q) hs
  change valuationOf q 1523 = false ∨ valuationOf q 1525 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause725 (q : Snake 81) (h : Conditions q) : valuation q 1523 = false ∨ valuation q 1525 = true := counterClause725 (baseVal q)

theorem counterClause726 (q : Nat → Bool) : valuationOf q 1524 = false ∨ valuationOf q 1526 = true := by
  have hs : count1525 q = (countLit q [-46, -48]) + (countLit q [-49, -51]) := List.countP_append (p := literal q) (l₁ := [-46, -48]) (l₂ := [-49, -51])
  have hm := merge_right (literal (valuationOf q) (1524)) (literal (valuationOf q) (1526)) (countLit q [-46, -48]) (countLit q [-49, -51]) (count1525 q) 2 (meaning1524 q) (meaning1526 q) hs
  change valuationOf q 1524 = false ∨ valuationOf q 1526 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause726 (q : Snake 81) (h : Conditions q) : valuation q 1524 = false ∨ valuation q 1526 = true := counterClause726 (baseVal q)

theorem counterClause727 (q : Nat → Bool) : valuationOf q 1521 = false ∨ valuationOf q 1525 = true := by
  have hs : count1525 q = (countLit q [-46, -48]) + (countLit q [-49, -51]) := List.countP_append (p := literal q) (l₁ := [-46, -48]) (l₂ := [-49, -51])
  have hm := merge_left (literal (valuationOf q) (1521)) (literal (valuationOf q) (1525)) (countLit q [-46, -48]) (countLit q [-49, -51]) (count1525 q) 1 (meaning1521 q) (meaning1525 q) hs
  change valuationOf q 1521 = false ∨ valuationOf q 1525 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause727 (q : Snake 81) (h : Conditions q) : valuation q 1521 = false ∨ valuation q 1525 = true := counterClause727 (baseVal q)

theorem counterClause728 (q : Nat → Bool) : valuationOf q 1521 = false ∨ valuationOf q 1523 = false ∨ valuationOf q 1526 = true := by
  have hs : count1525 q = (countLit q [-46, -48]) + (countLit q [-49, -51]) := List.countP_append (p := literal q) (l₁ := [-46, -48]) (l₂ := [-49, -51])
  have hm := merge_two (literal (valuationOf q) (1521)) (literal (valuationOf q) (1523)) (literal (valuationOf q) (1526)) (countLit q [-46, -48]) (countLit q [-49, -51]) (count1525 q) 1 1 (meaning1521 q) (meaning1523 q) (meaning1526 q) hs
  change valuationOf q 1521 = false ∨ valuationOf q 1523 = false ∨ valuationOf q 1526 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause728 (q : Snake 81) (h : Conditions q) : valuation q 1521 = false ∨ valuation q 1523 = false ∨ valuation q 1526 = true := counterClause728 (baseVal q)

theorem counterClause729 (q : Nat → Bool) : valuationOf q 1521 = false ∨ valuationOf q 1524 = false ∨ valuationOf q 1527 = true := by
  have hs : count1525 q = (countLit q [-46, -48]) + (countLit q [-49, -51]) := List.countP_append (p := literal q) (l₁ := [-46, -48]) (l₂ := [-49, -51])
  have hm := merge_two (literal (valuationOf q) (1521)) (literal (valuationOf q) (1524)) (literal (valuationOf q) (1527)) (countLit q [-46, -48]) (countLit q [-49, -51]) (count1525 q) 1 2 (meaning1521 q) (meaning1524 q) (meaning1527 q) hs
  change valuationOf q 1521 = false ∨ valuationOf q 1524 = false ∨ valuationOf q 1527 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause729 (q : Snake 81) (h : Conditions q) : valuation q 1521 = false ∨ valuation q 1524 = false ∨ valuation q 1527 = true := counterClause729 (baseVal q)

theorem counterClause730 (q : Nat → Bool) : valuationOf q 1522 = false ∨ valuationOf q 1526 = true := by
  have hs : count1525 q = (countLit q [-46, -48]) + (countLit q [-49, -51]) := List.countP_append (p := literal q) (l₁ := [-46, -48]) (l₂ := [-49, -51])
  have hm := merge_left (literal (valuationOf q) (1522)) (literal (valuationOf q) (1526)) (countLit q [-46, -48]) (countLit q [-49, -51]) (count1525 q) 2 (meaning1522 q) (meaning1526 q) hs
  change valuationOf q 1522 = false ∨ valuationOf q 1526 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause730 (q : Snake 81) (h : Conditions q) : valuation q 1522 = false ∨ valuation q 1526 = true := counterClause730 (baseVal q)

theorem counterClause731 (q : Nat → Bool) : valuationOf q 1522 = false ∨ valuationOf q 1523 = false ∨ valuationOf q 1527 = true := by
  have hs : count1525 q = (countLit q [-46, -48]) + (countLit q [-49, -51]) := List.countP_append (p := literal q) (l₁ := [-46, -48]) (l₂ := [-49, -51])
  have hm := merge_two (literal (valuationOf q) (1522)) (literal (valuationOf q) (1523)) (literal (valuationOf q) (1527)) (countLit q [-46, -48]) (countLit q [-49, -51]) (count1525 q) 2 1 (meaning1522 q) (meaning1523 q) (meaning1527 q) hs
  change valuationOf q 1522 = false ∨ valuationOf q 1523 = false ∨ valuationOf q 1527 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause731 (q : Snake 81) (h : Conditions q) : valuation q 1522 = false ∨ valuation q 1523 = false ∨ valuation q 1527 = true := counterClause731 (baseVal q)

theorem counterClause732 (q : Nat → Bool) : valuationOf q 56 = true ∨ valuationOf q 1529 = true := by
  have hs : count1529 q = (countLit q [-52]) + (countLit q [-56]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-56])
  have hm := merge_right (literal (valuationOf q) (-56)) (literal (valuationOf q) (1529)) (countLit q [-52]) (countLit q [-56]) (count1529 q) 1 (meaningNeg56 q) (meaning1529 q) hs
  change (! (valuationOf q 56)) = false ∨ valuationOf q 1529 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause732 (q : Snake 81) (h : Conditions q) : valuation q 56 = true ∨ valuation q 1529 = true := counterClause732 (baseVal q)

theorem counterClause733 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 1529 = true := by
  have hs : count1529 q = (countLit q [-52]) + (countLit q [-56]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-56])
  have hm := merge_left (literal (valuationOf q) (-52)) (literal (valuationOf q) (1529)) (countLit q [-52]) (countLit q [-56]) (count1529 q) 1 (meaningNeg52 q) (meaning1529 q) hs
  change (! (valuationOf q 52)) = false ∨ valuationOf q 1529 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause733 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 1529 = true := counterClause733 (baseVal q)

theorem counterClause734 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 56 = true ∨ valuationOf q 1530 = true := by
  have hs : count1529 q = (countLit q [-52]) + (countLit q [-56]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-56])
  have hm := merge_two (literal (valuationOf q) (-52)) (literal (valuationOf q) (-56)) (literal (valuationOf q) (1530)) (countLit q [-52]) (countLit q [-56]) (count1529 q) 1 1 (meaningNeg52 q) (meaningNeg56 q) (meaning1530 q) hs
  change (! (valuationOf q 52)) = false ∨ (! (valuationOf q 56)) = false ∨ valuationOf q 1530 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause734 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 56 = true ∨ valuation q 1530 = true := counterClause734 (baseVal q)

theorem counterClause735 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 1531 = true := by
  have hs : count1531 q = (countLit q [-58]) + (countLit q [-59]) := List.countP_append (p := literal q) (l₁ := [-58]) (l₂ := [-59])
  have hm := merge_right (literal (valuationOf q) (-59)) (literal (valuationOf q) (1531)) (countLit q [-58]) (countLit q [-59]) (count1531 q) 1 (meaningNeg59 q) (meaning1531 q) hs
  change (! (valuationOf q 59)) = false ∨ valuationOf q 1531 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause735 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 1531 = true := counterClause735 (baseVal q)

theorem counterClause736 (q : Nat → Bool) : valuationOf q 58 = true ∨ valuationOf q 1531 = true := by
  have hs : count1531 q = (countLit q [-58]) + (countLit q [-59]) := List.countP_append (p := literal q) (l₁ := [-58]) (l₂ := [-59])
  have hm := merge_left (literal (valuationOf q) (-58)) (literal (valuationOf q) (1531)) (countLit q [-58]) (countLit q [-59]) (count1531 q) 1 (meaningNeg58 q) (meaning1531 q) hs
  change (! (valuationOf q 58)) = false ∨ valuationOf q 1531 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause736 (q : Snake 81) (h : Conditions q) : valuation q 58 = true ∨ valuation q 1531 = true := counterClause736 (baseVal q)

theorem block22 (q : Snake 81) (h : Conditions q) : B112E187.Block22 (valuation q) :=
  ⟨clause705 q h, clause706 q h, clause707 q h, clause708 q h, clause709 q h, clause710 q h, clause711 q h, clause712 q h, clause713 q h, clause714 q h, clause715 q h, clause716 q h, clause717 q h, clause718 q h, clause719 q h, clause720 q h, clause721 q h, clause722 q h, clause723 q h, clause724 q h, clause725 q h, clause726 q h, clause727 q h, clause728 q h, clause729 q h, clause730 q h, clause731 q h, clause732 q h, clause733 q h, clause734 q h, clause735 q h, clause736 q h⟩

end
end Snake9.Regrowth.E112187
