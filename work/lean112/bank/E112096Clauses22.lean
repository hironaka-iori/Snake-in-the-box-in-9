import E112096Semantics
import B112E096Inputs
namespace Snake9.Regrowth.E112096
noncomputable section
local instance blockDec22 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause705 (q : Nat → Bool) : valuationOf q 1500 = false ∨ valuationOf q 1502 = false ∨ valuationOf q 1505 = true := by
  have hs : count1504 q = (countLit q [-52, -54]) + (countLit q [-56, -58]) := List.countP_append (p := literal q) (l₁ := [-52, -54]) (l₂ := [-56, -58])
  have hm := merge_two (literal (valuationOf q) (1500)) (literal (valuationOf q) (1502)) (literal (valuationOf q) (1505)) (countLit q [-52, -54]) (countLit q [-56, -58]) (count1504 q) 1 1 (meaning1500 q) (meaning1502 q) (meaning1505 q) hs
  change valuationOf q 1500 = false ∨ valuationOf q 1502 = false ∨ valuationOf q 1505 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause705 (q : Snake 81) (h : Conditions q) : valuation q 1500 = false ∨ valuation q 1502 = false ∨ valuation q 1505 = true := counterClause705 (baseVal q)

theorem counterClause706 (q : Nat → Bool) : valuationOf q 1501 = false ∨ valuationOf q 1505 = true := by
  have hs : count1504 q = (countLit q [-52, -54]) + (countLit q [-56, -58]) := List.countP_append (p := literal q) (l₁ := [-52, -54]) (l₂ := [-56, -58])
  have hm := merge_left (literal (valuationOf q) (1501)) (literal (valuationOf q) (1505)) (countLit q [-52, -54]) (countLit q [-56, -58]) (count1504 q) 2 (meaning1501 q) (meaning1505 q) hs
  change valuationOf q 1501 = false ∨ valuationOf q 1505 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause706 (q : Snake 81) (h : Conditions q) : valuation q 1501 = false ∨ valuation q 1505 = true := counterClause706 (baseVal q)

theorem counterClause707 (q : Nat → Bool) : valuationOf q 1504 = false ∨ valuationOf q 1508 = true := by
  have hs : count1508 q = (countLit q [-44, -47, -48, -51]) + (countLit q [-52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-44, -47, -48, -51]) (l₂ := [-52, -54, -56, -58])
  have hm := merge_right (literal (valuationOf q) (1504)) (literal (valuationOf q) (1508)) (countLit q [-44, -47, -48, -51]) (countLit q [-52, -54, -56, -58]) (count1508 q) 1 (meaning1504 q) (meaning1508 q) hs
  change valuationOf q 1504 = false ∨ valuationOf q 1508 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause707 (q : Snake 81) (h : Conditions q) : valuation q 1504 = false ∨ valuation q 1508 = true := counterClause707 (baseVal q)

theorem counterClause708 (q : Nat → Bool) : valuationOf q 1505 = false ∨ valuationOf q 1509 = true := by
  have hs : count1508 q = (countLit q [-44, -47, -48, -51]) + (countLit q [-52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-44, -47, -48, -51]) (l₂ := [-52, -54, -56, -58])
  have hm := merge_right (literal (valuationOf q) (1505)) (literal (valuationOf q) (1509)) (countLit q [-44, -47, -48, -51]) (countLit q [-52, -54, -56, -58]) (count1508 q) 2 (meaning1505 q) (meaning1509 q) hs
  change valuationOf q 1505 = false ∨ valuationOf q 1509 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause708 (q : Snake 81) (h : Conditions q) : valuation q 1505 = false ∨ valuation q 1509 = true := counterClause708 (baseVal q)

theorem counterClause709 (q : Nat → Bool) : valuationOf q 1496 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1509 = true := by
  have hs : count1508 q = (countLit q [-44, -47, -48, -51]) + (countLit q [-52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-44, -47, -48, -51]) (l₂ := [-52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1496)) (literal (valuationOf q) (1504)) (literal (valuationOf q) (1509)) (countLit q [-44, -47, -48, -51]) (countLit q [-52, -54, -56, -58]) (count1508 q) 1 1 (meaning1496 q) (meaning1504 q) (meaning1509 q) hs
  change valuationOf q 1496 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1509 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause709 (q : Snake 81) (h : Conditions q) : valuation q 1496 = false ∨ valuation q 1504 = false ∨ valuation q 1509 = true := counterClause709 (baseVal q)

theorem counterClause710 (q : Nat → Bool) : valuationOf q 1496 = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1510 = true := by
  have hs : count1508 q = (countLit q [-44, -47, -48, -51]) + (countLit q [-52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-44, -47, -48, -51]) (l₂ := [-52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1496)) (literal (valuationOf q) (1505)) (literal (valuationOf q) (1510)) (countLit q [-44, -47, -48, -51]) (countLit q [-52, -54, -56, -58]) (count1508 q) 1 2 (meaning1496 q) (meaning1505 q) (meaning1510 q) hs
  change valuationOf q 1496 = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1510 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause710 (q : Snake 81) (h : Conditions q) : valuation q 1496 = false ∨ valuation q 1505 = false ∨ valuation q 1510 = true := counterClause710 (baseVal q)

theorem counterClause711 (q : Nat → Bool) : valuationOf q 1497 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1510 = true := by
  have hs : count1508 q = (countLit q [-44, -47, -48, -51]) + (countLit q [-52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-44, -47, -48, -51]) (l₂ := [-52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1497)) (literal (valuationOf q) (1504)) (literal (valuationOf q) (1510)) (countLit q [-44, -47, -48, -51]) (countLit q [-52, -54, -56, -58]) (count1508 q) 2 1 (meaning1497 q) (meaning1504 q) (meaning1510 q) hs
  change valuationOf q 1497 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1510 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause711 (q : Snake 81) (h : Conditions q) : valuation q 1497 = false ∨ valuation q 1504 = false ∨ valuation q 1510 = true := counterClause711 (baseVal q)

theorem counterClause712 (q : Nat → Bool) : valuationOf q 1497 = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1511 = true := by
  have hs : count1508 q = (countLit q [-44, -47, -48, -51]) + (countLit q [-52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-44, -47, -48, -51]) (l₂ := [-52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1497)) (literal (valuationOf q) (1505)) (literal (valuationOf q) (1511)) (countLit q [-44, -47, -48, -51]) (countLit q [-52, -54, -56, -58]) (count1508 q) 2 2 (meaning1497 q) (meaning1505 q) (meaning1511 q) hs
  change valuationOf q 1497 = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1511 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause712 (q : Snake 81) (h : Conditions q) : valuation q 1497 = false ∨ valuation q 1505 = false ∨ valuation q 1511 = true := counterClause712 (baseVal q)

theorem counterClause713 (q : Nat → Bool) : valuationOf q 1498 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1511 = true := by
  have hs : count1508 q = (countLit q [-44, -47, -48, -51]) + (countLit q [-52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-44, -47, -48, -51]) (l₂ := [-52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1498)) (literal (valuationOf q) (1504)) (literal (valuationOf q) (1511)) (countLit q [-44, -47, -48, -51]) (countLit q [-52, -54, -56, -58]) (count1508 q) 3 1 (meaning1498 q) (meaning1504 q) (meaning1511 q) hs
  change valuationOf q 1498 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1511 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause713 (q : Snake 81) (h : Conditions q) : valuation q 1498 = false ∨ valuation q 1504 = false ∨ valuation q 1511 = true := counterClause713 (baseVal q)

theorem counterClause714 (q : Nat → Bool) : valuationOf q 1508 = false ∨ valuationOf q 1516 = true := by
  have hs : count1516 q = (countLit q [-31, -34, -35, -37, -39, -41, -43]) + (countLit q [-44, -47, -48, -51, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-31, -34, -35, -37, -39, -41, -43]) (l₂ := [-44, -47, -48, -51, -52, -54, -56, -58])
  have hm := merge_right (literal (valuationOf q) (1508)) (literal (valuationOf q) (1516)) (countLit q [-31, -34, -35, -37, -39, -41, -43]) (countLit q [-44, -47, -48, -51, -52, -54, -56, -58]) (count1516 q) 1 (meaning1508 q) (meaning1516 q) hs
  change valuationOf q 1508 = false ∨ valuationOf q 1516 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause714 (q : Snake 81) (h : Conditions q) : valuation q 1508 = false ∨ valuation q 1516 = true := counterClause714 (baseVal q)

theorem counterClause715 (q : Nat → Bool) : valuationOf q 1509 = false ∨ valuationOf q 1517 = true := by
  have hs : count1516 q = (countLit q [-31, -34, -35, -37, -39, -41, -43]) + (countLit q [-44, -47, -48, -51, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-31, -34, -35, -37, -39, -41, -43]) (l₂ := [-44, -47, -48, -51, -52, -54, -56, -58])
  have hm := merge_right (literal (valuationOf q) (1509)) (literal (valuationOf q) (1517)) (countLit q [-31, -34, -35, -37, -39, -41, -43]) (countLit q [-44, -47, -48, -51, -52, -54, -56, -58]) (count1516 q) 2 (meaning1509 q) (meaning1517 q) hs
  change valuationOf q 1509 = false ∨ valuationOf q 1517 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause715 (q : Snake 81) (h : Conditions q) : valuation q 1509 = false ∨ valuation q 1517 = true := counterClause715 (baseVal q)

theorem counterClause716 (q : Nat → Bool) : valuationOf q 1510 = false ∨ valuationOf q 1518 = true := by
  have hs : count1516 q = (countLit q [-31, -34, -35, -37, -39, -41, -43]) + (countLit q [-44, -47, -48, -51, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-31, -34, -35, -37, -39, -41, -43]) (l₂ := [-44, -47, -48, -51, -52, -54, -56, -58])
  have hm := merge_right (literal (valuationOf q) (1510)) (literal (valuationOf q) (1518)) (countLit q [-31, -34, -35, -37, -39, -41, -43]) (countLit q [-44, -47, -48, -51, -52, -54, -56, -58]) (count1516 q) 3 (meaning1510 q) (meaning1518 q) hs
  change valuationOf q 1510 = false ∨ valuationOf q 1518 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause716 (q : Snake 81) (h : Conditions q) : valuation q 1510 = false ∨ valuation q 1518 = true := counterClause716 (baseVal q)

theorem counterClause717 (q : Nat → Bool) : valuationOf q 1511 = false ∨ valuationOf q 1519 = true := by
  have hs : count1516 q = (countLit q [-31, -34, -35, -37, -39, -41, -43]) + (countLit q [-44, -47, -48, -51, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-31, -34, -35, -37, -39, -41, -43]) (l₂ := [-44, -47, -48, -51, -52, -54, -56, -58])
  have hm := merge_right (literal (valuationOf q) (1511)) (literal (valuationOf q) (1519)) (countLit q [-31, -34, -35, -37, -39, -41, -43]) (countLit q [-44, -47, -48, -51, -52, -54, -56, -58]) (count1516 q) 4 (meaning1511 q) (meaning1519 q) hs
  change valuationOf q 1511 = false ∨ valuationOf q 1519 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause717 (q : Snake 81) (h : Conditions q) : valuation q 1511 = false ∨ valuation q 1519 = true := counterClause717 (baseVal q)

theorem counterClause718 (q : Nat → Bool) : valuationOf q 1485 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1517 = true := by
  have hs : count1516 q = (countLit q [-31, -34, -35, -37, -39, -41, -43]) + (countLit q [-44, -47, -48, -51, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-31, -34, -35, -37, -39, -41, -43]) (l₂ := [-44, -47, -48, -51, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1485)) (literal (valuationOf q) (1508)) (literal (valuationOf q) (1517)) (countLit q [-31, -34, -35, -37, -39, -41, -43]) (countLit q [-44, -47, -48, -51, -52, -54, -56, -58]) (count1516 q) 1 1 (meaning1485 q) (meaning1508 q) (meaning1517 q) hs
  change valuationOf q 1485 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1517 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause718 (q : Snake 81) (h : Conditions q) : valuation q 1485 = false ∨ valuation q 1508 = false ∨ valuation q 1517 = true := counterClause718 (baseVal q)

theorem counterClause719 (q : Nat → Bool) : valuationOf q 1485 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1518 = true := by
  have hs : count1516 q = (countLit q [-31, -34, -35, -37, -39, -41, -43]) + (countLit q [-44, -47, -48, -51, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-31, -34, -35, -37, -39, -41, -43]) (l₂ := [-44, -47, -48, -51, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1485)) (literal (valuationOf q) (1509)) (literal (valuationOf q) (1518)) (countLit q [-31, -34, -35, -37, -39, -41, -43]) (countLit q [-44, -47, -48, -51, -52, -54, -56, -58]) (count1516 q) 1 2 (meaning1485 q) (meaning1509 q) (meaning1518 q) hs
  change valuationOf q 1485 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1518 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause719 (q : Snake 81) (h : Conditions q) : valuation q 1485 = false ∨ valuation q 1509 = false ∨ valuation q 1518 = true := counterClause719 (baseVal q)

theorem counterClause720 (q : Nat → Bool) : valuationOf q 1485 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1519 = true := by
  have hs : count1516 q = (countLit q [-31, -34, -35, -37, -39, -41, -43]) + (countLit q [-44, -47, -48, -51, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-31, -34, -35, -37, -39, -41, -43]) (l₂ := [-44, -47, -48, -51, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1485)) (literal (valuationOf q) (1510)) (literal (valuationOf q) (1519)) (countLit q [-31, -34, -35, -37, -39, -41, -43]) (countLit q [-44, -47, -48, -51, -52, -54, -56, -58]) (count1516 q) 1 3 (meaning1485 q) (meaning1510 q) (meaning1519 q) hs
  change valuationOf q 1485 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1519 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause720 (q : Snake 81) (h : Conditions q) : valuation q 1485 = false ∨ valuation q 1510 = false ∨ valuation q 1519 = true := counterClause720 (baseVal q)

theorem counterClause721 (q : Nat → Bool) : valuationOf q 1485 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1520 = true := by
  have hs : count1516 q = (countLit q [-31, -34, -35, -37, -39, -41, -43]) + (countLit q [-44, -47, -48, -51, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-31, -34, -35, -37, -39, -41, -43]) (l₂ := [-44, -47, -48, -51, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1485)) (literal (valuationOf q) (1511)) (literal (valuationOf q) (1520)) (countLit q [-31, -34, -35, -37, -39, -41, -43]) (countLit q [-44, -47, -48, -51, -52, -54, -56, -58]) (count1516 q) 1 4 (meaning1485 q) (meaning1511 q) (meaning1520 q) hs
  change valuationOf q 1485 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause721 (q : Snake 81) (h : Conditions q) : valuation q 1485 = false ∨ valuation q 1511 = false ∨ valuation q 1520 = true := counterClause721 (baseVal q)

theorem counterClause722 (q : Nat → Bool) : valuationOf q 1486 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1518 = true := by
  have hs : count1516 q = (countLit q [-31, -34, -35, -37, -39, -41, -43]) + (countLit q [-44, -47, -48, -51, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-31, -34, -35, -37, -39, -41, -43]) (l₂ := [-44, -47, -48, -51, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1486)) (literal (valuationOf q) (1508)) (literal (valuationOf q) (1518)) (countLit q [-31, -34, -35, -37, -39, -41, -43]) (countLit q [-44, -47, -48, -51, -52, -54, -56, -58]) (count1516 q) 2 1 (meaning1486 q) (meaning1508 q) (meaning1518 q) hs
  change valuationOf q 1486 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1518 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause722 (q : Snake 81) (h : Conditions q) : valuation q 1486 = false ∨ valuation q 1508 = false ∨ valuation q 1518 = true := counterClause722 (baseVal q)

theorem counterClause723 (q : Nat → Bool) : valuationOf q 1486 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1519 = true := by
  have hs : count1516 q = (countLit q [-31, -34, -35, -37, -39, -41, -43]) + (countLit q [-44, -47, -48, -51, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-31, -34, -35, -37, -39, -41, -43]) (l₂ := [-44, -47, -48, -51, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1486)) (literal (valuationOf q) (1509)) (literal (valuationOf q) (1519)) (countLit q [-31, -34, -35, -37, -39, -41, -43]) (countLit q [-44, -47, -48, -51, -52, -54, -56, -58]) (count1516 q) 2 2 (meaning1486 q) (meaning1509 q) (meaning1519 q) hs
  change valuationOf q 1486 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1519 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause723 (q : Snake 81) (h : Conditions q) : valuation q 1486 = false ∨ valuation q 1509 = false ∨ valuation q 1519 = true := counterClause723 (baseVal q)

theorem counterClause724 (q : Nat → Bool) : valuationOf q 1486 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1520 = true := by
  have hs : count1516 q = (countLit q [-31, -34, -35, -37, -39, -41, -43]) + (countLit q [-44, -47, -48, -51, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-31, -34, -35, -37, -39, -41, -43]) (l₂ := [-44, -47, -48, -51, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1486)) (literal (valuationOf q) (1510)) (literal (valuationOf q) (1520)) (countLit q [-31, -34, -35, -37, -39, -41, -43]) (countLit q [-44, -47, -48, -51, -52, -54, -56, -58]) (count1516 q) 2 3 (meaning1486 q) (meaning1510 q) (meaning1520 q) hs
  change valuationOf q 1486 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause724 (q : Snake 81) (h : Conditions q) : valuation q 1486 = false ∨ valuation q 1510 = false ∨ valuation q 1520 = true := counterClause724 (baseVal q)

theorem counterClause725 (q : Nat → Bool) : valuationOf q 1486 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1521 = true := by
  have hs : count1516 q = (countLit q [-31, -34, -35, -37, -39, -41, -43]) + (countLit q [-44, -47, -48, -51, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-31, -34, -35, -37, -39, -41, -43]) (l₂ := [-44, -47, -48, -51, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1486)) (literal (valuationOf q) (1511)) (literal (valuationOf q) (1521)) (countLit q [-31, -34, -35, -37, -39, -41, -43]) (countLit q [-44, -47, -48, -51, -52, -54, -56, -58]) (count1516 q) 2 4 (meaning1486 q) (meaning1511 q) (meaning1521 q) hs
  change valuationOf q 1486 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1521 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause725 (q : Snake 81) (h : Conditions q) : valuation q 1486 = false ∨ valuation q 1511 = false ∨ valuation q 1521 = true := counterClause725 (baseVal q)

theorem counterClause726 (q : Nat → Bool) : valuationOf q 1487 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1519 = true := by
  have hs : count1516 q = (countLit q [-31, -34, -35, -37, -39, -41, -43]) + (countLit q [-44, -47, -48, -51, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-31, -34, -35, -37, -39, -41, -43]) (l₂ := [-44, -47, -48, -51, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1487)) (literal (valuationOf q) (1508)) (literal (valuationOf q) (1519)) (countLit q [-31, -34, -35, -37, -39, -41, -43]) (countLit q [-44, -47, -48, -51, -52, -54, -56, -58]) (count1516 q) 3 1 (meaning1487 q) (meaning1508 q) (meaning1519 q) hs
  change valuationOf q 1487 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1519 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause726 (q : Snake 81) (h : Conditions q) : valuation q 1487 = false ∨ valuation q 1508 = false ∨ valuation q 1519 = true := counterClause726 (baseVal q)

theorem counterClause727 (q : Nat → Bool) : valuationOf q 1487 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1520 = true := by
  have hs : count1516 q = (countLit q [-31, -34, -35, -37, -39, -41, -43]) + (countLit q [-44, -47, -48, -51, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-31, -34, -35, -37, -39, -41, -43]) (l₂ := [-44, -47, -48, -51, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1487)) (literal (valuationOf q) (1509)) (literal (valuationOf q) (1520)) (countLit q [-31, -34, -35, -37, -39, -41, -43]) (countLit q [-44, -47, -48, -51, -52, -54, -56, -58]) (count1516 q) 3 2 (meaning1487 q) (meaning1509 q) (meaning1520 q) hs
  change valuationOf q 1487 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause727 (q : Snake 81) (h : Conditions q) : valuation q 1487 = false ∨ valuation q 1509 = false ∨ valuation q 1520 = true := counterClause727 (baseVal q)

theorem counterClause728 (q : Nat → Bool) : valuationOf q 1487 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1521 = true := by
  have hs : count1516 q = (countLit q [-31, -34, -35, -37, -39, -41, -43]) + (countLit q [-44, -47, -48, -51, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-31, -34, -35, -37, -39, -41, -43]) (l₂ := [-44, -47, -48, -51, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1487)) (literal (valuationOf q) (1510)) (literal (valuationOf q) (1521)) (countLit q [-31, -34, -35, -37, -39, -41, -43]) (countLit q [-44, -47, -48, -51, -52, -54, -56, -58]) (count1516 q) 3 3 (meaning1487 q) (meaning1510 q) (meaning1521 q) hs
  change valuationOf q 1487 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1521 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause728 (q : Snake 81) (h : Conditions q) : valuation q 1487 = false ∨ valuation q 1510 = false ∨ valuation q 1521 = true := counterClause728 (baseVal q)

theorem counterClause729 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1520 = true := by
  have hs : count1516 q = (countLit q [-31, -34, -35, -37, -39, -41, -43]) + (countLit q [-44, -47, -48, -51, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-31, -34, -35, -37, -39, -41, -43]) (l₂ := [-44, -47, -48, -51, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1488)) (literal (valuationOf q) (1508)) (literal (valuationOf q) (1520)) (countLit q [-31, -34, -35, -37, -39, -41, -43]) (countLit q [-44, -47, -48, -51, -52, -54, -56, -58]) (count1516 q) 4 1 (meaning1488 q) (meaning1508 q) (meaning1520 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause729 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1508 = false ∨ valuation q 1520 = true := counterClause729 (baseVal q)

theorem counterClause730 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1521 = true := by
  have hs : count1516 q = (countLit q [-31, -34, -35, -37, -39, -41, -43]) + (countLit q [-44, -47, -48, -51, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-31, -34, -35, -37, -39, -41, -43]) (l₂ := [-44, -47, -48, -51, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1488)) (literal (valuationOf q) (1509)) (literal (valuationOf q) (1521)) (countLit q [-31, -34, -35, -37, -39, -41, -43]) (countLit q [-44, -47, -48, -51, -52, -54, -56, -58]) (count1516 q) 4 2 (meaning1488 q) (meaning1509 q) (meaning1521 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1521 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause730 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1509 = false ∨ valuation q 1521 = true := counterClause730 (baseVal q)

theorem counterClause731 (q : Nat → Bool) : valuationOf q 1459 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1536 = true := by
  have hs : count1531 q = (countLit q [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29]) + (countLit q [-31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29]) (l₂ := [-31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1459)) (literal (valuationOf q) (1518)) (literal (valuationOf q) (1536)) (countLit q [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29]) (countLit q [-31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58]) (count1531 q) 3 3 (meaning1459 q) (meaning1518 q) (meaning1536 q) hs
  change valuationOf q 1459 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1536 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause731 (q : Snake 81) (h : Conditions q) : valuation q 1459 = false ∨ valuation q 1518 = false ∨ valuation q 1536 = true := counterClause731 (baseVal q)

theorem counterClause732 (q : Nat → Bool) : valuationOf q 1459 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1537 = true := by
  have hs : count1531 q = (countLit q [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29]) + (countLit q [-31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29]) (l₂ := [-31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1459)) (literal (valuationOf q) (1519)) (literal (valuationOf q) (1537)) (countLit q [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29]) (countLit q [-31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58]) (count1531 q) 3 4 (meaning1459 q) (meaning1519 q) (meaning1537 q) hs
  change valuationOf q 1459 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1537 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause732 (q : Snake 81) (h : Conditions q) : valuation q 1459 = false ∨ valuation q 1519 = false ∨ valuation q 1537 = true := counterClause732 (baseVal q)

theorem counterClause733 (q : Nat → Bool) : valuationOf q 1459 = false ∨ valuationOf q 1520 = false ∨ valuationOf q 1538 = true := by
  have hs : count1531 q = (countLit q [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29]) + (countLit q [-31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29]) (l₂ := [-31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1459)) (literal (valuationOf q) (1520)) (literal (valuationOf q) (1538)) (countLit q [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29]) (countLit q [-31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58]) (count1531 q) 3 5 (meaning1459 q) (meaning1520 q) (meaning1538 q) hs
  change valuationOf q 1459 = false ∨ valuationOf q 1520 = false ∨ valuationOf q 1538 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause733 (q : Snake 81) (h : Conditions q) : valuation q 1459 = false ∨ valuation q 1520 = false ∨ valuation q 1538 = true := counterClause733 (baseVal q)

theorem counterClause734 (q : Nat → Bool) : valuationOf q 1459 = false ∨ valuationOf q 1521 = false ∨ valuationOf q 1539 = true := by
  have hs : count1531 q = (countLit q [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29]) + (countLit q [-31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29]) (l₂ := [-31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1459)) (literal (valuationOf q) (1521)) (literal (valuationOf q) (1539)) (countLit q [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29]) (countLit q [-31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58]) (count1531 q) 3 6 (meaning1459 q) (meaning1521 q) (meaning1539 q) hs
  change valuationOf q 1459 = false ∨ valuationOf q 1521 = false ∨ valuationOf q 1539 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause734 (q : Snake 81) (h : Conditions q) : valuation q 1459 = false ∨ valuation q 1521 = false ∨ valuation q 1539 = true := counterClause734 (baseVal q)

theorem counterClause735 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1517 = false ∨ valuationOf q 1536 = true := by
  have hs : count1531 q = (countLit q [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29]) + (countLit q [-31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29]) (l₂ := [-31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1460)) (literal (valuationOf q) (1517)) (literal (valuationOf q) (1536)) (countLit q [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29]) (countLit q [-31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58]) (count1531 q) 4 2 (meaning1460 q) (meaning1517 q) (meaning1536 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1517 = false ∨ valuationOf q 1536 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause735 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1517 = false ∨ valuation q 1536 = true := counterClause735 (baseVal q)

theorem counterClause736 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1537 = true := by
  have hs : count1531 q = (countLit q [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29]) + (countLit q [-31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29]) (l₂ := [-31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1460)) (literal (valuationOf q) (1518)) (literal (valuationOf q) (1537)) (countLit q [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29]) (countLit q [-31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58]) (count1531 q) 4 3 (meaning1460 q) (meaning1518 q) (meaning1537 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1537 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause736 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1518 = false ∨ valuation q 1537 = true := counterClause736 (baseVal q)

theorem block22 (q : Snake 81) (h : Conditions q) : B112E096.Block22 (valuation q) :=
  ⟨clause705 q h, clause706 q h, clause707 q h, clause708 q h, clause709 q h, clause710 q h, clause711 q h, clause712 q h, clause713 q h, clause714 q h, clause715 q h, clause716 q h, clause717 q h, clause718 q h, clause719 q h, clause720 q h, clause721 q h, clause722 q h, clause723 q h, clause724 q h, clause725 q h, clause726 q h, clause727 q h, clause728 q h, clause729 q h, clause730 q h, clause731 q h, clause732 q h, clause733 q h, clause734 q h, clause735 q h, clause736 q h⟩

end
end Snake9.Regrowth.E112096
