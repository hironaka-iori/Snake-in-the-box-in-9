import E112258Semantics
import B112E258Inputs
namespace Snake9.Regrowth.E112258
noncomputable section
local instance blockDec29 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause929 (q : Nat → Bool) : valuationOf q 12 = true ∨ valuationOf q 13 = true ∨ valuationOf q 1507 = true := by
  have hs : count1506 q = (countLit q [-12]) + (countLit q [-13]) := List.countP_append (p := literal q) (l₁ := [-12]) (l₂ := [-13])
  have hm := merge_two (literal (valuationOf q) (-12)) (literal (valuationOf q) (-13)) (literal (valuationOf q) (1507)) (countLit q [-12]) (countLit q [-13]) (count1506 q) 1 1 (meaningNeg12 q) (meaningNeg13 q) (meaning1507 q) hs
  change (! (valuationOf q 12)) = false ∨ (! (valuationOf q 13)) = false ∨ valuationOf q 1507 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause929 (q : Snake 81) (h : Conditions q) : valuation q 12 = true ∨ valuation q 13 = true ∨ valuation q 1507 = true := counterClause929 (baseVal q)

theorem counterClause930 (q : Nat → Bool) : valuationOf q 17 = true ∨ valuationOf q 1508 = true := by
  have hs : count1508 q = (countLit q [-15]) + (countLit q [-17]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-17])
  have hm := merge_right (literal (valuationOf q) (-17)) (literal (valuationOf q) (1508)) (countLit q [-15]) (countLit q [-17]) (count1508 q) 1 (meaningNeg17 q) (meaning1508 q) hs
  change (! (valuationOf q 17)) = false ∨ valuationOf q 1508 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause930 (q : Snake 81) (h : Conditions q) : valuation q 17 = true ∨ valuation q 1508 = true := counterClause930 (baseVal q)

theorem counterClause931 (q : Nat → Bool) : valuationOf q 15 = true ∨ valuationOf q 1508 = true := by
  have hs : count1508 q = (countLit q [-15]) + (countLit q [-17]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-17])
  have hm := merge_left (literal (valuationOf q) (-15)) (literal (valuationOf q) (1508)) (countLit q [-15]) (countLit q [-17]) (count1508 q) 1 (meaningNeg15 q) (meaning1508 q) hs
  change (! (valuationOf q 15)) = false ∨ valuationOf q 1508 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause931 (q : Snake 81) (h : Conditions q) : valuation q 15 = true ∨ valuation q 1508 = true := counterClause931 (baseVal q)

theorem counterClause932 (q : Nat → Bool) : valuationOf q 15 = true ∨ valuationOf q 17 = true ∨ valuationOf q 1509 = true := by
  have hs : count1508 q = (countLit q [-15]) + (countLit q [-17]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-17])
  have hm := merge_two (literal (valuationOf q) (-15)) (literal (valuationOf q) (-17)) (literal (valuationOf q) (1509)) (countLit q [-15]) (countLit q [-17]) (count1508 q) 1 1 (meaningNeg15 q) (meaningNeg17 q) (meaning1509 q) hs
  change (! (valuationOf q 15)) = false ∨ (! (valuationOf q 17)) = false ∨ valuationOf q 1509 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause932 (q : Snake 81) (h : Conditions q) : valuation q 15 = true ∨ valuation q 17 = true ∨ valuation q 1509 = true := counterClause932 (baseVal q)

theorem counterClause933 (q : Nat → Bool) : valuationOf q 1508 = false ∨ valuationOf q 1510 = true := by
  have hs : count1510 q = (countLit q [-12, -13]) + (countLit q [-15, -17]) := List.countP_append (p := literal q) (l₁ := [-12, -13]) (l₂ := [-15, -17])
  have hm := merge_right (literal (valuationOf q) (1508)) (literal (valuationOf q) (1510)) (countLit q [-12, -13]) (countLit q [-15, -17]) (count1510 q) 1 (meaning1508 q) (meaning1510 q) hs
  change valuationOf q 1508 = false ∨ valuationOf q 1510 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause933 (q : Snake 81) (h : Conditions q) : valuation q 1508 = false ∨ valuation q 1510 = true := counterClause933 (baseVal q)

theorem counterClause934 (q : Nat → Bool) : valuationOf q 1509 = false ∨ valuationOf q 1511 = true := by
  have hs : count1510 q = (countLit q [-12, -13]) + (countLit q [-15, -17]) := List.countP_append (p := literal q) (l₁ := [-12, -13]) (l₂ := [-15, -17])
  have hm := merge_right (literal (valuationOf q) (1509)) (literal (valuationOf q) (1511)) (countLit q [-12, -13]) (countLit q [-15, -17]) (count1510 q) 2 (meaning1509 q) (meaning1511 q) hs
  change valuationOf q 1509 = false ∨ valuationOf q 1511 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause934 (q : Snake 81) (h : Conditions q) : valuation q 1509 = false ∨ valuation q 1511 = true := counterClause934 (baseVal q)

theorem counterClause935 (q : Nat → Bool) : valuationOf q 1506 = false ∨ valuationOf q 1510 = true := by
  have hs : count1510 q = (countLit q [-12, -13]) + (countLit q [-15, -17]) := List.countP_append (p := literal q) (l₁ := [-12, -13]) (l₂ := [-15, -17])
  have hm := merge_left (literal (valuationOf q) (1506)) (literal (valuationOf q) (1510)) (countLit q [-12, -13]) (countLit q [-15, -17]) (count1510 q) 1 (meaning1506 q) (meaning1510 q) hs
  change valuationOf q 1506 = false ∨ valuationOf q 1510 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause935 (q : Snake 81) (h : Conditions q) : valuation q 1506 = false ∨ valuation q 1510 = true := counterClause935 (baseVal q)

theorem counterClause936 (q : Nat → Bool) : valuationOf q 1506 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1511 = true := by
  have hs : count1510 q = (countLit q [-12, -13]) + (countLit q [-15, -17]) := List.countP_append (p := literal q) (l₁ := [-12, -13]) (l₂ := [-15, -17])
  have hm := merge_two (literal (valuationOf q) (1506)) (literal (valuationOf q) (1508)) (literal (valuationOf q) (1511)) (countLit q [-12, -13]) (countLit q [-15, -17]) (count1510 q) 1 1 (meaning1506 q) (meaning1508 q) (meaning1511 q) hs
  change valuationOf q 1506 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1511 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause936 (q : Snake 81) (h : Conditions q) : valuation q 1506 = false ∨ valuation q 1508 = false ∨ valuation q 1511 = true := counterClause936 (baseVal q)

theorem counterClause937 (q : Nat → Bool) : valuationOf q 1506 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1512 = true := by
  have hs : count1510 q = (countLit q [-12, -13]) + (countLit q [-15, -17]) := List.countP_append (p := literal q) (l₁ := [-12, -13]) (l₂ := [-15, -17])
  have hm := merge_two (literal (valuationOf q) (1506)) (literal (valuationOf q) (1509)) (literal (valuationOf q) (1512)) (countLit q [-12, -13]) (countLit q [-15, -17]) (count1510 q) 1 2 (meaning1506 q) (meaning1509 q) (meaning1512 q) hs
  change valuationOf q 1506 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1512 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause937 (q : Snake 81) (h : Conditions q) : valuation q 1506 = false ∨ valuation q 1509 = false ∨ valuation q 1512 = true := counterClause937 (baseVal q)

theorem counterClause938 (q : Nat → Bool) : valuationOf q 1507 = false ∨ valuationOf q 1511 = true := by
  have hs : count1510 q = (countLit q [-12, -13]) + (countLit q [-15, -17]) := List.countP_append (p := literal q) (l₁ := [-12, -13]) (l₂ := [-15, -17])
  have hm := merge_left (literal (valuationOf q) (1507)) (literal (valuationOf q) (1511)) (countLit q [-12, -13]) (countLit q [-15, -17]) (count1510 q) 2 (meaning1507 q) (meaning1511 q) hs
  change valuationOf q 1507 = false ∨ valuationOf q 1511 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause938 (q : Snake 81) (h : Conditions q) : valuation q 1507 = false ∨ valuation q 1511 = true := counterClause938 (baseVal q)

theorem counterClause939 (q : Nat → Bool) : valuationOf q 1507 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1512 = true := by
  have hs : count1510 q = (countLit q [-12, -13]) + (countLit q [-15, -17]) := List.countP_append (p := literal q) (l₁ := [-12, -13]) (l₂ := [-15, -17])
  have hm := merge_two (literal (valuationOf q) (1507)) (literal (valuationOf q) (1508)) (literal (valuationOf q) (1512)) (countLit q [-12, -13]) (countLit q [-15, -17]) (count1510 q) 2 1 (meaning1507 q) (meaning1508 q) (meaning1512 q) hs
  change valuationOf q 1507 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1512 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause939 (q : Snake 81) (h : Conditions q) : valuation q 1507 = false ∨ valuation q 1508 = false ∨ valuation q 1512 = true := counterClause939 (baseVal q)

theorem counterClause940 (q : Nat → Bool) : valuationOf q 1507 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1513 = true := by
  have hs : count1510 q = (countLit q [-12, -13]) + (countLit q [-15, -17]) := List.countP_append (p := literal q) (l₁ := [-12, -13]) (l₂ := [-15, -17])
  have hm := merge_two (literal (valuationOf q) (1507)) (literal (valuationOf q) (1509)) (literal (valuationOf q) (1513)) (countLit q [-12, -13]) (countLit q [-15, -17]) (count1510 q) 2 2 (meaning1507 q) (meaning1509 q) (meaning1513 q) hs
  change valuationOf q 1507 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1513 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause940 (q : Snake 81) (h : Conditions q) : valuation q 1507 = false ∨ valuation q 1509 = false ∨ valuation q 1513 = true := counterClause940 (baseVal q)

theorem counterClause941 (q : Nat → Bool) : valuationOf q 1503 = false ∨ valuationOf q 1514 = true := by
  have hs : count1514 q = (countLit q [-2, -5, -8]) + (countLit q [-12, -13, -15, -17]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8]) (l₂ := [-12, -13, -15, -17])
  have hm := merge_left (literal (valuationOf q) (1503)) (literal (valuationOf q) (1514)) (countLit q [-2, -5, -8]) (countLit q [-12, -13, -15, -17]) (count1514 q) 1 (meaning1503 q) (meaning1514 q) hs
  change valuationOf q 1503 = false ∨ valuationOf q 1514 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause941 (q : Snake 81) (h : Conditions q) : valuation q 1503 = false ∨ valuation q 1514 = true := counterClause941 (baseVal q)

theorem counterClause942 (q : Nat → Bool) : valuationOf q 1503 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1515 = true := by
  have hs : count1514 q = (countLit q [-2, -5, -8]) + (countLit q [-12, -13, -15, -17]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8]) (l₂ := [-12, -13, -15, -17])
  have hm := merge_two (literal (valuationOf q) (1503)) (literal (valuationOf q) (1510)) (literal (valuationOf q) (1515)) (countLit q [-2, -5, -8]) (countLit q [-12, -13, -15, -17]) (count1514 q) 1 1 (meaning1503 q) (meaning1510 q) (meaning1515 q) hs
  change valuationOf q 1503 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1515 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause942 (q : Snake 81) (h : Conditions q) : valuation q 1503 = false ∨ valuation q 1510 = false ∨ valuation q 1515 = true := counterClause942 (baseVal q)

theorem counterClause943 (q : Nat → Bool) : valuationOf q 1503 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1516 = true := by
  have hs : count1514 q = (countLit q [-2, -5, -8]) + (countLit q [-12, -13, -15, -17]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8]) (l₂ := [-12, -13, -15, -17])
  have hm := merge_two (literal (valuationOf q) (1503)) (literal (valuationOf q) (1511)) (literal (valuationOf q) (1516)) (countLit q [-2, -5, -8]) (countLit q [-12, -13, -15, -17]) (count1514 q) 1 2 (meaning1503 q) (meaning1511 q) (meaning1516 q) hs
  change valuationOf q 1503 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1516 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause943 (q : Snake 81) (h : Conditions q) : valuation q 1503 = false ∨ valuation q 1511 = false ∨ valuation q 1516 = true := counterClause943 (baseVal q)

theorem counterClause944 (q : Nat → Bool) : valuationOf q 1503 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1517 = true := by
  have hs : count1514 q = (countLit q [-2, -5, -8]) + (countLit q [-12, -13, -15, -17]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8]) (l₂ := [-12, -13, -15, -17])
  have hm := merge_two (literal (valuationOf q) (1503)) (literal (valuationOf q) (1512)) (literal (valuationOf q) (1517)) (countLit q [-2, -5, -8]) (countLit q [-12, -13, -15, -17]) (count1514 q) 1 3 (meaning1503 q) (meaning1512 q) (meaning1517 q) hs
  change valuationOf q 1503 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1517 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause944 (q : Snake 81) (h : Conditions q) : valuation q 1503 = false ∨ valuation q 1512 = false ∨ valuation q 1517 = true := counterClause944 (baseVal q)

theorem counterClause945 (q : Nat → Bool) : valuationOf q 1503 = false ∨ valuationOf q 1513 = false ∨ valuationOf q 1518 = true := by
  have hs : count1514 q = (countLit q [-2, -5, -8]) + (countLit q [-12, -13, -15, -17]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8]) (l₂ := [-12, -13, -15, -17])
  have hm := merge_two (literal (valuationOf q) (1503)) (literal (valuationOf q) (1513)) (literal (valuationOf q) (1518)) (countLit q [-2, -5, -8]) (countLit q [-12, -13, -15, -17]) (count1514 q) 1 4 (meaning1503 q) (meaning1513 q) (meaning1518 q) hs
  change valuationOf q 1503 = false ∨ valuationOf q 1513 = false ∨ valuationOf q 1518 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause945 (q : Snake 81) (h : Conditions q) : valuation q 1503 = false ∨ valuation q 1513 = false ∨ valuation q 1518 = true := counterClause945 (baseVal q)

theorem counterClause946 (q : Nat → Bool) : valuationOf q 1504 = false ∨ valuationOf q 1515 = true := by
  have hs : count1514 q = (countLit q [-2, -5, -8]) + (countLit q [-12, -13, -15, -17]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8]) (l₂ := [-12, -13, -15, -17])
  have hm := merge_left (literal (valuationOf q) (1504)) (literal (valuationOf q) (1515)) (countLit q [-2, -5, -8]) (countLit q [-12, -13, -15, -17]) (count1514 q) 2 (meaning1504 q) (meaning1515 q) hs
  change valuationOf q 1504 = false ∨ valuationOf q 1515 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause946 (q : Snake 81) (h : Conditions q) : valuation q 1504 = false ∨ valuation q 1515 = true := counterClause946 (baseVal q)

theorem counterClause947 (q : Nat → Bool) : valuationOf q 1504 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1516 = true := by
  have hs : count1514 q = (countLit q [-2, -5, -8]) + (countLit q [-12, -13, -15, -17]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8]) (l₂ := [-12, -13, -15, -17])
  have hm := merge_two (literal (valuationOf q) (1504)) (literal (valuationOf q) (1510)) (literal (valuationOf q) (1516)) (countLit q [-2, -5, -8]) (countLit q [-12, -13, -15, -17]) (count1514 q) 2 1 (meaning1504 q) (meaning1510 q) (meaning1516 q) hs
  change valuationOf q 1504 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1516 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause947 (q : Snake 81) (h : Conditions q) : valuation q 1504 = false ∨ valuation q 1510 = false ∨ valuation q 1516 = true := counterClause947 (baseVal q)

theorem counterClause948 (q : Nat → Bool) : valuationOf q 1504 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1517 = true := by
  have hs : count1514 q = (countLit q [-2, -5, -8]) + (countLit q [-12, -13, -15, -17]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8]) (l₂ := [-12, -13, -15, -17])
  have hm := merge_two (literal (valuationOf q) (1504)) (literal (valuationOf q) (1511)) (literal (valuationOf q) (1517)) (countLit q [-2, -5, -8]) (countLit q [-12, -13, -15, -17]) (count1514 q) 2 2 (meaning1504 q) (meaning1511 q) (meaning1517 q) hs
  change valuationOf q 1504 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1517 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause948 (q : Snake 81) (h : Conditions q) : valuation q 1504 = false ∨ valuation q 1511 = false ∨ valuation q 1517 = true := counterClause948 (baseVal q)

theorem counterClause949 (q : Nat → Bool) : valuationOf q 1504 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1518 = true := by
  have hs : count1514 q = (countLit q [-2, -5, -8]) + (countLit q [-12, -13, -15, -17]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8]) (l₂ := [-12, -13, -15, -17])
  have hm := merge_two (literal (valuationOf q) (1504)) (literal (valuationOf q) (1512)) (literal (valuationOf q) (1518)) (countLit q [-2, -5, -8]) (countLit q [-12, -13, -15, -17]) (count1514 q) 2 3 (meaning1504 q) (meaning1512 q) (meaning1518 q) hs
  change valuationOf q 1504 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1518 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause949 (q : Snake 81) (h : Conditions q) : valuation q 1504 = false ∨ valuation q 1512 = false ∨ valuation q 1518 = true := counterClause949 (baseVal q)

theorem counterClause950 (q : Nat → Bool) : valuationOf q 1504 = false ∨ valuationOf q 1513 = false ∨ valuationOf q 1519 = true := by
  have hs : count1514 q = (countLit q [-2, -5, -8]) + (countLit q [-12, -13, -15, -17]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8]) (l₂ := [-12, -13, -15, -17])
  have hm := merge_two (literal (valuationOf q) (1504)) (literal (valuationOf q) (1513)) (literal (valuationOf q) (1519)) (countLit q [-2, -5, -8]) (countLit q [-12, -13, -15, -17]) (count1514 q) 2 4 (meaning1504 q) (meaning1513 q) (meaning1519 q) hs
  change valuationOf q 1504 = false ∨ valuationOf q 1513 = false ∨ valuationOf q 1519 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause950 (q : Snake 81) (h : Conditions q) : valuation q 1504 = false ∨ valuation q 1513 = false ∨ valuation q 1519 = true := counterClause950 (baseVal q)

theorem counterClause951 (q : Nat → Bool) : valuationOf q 1505 = false ∨ valuationOf q 1516 = true := by
  have hs : count1514 q = (countLit q [-2, -5, -8]) + (countLit q [-12, -13, -15, -17]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8]) (l₂ := [-12, -13, -15, -17])
  have hm := merge_left (literal (valuationOf q) (1505)) (literal (valuationOf q) (1516)) (countLit q [-2, -5, -8]) (countLit q [-12, -13, -15, -17]) (count1514 q) 3 (meaning1505 q) (meaning1516 q) hs
  change valuationOf q 1505 = false ∨ valuationOf q 1516 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause951 (q : Snake 81) (h : Conditions q) : valuation q 1505 = false ∨ valuation q 1516 = true := counterClause951 (baseVal q)

theorem counterClause952 (q : Nat → Bool) : valuationOf q 1505 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1517 = true := by
  have hs : count1514 q = (countLit q [-2, -5, -8]) + (countLit q [-12, -13, -15, -17]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8]) (l₂ := [-12, -13, -15, -17])
  have hm := merge_two (literal (valuationOf q) (1505)) (literal (valuationOf q) (1510)) (literal (valuationOf q) (1517)) (countLit q [-2, -5, -8]) (countLit q [-12, -13, -15, -17]) (count1514 q) 3 1 (meaning1505 q) (meaning1510 q) (meaning1517 q) hs
  change valuationOf q 1505 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1517 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause952 (q : Snake 81) (h : Conditions q) : valuation q 1505 = false ∨ valuation q 1510 = false ∨ valuation q 1517 = true := counterClause952 (baseVal q)

theorem counterClause953 (q : Nat → Bool) : valuationOf q 1505 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1518 = true := by
  have hs : count1514 q = (countLit q [-2, -5, -8]) + (countLit q [-12, -13, -15, -17]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8]) (l₂ := [-12, -13, -15, -17])
  have hm := merge_two (literal (valuationOf q) (1505)) (literal (valuationOf q) (1511)) (literal (valuationOf q) (1518)) (countLit q [-2, -5, -8]) (countLit q [-12, -13, -15, -17]) (count1514 q) 3 2 (meaning1505 q) (meaning1511 q) (meaning1518 q) hs
  change valuationOf q 1505 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1518 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause953 (q : Snake 81) (h : Conditions q) : valuation q 1505 = false ∨ valuation q 1511 = false ∨ valuation q 1518 = true := counterClause953 (baseVal q)

theorem counterClause954 (q : Nat → Bool) : valuationOf q 1505 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1519 = true := by
  have hs : count1514 q = (countLit q [-2, -5, -8]) + (countLit q [-12, -13, -15, -17]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8]) (l₂ := [-12, -13, -15, -17])
  have hm := merge_two (literal (valuationOf q) (1505)) (literal (valuationOf q) (1512)) (literal (valuationOf q) (1519)) (countLit q [-2, -5, -8]) (countLit q [-12, -13, -15, -17]) (count1514 q) 3 3 (meaning1505 q) (meaning1512 q) (meaning1519 q) hs
  change valuationOf q 1505 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1519 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause954 (q : Snake 81) (h : Conditions q) : valuation q 1505 = false ∨ valuation q 1512 = false ∨ valuation q 1519 = true := counterClause954 (baseVal q)

theorem counterClause955 (q : Nat → Bool) : valuationOf q 22 = true ∨ valuationOf q 1521 = true := by
  have hs : count1521 q = (countLit q [-21]) + (countLit q [-22]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-22])
  have hm := merge_right (literal (valuationOf q) (-22)) (literal (valuationOf q) (1521)) (countLit q [-21]) (countLit q [-22]) (count1521 q) 1 (meaningNeg22 q) (meaning1521 q) hs
  change (! (valuationOf q 22)) = false ∨ valuationOf q 1521 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause955 (q : Snake 81) (h : Conditions q) : valuation q 22 = true ∨ valuation q 1521 = true := counterClause955 (baseVal q)

theorem counterClause956 (q : Nat → Bool) : valuationOf q 21 = true ∨ valuationOf q 1521 = true := by
  have hs : count1521 q = (countLit q [-21]) + (countLit q [-22]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-22])
  have hm := merge_left (literal (valuationOf q) (-21)) (literal (valuationOf q) (1521)) (countLit q [-21]) (countLit q [-22]) (count1521 q) 1 (meaningNeg21 q) (meaning1521 q) hs
  change (! (valuationOf q 21)) = false ∨ valuationOf q 1521 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause956 (q : Snake 81) (h : Conditions q) : valuation q 21 = true ∨ valuation q 1521 = true := counterClause956 (baseVal q)

theorem counterClause957 (q : Nat → Bool) : valuationOf q 21 = true ∨ valuationOf q 22 = true ∨ valuationOf q 1522 = true := by
  have hs : count1521 q = (countLit q [-21]) + (countLit q [-22]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-22])
  have hm := merge_two (literal (valuationOf q) (-21)) (literal (valuationOf q) (-22)) (literal (valuationOf q) (1522)) (countLit q [-21]) (countLit q [-22]) (count1521 q) 1 1 (meaningNeg21 q) (meaningNeg22 q) (meaning1522 q) hs
  change (! (valuationOf q 21)) = false ∨ (! (valuationOf q 22)) = false ∨ valuationOf q 1522 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause957 (q : Snake 81) (h : Conditions q) : valuation q 21 = true ∨ valuation q 22 = true ∨ valuation q 1522 = true := counterClause957 (baseVal q)

theorem counterClause958 (q : Nat → Bool) : valuationOf q 1521 = false ∨ valuationOf q 1523 = true := by
  have hs : count1523 q = (countLit q [-18]) + (countLit q [-21, -22]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-21, -22])
  have hm := merge_right (literal (valuationOf q) (1521)) (literal (valuationOf q) (1523)) (countLit q [-18]) (countLit q [-21, -22]) (count1523 q) 1 (meaning1521 q) (meaning1523 q) hs
  change valuationOf q 1521 = false ∨ valuationOf q 1523 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause958 (q : Snake 81) (h : Conditions q) : valuation q 1521 = false ∨ valuation q 1523 = true := counterClause958 (baseVal q)

theorem counterClause959 (q : Nat → Bool) : valuationOf q 1522 = false ∨ valuationOf q 1524 = true := by
  have hs : count1523 q = (countLit q [-18]) + (countLit q [-21, -22]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-21, -22])
  have hm := merge_right (literal (valuationOf q) (1522)) (literal (valuationOf q) (1524)) (countLit q [-18]) (countLit q [-21, -22]) (count1523 q) 2 (meaning1522 q) (meaning1524 q) hs
  change valuationOf q 1522 = false ∨ valuationOf q 1524 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause959 (q : Snake 81) (h : Conditions q) : valuation q 1522 = false ∨ valuation q 1524 = true := counterClause959 (baseVal q)

theorem counterClause960 (q : Nat → Bool) : valuationOf q 18 = true ∨ valuationOf q 1523 = true := by
  have hs : count1523 q = (countLit q [-18]) + (countLit q [-21, -22]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-21, -22])
  have hm := merge_left (literal (valuationOf q) (-18)) (literal (valuationOf q) (1523)) (countLit q [-18]) (countLit q [-21, -22]) (count1523 q) 1 (meaningNeg18 q) (meaning1523 q) hs
  change (! (valuationOf q 18)) = false ∨ valuationOf q 1523 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause960 (q : Snake 81) (h : Conditions q) : valuation q 18 = true ∨ valuation q 1523 = true := counterClause960 (baseVal q)

theorem block29 (q : Snake 81) (h : Conditions q) : B112E258.Block29 (valuation q) :=
  ⟨clause929 q h, clause930 q h, clause931 q h, clause932 q h, clause933 q h, clause934 q h, clause935 q h, clause936 q h, clause937 q h, clause938 q h, clause939 q h, clause940 q h, clause941 q h, clause942 q h, clause943 q h, clause944 q h, clause945 q h, clause946 q h, clause947 q h, clause948 q h, clause949 q h, clause950 q h, clause951 q h, clause952 q h, clause953 q h, clause954 q h, clause955 q h, clause956 q h, clause957 q h, clause958 q h, clause959 q h, clause960 q h⟩

end
end Snake9.Regrowth.E112258
