import E112020Semantics
import B112E020Inputs
namespace Snake9.Regrowth.E112020
noncomputable section
local instance blockDec32 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1025 (q : Nat → Bool) : valuationOf q 9 = true ∨ valuationOf q 1504 = true := by
  have hs : count1504 q = (countLit q [-9]) + (countLit q [-12]) := List.countP_append (p := literal q) (l₁ := [-9]) (l₂ := [-12])
  have hm := merge_left (literal (valuationOf q) (-9)) (literal (valuationOf q) (1504)) (countLit q [-9]) (countLit q [-12]) (count1504 q) 1 (meaningNeg9 q) (meaning1504 q) hs
  change (! (valuationOf q 9)) = false ∨ valuationOf q 1504 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1025 (q : Snake 81) (h : Conditions q) : valuation q 9 = true ∨ valuation q 1504 = true := counterClause1025 (baseVal q)

theorem counterClause1026 (q : Nat → Bool) : valuationOf q 9 = true ∨ valuationOf q 12 = true ∨ valuationOf q 1505 = true := by
  have hs : count1504 q = (countLit q [-9]) + (countLit q [-12]) := List.countP_append (p := literal q) (l₁ := [-9]) (l₂ := [-12])
  have hm := merge_two (literal (valuationOf q) (-9)) (literal (valuationOf q) (-12)) (literal (valuationOf q) (1505)) (countLit q [-9]) (countLit q [-12]) (count1504 q) 1 1 (meaningNeg9 q) (meaningNeg12 q) (meaning1505 q) hs
  change (! (valuationOf q 9)) = false ∨ (! (valuationOf q 12)) = false ∨ valuationOf q 1505 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1026 (q : Snake 81) (h : Conditions q) : valuation q 9 = true ∨ valuation q 12 = true ∨ valuation q 1505 = true := counterClause1026 (baseVal q)

theorem counterClause1027 (q : Nat → Bool) : valuationOf q 1504 = false ∨ valuationOf q 1506 = true := by
  have hs : count1506 q = (countLit q [-6, -8]) + (countLit q [-9, -12]) := List.countP_append (p := literal q) (l₁ := [-6, -8]) (l₂ := [-9, -12])
  have hm := merge_right (literal (valuationOf q) (1504)) (literal (valuationOf q) (1506)) (countLit q [-6, -8]) (countLit q [-9, -12]) (count1506 q) 1 (meaning1504 q) (meaning1506 q) hs
  change valuationOf q 1504 = false ∨ valuationOf q 1506 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1027 (q : Snake 81) (h : Conditions q) : valuation q 1504 = false ∨ valuation q 1506 = true := counterClause1027 (baseVal q)

theorem counterClause1028 (q : Nat → Bool) : valuationOf q 1505 = false ∨ valuationOf q 1507 = true := by
  have hs : count1506 q = (countLit q [-6, -8]) + (countLit q [-9, -12]) := List.countP_append (p := literal q) (l₁ := [-6, -8]) (l₂ := [-9, -12])
  have hm := merge_right (literal (valuationOf q) (1505)) (literal (valuationOf q) (1507)) (countLit q [-6, -8]) (countLit q [-9, -12]) (count1506 q) 2 (meaning1505 q) (meaning1507 q) hs
  change valuationOf q 1505 = false ∨ valuationOf q 1507 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1028 (q : Snake 81) (h : Conditions q) : valuation q 1505 = false ∨ valuation q 1507 = true := counterClause1028 (baseVal q)

theorem counterClause1029 (q : Nat → Bool) : valuationOf q 1502 = false ∨ valuationOf q 1506 = true := by
  have hs : count1506 q = (countLit q [-6, -8]) + (countLit q [-9, -12]) := List.countP_append (p := literal q) (l₁ := [-6, -8]) (l₂ := [-9, -12])
  have hm := merge_left (literal (valuationOf q) (1502)) (literal (valuationOf q) (1506)) (countLit q [-6, -8]) (countLit q [-9, -12]) (count1506 q) 1 (meaning1502 q) (meaning1506 q) hs
  change valuationOf q 1502 = false ∨ valuationOf q 1506 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1029 (q : Snake 81) (h : Conditions q) : valuation q 1502 = false ∨ valuation q 1506 = true := counterClause1029 (baseVal q)

theorem counterClause1030 (q : Nat → Bool) : valuationOf q 1502 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1507 = true := by
  have hs : count1506 q = (countLit q [-6, -8]) + (countLit q [-9, -12]) := List.countP_append (p := literal q) (l₁ := [-6, -8]) (l₂ := [-9, -12])
  have hm := merge_two (literal (valuationOf q) (1502)) (literal (valuationOf q) (1504)) (literal (valuationOf q) (1507)) (countLit q [-6, -8]) (countLit q [-9, -12]) (count1506 q) 1 1 (meaning1502 q) (meaning1504 q) (meaning1507 q) hs
  change valuationOf q 1502 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1507 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1030 (q : Snake 81) (h : Conditions q) : valuation q 1502 = false ∨ valuation q 1504 = false ∨ valuation q 1507 = true := counterClause1030 (baseVal q)

theorem counterClause1031 (q : Nat → Bool) : valuationOf q 1502 = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1508 = true := by
  have hs : count1506 q = (countLit q [-6, -8]) + (countLit q [-9, -12]) := List.countP_append (p := literal q) (l₁ := [-6, -8]) (l₂ := [-9, -12])
  have hm := merge_two (literal (valuationOf q) (1502)) (literal (valuationOf q) (1505)) (literal (valuationOf q) (1508)) (countLit q [-6, -8]) (countLit q [-9, -12]) (count1506 q) 1 2 (meaning1502 q) (meaning1505 q) (meaning1508 q) hs
  change valuationOf q 1502 = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1508 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1031 (q : Snake 81) (h : Conditions q) : valuation q 1502 = false ∨ valuation q 1505 = false ∨ valuation q 1508 = true := counterClause1031 (baseVal q)

theorem counterClause1032 (q : Nat → Bool) : valuationOf q 1503 = false ∨ valuationOf q 1507 = true := by
  have hs : count1506 q = (countLit q [-6, -8]) + (countLit q [-9, -12]) := List.countP_append (p := literal q) (l₁ := [-6, -8]) (l₂ := [-9, -12])
  have hm := merge_left (literal (valuationOf q) (1503)) (literal (valuationOf q) (1507)) (countLit q [-6, -8]) (countLit q [-9, -12]) (count1506 q) 2 (meaning1503 q) (meaning1507 q) hs
  change valuationOf q 1503 = false ∨ valuationOf q 1507 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1032 (q : Snake 81) (h : Conditions q) : valuation q 1503 = false ∨ valuation q 1507 = true := counterClause1032 (baseVal q)

theorem counterClause1033 (q : Nat → Bool) : valuationOf q 1503 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1508 = true := by
  have hs : count1506 q = (countLit q [-6, -8]) + (countLit q [-9, -12]) := List.countP_append (p := literal q) (l₁ := [-6, -8]) (l₂ := [-9, -12])
  have hm := merge_two (literal (valuationOf q) (1503)) (literal (valuationOf q) (1504)) (literal (valuationOf q) (1508)) (countLit q [-6, -8]) (countLit q [-9, -12]) (count1506 q) 2 1 (meaning1503 q) (meaning1504 q) (meaning1508 q) hs
  change valuationOf q 1503 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1508 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1033 (q : Snake 81) (h : Conditions q) : valuation q 1503 = false ∨ valuation q 1504 = false ∨ valuation q 1508 = true := counterClause1033 (baseVal q)

theorem counterClause1034 (q : Nat → Bool) : valuationOf q 1503 = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1509 = true := by
  have hs : count1506 q = (countLit q [-6, -8]) + (countLit q [-9, -12]) := List.countP_append (p := literal q) (l₁ := [-6, -8]) (l₂ := [-9, -12])
  have hm := merge_two (literal (valuationOf q) (1503)) (literal (valuationOf q) (1505)) (literal (valuationOf q) (1509)) (countLit q [-6, -8]) (countLit q [-9, -12]) (count1506 q) 2 2 (meaning1503 q) (meaning1505 q) (meaning1509 q) hs
  change valuationOf q 1503 = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1509 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1034 (q : Snake 81) (h : Conditions q) : valuation q 1503 = false ∨ valuation q 1505 = false ∨ valuation q 1509 = true := counterClause1034 (baseVal q)

theorem counterClause1035 (q : Nat → Bool) : valuationOf q 1507 = false ∨ valuationOf q 1511 = true := by
  have hs : count1510 q = (countLit q [-2, -3, -5]) + (countLit q [-6, -8, -9, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-6, -8, -9, -12])
  have hm := merge_right (literal (valuationOf q) (1507)) (literal (valuationOf q) (1511)) (countLit q [-2, -3, -5]) (countLit q [-6, -8, -9, -12]) (count1510 q) 2 (meaning1507 q) (meaning1511 q) hs
  change valuationOf q 1507 = false ∨ valuationOf q 1511 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1035 (q : Snake 81) (h : Conditions q) : valuation q 1507 = false ∨ valuation q 1511 = true := counterClause1035 (baseVal q)

theorem counterClause1036 (q : Nat → Bool) : valuationOf q 1508 = false ∨ valuationOf q 1512 = true := by
  have hs : count1510 q = (countLit q [-2, -3, -5]) + (countLit q [-6, -8, -9, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-6, -8, -9, -12])
  have hm := merge_right (literal (valuationOf q) (1508)) (literal (valuationOf q) (1512)) (countLit q [-2, -3, -5]) (countLit q [-6, -8, -9, -12]) (count1510 q) 3 (meaning1508 q) (meaning1512 q) hs
  change valuationOf q 1508 = false ∨ valuationOf q 1512 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1036 (q : Snake 81) (h : Conditions q) : valuation q 1508 = false ∨ valuation q 1512 = true := counterClause1036 (baseVal q)

theorem counterClause1037 (q : Nat → Bool) : valuationOf q 1509 = false ∨ valuationOf q 1513 = true := by
  have hs : count1510 q = (countLit q [-2, -3, -5]) + (countLit q [-6, -8, -9, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-6, -8, -9, -12])
  have hm := merge_right (literal (valuationOf q) (1509)) (literal (valuationOf q) (1513)) (countLit q [-2, -3, -5]) (countLit q [-6, -8, -9, -12]) (count1510 q) 4 (meaning1509 q) (meaning1513 q) hs
  change valuationOf q 1509 = false ∨ valuationOf q 1513 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1037 (q : Snake 81) (h : Conditions q) : valuation q 1509 = false ∨ valuation q 1513 = true := counterClause1037 (baseVal q)

theorem counterClause1038 (q : Nat → Bool) : valuationOf q 1499 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1511 = true := by
  have hs : count1510 q = (countLit q [-2, -3, -5]) + (countLit q [-6, -8, -9, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-6, -8, -9, -12])
  have hm := merge_two (literal (valuationOf q) (1499)) (literal (valuationOf q) (1506)) (literal (valuationOf q) (1511)) (countLit q [-2, -3, -5]) (countLit q [-6, -8, -9, -12]) (count1510 q) 1 1 (meaning1499 q) (meaning1506 q) (meaning1511 q) hs
  change valuationOf q 1499 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1511 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1038 (q : Snake 81) (h : Conditions q) : valuation q 1499 = false ∨ valuation q 1506 = false ∨ valuation q 1511 = true := counterClause1038 (baseVal q)

theorem counterClause1039 (q : Nat → Bool) : valuationOf q 1499 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1512 = true := by
  have hs : count1510 q = (countLit q [-2, -3, -5]) + (countLit q [-6, -8, -9, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-6, -8, -9, -12])
  have hm := merge_two (literal (valuationOf q) (1499)) (literal (valuationOf q) (1507)) (literal (valuationOf q) (1512)) (countLit q [-2, -3, -5]) (countLit q [-6, -8, -9, -12]) (count1510 q) 1 2 (meaning1499 q) (meaning1507 q) (meaning1512 q) hs
  change valuationOf q 1499 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1512 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1039 (q : Snake 81) (h : Conditions q) : valuation q 1499 = false ∨ valuation q 1507 = false ∨ valuation q 1512 = true := counterClause1039 (baseVal q)

theorem counterClause1040 (q : Nat → Bool) : valuationOf q 1499 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1513 = true := by
  have hs : count1510 q = (countLit q [-2, -3, -5]) + (countLit q [-6, -8, -9, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-6, -8, -9, -12])
  have hm := merge_two (literal (valuationOf q) (1499)) (literal (valuationOf q) (1508)) (literal (valuationOf q) (1513)) (countLit q [-2, -3, -5]) (countLit q [-6, -8, -9, -12]) (count1510 q) 1 3 (meaning1499 q) (meaning1508 q) (meaning1513 q) hs
  change valuationOf q 1499 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1513 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1040 (q : Snake 81) (h : Conditions q) : valuation q 1499 = false ∨ valuation q 1508 = false ∨ valuation q 1513 = true := counterClause1040 (baseVal q)

theorem counterClause1041 (q : Nat → Bool) : valuationOf q 1499 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1514 = true := by
  have hs : count1510 q = (countLit q [-2, -3, -5]) + (countLit q [-6, -8, -9, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-6, -8, -9, -12])
  have hm := merge_two (literal (valuationOf q) (1499)) (literal (valuationOf q) (1509)) (literal (valuationOf q) (1514)) (countLit q [-2, -3, -5]) (countLit q [-6, -8, -9, -12]) (count1510 q) 1 4 (meaning1499 q) (meaning1509 q) (meaning1514 q) hs
  change valuationOf q 1499 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1514 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1041 (q : Snake 81) (h : Conditions q) : valuation q 1499 = false ∨ valuation q 1509 = false ∨ valuation q 1514 = true := counterClause1041 (baseVal q)

theorem counterClause1042 (q : Nat → Bool) : valuationOf q 1500 = false ∨ valuationOf q 1511 = true := by
  have hs : count1510 q = (countLit q [-2, -3, -5]) + (countLit q [-6, -8, -9, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-6, -8, -9, -12])
  have hm := merge_left (literal (valuationOf q) (1500)) (literal (valuationOf q) (1511)) (countLit q [-2, -3, -5]) (countLit q [-6, -8, -9, -12]) (count1510 q) 2 (meaning1500 q) (meaning1511 q) hs
  change valuationOf q 1500 = false ∨ valuationOf q 1511 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1042 (q : Snake 81) (h : Conditions q) : valuation q 1500 = false ∨ valuation q 1511 = true := counterClause1042 (baseVal q)

theorem counterClause1043 (q : Nat → Bool) : valuationOf q 1500 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1512 = true := by
  have hs : count1510 q = (countLit q [-2, -3, -5]) + (countLit q [-6, -8, -9, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-6, -8, -9, -12])
  have hm := merge_two (literal (valuationOf q) (1500)) (literal (valuationOf q) (1506)) (literal (valuationOf q) (1512)) (countLit q [-2, -3, -5]) (countLit q [-6, -8, -9, -12]) (count1510 q) 2 1 (meaning1500 q) (meaning1506 q) (meaning1512 q) hs
  change valuationOf q 1500 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1512 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1043 (q : Snake 81) (h : Conditions q) : valuation q 1500 = false ∨ valuation q 1506 = false ∨ valuation q 1512 = true := counterClause1043 (baseVal q)

theorem counterClause1044 (q : Nat → Bool) : valuationOf q 1500 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1513 = true := by
  have hs : count1510 q = (countLit q [-2, -3, -5]) + (countLit q [-6, -8, -9, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-6, -8, -9, -12])
  have hm := merge_two (literal (valuationOf q) (1500)) (literal (valuationOf q) (1507)) (literal (valuationOf q) (1513)) (countLit q [-2, -3, -5]) (countLit q [-6, -8, -9, -12]) (count1510 q) 2 2 (meaning1500 q) (meaning1507 q) (meaning1513 q) hs
  change valuationOf q 1500 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1513 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1044 (q : Snake 81) (h : Conditions q) : valuation q 1500 = false ∨ valuation q 1507 = false ∨ valuation q 1513 = true := counterClause1044 (baseVal q)

theorem counterClause1045 (q : Nat → Bool) : valuationOf q 1500 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1514 = true := by
  have hs : count1510 q = (countLit q [-2, -3, -5]) + (countLit q [-6, -8, -9, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-6, -8, -9, -12])
  have hm := merge_two (literal (valuationOf q) (1500)) (literal (valuationOf q) (1508)) (literal (valuationOf q) (1514)) (countLit q [-2, -3, -5]) (countLit q [-6, -8, -9, -12]) (count1510 q) 2 3 (meaning1500 q) (meaning1508 q) (meaning1514 q) hs
  change valuationOf q 1500 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1514 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1045 (q : Snake 81) (h : Conditions q) : valuation q 1500 = false ∨ valuation q 1508 = false ∨ valuation q 1514 = true := counterClause1045 (baseVal q)

theorem counterClause1046 (q : Nat → Bool) : valuationOf q 1500 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1515 = true := by
  have hs : count1510 q = (countLit q [-2, -3, -5]) + (countLit q [-6, -8, -9, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-6, -8, -9, -12])
  have hm := merge_two (literal (valuationOf q) (1500)) (literal (valuationOf q) (1509)) (literal (valuationOf q) (1515)) (countLit q [-2, -3, -5]) (countLit q [-6, -8, -9, -12]) (count1510 q) 2 4 (meaning1500 q) (meaning1509 q) (meaning1515 q) hs
  change valuationOf q 1500 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1515 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1046 (q : Snake 81) (h : Conditions q) : valuation q 1500 = false ∨ valuation q 1509 = false ∨ valuation q 1515 = true := counterClause1046 (baseVal q)

theorem counterClause1047 (q : Nat → Bool) : valuationOf q 13 = true ∨ valuationOf q 1517 = true := by
  have hs : count1517 q = (countLit q [-13]) + (countLit q [-15]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-15])
  have hm := merge_left (literal (valuationOf q) (-13)) (literal (valuationOf q) (1517)) (countLit q [-13]) (countLit q [-15]) (count1517 q) 1 (meaningNeg13 q) (meaning1517 q) hs
  change (! (valuationOf q 13)) = false ∨ valuationOf q 1517 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1047 (q : Snake 81) (h : Conditions q) : valuation q 13 = true ∨ valuation q 1517 = true := counterClause1047 (baseVal q)

theorem counterClause1048 (q : Nat → Bool) : valuationOf q 13 = true ∨ valuationOf q 15 = true ∨ valuationOf q 1518 = true := by
  have hs : count1517 q = (countLit q [-13]) + (countLit q [-15]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-15])
  have hm := merge_two (literal (valuationOf q) (-13)) (literal (valuationOf q) (-15)) (literal (valuationOf q) (1518)) (countLit q [-13]) (countLit q [-15]) (count1517 q) 1 1 (meaningNeg13 q) (meaningNeg15 q) (meaning1518 q) hs
  change (! (valuationOf q 13)) = false ∨ (! (valuationOf q 15)) = false ∨ valuationOf q 1518 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1048 (q : Snake 81) (h : Conditions q) : valuation q 13 = true ∨ valuation q 15 = true ∨ valuation q 1518 = true := counterClause1048 (baseVal q)

theorem counterClause1049 (q : Nat → Bool) : valuationOf q 18 = true ∨ valuationOf q 1519 = true := by
  have hs : count1519 q = (countLit q [-16]) + (countLit q [-18]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-18])
  have hm := merge_right (literal (valuationOf q) (-18)) (literal (valuationOf q) (1519)) (countLit q [-16]) (countLit q [-18]) (count1519 q) 1 (meaningNeg18 q) (meaning1519 q) hs
  change (! (valuationOf q 18)) = false ∨ valuationOf q 1519 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1049 (q : Snake 81) (h : Conditions q) : valuation q 18 = true ∨ valuation q 1519 = true := counterClause1049 (baseVal q)

theorem counterClause1050 (q : Nat → Bool) : valuationOf q 16 = true ∨ valuationOf q 1519 = true := by
  have hs : count1519 q = (countLit q [-16]) + (countLit q [-18]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-18])
  have hm := merge_left (literal (valuationOf q) (-16)) (literal (valuationOf q) (1519)) (countLit q [-16]) (countLit q [-18]) (count1519 q) 1 (meaningNeg16 q) (meaning1519 q) hs
  change (! (valuationOf q 16)) = false ∨ valuationOf q 1519 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1050 (q : Snake 81) (h : Conditions q) : valuation q 16 = true ∨ valuation q 1519 = true := counterClause1050 (baseVal q)

theorem counterClause1051 (q : Nat → Bool) : valuationOf q 16 = true ∨ valuationOf q 18 = true ∨ valuationOf q 1520 = true := by
  have hs : count1519 q = (countLit q [-16]) + (countLit q [-18]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-18])
  have hm := merge_two (literal (valuationOf q) (-16)) (literal (valuationOf q) (-18)) (literal (valuationOf q) (1520)) (countLit q [-16]) (countLit q [-18]) (count1519 q) 1 1 (meaningNeg16 q) (meaningNeg18 q) (meaning1520 q) hs
  change (! (valuationOf q 16)) = false ∨ (! (valuationOf q 18)) = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1051 (q : Snake 81) (h : Conditions q) : valuation q 16 = true ∨ valuation q 18 = true ∨ valuation q 1520 = true := counterClause1051 (baseVal q)

theorem counterClause1052 (q : Nat → Bool) : valuationOf q 1517 = false ∨ valuationOf q 1521 = true := by
  have hs : count1521 q = (countLit q [-13, -15]) + (countLit q [-16, -18]) := List.countP_append (p := literal q) (l₁ := [-13, -15]) (l₂ := [-16, -18])
  have hm := merge_left (literal (valuationOf q) (1517)) (literal (valuationOf q) (1521)) (countLit q [-13, -15]) (countLit q [-16, -18]) (count1521 q) 1 (meaning1517 q) (meaning1521 q) hs
  change valuationOf q 1517 = false ∨ valuationOf q 1521 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1052 (q : Snake 81) (h : Conditions q) : valuation q 1517 = false ∨ valuation q 1521 = true := counterClause1052 (baseVal q)

theorem counterClause1053 (q : Nat → Bool) : valuationOf q 1517 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1522 = true := by
  have hs : count1521 q = (countLit q [-13, -15]) + (countLit q [-16, -18]) := List.countP_append (p := literal q) (l₁ := [-13, -15]) (l₂ := [-16, -18])
  have hm := merge_two (literal (valuationOf q) (1517)) (literal (valuationOf q) (1519)) (literal (valuationOf q) (1522)) (countLit q [-13, -15]) (countLit q [-16, -18]) (count1521 q) 1 1 (meaning1517 q) (meaning1519 q) (meaning1522 q) hs
  change valuationOf q 1517 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1522 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1053 (q : Snake 81) (h : Conditions q) : valuation q 1517 = false ∨ valuation q 1519 = false ∨ valuation q 1522 = true := counterClause1053 (baseVal q)

theorem counterClause1054 (q : Nat → Bool) : valuationOf q 1517 = false ∨ valuationOf q 1520 = false ∨ valuationOf q 1523 = true := by
  have hs : count1521 q = (countLit q [-13, -15]) + (countLit q [-16, -18]) := List.countP_append (p := literal q) (l₁ := [-13, -15]) (l₂ := [-16, -18])
  have hm := merge_two (literal (valuationOf q) (1517)) (literal (valuationOf q) (1520)) (literal (valuationOf q) (1523)) (countLit q [-13, -15]) (countLit q [-16, -18]) (count1521 q) 1 2 (meaning1517 q) (meaning1520 q) (meaning1523 q) hs
  change valuationOf q 1517 = false ∨ valuationOf q 1520 = false ∨ valuationOf q 1523 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1054 (q : Snake 81) (h : Conditions q) : valuation q 1517 = false ∨ valuation q 1520 = false ∨ valuation q 1523 = true := counterClause1054 (baseVal q)

theorem counterClause1055 (q : Nat → Bool) : valuationOf q 1518 = false ∨ valuationOf q 1522 = true := by
  have hs : count1521 q = (countLit q [-13, -15]) + (countLit q [-16, -18]) := List.countP_append (p := literal q) (l₁ := [-13, -15]) (l₂ := [-16, -18])
  have hm := merge_left (literal (valuationOf q) (1518)) (literal (valuationOf q) (1522)) (countLit q [-13, -15]) (countLit q [-16, -18]) (count1521 q) 2 (meaning1518 q) (meaning1522 q) hs
  change valuationOf q 1518 = false ∨ valuationOf q 1522 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1055 (q : Snake 81) (h : Conditions q) : valuation q 1518 = false ∨ valuation q 1522 = true := counterClause1055 (baseVal q)

theorem counterClause1056 (q : Nat → Bool) : valuationOf q 1518 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1523 = true := by
  have hs : count1521 q = (countLit q [-13, -15]) + (countLit q [-16, -18]) := List.countP_append (p := literal q) (l₁ := [-13, -15]) (l₂ := [-16, -18])
  have hm := merge_two (literal (valuationOf q) (1518)) (literal (valuationOf q) (1519)) (literal (valuationOf q) (1523)) (countLit q [-13, -15]) (countLit q [-16, -18]) (count1521 q) 2 1 (meaning1518 q) (meaning1519 q) (meaning1523 q) hs
  change valuationOf q 1518 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1523 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1056 (q : Snake 81) (h : Conditions q) : valuation q 1518 = false ∨ valuation q 1519 = false ∨ valuation q 1523 = true := counterClause1056 (baseVal q)

theorem block32 (q : Snake 81) (h : Conditions q) : B112E020.Block32 (valuation q) :=
  ⟨clause1025 q h, clause1026 q h, clause1027 q h, clause1028 q h, clause1029 q h, clause1030 q h, clause1031 q h, clause1032 q h, clause1033 q h, clause1034 q h, clause1035 q h, clause1036 q h, clause1037 q h, clause1038 q h, clause1039 q h, clause1040 q h, clause1041 q h, clause1042 q h, clause1043 q h, clause1044 q h, clause1045 q h, clause1046 q h, clause1047 q h, clause1048 q h, clause1049 q h, clause1050 q h, clause1051 q h, clause1052 q h, clause1053 q h, clause1054 q h, clause1055 q h, clause1056 q h⟩

end
end Snake9.Regrowth.E112020
