import E112008Semantics
import B112E008Inputs
namespace Snake9.Regrowth.E112008
noncomputable section
local instance blockDec32 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1025 (q : Nat → Bool) : valuationOf q 10 = true ∨ valuationOf q 1510 = true := by
  have hs : count1510 q = (countLit q [-8]) + (countLit q [-10]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-10])
  have hm := merge_right (literal (valuationOf q) (-10)) (literal (valuationOf q) (1510)) (countLit q [-8]) (countLit q [-10]) (count1510 q) 1 (meaningNeg10 q) (meaning1510 q) hs
  change (! (valuationOf q 10)) = false ∨ valuationOf q 1510 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1025 (q : Snake 81) (h : Conditions q) : valuation q 10 = true ∨ valuation q 1510 = true := counterClause1025 (baseVal q)

theorem counterClause1026 (q : Nat → Bool) : valuationOf q 8 = true ∨ valuationOf q 1510 = true := by
  have hs : count1510 q = (countLit q [-8]) + (countLit q [-10]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-10])
  have hm := merge_left (literal (valuationOf q) (-8)) (literal (valuationOf q) (1510)) (countLit q [-8]) (countLit q [-10]) (count1510 q) 1 (meaningNeg8 q) (meaning1510 q) hs
  change (! (valuationOf q 8)) = false ∨ valuationOf q 1510 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1026 (q : Snake 81) (h : Conditions q) : valuation q 8 = true ∨ valuation q 1510 = true := counterClause1026 (baseVal q)

theorem counterClause1027 (q : Nat → Bool) : valuationOf q 8 = true ∨ valuationOf q 10 = true ∨ valuationOf q 1511 = true := by
  have hs : count1510 q = (countLit q [-8]) + (countLit q [-10]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-10])
  have hm := merge_two (literal (valuationOf q) (-8)) (literal (valuationOf q) (-10)) (literal (valuationOf q) (1511)) (countLit q [-8]) (countLit q [-10]) (count1510 q) 1 1 (meaningNeg8 q) (meaningNeg10 q) (meaning1511 q) hs
  change (! (valuationOf q 8)) = false ∨ (! (valuationOf q 10)) = false ∨ valuationOf q 1511 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1027 (q : Snake 81) (h : Conditions q) : valuation q 8 = true ∨ valuation q 10 = true ∨ valuation q 1511 = true := counterClause1027 (baseVal q)

theorem counterClause1028 (q : Nat → Bool) : valuationOf q 13 = true ∨ valuationOf q 1512 = true := by
  have hs : count1512 q = (countLit q [-12]) + (countLit q [-13]) := List.countP_append (p := literal q) (l₁ := [-12]) (l₂ := [-13])
  have hm := merge_right (literal (valuationOf q) (-13)) (literal (valuationOf q) (1512)) (countLit q [-12]) (countLit q [-13]) (count1512 q) 1 (meaningNeg13 q) (meaning1512 q) hs
  change (! (valuationOf q 13)) = false ∨ valuationOf q 1512 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1028 (q : Snake 81) (h : Conditions q) : valuation q 13 = true ∨ valuation q 1512 = true := counterClause1028 (baseVal q)

theorem counterClause1029 (q : Nat → Bool) : valuationOf q 12 = true ∨ valuationOf q 1512 = true := by
  have hs : count1512 q = (countLit q [-12]) + (countLit q [-13]) := List.countP_append (p := literal q) (l₁ := [-12]) (l₂ := [-13])
  have hm := merge_left (literal (valuationOf q) (-12)) (literal (valuationOf q) (1512)) (countLit q [-12]) (countLit q [-13]) (count1512 q) 1 (meaningNeg12 q) (meaning1512 q) hs
  change (! (valuationOf q 12)) = false ∨ valuationOf q 1512 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1029 (q : Snake 81) (h : Conditions q) : valuation q 12 = true ∨ valuation q 1512 = true := counterClause1029 (baseVal q)

theorem counterClause1030 (q : Nat → Bool) : valuationOf q 12 = true ∨ valuationOf q 13 = true ∨ valuationOf q 1513 = true := by
  have hs : count1512 q = (countLit q [-12]) + (countLit q [-13]) := List.countP_append (p := literal q) (l₁ := [-12]) (l₂ := [-13])
  have hm := merge_two (literal (valuationOf q) (-12)) (literal (valuationOf q) (-13)) (literal (valuationOf q) (1513)) (countLit q [-12]) (countLit q [-13]) (count1512 q) 1 1 (meaningNeg12 q) (meaningNeg13 q) (meaning1513 q) hs
  change (! (valuationOf q 12)) = false ∨ (! (valuationOf q 13)) = false ∨ valuationOf q 1513 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1030 (q : Snake 81) (h : Conditions q) : valuation q 12 = true ∨ valuation q 13 = true ∨ valuation q 1513 = true := counterClause1030 (baseVal q)

theorem counterClause1031 (q : Nat → Bool) : valuationOf q 1512 = false ∨ valuationOf q 1514 = true := by
  have hs : count1514 q = (countLit q [-8, -10]) + (countLit q [-12, -13]) := List.countP_append (p := literal q) (l₁ := [-8, -10]) (l₂ := [-12, -13])
  have hm := merge_right (literal (valuationOf q) (1512)) (literal (valuationOf q) (1514)) (countLit q [-8, -10]) (countLit q [-12, -13]) (count1514 q) 1 (meaning1512 q) (meaning1514 q) hs
  change valuationOf q 1512 = false ∨ valuationOf q 1514 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1031 (q : Snake 81) (h : Conditions q) : valuation q 1512 = false ∨ valuation q 1514 = true := counterClause1031 (baseVal q)

theorem counterClause1032 (q : Nat → Bool) : valuationOf q 1513 = false ∨ valuationOf q 1515 = true := by
  have hs : count1514 q = (countLit q [-8, -10]) + (countLit q [-12, -13]) := List.countP_append (p := literal q) (l₁ := [-8, -10]) (l₂ := [-12, -13])
  have hm := merge_right (literal (valuationOf q) (1513)) (literal (valuationOf q) (1515)) (countLit q [-8, -10]) (countLit q [-12, -13]) (count1514 q) 2 (meaning1513 q) (meaning1515 q) hs
  change valuationOf q 1513 = false ∨ valuationOf q 1515 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1032 (q : Snake 81) (h : Conditions q) : valuation q 1513 = false ∨ valuation q 1515 = true := counterClause1032 (baseVal q)

theorem counterClause1033 (q : Nat → Bool) : valuationOf q 1510 = false ∨ valuationOf q 1514 = true := by
  have hs : count1514 q = (countLit q [-8, -10]) + (countLit q [-12, -13]) := List.countP_append (p := literal q) (l₁ := [-8, -10]) (l₂ := [-12, -13])
  have hm := merge_left (literal (valuationOf q) (1510)) (literal (valuationOf q) (1514)) (countLit q [-8, -10]) (countLit q [-12, -13]) (count1514 q) 1 (meaning1510 q) (meaning1514 q) hs
  change valuationOf q 1510 = false ∨ valuationOf q 1514 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1033 (q : Snake 81) (h : Conditions q) : valuation q 1510 = false ∨ valuation q 1514 = true := counterClause1033 (baseVal q)

theorem counterClause1034 (q : Nat → Bool) : valuationOf q 1510 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1515 = true := by
  have hs : count1514 q = (countLit q [-8, -10]) + (countLit q [-12, -13]) := List.countP_append (p := literal q) (l₁ := [-8, -10]) (l₂ := [-12, -13])
  have hm := merge_two (literal (valuationOf q) (1510)) (literal (valuationOf q) (1512)) (literal (valuationOf q) (1515)) (countLit q [-8, -10]) (countLit q [-12, -13]) (count1514 q) 1 1 (meaning1510 q) (meaning1512 q) (meaning1515 q) hs
  change valuationOf q 1510 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1515 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1034 (q : Snake 81) (h : Conditions q) : valuation q 1510 = false ∨ valuation q 1512 = false ∨ valuation q 1515 = true := counterClause1034 (baseVal q)

theorem counterClause1035 (q : Nat → Bool) : valuationOf q 1510 = false ∨ valuationOf q 1513 = false ∨ valuationOf q 1516 = true := by
  have hs : count1514 q = (countLit q [-8, -10]) + (countLit q [-12, -13]) := List.countP_append (p := literal q) (l₁ := [-8, -10]) (l₂ := [-12, -13])
  have hm := merge_two (literal (valuationOf q) (1510)) (literal (valuationOf q) (1513)) (literal (valuationOf q) (1516)) (countLit q [-8, -10]) (countLit q [-12, -13]) (count1514 q) 1 2 (meaning1510 q) (meaning1513 q) (meaning1516 q) hs
  change valuationOf q 1510 = false ∨ valuationOf q 1513 = false ∨ valuationOf q 1516 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1035 (q : Snake 81) (h : Conditions q) : valuation q 1510 = false ∨ valuation q 1513 = false ∨ valuation q 1516 = true := counterClause1035 (baseVal q)

theorem counterClause1036 (q : Nat → Bool) : valuationOf q 1511 = false ∨ valuationOf q 1515 = true := by
  have hs : count1514 q = (countLit q [-8, -10]) + (countLit q [-12, -13]) := List.countP_append (p := literal q) (l₁ := [-8, -10]) (l₂ := [-12, -13])
  have hm := merge_left (literal (valuationOf q) (1511)) (literal (valuationOf q) (1515)) (countLit q [-8, -10]) (countLit q [-12, -13]) (count1514 q) 2 (meaning1511 q) (meaning1515 q) hs
  change valuationOf q 1511 = false ∨ valuationOf q 1515 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1036 (q : Snake 81) (h : Conditions q) : valuation q 1511 = false ∨ valuation q 1515 = true := counterClause1036 (baseVal q)

theorem counterClause1037 (q : Nat → Bool) : valuationOf q 1511 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1516 = true := by
  have hs : count1514 q = (countLit q [-8, -10]) + (countLit q [-12, -13]) := List.countP_append (p := literal q) (l₁ := [-8, -10]) (l₂ := [-12, -13])
  have hm := merge_two (literal (valuationOf q) (1511)) (literal (valuationOf q) (1512)) (literal (valuationOf q) (1516)) (countLit q [-8, -10]) (countLit q [-12, -13]) (count1514 q) 2 1 (meaning1511 q) (meaning1512 q) (meaning1516 q) hs
  change valuationOf q 1511 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1516 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1037 (q : Snake 81) (h : Conditions q) : valuation q 1511 = false ∨ valuation q 1512 = false ∨ valuation q 1516 = true := counterClause1037 (baseVal q)

theorem counterClause1038 (q : Nat → Bool) : valuationOf q 1514 = false ∨ valuationOf q 1518 = true := by
  have hs : count1518 q = (countLit q [-3, -5, -6]) + (countLit q [-8, -10, -12, -13]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6]) (l₂ := [-8, -10, -12, -13])
  have hm := merge_right (literal (valuationOf q) (1514)) (literal (valuationOf q) (1518)) (countLit q [-3, -5, -6]) (countLit q [-8, -10, -12, -13]) (count1518 q) 1 (meaning1514 q) (meaning1518 q) hs
  change valuationOf q 1514 = false ∨ valuationOf q 1518 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1038 (q : Snake 81) (h : Conditions q) : valuation q 1514 = false ∨ valuation q 1518 = true := counterClause1038 (baseVal q)

theorem counterClause1039 (q : Nat → Bool) : valuationOf q 1515 = false ∨ valuationOf q 1519 = true := by
  have hs : count1518 q = (countLit q [-3, -5, -6]) + (countLit q [-8, -10, -12, -13]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6]) (l₂ := [-8, -10, -12, -13])
  have hm := merge_right (literal (valuationOf q) (1515)) (literal (valuationOf q) (1519)) (countLit q [-3, -5, -6]) (countLit q [-8, -10, -12, -13]) (count1518 q) 2 (meaning1515 q) (meaning1519 q) hs
  change valuationOf q 1515 = false ∨ valuationOf q 1519 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1039 (q : Snake 81) (h : Conditions q) : valuation q 1515 = false ∨ valuation q 1519 = true := counterClause1039 (baseVal q)

theorem counterClause1040 (q : Nat → Bool) : valuationOf q 1516 = false ∨ valuationOf q 1520 = true := by
  have hs : count1518 q = (countLit q [-3, -5, -6]) + (countLit q [-8, -10, -12, -13]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6]) (l₂ := [-8, -10, -12, -13])
  have hm := merge_right (literal (valuationOf q) (1516)) (literal (valuationOf q) (1520)) (countLit q [-3, -5, -6]) (countLit q [-8, -10, -12, -13]) (count1518 q) 3 (meaning1516 q) (meaning1520 q) hs
  change valuationOf q 1516 = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1040 (q : Snake 81) (h : Conditions q) : valuation q 1516 = false ∨ valuation q 1520 = true := counterClause1040 (baseVal q)

theorem counterClause1041 (q : Nat → Bool) : valuationOf q 1507 = false ∨ valuationOf q 1518 = true := by
  have hs : count1518 q = (countLit q [-3, -5, -6]) + (countLit q [-8, -10, -12, -13]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6]) (l₂ := [-8, -10, -12, -13])
  have hm := merge_left (literal (valuationOf q) (1507)) (literal (valuationOf q) (1518)) (countLit q [-3, -5, -6]) (countLit q [-8, -10, -12, -13]) (count1518 q) 1 (meaning1507 q) (meaning1518 q) hs
  change valuationOf q 1507 = false ∨ valuationOf q 1518 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1041 (q : Snake 81) (h : Conditions q) : valuation q 1507 = false ∨ valuation q 1518 = true := counterClause1041 (baseVal q)

theorem counterClause1042 (q : Nat → Bool) : valuationOf q 1507 = false ∨ valuationOf q 1514 = false ∨ valuationOf q 1519 = true := by
  have hs : count1518 q = (countLit q [-3, -5, -6]) + (countLit q [-8, -10, -12, -13]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6]) (l₂ := [-8, -10, -12, -13])
  have hm := merge_two (literal (valuationOf q) (1507)) (literal (valuationOf q) (1514)) (literal (valuationOf q) (1519)) (countLit q [-3, -5, -6]) (countLit q [-8, -10, -12, -13]) (count1518 q) 1 1 (meaning1507 q) (meaning1514 q) (meaning1519 q) hs
  change valuationOf q 1507 = false ∨ valuationOf q 1514 = false ∨ valuationOf q 1519 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1042 (q : Snake 81) (h : Conditions q) : valuation q 1507 = false ∨ valuation q 1514 = false ∨ valuation q 1519 = true := counterClause1042 (baseVal q)

theorem counterClause1043 (q : Nat → Bool) : valuationOf q 1507 = false ∨ valuationOf q 1515 = false ∨ valuationOf q 1520 = true := by
  have hs : count1518 q = (countLit q [-3, -5, -6]) + (countLit q [-8, -10, -12, -13]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6]) (l₂ := [-8, -10, -12, -13])
  have hm := merge_two (literal (valuationOf q) (1507)) (literal (valuationOf q) (1515)) (literal (valuationOf q) (1520)) (countLit q [-3, -5, -6]) (countLit q [-8, -10, -12, -13]) (count1518 q) 1 2 (meaning1507 q) (meaning1515 q) (meaning1520 q) hs
  change valuationOf q 1507 = false ∨ valuationOf q 1515 = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1043 (q : Snake 81) (h : Conditions q) : valuation q 1507 = false ∨ valuation q 1515 = false ∨ valuation q 1520 = true := counterClause1043 (baseVal q)

theorem counterClause1044 (q : Nat → Bool) : valuationOf q 1507 = false ∨ valuationOf q 1516 = false ∨ valuationOf q 1521 = true := by
  have hs : count1518 q = (countLit q [-3, -5, -6]) + (countLit q [-8, -10, -12, -13]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6]) (l₂ := [-8, -10, -12, -13])
  have hm := merge_two (literal (valuationOf q) (1507)) (literal (valuationOf q) (1516)) (literal (valuationOf q) (1521)) (countLit q [-3, -5, -6]) (countLit q [-8, -10, -12, -13]) (count1518 q) 1 3 (meaning1507 q) (meaning1516 q) (meaning1521 q) hs
  change valuationOf q 1507 = false ∨ valuationOf q 1516 = false ∨ valuationOf q 1521 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1044 (q : Snake 81) (h : Conditions q) : valuation q 1507 = false ∨ valuation q 1516 = false ∨ valuation q 1521 = true := counterClause1044 (baseVal q)

theorem counterClause1045 (q : Nat → Bool) : valuationOf q 1508 = false ∨ valuationOf q 1519 = true := by
  have hs : count1518 q = (countLit q [-3, -5, -6]) + (countLit q [-8, -10, -12, -13]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6]) (l₂ := [-8, -10, -12, -13])
  have hm := merge_left (literal (valuationOf q) (1508)) (literal (valuationOf q) (1519)) (countLit q [-3, -5, -6]) (countLit q [-8, -10, -12, -13]) (count1518 q) 2 (meaning1508 q) (meaning1519 q) hs
  change valuationOf q 1508 = false ∨ valuationOf q 1519 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1045 (q : Snake 81) (h : Conditions q) : valuation q 1508 = false ∨ valuation q 1519 = true := counterClause1045 (baseVal q)

theorem counterClause1046 (q : Nat → Bool) : valuationOf q 1508 = false ∨ valuationOf q 1514 = false ∨ valuationOf q 1520 = true := by
  have hs : count1518 q = (countLit q [-3, -5, -6]) + (countLit q [-8, -10, -12, -13]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6]) (l₂ := [-8, -10, -12, -13])
  have hm := merge_two (literal (valuationOf q) (1508)) (literal (valuationOf q) (1514)) (literal (valuationOf q) (1520)) (countLit q [-3, -5, -6]) (countLit q [-8, -10, -12, -13]) (count1518 q) 2 1 (meaning1508 q) (meaning1514 q) (meaning1520 q) hs
  change valuationOf q 1508 = false ∨ valuationOf q 1514 = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1046 (q : Snake 81) (h : Conditions q) : valuation q 1508 = false ∨ valuation q 1514 = false ∨ valuation q 1520 = true := counterClause1046 (baseVal q)

theorem counterClause1047 (q : Nat → Bool) : valuationOf q 1508 = false ∨ valuationOf q 1515 = false ∨ valuationOf q 1521 = true := by
  have hs : count1518 q = (countLit q [-3, -5, -6]) + (countLit q [-8, -10, -12, -13]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6]) (l₂ := [-8, -10, -12, -13])
  have hm := merge_two (literal (valuationOf q) (1508)) (literal (valuationOf q) (1515)) (literal (valuationOf q) (1521)) (countLit q [-3, -5, -6]) (countLit q [-8, -10, -12, -13]) (count1518 q) 2 2 (meaning1508 q) (meaning1515 q) (meaning1521 q) hs
  change valuationOf q 1508 = false ∨ valuationOf q 1515 = false ∨ valuationOf q 1521 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1047 (q : Snake 81) (h : Conditions q) : valuation q 1508 = false ∨ valuation q 1515 = false ∨ valuation q 1521 = true := counterClause1047 (baseVal q)

theorem counterClause1048 (q : Nat → Bool) : valuationOf q 1508 = false ∨ valuationOf q 1516 = false ∨ valuationOf q 1522 = true := by
  have hs : count1518 q = (countLit q [-3, -5, -6]) + (countLit q [-8, -10, -12, -13]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6]) (l₂ := [-8, -10, -12, -13])
  have hm := merge_two (literal (valuationOf q) (1508)) (literal (valuationOf q) (1516)) (literal (valuationOf q) (1522)) (countLit q [-3, -5, -6]) (countLit q [-8, -10, -12, -13]) (count1518 q) 2 3 (meaning1508 q) (meaning1516 q) (meaning1522 q) hs
  change valuationOf q 1508 = false ∨ valuationOf q 1516 = false ∨ valuationOf q 1522 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1048 (q : Snake 81) (h : Conditions q) : valuation q 1508 = false ∨ valuation q 1516 = false ∨ valuation q 1522 = true := counterClause1048 (baseVal q)

theorem counterClause1049 (q : Nat → Bool) : valuationOf q 1509 = false ∨ valuationOf q 1520 = true := by
  have hs : count1518 q = (countLit q [-3, -5, -6]) + (countLit q [-8, -10, -12, -13]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6]) (l₂ := [-8, -10, -12, -13])
  have hm := merge_left (literal (valuationOf q) (1509)) (literal (valuationOf q) (1520)) (countLit q [-3, -5, -6]) (countLit q [-8, -10, -12, -13]) (count1518 q) 3 (meaning1509 q) (meaning1520 q) hs
  change valuationOf q 1509 = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1049 (q : Snake 81) (h : Conditions q) : valuation q 1509 = false ∨ valuation q 1520 = true := counterClause1049 (baseVal q)

theorem counterClause1050 (q : Nat → Bool) : valuationOf q 1509 = false ∨ valuationOf q 1514 = false ∨ valuationOf q 1521 = true := by
  have hs : count1518 q = (countLit q [-3, -5, -6]) + (countLit q [-8, -10, -12, -13]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6]) (l₂ := [-8, -10, -12, -13])
  have hm := merge_two (literal (valuationOf q) (1509)) (literal (valuationOf q) (1514)) (literal (valuationOf q) (1521)) (countLit q [-3, -5, -6]) (countLit q [-8, -10, -12, -13]) (count1518 q) 3 1 (meaning1509 q) (meaning1514 q) (meaning1521 q) hs
  change valuationOf q 1509 = false ∨ valuationOf q 1514 = false ∨ valuationOf q 1521 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1050 (q : Snake 81) (h : Conditions q) : valuation q 1509 = false ∨ valuation q 1514 = false ∨ valuation q 1521 = true := counterClause1050 (baseVal q)

theorem counterClause1051 (q : Nat → Bool) : valuationOf q 1509 = false ∨ valuationOf q 1515 = false ∨ valuationOf q 1522 = true := by
  have hs : count1518 q = (countLit q [-3, -5, -6]) + (countLit q [-8, -10, -12, -13]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6]) (l₂ := [-8, -10, -12, -13])
  have hm := merge_two (literal (valuationOf q) (1509)) (literal (valuationOf q) (1515)) (literal (valuationOf q) (1522)) (countLit q [-3, -5, -6]) (countLit q [-8, -10, -12, -13]) (count1518 q) 3 2 (meaning1509 q) (meaning1515 q) (meaning1522 q) hs
  change valuationOf q 1509 = false ∨ valuationOf q 1515 = false ∨ valuationOf q 1522 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1051 (q : Snake 81) (h : Conditions q) : valuation q 1509 = false ∨ valuation q 1515 = false ∨ valuation q 1522 = true := counterClause1051 (baseVal q)

theorem counterClause1052 (q : Nat → Bool) : valuationOf q 1509 = false ∨ valuationOf q 1516 = false ∨ valuationOf q 1523 = true := by
  have hs : count1518 q = (countLit q [-3, -5, -6]) + (countLit q [-8, -10, -12, -13]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6]) (l₂ := [-8, -10, -12, -13])
  have hm := merge_two (literal (valuationOf q) (1509)) (literal (valuationOf q) (1516)) (literal (valuationOf q) (1523)) (countLit q [-3, -5, -6]) (countLit q [-8, -10, -12, -13]) (count1518 q) 3 3 (meaning1509 q) (meaning1516 q) (meaning1523 q) hs
  change valuationOf q 1509 = false ∨ valuationOf q 1516 = false ∨ valuationOf q 1523 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1052 (q : Snake 81) (h : Conditions q) : valuation q 1509 = false ∨ valuation q 1516 = false ∨ valuation q 1523 = true := counterClause1052 (baseVal q)

theorem counterClause1053 (q : Nat → Bool) : valuationOf q 17 = true ∨ valuationOf q 1525 = true := by
  have hs : count1525 q = (countLit q [-14]) + (countLit q [-17]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-17])
  have hm := merge_right (literal (valuationOf q) (-17)) (literal (valuationOf q) (1525)) (countLit q [-14]) (countLit q [-17]) (count1525 q) 1 (meaningNeg17 q) (meaning1525 q) hs
  change (! (valuationOf q 17)) = false ∨ valuationOf q 1525 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1053 (q : Snake 81) (h : Conditions q) : valuation q 17 = true ∨ valuation q 1525 = true := counterClause1053 (baseVal q)

theorem counterClause1054 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 1525 = true := by
  have hs : count1525 q = (countLit q [-14]) + (countLit q [-17]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-17])
  have hm := merge_left (literal (valuationOf q) (-14)) (literal (valuationOf q) (1525)) (countLit q [-14]) (countLit q [-17]) (count1525 q) 1 (meaningNeg14 q) (meaning1525 q) hs
  change (! (valuationOf q 14)) = false ∨ valuationOf q 1525 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1054 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 1525 = true := counterClause1054 (baseVal q)

theorem counterClause1055 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 17 = true ∨ valuationOf q 1526 = true := by
  have hs : count1525 q = (countLit q [-14]) + (countLit q [-17]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-17])
  have hm := merge_two (literal (valuationOf q) (-14)) (literal (valuationOf q) (-17)) (literal (valuationOf q) (1526)) (countLit q [-14]) (countLit q [-17]) (count1525 q) 1 1 (meaningNeg14 q) (meaningNeg17 q) (meaning1526 q) hs
  change (! (valuationOf q 14)) = false ∨ (! (valuationOf q 17)) = false ∨ valuationOf q 1526 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1055 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 17 = true ∨ valuation q 1526 = true := counterClause1055 (baseVal q)

theorem counterClause1056 (q : Nat → Bool) : valuationOf q 20 = true ∨ valuationOf q 1527 = true := by
  have hs : count1527 q = (countLit q [-19]) + (countLit q [-20]) := List.countP_append (p := literal q) (l₁ := [-19]) (l₂ := [-20])
  have hm := merge_right (literal (valuationOf q) (-20)) (literal (valuationOf q) (1527)) (countLit q [-19]) (countLit q [-20]) (count1527 q) 1 (meaningNeg20 q) (meaning1527 q) hs
  change (! (valuationOf q 20)) = false ∨ valuationOf q 1527 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1056 (q : Snake 81) (h : Conditions q) : valuation q 20 = true ∨ valuation q 1527 = true := counterClause1056 (baseVal q)

theorem block32 (q : Snake 81) (h : Conditions q) : B112E008.Block32 (valuation q) :=
  ⟨clause1025 q h, clause1026 q h, clause1027 q h, clause1028 q h, clause1029 q h, clause1030 q h, clause1031 q h, clause1032 q h, clause1033 q h, clause1034 q h, clause1035 q h, clause1036 q h, clause1037 q h, clause1038 q h, clause1039 q h, clause1040 q h, clause1041 q h, clause1042 q h, clause1043 q h, clause1044 q h, clause1045 q h, clause1046 q h, clause1047 q h, clause1048 q h, clause1049 q h, clause1050 q h, clause1051 q h, clause1052 q h, clause1053 q h, clause1054 q h, clause1055 q h, clause1056 q h⟩

end
end Snake9.Regrowth.E112008
