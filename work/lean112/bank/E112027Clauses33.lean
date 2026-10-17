import E112027Semantics
import B112E027Inputs
namespace Snake9.Regrowth.E112027
noncomputable section
local instance blockDec33 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1057 (q : Nat → Bool) : valuationOf q 48 = true ∨ valuationOf q 1511 = true := by
  have hs : count1511 q = (countLit q [-48]) + (countLit q [-52]) := List.countP_append (p := literal q) (l₁ := [-48]) (l₂ := [-52])
  have hm := merge_left (literal (valuationOf q) (-48)) (literal (valuationOf q) (1511)) (countLit q [-48]) (countLit q [-52]) (count1511 q) 1 (meaningNeg48 q) (meaning1511 q) hs
  change (! (valuationOf q 48)) = false ∨ valuationOf q 1511 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1057 (q : Snake 81) (h : Conditions q) : valuation q 48 = true ∨ valuation q 1511 = true := counterClause1057 (baseVal q)

theorem counterClause1058 (q : Nat → Bool) : valuationOf q 48 = true ∨ valuationOf q 52 = true ∨ valuationOf q 1512 = true := by
  have hs : count1511 q = (countLit q [-48]) + (countLit q [-52]) := List.countP_append (p := literal q) (l₁ := [-48]) (l₂ := [-52])
  have hm := merge_two (literal (valuationOf q) (-48)) (literal (valuationOf q) (-52)) (literal (valuationOf q) (1512)) (countLit q [-48]) (countLit q [-52]) (count1511 q) 1 1 (meaningNeg48 q) (meaningNeg52 q) (meaning1512 q) hs
  change (! (valuationOf q 48)) = false ∨ (! (valuationOf q 52)) = false ∨ valuationOf q 1512 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1058 (q : Snake 81) (h : Conditions q) : valuation q 48 = true ∨ valuation q 52 = true ∨ valuation q 1512 = true := counterClause1058 (baseVal q)

theorem counterClause1059 (q : Nat → Bool) : valuationOf q 1511 = false ∨ valuationOf q 1513 = true := by
  have hs : count1513 q = (countLit q [-47]) + (countLit q [-48, -52]) := List.countP_append (p := literal q) (l₁ := [-47]) (l₂ := [-48, -52])
  have hm := merge_right (literal (valuationOf q) (1511)) (literal (valuationOf q) (1513)) (countLit q [-47]) (countLit q [-48, -52]) (count1513 q) 1 (meaning1511 q) (meaning1513 q) hs
  change valuationOf q 1511 = false ∨ valuationOf q 1513 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1059 (q : Snake 81) (h : Conditions q) : valuation q 1511 = false ∨ valuation q 1513 = true := counterClause1059 (baseVal q)

theorem counterClause1060 (q : Nat → Bool) : valuationOf q 1512 = false ∨ valuationOf q 1514 = true := by
  have hs : count1513 q = (countLit q [-47]) + (countLit q [-48, -52]) := List.countP_append (p := literal q) (l₁ := [-47]) (l₂ := [-48, -52])
  have hm := merge_right (literal (valuationOf q) (1512)) (literal (valuationOf q) (1514)) (countLit q [-47]) (countLit q [-48, -52]) (count1513 q) 2 (meaning1512 q) (meaning1514 q) hs
  change valuationOf q 1512 = false ∨ valuationOf q 1514 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1060 (q : Snake 81) (h : Conditions q) : valuation q 1512 = false ∨ valuation q 1514 = true := counterClause1060 (baseVal q)

theorem counterClause1061 (q : Nat → Bool) : valuationOf q 47 = true ∨ valuationOf q 1513 = true := by
  have hs : count1513 q = (countLit q [-47]) + (countLit q [-48, -52]) := List.countP_append (p := literal q) (l₁ := [-47]) (l₂ := [-48, -52])
  have hm := merge_left (literal (valuationOf q) (-47)) (literal (valuationOf q) (1513)) (countLit q [-47]) (countLit q [-48, -52]) (count1513 q) 1 (meaningNeg47 q) (meaning1513 q) hs
  change (! (valuationOf q 47)) = false ∨ valuationOf q 1513 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1061 (q : Snake 81) (h : Conditions q) : valuation q 47 = true ∨ valuation q 1513 = true := counterClause1061 (baseVal q)

theorem counterClause1062 (q : Nat → Bool) : valuationOf q 47 = true ∨ valuationOf q 1511 = false ∨ valuationOf q 1514 = true := by
  have hs : count1513 q = (countLit q [-47]) + (countLit q [-48, -52]) := List.countP_append (p := literal q) (l₁ := [-47]) (l₂ := [-48, -52])
  have hm := merge_two (literal (valuationOf q) (-47)) (literal (valuationOf q) (1511)) (literal (valuationOf q) (1514)) (countLit q [-47]) (countLit q [-48, -52]) (count1513 q) 1 1 (meaningNeg47 q) (meaning1511 q) (meaning1514 q) hs
  change (! (valuationOf q 47)) = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1514 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1062 (q : Snake 81) (h : Conditions q) : valuation q 47 = true ∨ valuation q 1511 = false ∨ valuation q 1514 = true := counterClause1062 (baseVal q)

theorem counterClause1063 (q : Nat → Bool) : valuationOf q 47 = true ∨ valuationOf q 1512 = false ∨ valuationOf q 1515 = true := by
  have hs : count1513 q = (countLit q [-47]) + (countLit q [-48, -52]) := List.countP_append (p := literal q) (l₁ := [-47]) (l₂ := [-48, -52])
  have hm := merge_two (literal (valuationOf q) (-47)) (literal (valuationOf q) (1512)) (literal (valuationOf q) (1515)) (countLit q [-47]) (countLit q [-48, -52]) (count1513 q) 1 2 (meaningNeg47 q) (meaning1512 q) (meaning1515 q) hs
  change (! (valuationOf q 47)) = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1515 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1063 (q : Snake 81) (h : Conditions q) : valuation q 47 = true ∨ valuation q 1512 = false ∨ valuation q 1515 = true := counterClause1063 (baseVal q)

theorem counterClause1064 (q : Nat → Bool) : valuationOf q 55 = true ∨ valuationOf q 1516 = true := by
  have hs : count1516 q = (countLit q [-54]) + (countLit q [-55]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-55])
  have hm := merge_right (literal (valuationOf q) (-55)) (literal (valuationOf q) (1516)) (countLit q [-54]) (countLit q [-55]) (count1516 q) 1 (meaningNeg55 q) (meaning1516 q) hs
  change (! (valuationOf q 55)) = false ∨ valuationOf q 1516 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1064 (q : Snake 81) (h : Conditions q) : valuation q 55 = true ∨ valuation q 1516 = true := counterClause1064 (baseVal q)

theorem counterClause1065 (q : Nat → Bool) : valuationOf q 54 = true ∨ valuationOf q 1516 = true := by
  have hs : count1516 q = (countLit q [-54]) + (countLit q [-55]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-55])
  have hm := merge_left (literal (valuationOf q) (-54)) (literal (valuationOf q) (1516)) (countLit q [-54]) (countLit q [-55]) (count1516 q) 1 (meaningNeg54 q) (meaning1516 q) hs
  change (! (valuationOf q 54)) = false ∨ valuationOf q 1516 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1065 (q : Snake 81) (h : Conditions q) : valuation q 54 = true ∨ valuation q 1516 = true := counterClause1065 (baseVal q)

theorem counterClause1066 (q : Nat → Bool) : valuationOf q 54 = true ∨ valuationOf q 55 = true ∨ valuationOf q 1517 = true := by
  have hs : count1516 q = (countLit q [-54]) + (countLit q [-55]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-55])
  have hm := merge_two (literal (valuationOf q) (-54)) (literal (valuationOf q) (-55)) (literal (valuationOf q) (1517)) (countLit q [-54]) (countLit q [-55]) (count1516 q) 1 1 (meaningNeg54 q) (meaningNeg55 q) (meaning1517 q) hs
  change (! (valuationOf q 54)) = false ∨ (! (valuationOf q 55)) = false ∨ valuationOf q 1517 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1066 (q : Snake 81) (h : Conditions q) : valuation q 54 = true ∨ valuation q 55 = true ∨ valuation q 1517 = true := counterClause1066 (baseVal q)

theorem counterClause1067 (q : Nat → Bool) : valuationOf q 57 = true ∨ valuationOf q 1518 = true := by
  have hs : count1518 q = (countLit q [-56]) + (countLit q [-57]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-57])
  have hm := merge_right (literal (valuationOf q) (-57)) (literal (valuationOf q) (1518)) (countLit q [-56]) (countLit q [-57]) (count1518 q) 1 (meaningNeg57 q) (meaning1518 q) hs
  change (! (valuationOf q 57)) = false ∨ valuationOf q 1518 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1067 (q : Snake 81) (h : Conditions q) : valuation q 57 = true ∨ valuation q 1518 = true := counterClause1067 (baseVal q)

theorem counterClause1068 (q : Nat → Bool) : valuationOf q 56 = true ∨ valuationOf q 1518 = true := by
  have hs : count1518 q = (countLit q [-56]) + (countLit q [-57]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-57])
  have hm := merge_left (literal (valuationOf q) (-56)) (literal (valuationOf q) (1518)) (countLit q [-56]) (countLit q [-57]) (count1518 q) 1 (meaningNeg56 q) (meaning1518 q) hs
  change (! (valuationOf q 56)) = false ∨ valuationOf q 1518 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1068 (q : Snake 81) (h : Conditions q) : valuation q 56 = true ∨ valuation q 1518 = true := counterClause1068 (baseVal q)

theorem counterClause1069 (q : Nat → Bool) : valuationOf q 56 = true ∨ valuationOf q 57 = true ∨ valuationOf q 1519 = true := by
  have hs : count1518 q = (countLit q [-56]) + (countLit q [-57]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-57])
  have hm := merge_two (literal (valuationOf q) (-56)) (literal (valuationOf q) (-57)) (literal (valuationOf q) (1519)) (countLit q [-56]) (countLit q [-57]) (count1518 q) 1 1 (meaningNeg56 q) (meaningNeg57 q) (meaning1519 q) hs
  change (! (valuationOf q 56)) = false ∨ (! (valuationOf q 57)) = false ∨ valuationOf q 1519 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1069 (q : Snake 81) (h : Conditions q) : valuation q 56 = true ∨ valuation q 57 = true ∨ valuation q 1519 = true := counterClause1069 (baseVal q)

theorem counterClause1070 (q : Nat → Bool) : valuationOf q 1518 = false ∨ valuationOf q 1520 = true := by
  have hs : count1520 q = (countLit q [-54, -55]) + (countLit q [-56, -57]) := List.countP_append (p := literal q) (l₁ := [-54, -55]) (l₂ := [-56, -57])
  have hm := merge_right (literal (valuationOf q) (1518)) (literal (valuationOf q) (1520)) (countLit q [-54, -55]) (countLit q [-56, -57]) (count1520 q) 1 (meaning1518 q) (meaning1520 q) hs
  change valuationOf q 1518 = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1070 (q : Snake 81) (h : Conditions q) : valuation q 1518 = false ∨ valuation q 1520 = true := counterClause1070 (baseVal q)

theorem counterClause1071 (q : Nat → Bool) : valuationOf q 1519 = false ∨ valuationOf q 1521 = true := by
  have hs : count1520 q = (countLit q [-54, -55]) + (countLit q [-56, -57]) := List.countP_append (p := literal q) (l₁ := [-54, -55]) (l₂ := [-56, -57])
  have hm := merge_right (literal (valuationOf q) (1519)) (literal (valuationOf q) (1521)) (countLit q [-54, -55]) (countLit q [-56, -57]) (count1520 q) 2 (meaning1519 q) (meaning1521 q) hs
  change valuationOf q 1519 = false ∨ valuationOf q 1521 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1071 (q : Snake 81) (h : Conditions q) : valuation q 1519 = false ∨ valuation q 1521 = true := counterClause1071 (baseVal q)

theorem counterClause1072 (q : Nat → Bool) : valuationOf q 1516 = false ∨ valuationOf q 1520 = true := by
  have hs : count1520 q = (countLit q [-54, -55]) + (countLit q [-56, -57]) := List.countP_append (p := literal q) (l₁ := [-54, -55]) (l₂ := [-56, -57])
  have hm := merge_left (literal (valuationOf q) (1516)) (literal (valuationOf q) (1520)) (countLit q [-54, -55]) (countLit q [-56, -57]) (count1520 q) 1 (meaning1516 q) (meaning1520 q) hs
  change valuationOf q 1516 = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1072 (q : Snake 81) (h : Conditions q) : valuation q 1516 = false ∨ valuation q 1520 = true := counterClause1072 (baseVal q)

theorem counterClause1073 (q : Nat → Bool) : valuationOf q 1516 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1521 = true := by
  have hs : count1520 q = (countLit q [-54, -55]) + (countLit q [-56, -57]) := List.countP_append (p := literal q) (l₁ := [-54, -55]) (l₂ := [-56, -57])
  have hm := merge_two (literal (valuationOf q) (1516)) (literal (valuationOf q) (1518)) (literal (valuationOf q) (1521)) (countLit q [-54, -55]) (countLit q [-56, -57]) (count1520 q) 1 1 (meaning1516 q) (meaning1518 q) (meaning1521 q) hs
  change valuationOf q 1516 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1521 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1073 (q : Snake 81) (h : Conditions q) : valuation q 1516 = false ∨ valuation q 1518 = false ∨ valuation q 1521 = true := counterClause1073 (baseVal q)

theorem counterClause1074 (q : Nat → Bool) : valuationOf q 1516 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1522 = true := by
  have hs : count1520 q = (countLit q [-54, -55]) + (countLit q [-56, -57]) := List.countP_append (p := literal q) (l₁ := [-54, -55]) (l₂ := [-56, -57])
  have hm := merge_two (literal (valuationOf q) (1516)) (literal (valuationOf q) (1519)) (literal (valuationOf q) (1522)) (countLit q [-54, -55]) (countLit q [-56, -57]) (count1520 q) 1 2 (meaning1516 q) (meaning1519 q) (meaning1522 q) hs
  change valuationOf q 1516 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1522 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1074 (q : Snake 81) (h : Conditions q) : valuation q 1516 = false ∨ valuation q 1519 = false ∨ valuation q 1522 = true := counterClause1074 (baseVal q)

theorem counterClause1075 (q : Nat → Bool) : valuationOf q 1517 = false ∨ valuationOf q 1521 = true := by
  have hs : count1520 q = (countLit q [-54, -55]) + (countLit q [-56, -57]) := List.countP_append (p := literal q) (l₁ := [-54, -55]) (l₂ := [-56, -57])
  have hm := merge_left (literal (valuationOf q) (1517)) (literal (valuationOf q) (1521)) (countLit q [-54, -55]) (countLit q [-56, -57]) (count1520 q) 2 (meaning1517 q) (meaning1521 q) hs
  change valuationOf q 1517 = false ∨ valuationOf q 1521 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1075 (q : Snake 81) (h : Conditions q) : valuation q 1517 = false ∨ valuation q 1521 = true := counterClause1075 (baseVal q)

theorem counterClause1076 (q : Nat → Bool) : valuationOf q 1517 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1522 = true := by
  have hs : count1520 q = (countLit q [-54, -55]) + (countLit q [-56, -57]) := List.countP_append (p := literal q) (l₁ := [-54, -55]) (l₂ := [-56, -57])
  have hm := merge_two (literal (valuationOf q) (1517)) (literal (valuationOf q) (1518)) (literal (valuationOf q) (1522)) (countLit q [-54, -55]) (countLit q [-56, -57]) (count1520 q) 2 1 (meaning1517 q) (meaning1518 q) (meaning1522 q) hs
  change valuationOf q 1517 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1522 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1076 (q : Snake 81) (h : Conditions q) : valuation q 1517 = false ∨ valuation q 1518 = false ∨ valuation q 1522 = true := counterClause1076 (baseVal q)

theorem counterClause1077 (q : Nat → Bool) : valuationOf q 1517 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1523 = true := by
  have hs : count1520 q = (countLit q [-54, -55]) + (countLit q [-56, -57]) := List.countP_append (p := literal q) (l₁ := [-54, -55]) (l₂ := [-56, -57])
  have hm := merge_two (literal (valuationOf q) (1517)) (literal (valuationOf q) (1519)) (literal (valuationOf q) (1523)) (countLit q [-54, -55]) (countLit q [-56, -57]) (count1520 q) 2 2 (meaning1517 q) (meaning1519 q) (meaning1523 q) hs
  change valuationOf q 1517 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1523 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1077 (q : Snake 81) (h : Conditions q) : valuation q 1517 = false ∨ valuation q 1519 = false ∨ valuation q 1523 = true := counterClause1077 (baseVal q)

theorem counterClause1078 (q : Nat → Bool) : valuationOf q 1520 = false ∨ valuationOf q 1524 = true := by
  have hs : count1524 q = (countLit q [-47, -48, -52]) + (countLit q [-54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-47, -48, -52]) (l₂ := [-54, -55, -56, -57])
  have hm := merge_right (literal (valuationOf q) (1520)) (literal (valuationOf q) (1524)) (countLit q [-47, -48, -52]) (countLit q [-54, -55, -56, -57]) (count1524 q) 1 (meaning1520 q) (meaning1524 q) hs
  change valuationOf q 1520 = false ∨ valuationOf q 1524 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1078 (q : Snake 81) (h : Conditions q) : valuation q 1520 = false ∨ valuation q 1524 = true := counterClause1078 (baseVal q)

theorem counterClause1079 (q : Nat → Bool) : valuationOf q 1521 = false ∨ valuationOf q 1525 = true := by
  have hs : count1524 q = (countLit q [-47, -48, -52]) + (countLit q [-54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-47, -48, -52]) (l₂ := [-54, -55, -56, -57])
  have hm := merge_right (literal (valuationOf q) (1521)) (literal (valuationOf q) (1525)) (countLit q [-47, -48, -52]) (countLit q [-54, -55, -56, -57]) (count1524 q) 2 (meaning1521 q) (meaning1525 q) hs
  change valuationOf q 1521 = false ∨ valuationOf q 1525 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1079 (q : Snake 81) (h : Conditions q) : valuation q 1521 = false ∨ valuation q 1525 = true := counterClause1079 (baseVal q)

theorem counterClause1080 (q : Nat → Bool) : valuationOf q 1522 = false ∨ valuationOf q 1526 = true := by
  have hs : count1524 q = (countLit q [-47, -48, -52]) + (countLit q [-54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-47, -48, -52]) (l₂ := [-54, -55, -56, -57])
  have hm := merge_right (literal (valuationOf q) (1522)) (literal (valuationOf q) (1526)) (countLit q [-47, -48, -52]) (countLit q [-54, -55, -56, -57]) (count1524 q) 3 (meaning1522 q) (meaning1526 q) hs
  change valuationOf q 1522 = false ∨ valuationOf q 1526 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1080 (q : Snake 81) (h : Conditions q) : valuation q 1522 = false ∨ valuation q 1526 = true := counterClause1080 (baseVal q)

theorem counterClause1081 (q : Nat → Bool) : valuationOf q 1523 = false ∨ valuationOf q 1527 = true := by
  have hs : count1524 q = (countLit q [-47, -48, -52]) + (countLit q [-54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-47, -48, -52]) (l₂ := [-54, -55, -56, -57])
  have hm := merge_right (literal (valuationOf q) (1523)) (literal (valuationOf q) (1527)) (countLit q [-47, -48, -52]) (countLit q [-54, -55, -56, -57]) (count1524 q) 4 (meaning1523 q) (meaning1527 q) hs
  change valuationOf q 1523 = false ∨ valuationOf q 1527 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1081 (q : Snake 81) (h : Conditions q) : valuation q 1523 = false ∨ valuation q 1527 = true := counterClause1081 (baseVal q)

theorem counterClause1082 (q : Nat → Bool) : valuationOf q 1513 = false ∨ valuationOf q 1524 = true := by
  have hs : count1524 q = (countLit q [-47, -48, -52]) + (countLit q [-54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-47, -48, -52]) (l₂ := [-54, -55, -56, -57])
  have hm := merge_left (literal (valuationOf q) (1513)) (literal (valuationOf q) (1524)) (countLit q [-47, -48, -52]) (countLit q [-54, -55, -56, -57]) (count1524 q) 1 (meaning1513 q) (meaning1524 q) hs
  change valuationOf q 1513 = false ∨ valuationOf q 1524 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1082 (q : Snake 81) (h : Conditions q) : valuation q 1513 = false ∨ valuation q 1524 = true := counterClause1082 (baseVal q)

theorem counterClause1083 (q : Nat → Bool) : valuationOf q 1513 = false ∨ valuationOf q 1520 = false ∨ valuationOf q 1525 = true := by
  have hs : count1524 q = (countLit q [-47, -48, -52]) + (countLit q [-54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-47, -48, -52]) (l₂ := [-54, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1513)) (literal (valuationOf q) (1520)) (literal (valuationOf q) (1525)) (countLit q [-47, -48, -52]) (countLit q [-54, -55, -56, -57]) (count1524 q) 1 1 (meaning1513 q) (meaning1520 q) (meaning1525 q) hs
  change valuationOf q 1513 = false ∨ valuationOf q 1520 = false ∨ valuationOf q 1525 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1083 (q : Snake 81) (h : Conditions q) : valuation q 1513 = false ∨ valuation q 1520 = false ∨ valuation q 1525 = true := counterClause1083 (baseVal q)

theorem counterClause1084 (q : Nat → Bool) : valuationOf q 1513 = false ∨ valuationOf q 1521 = false ∨ valuationOf q 1526 = true := by
  have hs : count1524 q = (countLit q [-47, -48, -52]) + (countLit q [-54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-47, -48, -52]) (l₂ := [-54, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1513)) (literal (valuationOf q) (1521)) (literal (valuationOf q) (1526)) (countLit q [-47, -48, -52]) (countLit q [-54, -55, -56, -57]) (count1524 q) 1 2 (meaning1513 q) (meaning1521 q) (meaning1526 q) hs
  change valuationOf q 1513 = false ∨ valuationOf q 1521 = false ∨ valuationOf q 1526 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1084 (q : Snake 81) (h : Conditions q) : valuation q 1513 = false ∨ valuation q 1521 = false ∨ valuation q 1526 = true := counterClause1084 (baseVal q)

theorem counterClause1085 (q : Nat → Bool) : valuationOf q 1513 = false ∨ valuationOf q 1522 = false ∨ valuationOf q 1527 = true := by
  have hs : count1524 q = (countLit q [-47, -48, -52]) + (countLit q [-54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-47, -48, -52]) (l₂ := [-54, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1513)) (literal (valuationOf q) (1522)) (literal (valuationOf q) (1527)) (countLit q [-47, -48, -52]) (countLit q [-54, -55, -56, -57]) (count1524 q) 1 3 (meaning1513 q) (meaning1522 q) (meaning1527 q) hs
  change valuationOf q 1513 = false ∨ valuationOf q 1522 = false ∨ valuationOf q 1527 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1085 (q : Snake 81) (h : Conditions q) : valuation q 1513 = false ∨ valuation q 1522 = false ∨ valuation q 1527 = true := counterClause1085 (baseVal q)

theorem counterClause1086 (q : Nat → Bool) : valuationOf q 1513 = false ∨ valuationOf q 1523 = false ∨ valuationOf q 1528 = true := by
  have hs : count1524 q = (countLit q [-47, -48, -52]) + (countLit q [-54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-47, -48, -52]) (l₂ := [-54, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1513)) (literal (valuationOf q) (1523)) (literal (valuationOf q) (1528)) (countLit q [-47, -48, -52]) (countLit q [-54, -55, -56, -57]) (count1524 q) 1 4 (meaning1513 q) (meaning1523 q) (meaning1528 q) hs
  change valuationOf q 1513 = false ∨ valuationOf q 1523 = false ∨ valuationOf q 1528 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1086 (q : Snake 81) (h : Conditions q) : valuation q 1513 = false ∨ valuation q 1523 = false ∨ valuation q 1528 = true := counterClause1086 (baseVal q)

theorem counterClause1087 (q : Nat → Bool) : valuationOf q 1514 = false ∨ valuationOf q 1525 = true := by
  have hs : count1524 q = (countLit q [-47, -48, -52]) + (countLit q [-54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-47, -48, -52]) (l₂ := [-54, -55, -56, -57])
  have hm := merge_left (literal (valuationOf q) (1514)) (literal (valuationOf q) (1525)) (countLit q [-47, -48, -52]) (countLit q [-54, -55, -56, -57]) (count1524 q) 2 (meaning1514 q) (meaning1525 q) hs
  change valuationOf q 1514 = false ∨ valuationOf q 1525 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1087 (q : Snake 81) (h : Conditions q) : valuation q 1514 = false ∨ valuation q 1525 = true := counterClause1087 (baseVal q)

theorem counterClause1088 (q : Nat → Bool) : valuationOf q 1514 = false ∨ valuationOf q 1520 = false ∨ valuationOf q 1526 = true := by
  have hs : count1524 q = (countLit q [-47, -48, -52]) + (countLit q [-54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-47, -48, -52]) (l₂ := [-54, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1514)) (literal (valuationOf q) (1520)) (literal (valuationOf q) (1526)) (countLit q [-47, -48, -52]) (countLit q [-54, -55, -56, -57]) (count1524 q) 2 1 (meaning1514 q) (meaning1520 q) (meaning1526 q) hs
  change valuationOf q 1514 = false ∨ valuationOf q 1520 = false ∨ valuationOf q 1526 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1088 (q : Snake 81) (h : Conditions q) : valuation q 1514 = false ∨ valuation q 1520 = false ∨ valuation q 1526 = true := counterClause1088 (baseVal q)

theorem block33 (q : Snake 81) (h : Conditions q) : B112E027.Block33 (valuation q) :=
  ⟨clause1057 q h, clause1058 q h, clause1059 q h, clause1060 q h, clause1061 q h, clause1062 q h, clause1063 q h, clause1064 q h, clause1065 q h, clause1066 q h, clause1067 q h, clause1068 q h, clause1069 q h, clause1070 q h, clause1071 q h, clause1072 q h, clause1073 q h, clause1074 q h, clause1075 q h, clause1076 q h, clause1077 q h, clause1078 q h, clause1079 q h, clause1080 q h, clause1081 q h, clause1082 q h, clause1083 q h, clause1084 q h, clause1085 q h, clause1086 q h, clause1087 q h, clause1088 q h⟩

end
end Snake9.Regrowth.E112027
