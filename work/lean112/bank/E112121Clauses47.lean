import E112121Semantics
import B112E121Inputs
namespace Snake9.Regrowth.E112121
noncomputable section
local instance blockDec47 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1505 (q : Nat → Bool) : valuationOf q 103 = true ∨ valuationOf q 1087 = true := by
  have hs : count1087 q = (countLit q [-103]) + (countLit q [-106]) := List.countP_append (p := literal q) (l₁ := [-103]) (l₂ := [-106])
  have hm := merge_left (literal (valuationOf q) (-103)) (literal (valuationOf q) (1087)) (countLit q [-103]) (countLit q [-106]) (count1087 q) 1 (meaningNeg103 q) (meaning1087 q) hs
  change (! (valuationOf q 103)) = false ∨ valuationOf q 1087 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1505 (q : Snake 81) (h : Conditions q) : valuation q 103 = true ∨ valuation q 1087 = true := counterClause1505 (baseVal q)

theorem counterClause1506 (q : Nat → Bool) : valuationOf q 103 = true ∨ valuationOf q 106 = true ∨ valuationOf q 1088 = true := by
  have hs : count1087 q = (countLit q [-103]) + (countLit q [-106]) := List.countP_append (p := literal q) (l₁ := [-103]) (l₂ := [-106])
  have hm := merge_two (literal (valuationOf q) (-103)) (literal (valuationOf q) (-106)) (literal (valuationOf q) (1088)) (countLit q [-103]) (countLit q [-106]) (count1087 q) 1 1 (meaningNeg103 q) (meaningNeg106 q) (meaning1088 q) hs
  change (! (valuationOf q 103)) = false ∨ (! (valuationOf q 106)) = false ∨ valuationOf q 1088 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1506 (q : Snake 81) (h : Conditions q) : valuation q 103 = true ∨ valuation q 106 = true ∨ valuation q 1088 = true := counterClause1506 (baseVal q)

theorem counterClause1507 (q : Nat → Bool) : valuationOf q 109 = true ∨ valuationOf q 1089 = true := by
  have hs : count1089 q = (countLit q [-107]) + (countLit q [-109]) := List.countP_append (p := literal q) (l₁ := [-107]) (l₂ := [-109])
  have hm := merge_right (literal (valuationOf q) (-109)) (literal (valuationOf q) (1089)) (countLit q [-107]) (countLit q [-109]) (count1089 q) 1 (meaningNeg109 q) (meaning1089 q) hs
  change (! (valuationOf q 109)) = false ∨ valuationOf q 1089 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1507 (q : Snake 81) (h : Conditions q) : valuation q 109 = true ∨ valuation q 1089 = true := counterClause1507 (baseVal q)

theorem counterClause1508 (q : Nat → Bool) : valuationOf q 107 = true ∨ valuationOf q 1089 = true := by
  have hs : count1089 q = (countLit q [-107]) + (countLit q [-109]) := List.countP_append (p := literal q) (l₁ := [-107]) (l₂ := [-109])
  have hm := merge_left (literal (valuationOf q) (-107)) (literal (valuationOf q) (1089)) (countLit q [-107]) (countLit q [-109]) (count1089 q) 1 (meaningNeg107 q) (meaning1089 q) hs
  change (! (valuationOf q 107)) = false ∨ valuationOf q 1089 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1508 (q : Snake 81) (h : Conditions q) : valuation q 107 = true ∨ valuation q 1089 = true := counterClause1508 (baseVal q)

theorem counterClause1509 (q : Nat → Bool) : valuationOf q 107 = true ∨ valuationOf q 109 = true ∨ valuationOf q 1090 = true := by
  have hs : count1089 q = (countLit q [-107]) + (countLit q [-109]) := List.countP_append (p := literal q) (l₁ := [-107]) (l₂ := [-109])
  have hm := merge_two (literal (valuationOf q) (-107)) (literal (valuationOf q) (-109)) (literal (valuationOf q) (1090)) (countLit q [-107]) (countLit q [-109]) (count1089 q) 1 1 (meaningNeg107 q) (meaningNeg109 q) (meaning1090 q) hs
  change (! (valuationOf q 107)) = false ∨ (! (valuationOf q 109)) = false ∨ valuationOf q 1090 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1509 (q : Snake 81) (h : Conditions q) : valuation q 107 = true ∨ valuation q 109 = true ∨ valuation q 1090 = true := counterClause1509 (baseVal q)

theorem counterClause1510 (q : Nat → Bool) : valuationOf q 1089 = false ∨ valuationOf q 1091 = true := by
  have hs : count1091 q = (countLit q [-103, -106]) + (countLit q [-107, -109]) := List.countP_append (p := literal q) (l₁ := [-103, -106]) (l₂ := [-107, -109])
  have hm := merge_right (literal (valuationOf q) (1089)) (literal (valuationOf q) (1091)) (countLit q [-103, -106]) (countLit q [-107, -109]) (count1091 q) 1 (meaning1089 q) (meaning1091 q) hs
  change valuationOf q 1089 = false ∨ valuationOf q 1091 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1510 (q : Snake 81) (h : Conditions q) : valuation q 1089 = false ∨ valuation q 1091 = true := counterClause1510 (baseVal q)

theorem counterClause1511 (q : Nat → Bool) : valuationOf q 1090 = false ∨ valuationOf q 1092 = true := by
  have hs : count1091 q = (countLit q [-103, -106]) + (countLit q [-107, -109]) := List.countP_append (p := literal q) (l₁ := [-103, -106]) (l₂ := [-107, -109])
  have hm := merge_right (literal (valuationOf q) (1090)) (literal (valuationOf q) (1092)) (countLit q [-103, -106]) (countLit q [-107, -109]) (count1091 q) 2 (meaning1090 q) (meaning1092 q) hs
  change valuationOf q 1090 = false ∨ valuationOf q 1092 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1511 (q : Snake 81) (h : Conditions q) : valuation q 1090 = false ∨ valuation q 1092 = true := counterClause1511 (baseVal q)

theorem counterClause1512 (q : Nat → Bool) : valuationOf q 1087 = false ∨ valuationOf q 1091 = true := by
  have hs : count1091 q = (countLit q [-103, -106]) + (countLit q [-107, -109]) := List.countP_append (p := literal q) (l₁ := [-103, -106]) (l₂ := [-107, -109])
  have hm := merge_left (literal (valuationOf q) (1087)) (literal (valuationOf q) (1091)) (countLit q [-103, -106]) (countLit q [-107, -109]) (count1091 q) 1 (meaning1087 q) (meaning1091 q) hs
  change valuationOf q 1087 = false ∨ valuationOf q 1091 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1512 (q : Snake 81) (h : Conditions q) : valuation q 1087 = false ∨ valuation q 1091 = true := counterClause1512 (baseVal q)

theorem counterClause1513 (q : Nat → Bool) : valuationOf q 1087 = false ∨ valuationOf q 1089 = false ∨ valuationOf q 1092 = true := by
  have hs : count1091 q = (countLit q [-103, -106]) + (countLit q [-107, -109]) := List.countP_append (p := literal q) (l₁ := [-103, -106]) (l₂ := [-107, -109])
  have hm := merge_two (literal (valuationOf q) (1087)) (literal (valuationOf q) (1089)) (literal (valuationOf q) (1092)) (countLit q [-103, -106]) (countLit q [-107, -109]) (count1091 q) 1 1 (meaning1087 q) (meaning1089 q) (meaning1092 q) hs
  change valuationOf q 1087 = false ∨ valuationOf q 1089 = false ∨ valuationOf q 1092 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1513 (q : Snake 81) (h : Conditions q) : valuation q 1087 = false ∨ valuation q 1089 = false ∨ valuation q 1092 = true := counterClause1513 (baseVal q)

theorem counterClause1514 (q : Nat → Bool) : valuationOf q 1087 = false ∨ valuationOf q 1090 = false ∨ valuationOf q 1093 = true := by
  have hs : count1091 q = (countLit q [-103, -106]) + (countLit q [-107, -109]) := List.countP_append (p := literal q) (l₁ := [-103, -106]) (l₂ := [-107, -109])
  have hm := merge_two (literal (valuationOf q) (1087)) (literal (valuationOf q) (1090)) (literal (valuationOf q) (1093)) (countLit q [-103, -106]) (countLit q [-107, -109]) (count1091 q) 1 2 (meaning1087 q) (meaning1090 q) (meaning1093 q) hs
  change valuationOf q 1087 = false ∨ valuationOf q 1090 = false ∨ valuationOf q 1093 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1514 (q : Snake 81) (h : Conditions q) : valuation q 1087 = false ∨ valuation q 1090 = false ∨ valuation q 1093 = true := counterClause1514 (baseVal q)

theorem counterClause1515 (q : Nat → Bool) : valuationOf q 1088 = false ∨ valuationOf q 1092 = true := by
  have hs : count1091 q = (countLit q [-103, -106]) + (countLit q [-107, -109]) := List.countP_append (p := literal q) (l₁ := [-103, -106]) (l₂ := [-107, -109])
  have hm := merge_left (literal (valuationOf q) (1088)) (literal (valuationOf q) (1092)) (countLit q [-103, -106]) (countLit q [-107, -109]) (count1091 q) 2 (meaning1088 q) (meaning1092 q) hs
  change valuationOf q 1088 = false ∨ valuationOf q 1092 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1515 (q : Snake 81) (h : Conditions q) : valuation q 1088 = false ∨ valuation q 1092 = true := counterClause1515 (baseVal q)

theorem counterClause1516 (q : Nat → Bool) : valuationOf q 1088 = false ∨ valuationOf q 1089 = false ∨ valuationOf q 1093 = true := by
  have hs : count1091 q = (countLit q [-103, -106]) + (countLit q [-107, -109]) := List.countP_append (p := literal q) (l₁ := [-103, -106]) (l₂ := [-107, -109])
  have hm := merge_two (literal (valuationOf q) (1088)) (literal (valuationOf q) (1089)) (literal (valuationOf q) (1093)) (countLit q [-103, -106]) (countLit q [-107, -109]) (count1091 q) 2 1 (meaning1088 q) (meaning1089 q) (meaning1093 q) hs
  change valuationOf q 1088 = false ∨ valuationOf q 1089 = false ∨ valuationOf q 1093 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1516 (q : Snake 81) (h : Conditions q) : valuation q 1088 = false ∨ valuation q 1089 = false ∨ valuation q 1093 = true := counterClause1516 (baseVal q)

theorem counterClause1517 (q : Nat → Bool) : valuationOf q 1088 = false ∨ valuationOf q 1090 = false ∨ valuationOf q 1094 = true := by
  have hs : count1091 q = (countLit q [-103, -106]) + (countLit q [-107, -109]) := List.countP_append (p := literal q) (l₁ := [-103, -106]) (l₂ := [-107, -109])
  have hm := merge_two (literal (valuationOf q) (1088)) (literal (valuationOf q) (1090)) (literal (valuationOf q) (1094)) (countLit q [-103, -106]) (countLit q [-107, -109]) (count1091 q) 2 2 (meaning1088 q) (meaning1090 q) (meaning1094 q) hs
  change valuationOf q 1088 = false ∨ valuationOf q 1090 = false ∨ valuationOf q 1094 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1517 (q : Snake 81) (h : Conditions q) : valuation q 1088 = false ∨ valuation q 1090 = false ∨ valuation q 1094 = true := counterClause1517 (baseVal q)

theorem counterClause1518 (q : Nat → Bool) : valuationOf q 1091 = false ∨ valuationOf q 1095 = true := by
  have hs : count1095 q = (countLit q [-94, -96, -98, -101]) + (countLit q [-103, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -101]) (l₂ := [-103, -106, -107, -109])
  have hm := merge_right (literal (valuationOf q) (1091)) (literal (valuationOf q) (1095)) (countLit q [-94, -96, -98, -101]) (countLit q [-103, -106, -107, -109]) (count1095 q) 1 (meaning1091 q) (meaning1095 q) hs
  change valuationOf q 1091 = false ∨ valuationOf q 1095 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1518 (q : Snake 81) (h : Conditions q) : valuation q 1091 = false ∨ valuation q 1095 = true := counterClause1518 (baseVal q)

theorem counterClause1519 (q : Nat → Bool) : valuationOf q 1092 = false ∨ valuationOf q 1096 = true := by
  have hs : count1095 q = (countLit q [-94, -96, -98, -101]) + (countLit q [-103, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -101]) (l₂ := [-103, -106, -107, -109])
  have hm := merge_right (literal (valuationOf q) (1092)) (literal (valuationOf q) (1096)) (countLit q [-94, -96, -98, -101]) (countLit q [-103, -106, -107, -109]) (count1095 q) 2 (meaning1092 q) (meaning1096 q) hs
  change valuationOf q 1092 = false ∨ valuationOf q 1096 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1519 (q : Snake 81) (h : Conditions q) : valuation q 1092 = false ∨ valuation q 1096 = true := counterClause1519 (baseVal q)

theorem counterClause1520 (q : Nat → Bool) : valuationOf q 1093 = false ∨ valuationOf q 1097 = true := by
  have hs : count1095 q = (countLit q [-94, -96, -98, -101]) + (countLit q [-103, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -101]) (l₂ := [-103, -106, -107, -109])
  have hm := merge_right (literal (valuationOf q) (1093)) (literal (valuationOf q) (1097)) (countLit q [-94, -96, -98, -101]) (countLit q [-103, -106, -107, -109]) (count1095 q) 3 (meaning1093 q) (meaning1097 q) hs
  change valuationOf q 1093 = false ∨ valuationOf q 1097 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1520 (q : Snake 81) (h : Conditions q) : valuation q 1093 = false ∨ valuation q 1097 = true := counterClause1520 (baseVal q)

theorem counterClause1521 (q : Nat → Bool) : valuationOf q 1094 = false ∨ valuationOf q 1098 = true := by
  have hs : count1095 q = (countLit q [-94, -96, -98, -101]) + (countLit q [-103, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -101]) (l₂ := [-103, -106, -107, -109])
  have hm := merge_right (literal (valuationOf q) (1094)) (literal (valuationOf q) (1098)) (countLit q [-94, -96, -98, -101]) (countLit q [-103, -106, -107, -109]) (count1095 q) 4 (meaning1094 q) (meaning1098 q) hs
  change valuationOf q 1094 = false ∨ valuationOf q 1098 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1521 (q : Snake 81) (h : Conditions q) : valuation q 1094 = false ∨ valuation q 1098 = true := counterClause1521 (baseVal q)

theorem counterClause1522 (q : Nat → Bool) : valuationOf q 1083 = false ∨ valuationOf q 1095 = true := by
  have hs : count1095 q = (countLit q [-94, -96, -98, -101]) + (countLit q [-103, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -101]) (l₂ := [-103, -106, -107, -109])
  have hm := merge_left (literal (valuationOf q) (1083)) (literal (valuationOf q) (1095)) (countLit q [-94, -96, -98, -101]) (countLit q [-103, -106, -107, -109]) (count1095 q) 1 (meaning1083 q) (meaning1095 q) hs
  change valuationOf q 1083 = false ∨ valuationOf q 1095 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1522 (q : Snake 81) (h : Conditions q) : valuation q 1083 = false ∨ valuation q 1095 = true := counterClause1522 (baseVal q)

theorem counterClause1523 (q : Nat → Bool) : valuationOf q 1083 = false ∨ valuationOf q 1091 = false ∨ valuationOf q 1096 = true := by
  have hs : count1095 q = (countLit q [-94, -96, -98, -101]) + (countLit q [-103, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -101]) (l₂ := [-103, -106, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1083)) (literal (valuationOf q) (1091)) (literal (valuationOf q) (1096)) (countLit q [-94, -96, -98, -101]) (countLit q [-103, -106, -107, -109]) (count1095 q) 1 1 (meaning1083 q) (meaning1091 q) (meaning1096 q) hs
  change valuationOf q 1083 = false ∨ valuationOf q 1091 = false ∨ valuationOf q 1096 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1523 (q : Snake 81) (h : Conditions q) : valuation q 1083 = false ∨ valuation q 1091 = false ∨ valuation q 1096 = true := counterClause1523 (baseVal q)

theorem counterClause1524 (q : Nat → Bool) : valuationOf q 1083 = false ∨ valuationOf q 1092 = false ∨ valuationOf q 1097 = true := by
  have hs : count1095 q = (countLit q [-94, -96, -98, -101]) + (countLit q [-103, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -101]) (l₂ := [-103, -106, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1083)) (literal (valuationOf q) (1092)) (literal (valuationOf q) (1097)) (countLit q [-94, -96, -98, -101]) (countLit q [-103, -106, -107, -109]) (count1095 q) 1 2 (meaning1083 q) (meaning1092 q) (meaning1097 q) hs
  change valuationOf q 1083 = false ∨ valuationOf q 1092 = false ∨ valuationOf q 1097 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1524 (q : Snake 81) (h : Conditions q) : valuation q 1083 = false ∨ valuation q 1092 = false ∨ valuation q 1097 = true := counterClause1524 (baseVal q)

theorem counterClause1525 (q : Nat → Bool) : valuationOf q 1083 = false ∨ valuationOf q 1093 = false ∨ valuationOf q 1098 = true := by
  have hs : count1095 q = (countLit q [-94, -96, -98, -101]) + (countLit q [-103, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -101]) (l₂ := [-103, -106, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1083)) (literal (valuationOf q) (1093)) (literal (valuationOf q) (1098)) (countLit q [-94, -96, -98, -101]) (countLit q [-103, -106, -107, -109]) (count1095 q) 1 3 (meaning1083 q) (meaning1093 q) (meaning1098 q) hs
  change valuationOf q 1083 = false ∨ valuationOf q 1093 = false ∨ valuationOf q 1098 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1525 (q : Snake 81) (h : Conditions q) : valuation q 1083 = false ∨ valuation q 1093 = false ∨ valuation q 1098 = true := counterClause1525 (baseVal q)

theorem counterClause1526 (q : Nat → Bool) : valuationOf q 1083 = false ∨ valuationOf q 1094 = false ∨ valuationOf q 1099 = true := by
  have hs : count1095 q = (countLit q [-94, -96, -98, -101]) + (countLit q [-103, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -101]) (l₂ := [-103, -106, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1083)) (literal (valuationOf q) (1094)) (literal (valuationOf q) (1099)) (countLit q [-94, -96, -98, -101]) (countLit q [-103, -106, -107, -109]) (count1095 q) 1 4 (meaning1083 q) (meaning1094 q) (meaning1099 q) hs
  change valuationOf q 1083 = false ∨ valuationOf q 1094 = false ∨ valuationOf q 1099 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1526 (q : Snake 81) (h : Conditions q) : valuation q 1083 = false ∨ valuation q 1094 = false ∨ valuation q 1099 = true := counterClause1526 (baseVal q)

theorem counterClause1527 (q : Nat → Bool) : valuationOf q 1084 = false ∨ valuationOf q 1096 = true := by
  have hs : count1095 q = (countLit q [-94, -96, -98, -101]) + (countLit q [-103, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -101]) (l₂ := [-103, -106, -107, -109])
  have hm := merge_left (literal (valuationOf q) (1084)) (literal (valuationOf q) (1096)) (countLit q [-94, -96, -98, -101]) (countLit q [-103, -106, -107, -109]) (count1095 q) 2 (meaning1084 q) (meaning1096 q) hs
  change valuationOf q 1084 = false ∨ valuationOf q 1096 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1527 (q : Snake 81) (h : Conditions q) : valuation q 1084 = false ∨ valuation q 1096 = true := counterClause1527 (baseVal q)

theorem counterClause1528 (q : Nat → Bool) : valuationOf q 1084 = false ∨ valuationOf q 1091 = false ∨ valuationOf q 1097 = true := by
  have hs : count1095 q = (countLit q [-94, -96, -98, -101]) + (countLit q [-103, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -101]) (l₂ := [-103, -106, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1084)) (literal (valuationOf q) (1091)) (literal (valuationOf q) (1097)) (countLit q [-94, -96, -98, -101]) (countLit q [-103, -106, -107, -109]) (count1095 q) 2 1 (meaning1084 q) (meaning1091 q) (meaning1097 q) hs
  change valuationOf q 1084 = false ∨ valuationOf q 1091 = false ∨ valuationOf q 1097 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1528 (q : Snake 81) (h : Conditions q) : valuation q 1084 = false ∨ valuation q 1091 = false ∨ valuation q 1097 = true := counterClause1528 (baseVal q)

theorem counterClause1529 (q : Nat → Bool) : valuationOf q 1084 = false ∨ valuationOf q 1092 = false ∨ valuationOf q 1098 = true := by
  have hs : count1095 q = (countLit q [-94, -96, -98, -101]) + (countLit q [-103, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -101]) (l₂ := [-103, -106, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1084)) (literal (valuationOf q) (1092)) (literal (valuationOf q) (1098)) (countLit q [-94, -96, -98, -101]) (countLit q [-103, -106, -107, -109]) (count1095 q) 2 2 (meaning1084 q) (meaning1092 q) (meaning1098 q) hs
  change valuationOf q 1084 = false ∨ valuationOf q 1092 = false ∨ valuationOf q 1098 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1529 (q : Snake 81) (h : Conditions q) : valuation q 1084 = false ∨ valuation q 1092 = false ∨ valuation q 1098 = true := counterClause1529 (baseVal q)

theorem counterClause1530 (q : Nat → Bool) : valuationOf q 1084 = false ∨ valuationOf q 1093 = false ∨ valuationOf q 1099 = true := by
  have hs : count1095 q = (countLit q [-94, -96, -98, -101]) + (countLit q [-103, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -101]) (l₂ := [-103, -106, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1084)) (literal (valuationOf q) (1093)) (literal (valuationOf q) (1099)) (countLit q [-94, -96, -98, -101]) (countLit q [-103, -106, -107, -109]) (count1095 q) 2 3 (meaning1084 q) (meaning1093 q) (meaning1099 q) hs
  change valuationOf q 1084 = false ∨ valuationOf q 1093 = false ∨ valuationOf q 1099 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1530 (q : Snake 81) (h : Conditions q) : valuation q 1084 = false ∨ valuation q 1093 = false ∨ valuation q 1099 = true := counterClause1530 (baseVal q)

theorem counterClause1531 (q : Nat → Bool) : valuationOf q 1084 = false ∨ valuationOf q 1094 = false ∨ valuationOf q 1100 = true := by
  have hs : count1095 q = (countLit q [-94, -96, -98, -101]) + (countLit q [-103, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -101]) (l₂ := [-103, -106, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1084)) (literal (valuationOf q) (1094)) (literal (valuationOf q) (1100)) (countLit q [-94, -96, -98, -101]) (countLit q [-103, -106, -107, -109]) (count1095 q) 2 4 (meaning1084 q) (meaning1094 q) (meaning1100 q) hs
  change valuationOf q 1084 = false ∨ valuationOf q 1094 = false ∨ valuationOf q 1100 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1531 (q : Snake 81) (h : Conditions q) : valuation q 1084 = false ∨ valuation q 1094 = false ∨ valuation q 1100 = true := counterClause1531 (baseVal q)

theorem counterClause1532 (q : Nat → Bool) : valuationOf q 1085 = false ∨ valuationOf q 1097 = true := by
  have hs : count1095 q = (countLit q [-94, -96, -98, -101]) + (countLit q [-103, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -101]) (l₂ := [-103, -106, -107, -109])
  have hm := merge_left (literal (valuationOf q) (1085)) (literal (valuationOf q) (1097)) (countLit q [-94, -96, -98, -101]) (countLit q [-103, -106, -107, -109]) (count1095 q) 3 (meaning1085 q) (meaning1097 q) hs
  change valuationOf q 1085 = false ∨ valuationOf q 1097 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1532 (q : Snake 81) (h : Conditions q) : valuation q 1085 = false ∨ valuation q 1097 = true := counterClause1532 (baseVal q)

theorem counterClause1533 (q : Nat → Bool) : valuationOf q 1085 = false ∨ valuationOf q 1091 = false ∨ valuationOf q 1098 = true := by
  have hs : count1095 q = (countLit q [-94, -96, -98, -101]) + (countLit q [-103, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -101]) (l₂ := [-103, -106, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1085)) (literal (valuationOf q) (1091)) (literal (valuationOf q) (1098)) (countLit q [-94, -96, -98, -101]) (countLit q [-103, -106, -107, -109]) (count1095 q) 3 1 (meaning1085 q) (meaning1091 q) (meaning1098 q) hs
  change valuationOf q 1085 = false ∨ valuationOf q 1091 = false ∨ valuationOf q 1098 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1533 (q : Snake 81) (h : Conditions q) : valuation q 1085 = false ∨ valuation q 1091 = false ∨ valuation q 1098 = true := counterClause1533 (baseVal q)

theorem counterClause1534 (q : Nat → Bool) : valuationOf q 1085 = false ∨ valuationOf q 1092 = false ∨ valuationOf q 1099 = true := by
  have hs : count1095 q = (countLit q [-94, -96, -98, -101]) + (countLit q [-103, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -101]) (l₂ := [-103, -106, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1085)) (literal (valuationOf q) (1092)) (literal (valuationOf q) (1099)) (countLit q [-94, -96, -98, -101]) (countLit q [-103, -106, -107, -109]) (count1095 q) 3 2 (meaning1085 q) (meaning1092 q) (meaning1099 q) hs
  change valuationOf q 1085 = false ∨ valuationOf q 1092 = false ∨ valuationOf q 1099 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1534 (q : Snake 81) (h : Conditions q) : valuation q 1085 = false ∨ valuation q 1092 = false ∨ valuation q 1099 = true := counterClause1534 (baseVal q)

theorem counterClause1535 (q : Nat → Bool) : valuationOf q 1085 = false ∨ valuationOf q 1093 = false ∨ valuationOf q 1100 = true := by
  have hs : count1095 q = (countLit q [-94, -96, -98, -101]) + (countLit q [-103, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -101]) (l₂ := [-103, -106, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1085)) (literal (valuationOf q) (1093)) (literal (valuationOf q) (1100)) (countLit q [-94, -96, -98, -101]) (countLit q [-103, -106, -107, -109]) (count1095 q) 3 3 (meaning1085 q) (meaning1093 q) (meaning1100 q) hs
  change valuationOf q 1085 = false ∨ valuationOf q 1093 = false ∨ valuationOf q 1100 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1535 (q : Snake 81) (h : Conditions q) : valuation q 1085 = false ∨ valuation q 1093 = false ∨ valuation q 1100 = true := counterClause1535 (baseVal q)

theorem counterClause1536 (q : Nat → Bool) : valuationOf q 1086 = false ∨ valuationOf q 1098 = true := by
  have hs : count1095 q = (countLit q [-94, -96, -98, -101]) + (countLit q [-103, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -101]) (l₂ := [-103, -106, -107, -109])
  have hm := merge_left (literal (valuationOf q) (1086)) (literal (valuationOf q) (1098)) (countLit q [-94, -96, -98, -101]) (countLit q [-103, -106, -107, -109]) (count1095 q) 4 (meaning1086 q) (meaning1098 q) hs
  change valuationOf q 1086 = false ∨ valuationOf q 1098 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1536 (q : Snake 81) (h : Conditions q) : valuation q 1086 = false ∨ valuation q 1098 = true := counterClause1536 (baseVal q)

theorem block47 (q : Snake 81) (h : Conditions q) : B112E121.Block47 (valuation q) :=
  ⟨clause1505 q h, clause1506 q h, clause1507 q h, clause1508 q h, clause1509 q h, clause1510 q h, clause1511 q h, clause1512 q h, clause1513 q h, clause1514 q h, clause1515 q h, clause1516 q h, clause1517 q h, clause1518 q h, clause1519 q h, clause1520 q h, clause1521 q h, clause1522 q h, clause1523 q h, clause1524 q h, clause1525 q h, clause1526 q h, clause1527 q h, clause1528 q h, clause1529 q h, clause1530 q h, clause1531 q h, clause1532 q h, clause1533 q h, clause1534 q h, clause1535 q h, clause1536 q h⟩

end
end Snake9.Regrowth.E112121
