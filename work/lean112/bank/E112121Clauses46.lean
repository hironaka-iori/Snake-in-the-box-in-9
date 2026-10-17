import E112121Semantics
import B112E121Inputs
namespace Snake9.Regrowth.E112121
noncomputable section
local instance blockDec46 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1473 (q : Nat → Bool) : valuationOf q 1031 = false ∨ valuationOf q 1058 = false ∨ valuationOf q 1067 = true := by
  have hs : count1063 q = (countLit q [-63, -66, -68, -69, -71, -74, -77, -78]) + (countLit q [-79, -81, -85, -86, -88, -89, -90, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69, -71, -74, -77, -78]) (l₂ := [-79, -81, -85, -86, -88, -89, -90, -93])
  have hm := merge_two (literal (valuationOf q) (1031)) (literal (valuationOf q) (1058)) (literal (valuationOf q) (1067)) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78]) (countLit q [-79, -81, -85, -86, -88, -89, -90, -93]) (count1063 q) 1 4 (meaning1031 q) (meaning1058 q) (meaning1067 q) hs
  change valuationOf q 1031 = false ∨ valuationOf q 1058 = false ∨ valuationOf q 1067 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1473 (q : Snake 81) (h : Conditions q) : valuation q 1031 = false ∨ valuation q 1058 = false ∨ valuation q 1067 = true := counterClause1473 (baseVal q)

theorem counterClause1474 (q : Nat → Bool) : valuationOf q 1031 = false ∨ valuationOf q 1059 = false ∨ valuationOf q 1068 = true := by
  have hs : count1063 q = (countLit q [-63, -66, -68, -69, -71, -74, -77, -78]) + (countLit q [-79, -81, -85, -86, -88, -89, -90, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69, -71, -74, -77, -78]) (l₂ := [-79, -81, -85, -86, -88, -89, -90, -93])
  have hm := merge_two (literal (valuationOf q) (1031)) (literal (valuationOf q) (1059)) (literal (valuationOf q) (1068)) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78]) (countLit q [-79, -81, -85, -86, -88, -89, -90, -93]) (count1063 q) 1 5 (meaning1031 q) (meaning1059 q) (meaning1068 q) hs
  change valuationOf q 1031 = false ∨ valuationOf q 1059 = false ∨ valuationOf q 1068 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1474 (q : Snake 81) (h : Conditions q) : valuation q 1031 = false ∨ valuation q 1059 = false ∨ valuation q 1068 = true := counterClause1474 (baseVal q)

theorem counterClause1475 (q : Nat → Bool) : valuationOf q 1031 = false ∨ valuationOf q 1060 = false ∨ valuationOf q 1069 = true := by
  have hs : count1063 q = (countLit q [-63, -66, -68, -69, -71, -74, -77, -78]) + (countLit q [-79, -81, -85, -86, -88, -89, -90, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69, -71, -74, -77, -78]) (l₂ := [-79, -81, -85, -86, -88, -89, -90, -93])
  have hm := merge_two (literal (valuationOf q) (1031)) (literal (valuationOf q) (1060)) (literal (valuationOf q) (1069)) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78]) (countLit q [-79, -81, -85, -86, -88, -89, -90, -93]) (count1063 q) 1 6 (meaning1031 q) (meaning1060 q) (meaning1069 q) hs
  change valuationOf q 1031 = false ∨ valuationOf q 1060 = false ∨ valuationOf q 1069 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1475 (q : Snake 81) (h : Conditions q) : valuation q 1031 = false ∨ valuation q 1060 = false ∨ valuation q 1069 = true := counterClause1475 (baseVal q)

theorem counterClause1476 (q : Nat → Bool) : valuationOf q 1032 = false ∨ valuationOf q 1055 = false ∨ valuationOf q 1065 = true := by
  have hs : count1063 q = (countLit q [-63, -66, -68, -69, -71, -74, -77, -78]) + (countLit q [-79, -81, -85, -86, -88, -89, -90, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69, -71, -74, -77, -78]) (l₂ := [-79, -81, -85, -86, -88, -89, -90, -93])
  have hm := merge_two (literal (valuationOf q) (1032)) (literal (valuationOf q) (1055)) (literal (valuationOf q) (1065)) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78]) (countLit q [-79, -81, -85, -86, -88, -89, -90, -93]) (count1063 q) 2 1 (meaning1032 q) (meaning1055 q) (meaning1065 q) hs
  change valuationOf q 1032 = false ∨ valuationOf q 1055 = false ∨ valuationOf q 1065 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1476 (q : Snake 81) (h : Conditions q) : valuation q 1032 = false ∨ valuation q 1055 = false ∨ valuation q 1065 = true := counterClause1476 (baseVal q)

theorem counterClause1477 (q : Nat → Bool) : valuationOf q 1032 = false ∨ valuationOf q 1056 = false ∨ valuationOf q 1066 = true := by
  have hs : count1063 q = (countLit q [-63, -66, -68, -69, -71, -74, -77, -78]) + (countLit q [-79, -81, -85, -86, -88, -89, -90, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69, -71, -74, -77, -78]) (l₂ := [-79, -81, -85, -86, -88, -89, -90, -93])
  have hm := merge_two (literal (valuationOf q) (1032)) (literal (valuationOf q) (1056)) (literal (valuationOf q) (1066)) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78]) (countLit q [-79, -81, -85, -86, -88, -89, -90, -93]) (count1063 q) 2 2 (meaning1032 q) (meaning1056 q) (meaning1066 q) hs
  change valuationOf q 1032 = false ∨ valuationOf q 1056 = false ∨ valuationOf q 1066 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1477 (q : Snake 81) (h : Conditions q) : valuation q 1032 = false ∨ valuation q 1056 = false ∨ valuation q 1066 = true := counterClause1477 (baseVal q)

theorem counterClause1478 (q : Nat → Bool) : valuationOf q 1032 = false ∨ valuationOf q 1057 = false ∨ valuationOf q 1067 = true := by
  have hs : count1063 q = (countLit q [-63, -66, -68, -69, -71, -74, -77, -78]) + (countLit q [-79, -81, -85, -86, -88, -89, -90, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69, -71, -74, -77, -78]) (l₂ := [-79, -81, -85, -86, -88, -89, -90, -93])
  have hm := merge_two (literal (valuationOf q) (1032)) (literal (valuationOf q) (1057)) (literal (valuationOf q) (1067)) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78]) (countLit q [-79, -81, -85, -86, -88, -89, -90, -93]) (count1063 q) 2 3 (meaning1032 q) (meaning1057 q) (meaning1067 q) hs
  change valuationOf q 1032 = false ∨ valuationOf q 1057 = false ∨ valuationOf q 1067 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1478 (q : Snake 81) (h : Conditions q) : valuation q 1032 = false ∨ valuation q 1057 = false ∨ valuation q 1067 = true := counterClause1478 (baseVal q)

theorem counterClause1479 (q : Nat → Bool) : valuationOf q 1032 = false ∨ valuationOf q 1058 = false ∨ valuationOf q 1068 = true := by
  have hs : count1063 q = (countLit q [-63, -66, -68, -69, -71, -74, -77, -78]) + (countLit q [-79, -81, -85, -86, -88, -89, -90, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69, -71, -74, -77, -78]) (l₂ := [-79, -81, -85, -86, -88, -89, -90, -93])
  have hm := merge_two (literal (valuationOf q) (1032)) (literal (valuationOf q) (1058)) (literal (valuationOf q) (1068)) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78]) (countLit q [-79, -81, -85, -86, -88, -89, -90, -93]) (count1063 q) 2 4 (meaning1032 q) (meaning1058 q) (meaning1068 q) hs
  change valuationOf q 1032 = false ∨ valuationOf q 1058 = false ∨ valuationOf q 1068 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1479 (q : Snake 81) (h : Conditions q) : valuation q 1032 = false ∨ valuation q 1058 = false ∨ valuation q 1068 = true := counterClause1479 (baseVal q)

theorem counterClause1480 (q : Nat → Bool) : valuationOf q 1032 = false ∨ valuationOf q 1059 = false ∨ valuationOf q 1069 = true := by
  have hs : count1063 q = (countLit q [-63, -66, -68, -69, -71, -74, -77, -78]) + (countLit q [-79, -81, -85, -86, -88, -89, -90, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69, -71, -74, -77, -78]) (l₂ := [-79, -81, -85, -86, -88, -89, -90, -93])
  have hm := merge_two (literal (valuationOf q) (1032)) (literal (valuationOf q) (1059)) (literal (valuationOf q) (1069)) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78]) (countLit q [-79, -81, -85, -86, -88, -89, -90, -93]) (count1063 q) 2 5 (meaning1032 q) (meaning1059 q) (meaning1069 q) hs
  change valuationOf q 1032 = false ∨ valuationOf q 1059 = false ∨ valuationOf q 1069 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1480 (q : Snake 81) (h : Conditions q) : valuation q 1032 = false ∨ valuation q 1059 = false ∨ valuation q 1069 = true := counterClause1480 (baseVal q)

theorem counterClause1481 (q : Nat → Bool) : valuationOf q 1032 = false ∨ valuationOf q 1060 = false ∨ valuationOf q 1070 = true := by
  have hs : count1063 q = (countLit q [-63, -66, -68, -69, -71, -74, -77, -78]) + (countLit q [-79, -81, -85, -86, -88, -89, -90, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69, -71, -74, -77, -78]) (l₂ := [-79, -81, -85, -86, -88, -89, -90, -93])
  have hm := merge_two (literal (valuationOf q) (1032)) (literal (valuationOf q) (1060)) (literal (valuationOf q) (1070)) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78]) (countLit q [-79, -81, -85, -86, -88, -89, -90, -93]) (count1063 q) 2 6 (meaning1032 q) (meaning1060 q) (meaning1070 q) hs
  change valuationOf q 1032 = false ∨ valuationOf q 1060 = false ∨ valuationOf q 1070 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1481 (q : Snake 81) (h : Conditions q) : valuation q 1032 = false ∨ valuation q 1060 = false ∨ valuation q 1070 = true := counterClause1481 (baseVal q)

theorem counterClause1482 (q : Nat → Bool) : valuationOf q 1033 = false ∨ valuationOf q 1056 = false ∨ valuationOf q 1067 = true := by
  have hs : count1063 q = (countLit q [-63, -66, -68, -69, -71, -74, -77, -78]) + (countLit q [-79, -81, -85, -86, -88, -89, -90, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69, -71, -74, -77, -78]) (l₂ := [-79, -81, -85, -86, -88, -89, -90, -93])
  have hm := merge_two (literal (valuationOf q) (1033)) (literal (valuationOf q) (1056)) (literal (valuationOf q) (1067)) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78]) (countLit q [-79, -81, -85, -86, -88, -89, -90, -93]) (count1063 q) 3 2 (meaning1033 q) (meaning1056 q) (meaning1067 q) hs
  change valuationOf q 1033 = false ∨ valuationOf q 1056 = false ∨ valuationOf q 1067 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1482 (q : Snake 81) (h : Conditions q) : valuation q 1033 = false ∨ valuation q 1056 = false ∨ valuation q 1067 = true := counterClause1482 (baseVal q)

theorem counterClause1483 (q : Nat → Bool) : valuationOf q 1033 = false ∨ valuationOf q 1057 = false ∨ valuationOf q 1068 = true := by
  have hs : count1063 q = (countLit q [-63, -66, -68, -69, -71, -74, -77, -78]) + (countLit q [-79, -81, -85, -86, -88, -89, -90, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69, -71, -74, -77, -78]) (l₂ := [-79, -81, -85, -86, -88, -89, -90, -93])
  have hm := merge_two (literal (valuationOf q) (1033)) (literal (valuationOf q) (1057)) (literal (valuationOf q) (1068)) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78]) (countLit q [-79, -81, -85, -86, -88, -89, -90, -93]) (count1063 q) 3 3 (meaning1033 q) (meaning1057 q) (meaning1068 q) hs
  change valuationOf q 1033 = false ∨ valuationOf q 1057 = false ∨ valuationOf q 1068 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1483 (q : Snake 81) (h : Conditions q) : valuation q 1033 = false ∨ valuation q 1057 = false ∨ valuation q 1068 = true := counterClause1483 (baseVal q)

theorem counterClause1484 (q : Nat → Bool) : valuationOf q 1033 = false ∨ valuationOf q 1058 = false ∨ valuationOf q 1069 = true := by
  have hs : count1063 q = (countLit q [-63, -66, -68, -69, -71, -74, -77, -78]) + (countLit q [-79, -81, -85, -86, -88, -89, -90, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69, -71, -74, -77, -78]) (l₂ := [-79, -81, -85, -86, -88, -89, -90, -93])
  have hm := merge_two (literal (valuationOf q) (1033)) (literal (valuationOf q) (1058)) (literal (valuationOf q) (1069)) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78]) (countLit q [-79, -81, -85, -86, -88, -89, -90, -93]) (count1063 q) 3 4 (meaning1033 q) (meaning1058 q) (meaning1069 q) hs
  change valuationOf q 1033 = false ∨ valuationOf q 1058 = false ∨ valuationOf q 1069 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1484 (q : Snake 81) (h : Conditions q) : valuation q 1033 = false ∨ valuation q 1058 = false ∨ valuation q 1069 = true := counterClause1484 (baseVal q)

theorem counterClause1485 (q : Nat → Bool) : valuationOf q 1033 = false ∨ valuationOf q 1059 = false ∨ valuationOf q 1070 = true := by
  have hs : count1063 q = (countLit q [-63, -66, -68, -69, -71, -74, -77, -78]) + (countLit q [-79, -81, -85, -86, -88, -89, -90, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69, -71, -74, -77, -78]) (l₂ := [-79, -81, -85, -86, -88, -89, -90, -93])
  have hm := merge_two (literal (valuationOf q) (1033)) (literal (valuationOf q) (1059)) (literal (valuationOf q) (1070)) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78]) (countLit q [-79, -81, -85, -86, -88, -89, -90, -93]) (count1063 q) 3 5 (meaning1033 q) (meaning1059 q) (meaning1070 q) hs
  change valuationOf q 1033 = false ∨ valuationOf q 1059 = false ∨ valuationOf q 1070 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1485 (q : Snake 81) (h : Conditions q) : valuation q 1033 = false ∨ valuation q 1059 = false ∨ valuation q 1070 = true := counterClause1485 (baseVal q)

theorem counterClause1486 (q : Nat → Bool) : valuationOf q 1034 = false ∨ valuationOf q 1056 = false ∨ valuationOf q 1068 = true := by
  have hs : count1063 q = (countLit q [-63, -66, -68, -69, -71, -74, -77, -78]) + (countLit q [-79, -81, -85, -86, -88, -89, -90, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69, -71, -74, -77, -78]) (l₂ := [-79, -81, -85, -86, -88, -89, -90, -93])
  have hm := merge_two (literal (valuationOf q) (1034)) (literal (valuationOf q) (1056)) (literal (valuationOf q) (1068)) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78]) (countLit q [-79, -81, -85, -86, -88, -89, -90, -93]) (count1063 q) 4 2 (meaning1034 q) (meaning1056 q) (meaning1068 q) hs
  change valuationOf q 1034 = false ∨ valuationOf q 1056 = false ∨ valuationOf q 1068 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1486 (q : Snake 81) (h : Conditions q) : valuation q 1034 = false ∨ valuation q 1056 = false ∨ valuation q 1068 = true := counterClause1486 (baseVal q)

theorem counterClause1487 (q : Nat → Bool) : valuationOf q 1034 = false ∨ valuationOf q 1057 = false ∨ valuationOf q 1069 = true := by
  have hs : count1063 q = (countLit q [-63, -66, -68, -69, -71, -74, -77, -78]) + (countLit q [-79, -81, -85, -86, -88, -89, -90, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69, -71, -74, -77, -78]) (l₂ := [-79, -81, -85, -86, -88, -89, -90, -93])
  have hm := merge_two (literal (valuationOf q) (1034)) (literal (valuationOf q) (1057)) (literal (valuationOf q) (1069)) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78]) (countLit q [-79, -81, -85, -86, -88, -89, -90, -93]) (count1063 q) 4 3 (meaning1034 q) (meaning1057 q) (meaning1069 q) hs
  change valuationOf q 1034 = false ∨ valuationOf q 1057 = false ∨ valuationOf q 1069 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1487 (q : Snake 81) (h : Conditions q) : valuation q 1034 = false ∨ valuation q 1057 = false ∨ valuation q 1069 = true := counterClause1487 (baseVal q)

theorem counterClause1488 (q : Nat → Bool) : valuationOf q 1034 = false ∨ valuationOf q 1058 = false ∨ valuationOf q 1070 = true := by
  have hs : count1063 q = (countLit q [-63, -66, -68, -69, -71, -74, -77, -78]) + (countLit q [-79, -81, -85, -86, -88, -89, -90, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69, -71, -74, -77, -78]) (l₂ := [-79, -81, -85, -86, -88, -89, -90, -93])
  have hm := merge_two (literal (valuationOf q) (1034)) (literal (valuationOf q) (1058)) (literal (valuationOf q) (1070)) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78]) (countLit q [-79, -81, -85, -86, -88, -89, -90, -93]) (count1063 q) 4 4 (meaning1034 q) (meaning1058 q) (meaning1070 q) hs
  change valuationOf q 1034 = false ∨ valuationOf q 1058 = false ∨ valuationOf q 1070 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1488 (q : Snake 81) (h : Conditions q) : valuation q 1034 = false ∨ valuation q 1058 = false ∨ valuation q 1070 = true := counterClause1488 (baseVal q)

theorem counterClause1489 (q : Nat → Bool) : valuationOf q 1035 = false ∨ valuationOf q 1056 = false ∨ valuationOf q 1069 = true := by
  have hs : count1063 q = (countLit q [-63, -66, -68, -69, -71, -74, -77, -78]) + (countLit q [-79, -81, -85, -86, -88, -89, -90, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69, -71, -74, -77, -78]) (l₂ := [-79, -81, -85, -86, -88, -89, -90, -93])
  have hm := merge_two (literal (valuationOf q) (1035)) (literal (valuationOf q) (1056)) (literal (valuationOf q) (1069)) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78]) (countLit q [-79, -81, -85, -86, -88, -89, -90, -93]) (count1063 q) 5 2 (meaning1035 q) (meaning1056 q) (meaning1069 q) hs
  change valuationOf q 1035 = false ∨ valuationOf q 1056 = false ∨ valuationOf q 1069 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1489 (q : Snake 81) (h : Conditions q) : valuation q 1035 = false ∨ valuation q 1056 = false ∨ valuation q 1069 = true := counterClause1489 (baseVal q)

theorem counterClause1490 (q : Nat → Bool) : valuationOf q 96 = true ∨ valuationOf q 1079 = true := by
  have hs : count1079 q = (countLit q [-94]) + (countLit q [-96]) := List.countP_append (p := literal q) (l₁ := [-94]) (l₂ := [-96])
  have hm := merge_right (literal (valuationOf q) (-96)) (literal (valuationOf q) (1079)) (countLit q [-94]) (countLit q [-96]) (count1079 q) 1 (meaningNeg96 q) (meaning1079 q) hs
  change (! (valuationOf q 96)) = false ∨ valuationOf q 1079 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1490 (q : Snake 81) (h : Conditions q) : valuation q 96 = true ∨ valuation q 1079 = true := counterClause1490 (baseVal q)

theorem counterClause1491 (q : Nat → Bool) : valuationOf q 94 = true ∨ valuationOf q 1079 = true := by
  have hs : count1079 q = (countLit q [-94]) + (countLit q [-96]) := List.countP_append (p := literal q) (l₁ := [-94]) (l₂ := [-96])
  have hm := merge_left (literal (valuationOf q) (-94)) (literal (valuationOf q) (1079)) (countLit q [-94]) (countLit q [-96]) (count1079 q) 1 (meaningNeg94 q) (meaning1079 q) hs
  change (! (valuationOf q 94)) = false ∨ valuationOf q 1079 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1491 (q : Snake 81) (h : Conditions q) : valuation q 94 = true ∨ valuation q 1079 = true := counterClause1491 (baseVal q)

theorem counterClause1492 (q : Nat → Bool) : valuationOf q 94 = true ∨ valuationOf q 96 = true ∨ valuationOf q 1080 = true := by
  have hs : count1079 q = (countLit q [-94]) + (countLit q [-96]) := List.countP_append (p := literal q) (l₁ := [-94]) (l₂ := [-96])
  have hm := merge_two (literal (valuationOf q) (-94)) (literal (valuationOf q) (-96)) (literal (valuationOf q) (1080)) (countLit q [-94]) (countLit q [-96]) (count1079 q) 1 1 (meaningNeg94 q) (meaningNeg96 q) (meaning1080 q) hs
  change (! (valuationOf q 94)) = false ∨ (! (valuationOf q 96)) = false ∨ valuationOf q 1080 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1492 (q : Snake 81) (h : Conditions q) : valuation q 94 = true ∨ valuation q 96 = true ∨ valuation q 1080 = true := counterClause1492 (baseVal q)

theorem counterClause1493 (q : Nat → Bool) : valuationOf q 101 = true ∨ valuationOf q 1081 = true := by
  have hs : count1081 q = (countLit q [-98]) + (countLit q [-101]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-101])
  have hm := merge_right (literal (valuationOf q) (-101)) (literal (valuationOf q) (1081)) (countLit q [-98]) (countLit q [-101]) (count1081 q) 1 (meaningNeg101 q) (meaning1081 q) hs
  change (! (valuationOf q 101)) = false ∨ valuationOf q 1081 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1493 (q : Snake 81) (h : Conditions q) : valuation q 101 = true ∨ valuation q 1081 = true := counterClause1493 (baseVal q)

theorem counterClause1494 (q : Nat → Bool) : valuationOf q 98 = true ∨ valuationOf q 1081 = true := by
  have hs : count1081 q = (countLit q [-98]) + (countLit q [-101]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-101])
  have hm := merge_left (literal (valuationOf q) (-98)) (literal (valuationOf q) (1081)) (countLit q [-98]) (countLit q [-101]) (count1081 q) 1 (meaningNeg98 q) (meaning1081 q) hs
  change (! (valuationOf q 98)) = false ∨ valuationOf q 1081 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1494 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 1081 = true := counterClause1494 (baseVal q)

theorem counterClause1495 (q : Nat → Bool) : valuationOf q 98 = true ∨ valuationOf q 101 = true ∨ valuationOf q 1082 = true := by
  have hs : count1081 q = (countLit q [-98]) + (countLit q [-101]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-101])
  have hm := merge_two (literal (valuationOf q) (-98)) (literal (valuationOf q) (-101)) (literal (valuationOf q) (1082)) (countLit q [-98]) (countLit q [-101]) (count1081 q) 1 1 (meaningNeg98 q) (meaningNeg101 q) (meaning1082 q) hs
  change (! (valuationOf q 98)) = false ∨ (! (valuationOf q 101)) = false ∨ valuationOf q 1082 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1495 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 101 = true ∨ valuation q 1082 = true := counterClause1495 (baseVal q)

theorem counterClause1496 (q : Nat → Bool) : valuationOf q 1081 = false ∨ valuationOf q 1083 = true := by
  have hs : count1083 q = (countLit q [-94, -96]) + (countLit q [-98, -101]) := List.countP_append (p := literal q) (l₁ := [-94, -96]) (l₂ := [-98, -101])
  have hm := merge_right (literal (valuationOf q) (1081)) (literal (valuationOf q) (1083)) (countLit q [-94, -96]) (countLit q [-98, -101]) (count1083 q) 1 (meaning1081 q) (meaning1083 q) hs
  change valuationOf q 1081 = false ∨ valuationOf q 1083 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1496 (q : Snake 81) (h : Conditions q) : valuation q 1081 = false ∨ valuation q 1083 = true := counterClause1496 (baseVal q)

theorem counterClause1497 (q : Nat → Bool) : valuationOf q 1082 = false ∨ valuationOf q 1084 = true := by
  have hs : count1083 q = (countLit q [-94, -96]) + (countLit q [-98, -101]) := List.countP_append (p := literal q) (l₁ := [-94, -96]) (l₂ := [-98, -101])
  have hm := merge_right (literal (valuationOf q) (1082)) (literal (valuationOf q) (1084)) (countLit q [-94, -96]) (countLit q [-98, -101]) (count1083 q) 2 (meaning1082 q) (meaning1084 q) hs
  change valuationOf q 1082 = false ∨ valuationOf q 1084 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1497 (q : Snake 81) (h : Conditions q) : valuation q 1082 = false ∨ valuation q 1084 = true := counterClause1497 (baseVal q)

theorem counterClause1498 (q : Nat → Bool) : valuationOf q 1079 = false ∨ valuationOf q 1083 = true := by
  have hs : count1083 q = (countLit q [-94, -96]) + (countLit q [-98, -101]) := List.countP_append (p := literal q) (l₁ := [-94, -96]) (l₂ := [-98, -101])
  have hm := merge_left (literal (valuationOf q) (1079)) (literal (valuationOf q) (1083)) (countLit q [-94, -96]) (countLit q [-98, -101]) (count1083 q) 1 (meaning1079 q) (meaning1083 q) hs
  change valuationOf q 1079 = false ∨ valuationOf q 1083 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1498 (q : Snake 81) (h : Conditions q) : valuation q 1079 = false ∨ valuation q 1083 = true := counterClause1498 (baseVal q)

theorem counterClause1499 (q : Nat → Bool) : valuationOf q 1079 = false ∨ valuationOf q 1081 = false ∨ valuationOf q 1084 = true := by
  have hs : count1083 q = (countLit q [-94, -96]) + (countLit q [-98, -101]) := List.countP_append (p := literal q) (l₁ := [-94, -96]) (l₂ := [-98, -101])
  have hm := merge_two (literal (valuationOf q) (1079)) (literal (valuationOf q) (1081)) (literal (valuationOf q) (1084)) (countLit q [-94, -96]) (countLit q [-98, -101]) (count1083 q) 1 1 (meaning1079 q) (meaning1081 q) (meaning1084 q) hs
  change valuationOf q 1079 = false ∨ valuationOf q 1081 = false ∨ valuationOf q 1084 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1499 (q : Snake 81) (h : Conditions q) : valuation q 1079 = false ∨ valuation q 1081 = false ∨ valuation q 1084 = true := counterClause1499 (baseVal q)

theorem counterClause1500 (q : Nat → Bool) : valuationOf q 1079 = false ∨ valuationOf q 1082 = false ∨ valuationOf q 1085 = true := by
  have hs : count1083 q = (countLit q [-94, -96]) + (countLit q [-98, -101]) := List.countP_append (p := literal q) (l₁ := [-94, -96]) (l₂ := [-98, -101])
  have hm := merge_two (literal (valuationOf q) (1079)) (literal (valuationOf q) (1082)) (literal (valuationOf q) (1085)) (countLit q [-94, -96]) (countLit q [-98, -101]) (count1083 q) 1 2 (meaning1079 q) (meaning1082 q) (meaning1085 q) hs
  change valuationOf q 1079 = false ∨ valuationOf q 1082 = false ∨ valuationOf q 1085 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1500 (q : Snake 81) (h : Conditions q) : valuation q 1079 = false ∨ valuation q 1082 = false ∨ valuation q 1085 = true := counterClause1500 (baseVal q)

theorem counterClause1501 (q : Nat → Bool) : valuationOf q 1080 = false ∨ valuationOf q 1084 = true := by
  have hs : count1083 q = (countLit q [-94, -96]) + (countLit q [-98, -101]) := List.countP_append (p := literal q) (l₁ := [-94, -96]) (l₂ := [-98, -101])
  have hm := merge_left (literal (valuationOf q) (1080)) (literal (valuationOf q) (1084)) (countLit q [-94, -96]) (countLit q [-98, -101]) (count1083 q) 2 (meaning1080 q) (meaning1084 q) hs
  change valuationOf q 1080 = false ∨ valuationOf q 1084 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1501 (q : Snake 81) (h : Conditions q) : valuation q 1080 = false ∨ valuation q 1084 = true := counterClause1501 (baseVal q)

theorem counterClause1502 (q : Nat → Bool) : valuationOf q 1080 = false ∨ valuationOf q 1081 = false ∨ valuationOf q 1085 = true := by
  have hs : count1083 q = (countLit q [-94, -96]) + (countLit q [-98, -101]) := List.countP_append (p := literal q) (l₁ := [-94, -96]) (l₂ := [-98, -101])
  have hm := merge_two (literal (valuationOf q) (1080)) (literal (valuationOf q) (1081)) (literal (valuationOf q) (1085)) (countLit q [-94, -96]) (countLit q [-98, -101]) (count1083 q) 2 1 (meaning1080 q) (meaning1081 q) (meaning1085 q) hs
  change valuationOf q 1080 = false ∨ valuationOf q 1081 = false ∨ valuationOf q 1085 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1502 (q : Snake 81) (h : Conditions q) : valuation q 1080 = false ∨ valuation q 1081 = false ∨ valuation q 1085 = true := counterClause1502 (baseVal q)

theorem counterClause1503 (q : Nat → Bool) : valuationOf q 1080 = false ∨ valuationOf q 1082 = false ∨ valuationOf q 1086 = true := by
  have hs : count1083 q = (countLit q [-94, -96]) + (countLit q [-98, -101]) := List.countP_append (p := literal q) (l₁ := [-94, -96]) (l₂ := [-98, -101])
  have hm := merge_two (literal (valuationOf q) (1080)) (literal (valuationOf q) (1082)) (literal (valuationOf q) (1086)) (countLit q [-94, -96]) (countLit q [-98, -101]) (count1083 q) 2 2 (meaning1080 q) (meaning1082 q) (meaning1086 q) hs
  change valuationOf q 1080 = false ∨ valuationOf q 1082 = false ∨ valuationOf q 1086 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1503 (q : Snake 81) (h : Conditions q) : valuation q 1080 = false ∨ valuation q 1082 = false ∨ valuation q 1086 = true := counterClause1503 (baseVal q)

theorem counterClause1504 (q : Nat → Bool) : valuationOf q 106 = true ∨ valuationOf q 1087 = true := by
  have hs : count1087 q = (countLit q [-103]) + (countLit q [-106]) := List.countP_append (p := literal q) (l₁ := [-103]) (l₂ := [-106])
  have hm := merge_right (literal (valuationOf q) (-106)) (literal (valuationOf q) (1087)) (countLit q [-103]) (countLit q [-106]) (count1087 q) 1 (meaningNeg106 q) (meaning1087 q) hs
  change (! (valuationOf q 106)) = false ∨ valuationOf q 1087 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1504 (q : Snake 81) (h : Conditions q) : valuation q 106 = true ∨ valuation q 1087 = true := counterClause1504 (baseVal q)

theorem block46 (q : Snake 81) (h : Conditions q) : B112E121.Block46 (valuation q) :=
  ⟨clause1473 q h, clause1474 q h, clause1475 q h, clause1476 q h, clause1477 q h, clause1478 q h, clause1479 q h, clause1480 q h, clause1481 q h, clause1482 q h, clause1483 q h, clause1484 q h, clause1485 q h, clause1486 q h, clause1487 q h, clause1488 q h, clause1489 q h, clause1490 q h, clause1491 q h, clause1492 q h, clause1493 q h, clause1494 q h, clause1495 q h, clause1496 q h, clause1497 q h, clause1498 q h, clause1499 q h, clause1500 q h, clause1501 q h, clause1502 q h, clause1503 q h, clause1504 q h⟩

end
end Snake9.Regrowth.E112121
