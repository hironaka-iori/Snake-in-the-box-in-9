import E112153Semantics
import B112E153Inputs
namespace Snake9.Regrowth.E112153
noncomputable section
local instance blockDec34 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1089 (q : Nat → Bool) : valuationOf q 998 = false ∨ valuationOf q 1002 = true := by
  have hs : count1001 q = (countLit q [-63, -65, -68]) + (countLit q [-71, -73, -74, -75]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68]) (l₂ := [-71, -73, -74, -75])
  have hm := merge_right (literal (valuationOf q) (998)) (literal (valuationOf q) (1002)) (countLit q [-63, -65, -68]) (countLit q [-71, -73, -74, -75]) (count1001 q) 2 (meaning998 q) (meaning1002 q) hs
  change valuationOf q 998 = false ∨ valuationOf q 1002 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1089 (q : Snake 81) (h : Conditions q) : valuation q 998 = false ∨ valuation q 1002 = true := counterClause1089 (baseVal q)

theorem counterClause1090 (q : Nat → Bool) : valuationOf q 999 = false ∨ valuationOf q 1003 = true := by
  have hs : count1001 q = (countLit q [-63, -65, -68]) + (countLit q [-71, -73, -74, -75]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68]) (l₂ := [-71, -73, -74, -75])
  have hm := merge_right (literal (valuationOf q) (999)) (literal (valuationOf q) (1003)) (countLit q [-63, -65, -68]) (countLit q [-71, -73, -74, -75]) (count1001 q) 3 (meaning999 q) (meaning1003 q) hs
  change valuationOf q 999 = false ∨ valuationOf q 1003 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1090 (q : Snake 81) (h : Conditions q) : valuation q 999 = false ∨ valuation q 1003 = true := counterClause1090 (baseVal q)

theorem counterClause1091 (q : Nat → Bool) : valuationOf q 1000 = false ∨ valuationOf q 1004 = true := by
  have hs : count1001 q = (countLit q [-63, -65, -68]) + (countLit q [-71, -73, -74, -75]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68]) (l₂ := [-71, -73, -74, -75])
  have hm := merge_right (literal (valuationOf q) (1000)) (literal (valuationOf q) (1004)) (countLit q [-63, -65, -68]) (countLit q [-71, -73, -74, -75]) (count1001 q) 4 (meaning1000 q) (meaning1004 q) hs
  change valuationOf q 1000 = false ∨ valuationOf q 1004 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1091 (q : Snake 81) (h : Conditions q) : valuation q 1000 = false ∨ valuation q 1004 = true := counterClause1091 (baseVal q)

theorem counterClause1092 (q : Nat → Bool) : valuationOf q 990 = false ∨ valuationOf q 1001 = true := by
  have hs : count1001 q = (countLit q [-63, -65, -68]) + (countLit q [-71, -73, -74, -75]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68]) (l₂ := [-71, -73, -74, -75])
  have hm := merge_left (literal (valuationOf q) (990)) (literal (valuationOf q) (1001)) (countLit q [-63, -65, -68]) (countLit q [-71, -73, -74, -75]) (count1001 q) 1 (meaning990 q) (meaning1001 q) hs
  change valuationOf q 990 = false ∨ valuationOf q 1001 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1092 (q : Snake 81) (h : Conditions q) : valuation q 990 = false ∨ valuation q 1001 = true := counterClause1092 (baseVal q)

theorem counterClause1093 (q : Nat → Bool) : valuationOf q 990 = false ∨ valuationOf q 997 = false ∨ valuationOf q 1002 = true := by
  have hs : count1001 q = (countLit q [-63, -65, -68]) + (countLit q [-71, -73, -74, -75]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68]) (l₂ := [-71, -73, -74, -75])
  have hm := merge_two (literal (valuationOf q) (990)) (literal (valuationOf q) (997)) (literal (valuationOf q) (1002)) (countLit q [-63, -65, -68]) (countLit q [-71, -73, -74, -75]) (count1001 q) 1 1 (meaning990 q) (meaning997 q) (meaning1002 q) hs
  change valuationOf q 990 = false ∨ valuationOf q 997 = false ∨ valuationOf q 1002 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1093 (q : Snake 81) (h : Conditions q) : valuation q 990 = false ∨ valuation q 997 = false ∨ valuation q 1002 = true := counterClause1093 (baseVal q)

theorem counterClause1094 (q : Nat → Bool) : valuationOf q 990 = false ∨ valuationOf q 998 = false ∨ valuationOf q 1003 = true := by
  have hs : count1001 q = (countLit q [-63, -65, -68]) + (countLit q [-71, -73, -74, -75]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68]) (l₂ := [-71, -73, -74, -75])
  have hm := merge_two (literal (valuationOf q) (990)) (literal (valuationOf q) (998)) (literal (valuationOf q) (1003)) (countLit q [-63, -65, -68]) (countLit q [-71, -73, -74, -75]) (count1001 q) 1 2 (meaning990 q) (meaning998 q) (meaning1003 q) hs
  change valuationOf q 990 = false ∨ valuationOf q 998 = false ∨ valuationOf q 1003 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1094 (q : Snake 81) (h : Conditions q) : valuation q 990 = false ∨ valuation q 998 = false ∨ valuation q 1003 = true := counterClause1094 (baseVal q)

theorem counterClause1095 (q : Nat → Bool) : valuationOf q 990 = false ∨ valuationOf q 999 = false ∨ valuationOf q 1004 = true := by
  have hs : count1001 q = (countLit q [-63, -65, -68]) + (countLit q [-71, -73, -74, -75]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68]) (l₂ := [-71, -73, -74, -75])
  have hm := merge_two (literal (valuationOf q) (990)) (literal (valuationOf q) (999)) (literal (valuationOf q) (1004)) (countLit q [-63, -65, -68]) (countLit q [-71, -73, -74, -75]) (count1001 q) 1 3 (meaning990 q) (meaning999 q) (meaning1004 q) hs
  change valuationOf q 990 = false ∨ valuationOf q 999 = false ∨ valuationOf q 1004 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1095 (q : Snake 81) (h : Conditions q) : valuation q 990 = false ∨ valuation q 999 = false ∨ valuation q 1004 = true := counterClause1095 (baseVal q)

theorem counterClause1096 (q : Nat → Bool) : valuationOf q 990 = false ∨ valuationOf q 1000 = false ∨ valuationOf q 1005 = true := by
  have hs : count1001 q = (countLit q [-63, -65, -68]) + (countLit q [-71, -73, -74, -75]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68]) (l₂ := [-71, -73, -74, -75])
  have hm := merge_two (literal (valuationOf q) (990)) (literal (valuationOf q) (1000)) (literal (valuationOf q) (1005)) (countLit q [-63, -65, -68]) (countLit q [-71, -73, -74, -75]) (count1001 q) 1 4 (meaning990 q) (meaning1000 q) (meaning1005 q) hs
  change valuationOf q 990 = false ∨ valuationOf q 1000 = false ∨ valuationOf q 1005 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1096 (q : Snake 81) (h : Conditions q) : valuation q 990 = false ∨ valuation q 1000 = false ∨ valuation q 1005 = true := counterClause1096 (baseVal q)

theorem counterClause1097 (q : Nat → Bool) : valuationOf q 991 = false ∨ valuationOf q 1002 = true := by
  have hs : count1001 q = (countLit q [-63, -65, -68]) + (countLit q [-71, -73, -74, -75]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68]) (l₂ := [-71, -73, -74, -75])
  have hm := merge_left (literal (valuationOf q) (991)) (literal (valuationOf q) (1002)) (countLit q [-63, -65, -68]) (countLit q [-71, -73, -74, -75]) (count1001 q) 2 (meaning991 q) (meaning1002 q) hs
  change valuationOf q 991 = false ∨ valuationOf q 1002 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1097 (q : Snake 81) (h : Conditions q) : valuation q 991 = false ∨ valuation q 1002 = true := counterClause1097 (baseVal q)

theorem counterClause1098 (q : Nat → Bool) : valuationOf q 991 = false ∨ valuationOf q 997 = false ∨ valuationOf q 1003 = true := by
  have hs : count1001 q = (countLit q [-63, -65, -68]) + (countLit q [-71, -73, -74, -75]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68]) (l₂ := [-71, -73, -74, -75])
  have hm := merge_two (literal (valuationOf q) (991)) (literal (valuationOf q) (997)) (literal (valuationOf q) (1003)) (countLit q [-63, -65, -68]) (countLit q [-71, -73, -74, -75]) (count1001 q) 2 1 (meaning991 q) (meaning997 q) (meaning1003 q) hs
  change valuationOf q 991 = false ∨ valuationOf q 997 = false ∨ valuationOf q 1003 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1098 (q : Snake 81) (h : Conditions q) : valuation q 991 = false ∨ valuation q 997 = false ∨ valuation q 1003 = true := counterClause1098 (baseVal q)

theorem counterClause1099 (q : Nat → Bool) : valuationOf q 991 = false ∨ valuationOf q 998 = false ∨ valuationOf q 1004 = true := by
  have hs : count1001 q = (countLit q [-63, -65, -68]) + (countLit q [-71, -73, -74, -75]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68]) (l₂ := [-71, -73, -74, -75])
  have hm := merge_two (literal (valuationOf q) (991)) (literal (valuationOf q) (998)) (literal (valuationOf q) (1004)) (countLit q [-63, -65, -68]) (countLit q [-71, -73, -74, -75]) (count1001 q) 2 2 (meaning991 q) (meaning998 q) (meaning1004 q) hs
  change valuationOf q 991 = false ∨ valuationOf q 998 = false ∨ valuationOf q 1004 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1099 (q : Snake 81) (h : Conditions q) : valuation q 991 = false ∨ valuation q 998 = false ∨ valuation q 1004 = true := counterClause1099 (baseVal q)

theorem counterClause1100 (q : Nat → Bool) : valuationOf q 991 = false ∨ valuationOf q 999 = false ∨ valuationOf q 1005 = true := by
  have hs : count1001 q = (countLit q [-63, -65, -68]) + (countLit q [-71, -73, -74, -75]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68]) (l₂ := [-71, -73, -74, -75])
  have hm := merge_two (literal (valuationOf q) (991)) (literal (valuationOf q) (999)) (literal (valuationOf q) (1005)) (countLit q [-63, -65, -68]) (countLit q [-71, -73, -74, -75]) (count1001 q) 2 3 (meaning991 q) (meaning999 q) (meaning1005 q) hs
  change valuationOf q 991 = false ∨ valuationOf q 999 = false ∨ valuationOf q 1005 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1100 (q : Snake 81) (h : Conditions q) : valuation q 991 = false ∨ valuation q 999 = false ∨ valuation q 1005 = true := counterClause1100 (baseVal q)

theorem counterClause1101 (q : Nat → Bool) : valuationOf q 991 = false ∨ valuationOf q 1000 = false ∨ valuationOf q 1006 = true := by
  have hs : count1001 q = (countLit q [-63, -65, -68]) + (countLit q [-71, -73, -74, -75]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68]) (l₂ := [-71, -73, -74, -75])
  have hm := merge_two (literal (valuationOf q) (991)) (literal (valuationOf q) (1000)) (literal (valuationOf q) (1006)) (countLit q [-63, -65, -68]) (countLit q [-71, -73, -74, -75]) (count1001 q) 2 4 (meaning991 q) (meaning1000 q) (meaning1006 q) hs
  change valuationOf q 991 = false ∨ valuationOf q 1000 = false ∨ valuationOf q 1006 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1101 (q : Snake 81) (h : Conditions q) : valuation q 991 = false ∨ valuation q 1000 = false ∨ valuation q 1006 = true := counterClause1101 (baseVal q)

theorem counterClause1102 (q : Nat → Bool) : valuationOf q 992 = false ∨ valuationOf q 1003 = true := by
  have hs : count1001 q = (countLit q [-63, -65, -68]) + (countLit q [-71, -73, -74, -75]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68]) (l₂ := [-71, -73, -74, -75])
  have hm := merge_left (literal (valuationOf q) (992)) (literal (valuationOf q) (1003)) (countLit q [-63, -65, -68]) (countLit q [-71, -73, -74, -75]) (count1001 q) 3 (meaning992 q) (meaning1003 q) hs
  change valuationOf q 992 = false ∨ valuationOf q 1003 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1102 (q : Snake 81) (h : Conditions q) : valuation q 992 = false ∨ valuation q 1003 = true := counterClause1102 (baseVal q)

theorem counterClause1103 (q : Nat → Bool) : valuationOf q 992 = false ∨ valuationOf q 997 = false ∨ valuationOf q 1004 = true := by
  have hs : count1001 q = (countLit q [-63, -65, -68]) + (countLit q [-71, -73, -74, -75]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68]) (l₂ := [-71, -73, -74, -75])
  have hm := merge_two (literal (valuationOf q) (992)) (literal (valuationOf q) (997)) (literal (valuationOf q) (1004)) (countLit q [-63, -65, -68]) (countLit q [-71, -73, -74, -75]) (count1001 q) 3 1 (meaning992 q) (meaning997 q) (meaning1004 q) hs
  change valuationOf q 992 = false ∨ valuationOf q 997 = false ∨ valuationOf q 1004 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1103 (q : Snake 81) (h : Conditions q) : valuation q 992 = false ∨ valuation q 997 = false ∨ valuation q 1004 = true := counterClause1103 (baseVal q)

theorem counterClause1104 (q : Nat → Bool) : valuationOf q 992 = false ∨ valuationOf q 998 = false ∨ valuationOf q 1005 = true := by
  have hs : count1001 q = (countLit q [-63, -65, -68]) + (countLit q [-71, -73, -74, -75]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68]) (l₂ := [-71, -73, -74, -75])
  have hm := merge_two (literal (valuationOf q) (992)) (literal (valuationOf q) (998)) (literal (valuationOf q) (1005)) (countLit q [-63, -65, -68]) (countLit q [-71, -73, -74, -75]) (count1001 q) 3 2 (meaning992 q) (meaning998 q) (meaning1005 q) hs
  change valuationOf q 992 = false ∨ valuationOf q 998 = false ∨ valuationOf q 1005 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1104 (q : Snake 81) (h : Conditions q) : valuation q 992 = false ∨ valuation q 998 = false ∨ valuation q 1005 = true := counterClause1104 (baseVal q)

theorem counterClause1105 (q : Nat → Bool) : valuationOf q 992 = false ∨ valuationOf q 999 = false ∨ valuationOf q 1006 = true := by
  have hs : count1001 q = (countLit q [-63, -65, -68]) + (countLit q [-71, -73, -74, -75]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68]) (l₂ := [-71, -73, -74, -75])
  have hm := merge_two (literal (valuationOf q) (992)) (literal (valuationOf q) (999)) (literal (valuationOf q) (1006)) (countLit q [-63, -65, -68]) (countLit q [-71, -73, -74, -75]) (count1001 q) 3 3 (meaning992 q) (meaning999 q) (meaning1006 q) hs
  change valuationOf q 992 = false ∨ valuationOf q 999 = false ∨ valuationOf q 1006 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1105 (q : Snake 81) (h : Conditions q) : valuation q 992 = false ∨ valuation q 999 = false ∨ valuation q 1006 = true := counterClause1105 (baseVal q)

theorem counterClause1106 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 1008 = true := by
  have hs : count1008 q = (countLit q [-80]) + (countLit q [-81]) := List.countP_append (p := literal q) (l₁ := [-80]) (l₂ := [-81])
  have hm := merge_right (literal (valuationOf q) (-81)) (literal (valuationOf q) (1008)) (countLit q [-80]) (countLit q [-81]) (count1008 q) 1 (meaningNeg81 q) (meaning1008 q) hs
  change (! (valuationOf q 81)) = false ∨ valuationOf q 1008 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1106 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 1008 = true := counterClause1106 (baseVal q)

theorem counterClause1107 (q : Nat → Bool) : valuationOf q 80 = true ∨ valuationOf q 1008 = true := by
  have hs : count1008 q = (countLit q [-80]) + (countLit q [-81]) := List.countP_append (p := literal q) (l₁ := [-80]) (l₂ := [-81])
  have hm := merge_left (literal (valuationOf q) (-80)) (literal (valuationOf q) (1008)) (countLit q [-80]) (countLit q [-81]) (count1008 q) 1 (meaningNeg80 q) (meaning1008 q) hs
  change (! (valuationOf q 80)) = false ∨ valuationOf q 1008 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1107 (q : Snake 81) (h : Conditions q) : valuation q 80 = true ∨ valuation q 1008 = true := counterClause1107 (baseVal q)

theorem counterClause1108 (q : Nat → Bool) : valuationOf q 80 = true ∨ valuationOf q 81 = true ∨ valuationOf q 1009 = true := by
  have hs : count1008 q = (countLit q [-80]) + (countLit q [-81]) := List.countP_append (p := literal q) (l₁ := [-80]) (l₂ := [-81])
  have hm := merge_two (literal (valuationOf q) (-80)) (literal (valuationOf q) (-81)) (literal (valuationOf q) (1009)) (countLit q [-80]) (countLit q [-81]) (count1008 q) 1 1 (meaningNeg80 q) (meaningNeg81 q) (meaning1009 q) hs
  change (! (valuationOf q 80)) = false ∨ (! (valuationOf q 81)) = false ∨ valuationOf q 1009 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1108 (q : Snake 81) (h : Conditions q) : valuation q 80 = true ∨ valuation q 81 = true ∨ valuation q 1009 = true := counterClause1108 (baseVal q)

theorem counterClause1109 (q : Nat → Bool) : valuationOf q 86 = true ∨ valuationOf q 1010 = true := by
  have hs : count1010 q = (countLit q [-82]) + (countLit q [-86]) := List.countP_append (p := literal q) (l₁ := [-82]) (l₂ := [-86])
  have hm := merge_right (literal (valuationOf q) (-86)) (literal (valuationOf q) (1010)) (countLit q [-82]) (countLit q [-86]) (count1010 q) 1 (meaningNeg86 q) (meaning1010 q) hs
  change (! (valuationOf q 86)) = false ∨ valuationOf q 1010 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1109 (q : Snake 81) (h : Conditions q) : valuation q 86 = true ∨ valuation q 1010 = true := counterClause1109 (baseVal q)

theorem counterClause1110 (q : Nat → Bool) : valuationOf q 82 = true ∨ valuationOf q 1010 = true := by
  have hs : count1010 q = (countLit q [-82]) + (countLit q [-86]) := List.countP_append (p := literal q) (l₁ := [-82]) (l₂ := [-86])
  have hm := merge_left (literal (valuationOf q) (-82)) (literal (valuationOf q) (1010)) (countLit q [-82]) (countLit q [-86]) (count1010 q) 1 (meaningNeg82 q) (meaning1010 q) hs
  change (! (valuationOf q 82)) = false ∨ valuationOf q 1010 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1110 (q : Snake 81) (h : Conditions q) : valuation q 82 = true ∨ valuation q 1010 = true := counterClause1110 (baseVal q)

theorem counterClause1111 (q : Nat → Bool) : valuationOf q 82 = true ∨ valuationOf q 86 = true ∨ valuationOf q 1011 = true := by
  have hs : count1010 q = (countLit q [-82]) + (countLit q [-86]) := List.countP_append (p := literal q) (l₁ := [-82]) (l₂ := [-86])
  have hm := merge_two (literal (valuationOf q) (-82)) (literal (valuationOf q) (-86)) (literal (valuationOf q) (1011)) (countLit q [-82]) (countLit q [-86]) (count1010 q) 1 1 (meaningNeg82 q) (meaningNeg86 q) (meaning1011 q) hs
  change (! (valuationOf q 82)) = false ∨ (! (valuationOf q 86)) = false ∨ valuationOf q 1011 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1111 (q : Snake 81) (h : Conditions q) : valuation q 82 = true ∨ valuation q 86 = true ∨ valuation q 1011 = true := counterClause1111 (baseVal q)

theorem counterClause1112 (q : Nat → Bool) : valuationOf q 1010 = false ∨ valuationOf q 1012 = true := by
  have hs : count1012 q = (countLit q [-80, -81]) + (countLit q [-82, -86]) := List.countP_append (p := literal q) (l₁ := [-80, -81]) (l₂ := [-82, -86])
  have hm := merge_right (literal (valuationOf q) (1010)) (literal (valuationOf q) (1012)) (countLit q [-80, -81]) (countLit q [-82, -86]) (count1012 q) 1 (meaning1010 q) (meaning1012 q) hs
  change valuationOf q 1010 = false ∨ valuationOf q 1012 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1112 (q : Snake 81) (h : Conditions q) : valuation q 1010 = false ∨ valuation q 1012 = true := counterClause1112 (baseVal q)

theorem counterClause1113 (q : Nat → Bool) : valuationOf q 1011 = false ∨ valuationOf q 1013 = true := by
  have hs : count1012 q = (countLit q [-80, -81]) + (countLit q [-82, -86]) := List.countP_append (p := literal q) (l₁ := [-80, -81]) (l₂ := [-82, -86])
  have hm := merge_right (literal (valuationOf q) (1011)) (literal (valuationOf q) (1013)) (countLit q [-80, -81]) (countLit q [-82, -86]) (count1012 q) 2 (meaning1011 q) (meaning1013 q) hs
  change valuationOf q 1011 = false ∨ valuationOf q 1013 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1113 (q : Snake 81) (h : Conditions q) : valuation q 1011 = false ∨ valuation q 1013 = true := counterClause1113 (baseVal q)

theorem counterClause1114 (q : Nat → Bool) : valuationOf q 1008 = false ∨ valuationOf q 1012 = true := by
  have hs : count1012 q = (countLit q [-80, -81]) + (countLit q [-82, -86]) := List.countP_append (p := literal q) (l₁ := [-80, -81]) (l₂ := [-82, -86])
  have hm := merge_left (literal (valuationOf q) (1008)) (literal (valuationOf q) (1012)) (countLit q [-80, -81]) (countLit q [-82, -86]) (count1012 q) 1 (meaning1008 q) (meaning1012 q) hs
  change valuationOf q 1008 = false ∨ valuationOf q 1012 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1114 (q : Snake 81) (h : Conditions q) : valuation q 1008 = false ∨ valuation q 1012 = true := counterClause1114 (baseVal q)

theorem counterClause1115 (q : Nat → Bool) : valuationOf q 1008 = false ∨ valuationOf q 1010 = false ∨ valuationOf q 1013 = true := by
  have hs : count1012 q = (countLit q [-80, -81]) + (countLit q [-82, -86]) := List.countP_append (p := literal q) (l₁ := [-80, -81]) (l₂ := [-82, -86])
  have hm := merge_two (literal (valuationOf q) (1008)) (literal (valuationOf q) (1010)) (literal (valuationOf q) (1013)) (countLit q [-80, -81]) (countLit q [-82, -86]) (count1012 q) 1 1 (meaning1008 q) (meaning1010 q) (meaning1013 q) hs
  change valuationOf q 1008 = false ∨ valuationOf q 1010 = false ∨ valuationOf q 1013 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1115 (q : Snake 81) (h : Conditions q) : valuation q 1008 = false ∨ valuation q 1010 = false ∨ valuation q 1013 = true := counterClause1115 (baseVal q)

theorem counterClause1116 (q : Nat → Bool) : valuationOf q 1008 = false ∨ valuationOf q 1011 = false ∨ valuationOf q 1014 = true := by
  have hs : count1012 q = (countLit q [-80, -81]) + (countLit q [-82, -86]) := List.countP_append (p := literal q) (l₁ := [-80, -81]) (l₂ := [-82, -86])
  have hm := merge_two (literal (valuationOf q) (1008)) (literal (valuationOf q) (1011)) (literal (valuationOf q) (1014)) (countLit q [-80, -81]) (countLit q [-82, -86]) (count1012 q) 1 2 (meaning1008 q) (meaning1011 q) (meaning1014 q) hs
  change valuationOf q 1008 = false ∨ valuationOf q 1011 = false ∨ valuationOf q 1014 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1116 (q : Snake 81) (h : Conditions q) : valuation q 1008 = false ∨ valuation q 1011 = false ∨ valuation q 1014 = true := counterClause1116 (baseVal q)

theorem counterClause1117 (q : Nat → Bool) : valuationOf q 1009 = false ∨ valuationOf q 1013 = true := by
  have hs : count1012 q = (countLit q [-80, -81]) + (countLit q [-82, -86]) := List.countP_append (p := literal q) (l₁ := [-80, -81]) (l₂ := [-82, -86])
  have hm := merge_left (literal (valuationOf q) (1009)) (literal (valuationOf q) (1013)) (countLit q [-80, -81]) (countLit q [-82, -86]) (count1012 q) 2 (meaning1009 q) (meaning1013 q) hs
  change valuationOf q 1009 = false ∨ valuationOf q 1013 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1117 (q : Snake 81) (h : Conditions q) : valuation q 1009 = false ∨ valuation q 1013 = true := counterClause1117 (baseVal q)

theorem counterClause1118 (q : Nat → Bool) : valuationOf q 1009 = false ∨ valuationOf q 1010 = false ∨ valuationOf q 1014 = true := by
  have hs : count1012 q = (countLit q [-80, -81]) + (countLit q [-82, -86]) := List.countP_append (p := literal q) (l₁ := [-80, -81]) (l₂ := [-82, -86])
  have hm := merge_two (literal (valuationOf q) (1009)) (literal (valuationOf q) (1010)) (literal (valuationOf q) (1014)) (countLit q [-80, -81]) (countLit q [-82, -86]) (count1012 q) 2 1 (meaning1009 q) (meaning1010 q) (meaning1014 q) hs
  change valuationOf q 1009 = false ∨ valuationOf q 1010 = false ∨ valuationOf q 1014 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1118 (q : Snake 81) (h : Conditions q) : valuation q 1009 = false ∨ valuation q 1010 = false ∨ valuation q 1014 = true := counterClause1118 (baseVal q)

theorem counterClause1119 (q : Nat → Bool) : valuationOf q 1009 = false ∨ valuationOf q 1011 = false ∨ valuationOf q 1015 = true := by
  have hs : count1012 q = (countLit q [-80, -81]) + (countLit q [-82, -86]) := List.countP_append (p := literal q) (l₁ := [-80, -81]) (l₂ := [-82, -86])
  have hm := merge_two (literal (valuationOf q) (1009)) (literal (valuationOf q) (1011)) (literal (valuationOf q) (1015)) (countLit q [-80, -81]) (countLit q [-82, -86]) (count1012 q) 2 2 (meaning1009 q) (meaning1011 q) (meaning1015 q) hs
  change valuationOf q 1009 = false ∨ valuationOf q 1011 = false ∨ valuationOf q 1015 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1119 (q : Snake 81) (h : Conditions q) : valuation q 1009 = false ∨ valuation q 1011 = false ∨ valuation q 1015 = true := counterClause1119 (baseVal q)

theorem counterClause1120 (q : Nat → Bool) : valuationOf q 88 = true ∨ valuationOf q 1016 = true := by
  have hs : count1016 q = (countLit q [-87]) + (countLit q [-88]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-88])
  have hm := merge_right (literal (valuationOf q) (-88)) (literal (valuationOf q) (1016)) (countLit q [-87]) (countLit q [-88]) (count1016 q) 1 (meaningNeg88 q) (meaning1016 q) hs
  change (! (valuationOf q 88)) = false ∨ valuationOf q 1016 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1120 (q : Snake 81) (h : Conditions q) : valuation q 88 = true ∨ valuation q 1016 = true := counterClause1120 (baseVal q)

theorem block34 (q : Snake 81) (h : Conditions q) : B112E153.Block34 (valuation q) :=
  ⟨clause1089 q h, clause1090 q h, clause1091 q h, clause1092 q h, clause1093 q h, clause1094 q h, clause1095 q h, clause1096 q h, clause1097 q h, clause1098 q h, clause1099 q h, clause1100 q h, clause1101 q h, clause1102 q h, clause1103 q h, clause1104 q h, clause1105 q h, clause1106 q h, clause1107 q h, clause1108 q h, clause1109 q h, clause1110 q h, clause1111 q h, clause1112 q h, clause1113 q h, clause1114 q h, clause1115 q h, clause1116 q h, clause1117 q h, clause1118 q h, clause1119 q h, clause1120 q h⟩

end
end Snake9.Regrowth.E112153
