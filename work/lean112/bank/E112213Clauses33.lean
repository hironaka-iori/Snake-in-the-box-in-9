import E112213Semantics
import B112E213Inputs
namespace Snake9.Regrowth.E112213
noncomputable section
local instance blockDec33 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1057 (q : Nat → Bool) : valuationOf q 942 = false ∨ valuationOf q 965 = false ∨ valuationOf q 974 = true := by
  have hs : count973 q = (countLit q [-59, -62, -64, -66, -69, -72, -73]) + (countLit q [-74, -76, -79, -81, -83, -84, -87, -90]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -64, -66, -69, -72, -73]) (l₂ := [-74, -76, -79, -81, -83, -84, -87, -90])
  have hm := merge_two (literal (valuationOf q) (942)) (literal (valuationOf q) (965)) (literal (valuationOf q) (974)) (countLit q [-59, -62, -64, -66, -69, -72, -73]) (countLit q [-74, -76, -79, -81, -83, -84, -87, -90]) (count973 q) 1 1 (meaning942 q) (meaning965 q) (meaning974 q) hs
  change valuationOf q 942 = false ∨ valuationOf q 965 = false ∨ valuationOf q 974 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1057 (q : Snake 81) (h : Conditions q) : valuation q 942 = false ∨ valuation q 965 = false ∨ valuation q 974 = true := counterClause1057 (baseVal q)

theorem counterClause1058 (q : Nat → Bool) : valuationOf q 942 = false ∨ valuationOf q 966 = false ∨ valuationOf q 975 = true := by
  have hs : count973 q = (countLit q [-59, -62, -64, -66, -69, -72, -73]) + (countLit q [-74, -76, -79, -81, -83, -84, -87, -90]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -64, -66, -69, -72, -73]) (l₂ := [-74, -76, -79, -81, -83, -84, -87, -90])
  have hm := merge_two (literal (valuationOf q) (942)) (literal (valuationOf q) (966)) (literal (valuationOf q) (975)) (countLit q [-59, -62, -64, -66, -69, -72, -73]) (countLit q [-74, -76, -79, -81, -83, -84, -87, -90]) (count973 q) 1 2 (meaning942 q) (meaning966 q) (meaning975 q) hs
  change valuationOf q 942 = false ∨ valuationOf q 966 = false ∨ valuationOf q 975 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1058 (q : Snake 81) (h : Conditions q) : valuation q 942 = false ∨ valuation q 966 = false ∨ valuation q 975 = true := counterClause1058 (baseVal q)

theorem counterClause1059 (q : Nat → Bool) : valuationOf q 942 = false ∨ valuationOf q 967 = false ∨ valuationOf q 976 = true := by
  have hs : count973 q = (countLit q [-59, -62, -64, -66, -69, -72, -73]) + (countLit q [-74, -76, -79, -81, -83, -84, -87, -90]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -64, -66, -69, -72, -73]) (l₂ := [-74, -76, -79, -81, -83, -84, -87, -90])
  have hm := merge_two (literal (valuationOf q) (942)) (literal (valuationOf q) (967)) (literal (valuationOf q) (976)) (countLit q [-59, -62, -64, -66, -69, -72, -73]) (countLit q [-74, -76, -79, -81, -83, -84, -87, -90]) (count973 q) 1 3 (meaning942 q) (meaning967 q) (meaning976 q) hs
  change valuationOf q 942 = false ∨ valuationOf q 967 = false ∨ valuationOf q 976 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1059 (q : Snake 81) (h : Conditions q) : valuation q 942 = false ∨ valuation q 967 = false ∨ valuation q 976 = true := counterClause1059 (baseVal q)

theorem counterClause1060 (q : Nat → Bool) : valuationOf q 942 = false ∨ valuationOf q 968 = false ∨ valuationOf q 977 = true := by
  have hs : count973 q = (countLit q [-59, -62, -64, -66, -69, -72, -73]) + (countLit q [-74, -76, -79, -81, -83, -84, -87, -90]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -64, -66, -69, -72, -73]) (l₂ := [-74, -76, -79, -81, -83, -84, -87, -90])
  have hm := merge_two (literal (valuationOf q) (942)) (literal (valuationOf q) (968)) (literal (valuationOf q) (977)) (countLit q [-59, -62, -64, -66, -69, -72, -73]) (countLit q [-74, -76, -79, -81, -83, -84, -87, -90]) (count973 q) 1 4 (meaning942 q) (meaning968 q) (meaning977 q) hs
  change valuationOf q 942 = false ∨ valuationOf q 968 = false ∨ valuationOf q 977 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1060 (q : Snake 81) (h : Conditions q) : valuation q 942 = false ∨ valuation q 968 = false ∨ valuation q 977 = true := counterClause1060 (baseVal q)

theorem counterClause1061 (q : Nat → Bool) : valuationOf q 943 = false ∨ valuationOf q 974 = true := by
  have hs : count973 q = (countLit q [-59, -62, -64, -66, -69, -72, -73]) + (countLit q [-74, -76, -79, -81, -83, -84, -87, -90]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -64, -66, -69, -72, -73]) (l₂ := [-74, -76, -79, -81, -83, -84, -87, -90])
  have hm := merge_left (literal (valuationOf q) (943)) (literal (valuationOf q) (974)) (countLit q [-59, -62, -64, -66, -69, -72, -73]) (countLit q [-74, -76, -79, -81, -83, -84, -87, -90]) (count973 q) 2 (meaning943 q) (meaning974 q) hs
  change valuationOf q 943 = false ∨ valuationOf q 974 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1061 (q : Snake 81) (h : Conditions q) : valuation q 943 = false ∨ valuation q 974 = true := counterClause1061 (baseVal q)

theorem counterClause1062 (q : Nat → Bool) : valuationOf q 943 = false ∨ valuationOf q 965 = false ∨ valuationOf q 975 = true := by
  have hs : count973 q = (countLit q [-59, -62, -64, -66, -69, -72, -73]) + (countLit q [-74, -76, -79, -81, -83, -84, -87, -90]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -64, -66, -69, -72, -73]) (l₂ := [-74, -76, -79, -81, -83, -84, -87, -90])
  have hm := merge_two (literal (valuationOf q) (943)) (literal (valuationOf q) (965)) (literal (valuationOf q) (975)) (countLit q [-59, -62, -64, -66, -69, -72, -73]) (countLit q [-74, -76, -79, -81, -83, -84, -87, -90]) (count973 q) 2 1 (meaning943 q) (meaning965 q) (meaning975 q) hs
  change valuationOf q 943 = false ∨ valuationOf q 965 = false ∨ valuationOf q 975 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1062 (q : Snake 81) (h : Conditions q) : valuation q 943 = false ∨ valuation q 965 = false ∨ valuation q 975 = true := counterClause1062 (baseVal q)

theorem counterClause1063 (q : Nat → Bool) : valuationOf q 943 = false ∨ valuationOf q 966 = false ∨ valuationOf q 976 = true := by
  have hs : count973 q = (countLit q [-59, -62, -64, -66, -69, -72, -73]) + (countLit q [-74, -76, -79, -81, -83, -84, -87, -90]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -64, -66, -69, -72, -73]) (l₂ := [-74, -76, -79, -81, -83, -84, -87, -90])
  have hm := merge_two (literal (valuationOf q) (943)) (literal (valuationOf q) (966)) (literal (valuationOf q) (976)) (countLit q [-59, -62, -64, -66, -69, -72, -73]) (countLit q [-74, -76, -79, -81, -83, -84, -87, -90]) (count973 q) 2 2 (meaning943 q) (meaning966 q) (meaning976 q) hs
  change valuationOf q 943 = false ∨ valuationOf q 966 = false ∨ valuationOf q 976 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1063 (q : Snake 81) (h : Conditions q) : valuation q 943 = false ∨ valuation q 966 = false ∨ valuation q 976 = true := counterClause1063 (baseVal q)

theorem counterClause1064 (q : Nat → Bool) : valuationOf q 943 = false ∨ valuationOf q 967 = false ∨ valuationOf q 977 = true := by
  have hs : count973 q = (countLit q [-59, -62, -64, -66, -69, -72, -73]) + (countLit q [-74, -76, -79, -81, -83, -84, -87, -90]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -64, -66, -69, -72, -73]) (l₂ := [-74, -76, -79, -81, -83, -84, -87, -90])
  have hm := merge_two (literal (valuationOf q) (943)) (literal (valuationOf q) (967)) (literal (valuationOf q) (977)) (countLit q [-59, -62, -64, -66, -69, -72, -73]) (countLit q [-74, -76, -79, -81, -83, -84, -87, -90]) (count973 q) 2 3 (meaning943 q) (meaning967 q) (meaning977 q) hs
  change valuationOf q 943 = false ∨ valuationOf q 967 = false ∨ valuationOf q 977 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1064 (q : Snake 81) (h : Conditions q) : valuation q 943 = false ∨ valuation q 967 = false ∨ valuation q 977 = true := counterClause1064 (baseVal q)

theorem counterClause1065 (q : Nat → Bool) : valuationOf q 943 = false ∨ valuationOf q 968 = false ∨ valuationOf q 978 = true := by
  have hs : count973 q = (countLit q [-59, -62, -64, -66, -69, -72, -73]) + (countLit q [-74, -76, -79, -81, -83, -84, -87, -90]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -64, -66, -69, -72, -73]) (l₂ := [-74, -76, -79, -81, -83, -84, -87, -90])
  have hm := merge_two (literal (valuationOf q) (943)) (literal (valuationOf q) (968)) (literal (valuationOf q) (978)) (countLit q [-59, -62, -64, -66, -69, -72, -73]) (countLit q [-74, -76, -79, -81, -83, -84, -87, -90]) (count973 q) 2 4 (meaning943 q) (meaning968 q) (meaning978 q) hs
  change valuationOf q 943 = false ∨ valuationOf q 968 = false ∨ valuationOf q 978 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1065 (q : Snake 81) (h : Conditions q) : valuation q 943 = false ∨ valuation q 968 = false ∨ valuation q 978 = true := counterClause1065 (baseVal q)

theorem counterClause1066 (q : Nat → Bool) : valuationOf q 944 = false ∨ valuationOf q 975 = true := by
  have hs : count973 q = (countLit q [-59, -62, -64, -66, -69, -72, -73]) + (countLit q [-74, -76, -79, -81, -83, -84, -87, -90]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -64, -66, -69, -72, -73]) (l₂ := [-74, -76, -79, -81, -83, -84, -87, -90])
  have hm := merge_left (literal (valuationOf q) (944)) (literal (valuationOf q) (975)) (countLit q [-59, -62, -64, -66, -69, -72, -73]) (countLit q [-74, -76, -79, -81, -83, -84, -87, -90]) (count973 q) 3 (meaning944 q) (meaning975 q) hs
  change valuationOf q 944 = false ∨ valuationOf q 975 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1066 (q : Snake 81) (h : Conditions q) : valuation q 944 = false ∨ valuation q 975 = true := counterClause1066 (baseVal q)

theorem counterClause1067 (q : Nat → Bool) : valuationOf q 944 = false ∨ valuationOf q 965 = false ∨ valuationOf q 976 = true := by
  have hs : count973 q = (countLit q [-59, -62, -64, -66, -69, -72, -73]) + (countLit q [-74, -76, -79, -81, -83, -84, -87, -90]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -64, -66, -69, -72, -73]) (l₂ := [-74, -76, -79, -81, -83, -84, -87, -90])
  have hm := merge_two (literal (valuationOf q) (944)) (literal (valuationOf q) (965)) (literal (valuationOf q) (976)) (countLit q [-59, -62, -64, -66, -69, -72, -73]) (countLit q [-74, -76, -79, -81, -83, -84, -87, -90]) (count973 q) 3 1 (meaning944 q) (meaning965 q) (meaning976 q) hs
  change valuationOf q 944 = false ∨ valuationOf q 965 = false ∨ valuationOf q 976 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1067 (q : Snake 81) (h : Conditions q) : valuation q 944 = false ∨ valuation q 965 = false ∨ valuation q 976 = true := counterClause1067 (baseVal q)

theorem counterClause1068 (q : Nat → Bool) : valuationOf q 944 = false ∨ valuationOf q 966 = false ∨ valuationOf q 977 = true := by
  have hs : count973 q = (countLit q [-59, -62, -64, -66, -69, -72, -73]) + (countLit q [-74, -76, -79, -81, -83, -84, -87, -90]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -64, -66, -69, -72, -73]) (l₂ := [-74, -76, -79, -81, -83, -84, -87, -90])
  have hm := merge_two (literal (valuationOf q) (944)) (literal (valuationOf q) (966)) (literal (valuationOf q) (977)) (countLit q [-59, -62, -64, -66, -69, -72, -73]) (countLit q [-74, -76, -79, -81, -83, -84, -87, -90]) (count973 q) 3 2 (meaning944 q) (meaning966 q) (meaning977 q) hs
  change valuationOf q 944 = false ∨ valuationOf q 966 = false ∨ valuationOf q 977 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1068 (q : Snake 81) (h : Conditions q) : valuation q 944 = false ∨ valuation q 966 = false ∨ valuation q 977 = true := counterClause1068 (baseVal q)

theorem counterClause1069 (q : Nat → Bool) : valuationOf q 944 = false ∨ valuationOf q 967 = false ∨ valuationOf q 978 = true := by
  have hs : count973 q = (countLit q [-59, -62, -64, -66, -69, -72, -73]) + (countLit q [-74, -76, -79, -81, -83, -84, -87, -90]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -64, -66, -69, -72, -73]) (l₂ := [-74, -76, -79, -81, -83, -84, -87, -90])
  have hm := merge_two (literal (valuationOf q) (944)) (literal (valuationOf q) (967)) (literal (valuationOf q) (978)) (countLit q [-59, -62, -64, -66, -69, -72, -73]) (countLit q [-74, -76, -79, -81, -83, -84, -87, -90]) (count973 q) 3 3 (meaning944 q) (meaning967 q) (meaning978 q) hs
  change valuationOf q 944 = false ∨ valuationOf q 967 = false ∨ valuationOf q 978 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1069 (q : Snake 81) (h : Conditions q) : valuation q 944 = false ∨ valuation q 967 = false ∨ valuation q 978 = true := counterClause1069 (baseVal q)

theorem counterClause1070 (q : Nat → Bool) : valuationOf q 944 = false ∨ valuationOf q 968 = false ∨ valuationOf q 979 = true := by
  have hs : count973 q = (countLit q [-59, -62, -64, -66, -69, -72, -73]) + (countLit q [-74, -76, -79, -81, -83, -84, -87, -90]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -64, -66, -69, -72, -73]) (l₂ := [-74, -76, -79, -81, -83, -84, -87, -90])
  have hm := merge_two (literal (valuationOf q) (944)) (literal (valuationOf q) (968)) (literal (valuationOf q) (979)) (countLit q [-59, -62, -64, -66, -69, -72, -73]) (countLit q [-74, -76, -79, -81, -83, -84, -87, -90]) (count973 q) 3 4 (meaning944 q) (meaning968 q) (meaning979 q) hs
  change valuationOf q 944 = false ∨ valuationOf q 968 = false ∨ valuationOf q 979 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1070 (q : Snake 81) (h : Conditions q) : valuation q 944 = false ∨ valuation q 968 = false ∨ valuation q 979 = true := counterClause1070 (baseVal q)

theorem counterClause1071 (q : Nat → Bool) : valuationOf q 945 = false ∨ valuationOf q 965 = false ∨ valuationOf q 977 = true := by
  have hs : count973 q = (countLit q [-59, -62, -64, -66, -69, -72, -73]) + (countLit q [-74, -76, -79, -81, -83, -84, -87, -90]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -64, -66, -69, -72, -73]) (l₂ := [-74, -76, -79, -81, -83, -84, -87, -90])
  have hm := merge_two (literal (valuationOf q) (945)) (literal (valuationOf q) (965)) (literal (valuationOf q) (977)) (countLit q [-59, -62, -64, -66, -69, -72, -73]) (countLit q [-74, -76, -79, -81, -83, -84, -87, -90]) (count973 q) 4 1 (meaning945 q) (meaning965 q) (meaning977 q) hs
  change valuationOf q 945 = false ∨ valuationOf q 965 = false ∨ valuationOf q 977 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1071 (q : Snake 81) (h : Conditions q) : valuation q 945 = false ∨ valuation q 965 = false ∨ valuation q 977 = true := counterClause1071 (baseVal q)

theorem counterClause1072 (q : Nat → Bool) : valuationOf q 945 = false ∨ valuationOf q 966 = false ∨ valuationOf q 978 = true := by
  have hs : count973 q = (countLit q [-59, -62, -64, -66, -69, -72, -73]) + (countLit q [-74, -76, -79, -81, -83, -84, -87, -90]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -64, -66, -69, -72, -73]) (l₂ := [-74, -76, -79, -81, -83, -84, -87, -90])
  have hm := merge_two (literal (valuationOf q) (945)) (literal (valuationOf q) (966)) (literal (valuationOf q) (978)) (countLit q [-59, -62, -64, -66, -69, -72, -73]) (countLit q [-74, -76, -79, -81, -83, -84, -87, -90]) (count973 q) 4 2 (meaning945 q) (meaning966 q) (meaning978 q) hs
  change valuationOf q 945 = false ∨ valuationOf q 966 = false ∨ valuationOf q 978 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1072 (q : Snake 81) (h : Conditions q) : valuation q 945 = false ∨ valuation q 966 = false ∨ valuation q 978 = true := counterClause1072 (baseVal q)

theorem counterClause1073 (q : Nat → Bool) : valuationOf q 945 = false ∨ valuationOf q 967 = false ∨ valuationOf q 979 = true := by
  have hs : count973 q = (countLit q [-59, -62, -64, -66, -69, -72, -73]) + (countLit q [-74, -76, -79, -81, -83, -84, -87, -90]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -64, -66, -69, -72, -73]) (l₂ := [-74, -76, -79, -81, -83, -84, -87, -90])
  have hm := merge_two (literal (valuationOf q) (945)) (literal (valuationOf q) (967)) (literal (valuationOf q) (979)) (countLit q [-59, -62, -64, -66, -69, -72, -73]) (countLit q [-74, -76, -79, -81, -83, -84, -87, -90]) (count973 q) 4 3 (meaning945 q) (meaning967 q) (meaning979 q) hs
  change valuationOf q 945 = false ∨ valuationOf q 967 = false ∨ valuationOf q 979 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1073 (q : Snake 81) (h : Conditions q) : valuation q 945 = false ∨ valuation q 967 = false ∨ valuation q 979 = true := counterClause1073 (baseVal q)

theorem counterClause1074 (q : Nat → Bool) : valuationOf q 94 = true ∨ valuationOf q 988 = true := by
  have hs : count988 q = (countLit q [-93]) + (countLit q [-94]) := List.countP_append (p := literal q) (l₁ := [-93]) (l₂ := [-94])
  have hm := merge_right (literal (valuationOf q) (-94)) (literal (valuationOf q) (988)) (countLit q [-93]) (countLit q [-94]) (count988 q) 1 (meaningNeg94 q) (meaning988 q) hs
  change (! (valuationOf q 94)) = false ∨ valuationOf q 988 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1074 (q : Snake 81) (h : Conditions q) : valuation q 94 = true ∨ valuation q 988 = true := counterClause1074 (baseVal q)

theorem counterClause1075 (q : Nat → Bool) : valuationOf q 93 = true ∨ valuationOf q 988 = true := by
  have hs : count988 q = (countLit q [-93]) + (countLit q [-94]) := List.countP_append (p := literal q) (l₁ := [-93]) (l₂ := [-94])
  have hm := merge_left (literal (valuationOf q) (-93)) (literal (valuationOf q) (988)) (countLit q [-93]) (countLit q [-94]) (count988 q) 1 (meaningNeg93 q) (meaning988 q) hs
  change (! (valuationOf q 93)) = false ∨ valuationOf q 988 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1075 (q : Snake 81) (h : Conditions q) : valuation q 93 = true ∨ valuation q 988 = true := counterClause1075 (baseVal q)

theorem counterClause1076 (q : Nat → Bool) : valuationOf q 93 = true ∨ valuationOf q 94 = true ∨ valuationOf q 989 = true := by
  have hs : count988 q = (countLit q [-93]) + (countLit q [-94]) := List.countP_append (p := literal q) (l₁ := [-93]) (l₂ := [-94])
  have hm := merge_two (literal (valuationOf q) (-93)) (literal (valuationOf q) (-94)) (literal (valuationOf q) (989)) (countLit q [-93]) (countLit q [-94]) (count988 q) 1 1 (meaningNeg93 q) (meaningNeg94 q) (meaning989 q) hs
  change (! (valuationOf q 93)) = false ∨ (! (valuationOf q 94)) = false ∨ valuationOf q 989 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1076 (q : Snake 81) (h : Conditions q) : valuation q 93 = true ∨ valuation q 94 = true ∨ valuation q 989 = true := counterClause1076 (baseVal q)

theorem counterClause1077 (q : Nat → Bool) : valuationOf q 988 = false ∨ valuationOf q 990 = true := by
  have hs : count990 q = (countLit q [-91]) + (countLit q [-93, -94]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-93, -94])
  have hm := merge_right (literal (valuationOf q) (988)) (literal (valuationOf q) (990)) (countLit q [-91]) (countLit q [-93, -94]) (count990 q) 1 (meaning988 q) (meaning990 q) hs
  change valuationOf q 988 = false ∨ valuationOf q 990 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1077 (q : Snake 81) (h : Conditions q) : valuation q 988 = false ∨ valuation q 990 = true := counterClause1077 (baseVal q)

theorem counterClause1078 (q : Nat → Bool) : valuationOf q 989 = false ∨ valuationOf q 991 = true := by
  have hs : count990 q = (countLit q [-91]) + (countLit q [-93, -94]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-93, -94])
  have hm := merge_right (literal (valuationOf q) (989)) (literal (valuationOf q) (991)) (countLit q [-91]) (countLit q [-93, -94]) (count990 q) 2 (meaning989 q) (meaning991 q) hs
  change valuationOf q 989 = false ∨ valuationOf q 991 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1078 (q : Snake 81) (h : Conditions q) : valuation q 989 = false ∨ valuation q 991 = true := counterClause1078 (baseVal q)

theorem counterClause1079 (q : Nat → Bool) : valuationOf q 91 = true ∨ valuationOf q 990 = true := by
  have hs : count990 q = (countLit q [-91]) + (countLit q [-93, -94]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-93, -94])
  have hm := merge_left (literal (valuationOf q) (-91)) (literal (valuationOf q) (990)) (countLit q [-91]) (countLit q [-93, -94]) (count990 q) 1 (meaningNeg91 q) (meaning990 q) hs
  change (! (valuationOf q 91)) = false ∨ valuationOf q 990 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1079 (q : Snake 81) (h : Conditions q) : valuation q 91 = true ∨ valuation q 990 = true := counterClause1079 (baseVal q)

theorem counterClause1080 (q : Nat → Bool) : valuationOf q 91 = true ∨ valuationOf q 988 = false ∨ valuationOf q 991 = true := by
  have hs : count990 q = (countLit q [-91]) + (countLit q [-93, -94]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-93, -94])
  have hm := merge_two (literal (valuationOf q) (-91)) (literal (valuationOf q) (988)) (literal (valuationOf q) (991)) (countLit q [-91]) (countLit q [-93, -94]) (count990 q) 1 1 (meaningNeg91 q) (meaning988 q) (meaning991 q) hs
  change (! (valuationOf q 91)) = false ∨ valuationOf q 988 = false ∨ valuationOf q 991 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1080 (q : Snake 81) (h : Conditions q) : valuation q 91 = true ∨ valuation q 988 = false ∨ valuation q 991 = true := counterClause1080 (baseVal q)

theorem counterClause1081 (q : Nat → Bool) : valuationOf q 91 = true ∨ valuationOf q 989 = false ∨ valuationOf q 992 = true := by
  have hs : count990 q = (countLit q [-91]) + (countLit q [-93, -94]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-93, -94])
  have hm := merge_two (literal (valuationOf q) (-91)) (literal (valuationOf q) (989)) (literal (valuationOf q) (992)) (countLit q [-91]) (countLit q [-93, -94]) (count990 q) 1 2 (meaningNeg91 q) (meaning989 q) (meaning992 q) hs
  change (! (valuationOf q 91)) = false ∨ valuationOf q 989 = false ∨ valuationOf q 992 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1081 (q : Snake 81) (h : Conditions q) : valuation q 91 = true ∨ valuation q 989 = false ∨ valuation q 992 = true := counterClause1081 (baseVal q)

theorem counterClause1082 (q : Nat → Bool) : valuationOf q 99 = true ∨ valuationOf q 993 = true := by
  have hs : count993 q = (countLit q [-97]) + (countLit q [-99]) := List.countP_append (p := literal q) (l₁ := [-97]) (l₂ := [-99])
  have hm := merge_right (literal (valuationOf q) (-99)) (literal (valuationOf q) (993)) (countLit q [-97]) (countLit q [-99]) (count993 q) 1 (meaningNeg99 q) (meaning993 q) hs
  change (! (valuationOf q 99)) = false ∨ valuationOf q 993 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1082 (q : Snake 81) (h : Conditions q) : valuation q 99 = true ∨ valuation q 993 = true := counterClause1082 (baseVal q)

theorem counterClause1083 (q : Nat → Bool) : valuationOf q 97 = true ∨ valuationOf q 99 = true ∨ valuationOf q 994 = true := by
  have hs : count993 q = (countLit q [-97]) + (countLit q [-99]) := List.countP_append (p := literal q) (l₁ := [-97]) (l₂ := [-99])
  have hm := merge_two (literal (valuationOf q) (-97)) (literal (valuationOf q) (-99)) (literal (valuationOf q) (994)) (countLit q [-97]) (countLit q [-99]) (count993 q) 1 1 (meaningNeg97 q) (meaningNeg99 q) (meaning994 q) hs
  change (! (valuationOf q 97)) = false ∨ (! (valuationOf q 99)) = false ∨ valuationOf q 994 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1083 (q : Snake 81) (h : Conditions q) : valuation q 97 = true ∨ valuation q 99 = true ∨ valuation q 994 = true := counterClause1083 (baseVal q)

theorem counterClause1084 (q : Nat → Bool) : valuationOf q 101 = true ∨ valuationOf q 995 = true := by
  have hs : count995 q = (countLit q [-100]) + (countLit q [-101]) := List.countP_append (p := literal q) (l₁ := [-100]) (l₂ := [-101])
  have hm := merge_right (literal (valuationOf q) (-101)) (literal (valuationOf q) (995)) (countLit q [-100]) (countLit q [-101]) (count995 q) 1 (meaningNeg101 q) (meaning995 q) hs
  change (! (valuationOf q 101)) = false ∨ valuationOf q 995 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1084 (q : Snake 81) (h : Conditions q) : valuation q 101 = true ∨ valuation q 995 = true := counterClause1084 (baseVal q)

theorem counterClause1085 (q : Nat → Bool) : valuationOf q 100 = true ∨ valuationOf q 101 = true ∨ valuationOf q 996 = true := by
  have hs : count995 q = (countLit q [-100]) + (countLit q [-101]) := List.countP_append (p := literal q) (l₁ := [-100]) (l₂ := [-101])
  have hm := merge_two (literal (valuationOf q) (-100)) (literal (valuationOf q) (-101)) (literal (valuationOf q) (996)) (countLit q [-100]) (countLit q [-101]) (count995 q) 1 1 (meaningNeg100 q) (meaningNeg101 q) (meaning996 q) hs
  change (! (valuationOf q 100)) = false ∨ (! (valuationOf q 101)) = false ∨ valuationOf q 996 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1085 (q : Snake 81) (h : Conditions q) : valuation q 100 = true ∨ valuation q 101 = true ∨ valuation q 996 = true := counterClause1085 (baseVal q)

theorem counterClause1086 (q : Nat → Bool) : valuationOf q 995 = false ∨ valuationOf q 997 = true := by
  have hs : count997 q = (countLit q [-97, -99]) + (countLit q [-100, -101]) := List.countP_append (p := literal q) (l₁ := [-97, -99]) (l₂ := [-100, -101])
  have hm := merge_right (literal (valuationOf q) (995)) (literal (valuationOf q) (997)) (countLit q [-97, -99]) (countLit q [-100, -101]) (count997 q) 1 (meaning995 q) (meaning997 q) hs
  change valuationOf q 995 = false ∨ valuationOf q 997 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1086 (q : Snake 81) (h : Conditions q) : valuation q 995 = false ∨ valuation q 997 = true := counterClause1086 (baseVal q)

theorem counterClause1087 (q : Nat → Bool) : valuationOf q 993 = false ∨ valuationOf q 995 = false ∨ valuationOf q 998 = true := by
  have hs : count997 q = (countLit q [-97, -99]) + (countLit q [-100, -101]) := List.countP_append (p := literal q) (l₁ := [-97, -99]) (l₂ := [-100, -101])
  have hm := merge_two (literal (valuationOf q) (993)) (literal (valuationOf q) (995)) (literal (valuationOf q) (998)) (countLit q [-97, -99]) (countLit q [-100, -101]) (count997 q) 1 1 (meaning993 q) (meaning995 q) (meaning998 q) hs
  change valuationOf q 993 = false ∨ valuationOf q 995 = false ∨ valuationOf q 998 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1087 (q : Snake 81) (h : Conditions q) : valuation q 993 = false ∨ valuation q 995 = false ∨ valuation q 998 = true := counterClause1087 (baseVal q)

theorem counterClause1088 (q : Nat → Bool) : valuationOf q 993 = false ∨ valuationOf q 996 = false ∨ valuationOf q 999 = true := by
  have hs : count997 q = (countLit q [-97, -99]) + (countLit q [-100, -101]) := List.countP_append (p := literal q) (l₁ := [-97, -99]) (l₂ := [-100, -101])
  have hm := merge_two (literal (valuationOf q) (993)) (literal (valuationOf q) (996)) (literal (valuationOf q) (999)) (countLit q [-97, -99]) (countLit q [-100, -101]) (count997 q) 1 2 (meaning993 q) (meaning996 q) (meaning999 q) hs
  change valuationOf q 993 = false ∨ valuationOf q 996 = false ∨ valuationOf q 999 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1088 (q : Snake 81) (h : Conditions q) : valuation q 993 = false ∨ valuation q 996 = false ∨ valuation q 999 = true := counterClause1088 (baseVal q)

theorem block33 (q : Snake 81) (h : Conditions q) : B112E213.Block33 (valuation q) :=
  ⟨clause1057 q h, clause1058 q h, clause1059 q h, clause1060 q h, clause1061 q h, clause1062 q h, clause1063 q h, clause1064 q h, clause1065 q h, clause1066 q h, clause1067 q h, clause1068 q h, clause1069 q h, clause1070 q h, clause1071 q h, clause1072 q h, clause1073 q h, clause1074 q h, clause1075 q h, clause1076 q h, clause1077 q h, clause1078 q h, clause1079 q h, clause1080 q h, clause1081 q h, clause1082 q h, clause1083 q h, clause1084 q h, clause1085 q h, clause1086 q h, clause1087 q h, clause1088 q h⟩

end
end Snake9.Regrowth.E112213
