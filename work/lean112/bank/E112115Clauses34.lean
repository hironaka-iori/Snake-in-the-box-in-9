import E112115Semantics
import B112E115Inputs
namespace Snake9.Regrowth.E112115
noncomputable section
local instance blockDec34 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1089 (q : Nat → Bool) : valuationOf q 954 = false ∨ valuationOf q 961 = false ∨ valuationOf q 967 = true := by
  have hs : count965 q = (countLit q [-74, -75, -78, -79]) + (countLit q [-82, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-74, -75, -78, -79]) (l₂ := [-82, -84, -86, -88])
  have hm := merge_two (literal (valuationOf q) (954)) (literal (valuationOf q) (961)) (literal (valuationOf q) (967)) (countLit q [-74, -75, -78, -79]) (countLit q [-82, -84, -86, -88]) (count965 q) 2 1 (meaning954 q) (meaning961 q) (meaning967 q) hs
  change valuationOf q 954 = false ∨ valuationOf q 961 = false ∨ valuationOf q 967 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1089 (q : Snake 81) (h : Conditions q) : valuation q 954 = false ∨ valuation q 961 = false ∨ valuation q 967 = true := counterClause1089 (baseVal q)

theorem counterClause1090 (q : Nat → Bool) : valuationOf q 954 = false ∨ valuationOf q 962 = false ∨ valuationOf q 968 = true := by
  have hs : count965 q = (countLit q [-74, -75, -78, -79]) + (countLit q [-82, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-74, -75, -78, -79]) (l₂ := [-82, -84, -86, -88])
  have hm := merge_two (literal (valuationOf q) (954)) (literal (valuationOf q) (962)) (literal (valuationOf q) (968)) (countLit q [-74, -75, -78, -79]) (countLit q [-82, -84, -86, -88]) (count965 q) 2 2 (meaning954 q) (meaning962 q) (meaning968 q) hs
  change valuationOf q 954 = false ∨ valuationOf q 962 = false ∨ valuationOf q 968 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1090 (q : Snake 81) (h : Conditions q) : valuation q 954 = false ∨ valuation q 962 = false ∨ valuation q 968 = true := counterClause1090 (baseVal q)

theorem counterClause1091 (q : Nat → Bool) : valuationOf q 954 = false ∨ valuationOf q 963 = false ∨ valuationOf q 969 = true := by
  have hs : count965 q = (countLit q [-74, -75, -78, -79]) + (countLit q [-82, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-74, -75, -78, -79]) (l₂ := [-82, -84, -86, -88])
  have hm := merge_two (literal (valuationOf q) (954)) (literal (valuationOf q) (963)) (literal (valuationOf q) (969)) (countLit q [-74, -75, -78, -79]) (countLit q [-82, -84, -86, -88]) (count965 q) 2 3 (meaning954 q) (meaning963 q) (meaning969 q) hs
  change valuationOf q 954 = false ∨ valuationOf q 963 = false ∨ valuationOf q 969 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1091 (q : Snake 81) (h : Conditions q) : valuation q 954 = false ∨ valuation q 963 = false ∨ valuation q 969 = true := counterClause1091 (baseVal q)

theorem counterClause1092 (q : Nat → Bool) : valuationOf q 955 = false ∨ valuationOf q 967 = true := by
  have hs : count965 q = (countLit q [-74, -75, -78, -79]) + (countLit q [-82, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-74, -75, -78, -79]) (l₂ := [-82, -84, -86, -88])
  have hm := merge_left (literal (valuationOf q) (955)) (literal (valuationOf q) (967)) (countLit q [-74, -75, -78, -79]) (countLit q [-82, -84, -86, -88]) (count965 q) 3 (meaning955 q) (meaning967 q) hs
  change valuationOf q 955 = false ∨ valuationOf q 967 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1092 (q : Snake 81) (h : Conditions q) : valuation q 955 = false ∨ valuation q 967 = true := counterClause1092 (baseVal q)

theorem counterClause1093 (q : Nat → Bool) : valuationOf q 955 = false ∨ valuationOf q 961 = false ∨ valuationOf q 968 = true := by
  have hs : count965 q = (countLit q [-74, -75, -78, -79]) + (countLit q [-82, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-74, -75, -78, -79]) (l₂ := [-82, -84, -86, -88])
  have hm := merge_two (literal (valuationOf q) (955)) (literal (valuationOf q) (961)) (literal (valuationOf q) (968)) (countLit q [-74, -75, -78, -79]) (countLit q [-82, -84, -86, -88]) (count965 q) 3 1 (meaning955 q) (meaning961 q) (meaning968 q) hs
  change valuationOf q 955 = false ∨ valuationOf q 961 = false ∨ valuationOf q 968 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1093 (q : Snake 81) (h : Conditions q) : valuation q 955 = false ∨ valuation q 961 = false ∨ valuation q 968 = true := counterClause1093 (baseVal q)

theorem counterClause1094 (q : Nat → Bool) : valuationOf q 955 = false ∨ valuationOf q 962 = false ∨ valuationOf q 969 = true := by
  have hs : count965 q = (countLit q [-74, -75, -78, -79]) + (countLit q [-82, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-74, -75, -78, -79]) (l₂ := [-82, -84, -86, -88])
  have hm := merge_two (literal (valuationOf q) (955)) (literal (valuationOf q) (962)) (literal (valuationOf q) (969)) (countLit q [-74, -75, -78, -79]) (countLit q [-82, -84, -86, -88]) (count965 q) 3 2 (meaning955 q) (meaning962 q) (meaning969 q) hs
  change valuationOf q 955 = false ∨ valuationOf q 962 = false ∨ valuationOf q 969 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1094 (q : Snake 81) (h : Conditions q) : valuation q 955 = false ∨ valuation q 962 = false ∨ valuation q 969 = true := counterClause1094 (baseVal q)

theorem counterClause1095 (q : Nat → Bool) : valuationOf q 965 = false ∨ valuationOf q 973 = true := by
  have hs : count973 q = (countLit q [-61, -62, -65, -67, -68, -70, -73]) + (countLit q [-74, -75, -78, -79, -82, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -67, -68, -70, -73]) (l₂ := [-74, -75, -78, -79, -82, -84, -86, -88])
  have hm := merge_right (literal (valuationOf q) (965)) (literal (valuationOf q) (973)) (countLit q [-61, -62, -65, -67, -68, -70, -73]) (countLit q [-74, -75, -78, -79, -82, -84, -86, -88]) (count973 q) 1 (meaning965 q) (meaning973 q) hs
  change valuationOf q 965 = false ∨ valuationOf q 973 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1095 (q : Snake 81) (h : Conditions q) : valuation q 965 = false ∨ valuation q 973 = true := counterClause1095 (baseVal q)

theorem counterClause1096 (q : Nat → Bool) : valuationOf q 966 = false ∨ valuationOf q 974 = true := by
  have hs : count973 q = (countLit q [-61, -62, -65, -67, -68, -70, -73]) + (countLit q [-74, -75, -78, -79, -82, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -67, -68, -70, -73]) (l₂ := [-74, -75, -78, -79, -82, -84, -86, -88])
  have hm := merge_right (literal (valuationOf q) (966)) (literal (valuationOf q) (974)) (countLit q [-61, -62, -65, -67, -68, -70, -73]) (countLit q [-74, -75, -78, -79, -82, -84, -86, -88]) (count973 q) 2 (meaning966 q) (meaning974 q) hs
  change valuationOf q 966 = false ∨ valuationOf q 974 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1096 (q : Snake 81) (h : Conditions q) : valuation q 966 = false ∨ valuation q 974 = true := counterClause1096 (baseVal q)

theorem counterClause1097 (q : Nat → Bool) : valuationOf q 967 = false ∨ valuationOf q 975 = true := by
  have hs : count973 q = (countLit q [-61, -62, -65, -67, -68, -70, -73]) + (countLit q [-74, -75, -78, -79, -82, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -67, -68, -70, -73]) (l₂ := [-74, -75, -78, -79, -82, -84, -86, -88])
  have hm := merge_right (literal (valuationOf q) (967)) (literal (valuationOf q) (975)) (countLit q [-61, -62, -65, -67, -68, -70, -73]) (countLit q [-74, -75, -78, -79, -82, -84, -86, -88]) (count973 q) 3 (meaning967 q) (meaning975 q) hs
  change valuationOf q 967 = false ∨ valuationOf q 975 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1097 (q : Snake 81) (h : Conditions q) : valuation q 967 = false ∨ valuation q 975 = true := counterClause1097 (baseVal q)

theorem counterClause1098 (q : Nat → Bool) : valuationOf q 942 = false ∨ valuationOf q 965 = false ∨ valuationOf q 974 = true := by
  have hs : count973 q = (countLit q [-61, -62, -65, -67, -68, -70, -73]) + (countLit q [-74, -75, -78, -79, -82, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -67, -68, -70, -73]) (l₂ := [-74, -75, -78, -79, -82, -84, -86, -88])
  have hm := merge_two (literal (valuationOf q) (942)) (literal (valuationOf q) (965)) (literal (valuationOf q) (974)) (countLit q [-61, -62, -65, -67, -68, -70, -73]) (countLit q [-74, -75, -78, -79, -82, -84, -86, -88]) (count973 q) 1 1 (meaning942 q) (meaning965 q) (meaning974 q) hs
  change valuationOf q 942 = false ∨ valuationOf q 965 = false ∨ valuationOf q 974 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1098 (q : Snake 81) (h : Conditions q) : valuation q 942 = false ∨ valuation q 965 = false ∨ valuation q 974 = true := counterClause1098 (baseVal q)

theorem counterClause1099 (q : Nat → Bool) : valuationOf q 942 = false ∨ valuationOf q 966 = false ∨ valuationOf q 975 = true := by
  have hs : count973 q = (countLit q [-61, -62, -65, -67, -68, -70, -73]) + (countLit q [-74, -75, -78, -79, -82, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -67, -68, -70, -73]) (l₂ := [-74, -75, -78, -79, -82, -84, -86, -88])
  have hm := merge_two (literal (valuationOf q) (942)) (literal (valuationOf q) (966)) (literal (valuationOf q) (975)) (countLit q [-61, -62, -65, -67, -68, -70, -73]) (countLit q [-74, -75, -78, -79, -82, -84, -86, -88]) (count973 q) 1 2 (meaning942 q) (meaning966 q) (meaning975 q) hs
  change valuationOf q 942 = false ∨ valuationOf q 966 = false ∨ valuationOf q 975 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1099 (q : Snake 81) (h : Conditions q) : valuation q 942 = false ∨ valuation q 966 = false ∨ valuation q 975 = true := counterClause1099 (baseVal q)

theorem counterClause1100 (q : Nat → Bool) : valuationOf q 942 = false ∨ valuationOf q 967 = false ∨ valuationOf q 976 = true := by
  have hs : count973 q = (countLit q [-61, -62, -65, -67, -68, -70, -73]) + (countLit q [-74, -75, -78, -79, -82, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -67, -68, -70, -73]) (l₂ := [-74, -75, -78, -79, -82, -84, -86, -88])
  have hm := merge_two (literal (valuationOf q) (942)) (literal (valuationOf q) (967)) (literal (valuationOf q) (976)) (countLit q [-61, -62, -65, -67, -68, -70, -73]) (countLit q [-74, -75, -78, -79, -82, -84, -86, -88]) (count973 q) 1 3 (meaning942 q) (meaning967 q) (meaning976 q) hs
  change valuationOf q 942 = false ∨ valuationOf q 967 = false ∨ valuationOf q 976 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1100 (q : Snake 81) (h : Conditions q) : valuation q 942 = false ∨ valuation q 967 = false ∨ valuation q 976 = true := counterClause1100 (baseVal q)

theorem counterClause1101 (q : Nat → Bool) : valuationOf q 942 = false ∨ valuationOf q 968 = false ∨ valuationOf q 977 = true := by
  have hs : count973 q = (countLit q [-61, -62, -65, -67, -68, -70, -73]) + (countLit q [-74, -75, -78, -79, -82, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -67, -68, -70, -73]) (l₂ := [-74, -75, -78, -79, -82, -84, -86, -88])
  have hm := merge_two (literal (valuationOf q) (942)) (literal (valuationOf q) (968)) (literal (valuationOf q) (977)) (countLit q [-61, -62, -65, -67, -68, -70, -73]) (countLit q [-74, -75, -78, -79, -82, -84, -86, -88]) (count973 q) 1 4 (meaning942 q) (meaning968 q) (meaning977 q) hs
  change valuationOf q 942 = false ∨ valuationOf q 968 = false ∨ valuationOf q 977 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1101 (q : Snake 81) (h : Conditions q) : valuation q 942 = false ∨ valuation q 968 = false ∨ valuation q 977 = true := counterClause1101 (baseVal q)

theorem counterClause1102 (q : Nat → Bool) : valuationOf q 942 = false ∨ valuationOf q 969 = false ∨ valuationOf q 978 = true := by
  have hs : count973 q = (countLit q [-61, -62, -65, -67, -68, -70, -73]) + (countLit q [-74, -75, -78, -79, -82, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -67, -68, -70, -73]) (l₂ := [-74, -75, -78, -79, -82, -84, -86, -88])
  have hm := merge_two (literal (valuationOf q) (942)) (literal (valuationOf q) (969)) (literal (valuationOf q) (978)) (countLit q [-61, -62, -65, -67, -68, -70, -73]) (countLit q [-74, -75, -78, -79, -82, -84, -86, -88]) (count973 q) 1 5 (meaning942 q) (meaning969 q) (meaning978 q) hs
  change valuationOf q 942 = false ∨ valuationOf q 969 = false ∨ valuationOf q 978 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1102 (q : Snake 81) (h : Conditions q) : valuation q 942 = false ∨ valuation q 969 = false ∨ valuation q 978 = true := counterClause1102 (baseVal q)

theorem counterClause1103 (q : Nat → Bool) : valuationOf q 943 = false ∨ valuationOf q 965 = false ∨ valuationOf q 975 = true := by
  have hs : count973 q = (countLit q [-61, -62, -65, -67, -68, -70, -73]) + (countLit q [-74, -75, -78, -79, -82, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -67, -68, -70, -73]) (l₂ := [-74, -75, -78, -79, -82, -84, -86, -88])
  have hm := merge_two (literal (valuationOf q) (943)) (literal (valuationOf q) (965)) (literal (valuationOf q) (975)) (countLit q [-61, -62, -65, -67, -68, -70, -73]) (countLit q [-74, -75, -78, -79, -82, -84, -86, -88]) (count973 q) 2 1 (meaning943 q) (meaning965 q) (meaning975 q) hs
  change valuationOf q 943 = false ∨ valuationOf q 965 = false ∨ valuationOf q 975 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1103 (q : Snake 81) (h : Conditions q) : valuation q 943 = false ∨ valuation q 965 = false ∨ valuation q 975 = true := counterClause1103 (baseVal q)

theorem counterClause1104 (q : Nat → Bool) : valuationOf q 943 = false ∨ valuationOf q 966 = false ∨ valuationOf q 976 = true := by
  have hs : count973 q = (countLit q [-61, -62, -65, -67, -68, -70, -73]) + (countLit q [-74, -75, -78, -79, -82, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -67, -68, -70, -73]) (l₂ := [-74, -75, -78, -79, -82, -84, -86, -88])
  have hm := merge_two (literal (valuationOf q) (943)) (literal (valuationOf q) (966)) (literal (valuationOf q) (976)) (countLit q [-61, -62, -65, -67, -68, -70, -73]) (countLit q [-74, -75, -78, -79, -82, -84, -86, -88]) (count973 q) 2 2 (meaning943 q) (meaning966 q) (meaning976 q) hs
  change valuationOf q 943 = false ∨ valuationOf q 966 = false ∨ valuationOf q 976 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1104 (q : Snake 81) (h : Conditions q) : valuation q 943 = false ∨ valuation q 966 = false ∨ valuation q 976 = true := counterClause1104 (baseVal q)

theorem counterClause1105 (q : Nat → Bool) : valuationOf q 943 = false ∨ valuationOf q 967 = false ∨ valuationOf q 977 = true := by
  have hs : count973 q = (countLit q [-61, -62, -65, -67, -68, -70, -73]) + (countLit q [-74, -75, -78, -79, -82, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -67, -68, -70, -73]) (l₂ := [-74, -75, -78, -79, -82, -84, -86, -88])
  have hm := merge_two (literal (valuationOf q) (943)) (literal (valuationOf q) (967)) (literal (valuationOf q) (977)) (countLit q [-61, -62, -65, -67, -68, -70, -73]) (countLit q [-74, -75, -78, -79, -82, -84, -86, -88]) (count973 q) 2 3 (meaning943 q) (meaning967 q) (meaning977 q) hs
  change valuationOf q 943 = false ∨ valuationOf q 967 = false ∨ valuationOf q 977 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1105 (q : Snake 81) (h : Conditions q) : valuation q 943 = false ∨ valuation q 967 = false ∨ valuation q 977 = true := counterClause1105 (baseVal q)

theorem counterClause1106 (q : Nat → Bool) : valuationOf q 943 = false ∨ valuationOf q 968 = false ∨ valuationOf q 978 = true := by
  have hs : count973 q = (countLit q [-61, -62, -65, -67, -68, -70, -73]) + (countLit q [-74, -75, -78, -79, -82, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -67, -68, -70, -73]) (l₂ := [-74, -75, -78, -79, -82, -84, -86, -88])
  have hm := merge_two (literal (valuationOf q) (943)) (literal (valuationOf q) (968)) (literal (valuationOf q) (978)) (countLit q [-61, -62, -65, -67, -68, -70, -73]) (countLit q [-74, -75, -78, -79, -82, -84, -86, -88]) (count973 q) 2 4 (meaning943 q) (meaning968 q) (meaning978 q) hs
  change valuationOf q 943 = false ∨ valuationOf q 968 = false ∨ valuationOf q 978 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1106 (q : Snake 81) (h : Conditions q) : valuation q 943 = false ∨ valuation q 968 = false ∨ valuation q 978 = true := counterClause1106 (baseVal q)

theorem counterClause1107 (q : Nat → Bool) : valuationOf q 943 = false ∨ valuationOf q 969 = false ∨ valuationOf q 979 = true := by
  have hs : count973 q = (countLit q [-61, -62, -65, -67, -68, -70, -73]) + (countLit q [-74, -75, -78, -79, -82, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -67, -68, -70, -73]) (l₂ := [-74, -75, -78, -79, -82, -84, -86, -88])
  have hm := merge_two (literal (valuationOf q) (943)) (literal (valuationOf q) (969)) (literal (valuationOf q) (979)) (countLit q [-61, -62, -65, -67, -68, -70, -73]) (countLit q [-74, -75, -78, -79, -82, -84, -86, -88]) (count973 q) 2 5 (meaning943 q) (meaning969 q) (meaning979 q) hs
  change valuationOf q 943 = false ∨ valuationOf q 969 = false ∨ valuationOf q 979 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1107 (q : Snake 81) (h : Conditions q) : valuation q 943 = false ∨ valuation q 969 = false ∨ valuation q 979 = true := counterClause1107 (baseVal q)

theorem counterClause1108 (q : Nat → Bool) : valuationOf q 944 = false ∨ valuationOf q 965 = false ∨ valuationOf q 976 = true := by
  have hs : count973 q = (countLit q [-61, -62, -65, -67, -68, -70, -73]) + (countLit q [-74, -75, -78, -79, -82, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -67, -68, -70, -73]) (l₂ := [-74, -75, -78, -79, -82, -84, -86, -88])
  have hm := merge_two (literal (valuationOf q) (944)) (literal (valuationOf q) (965)) (literal (valuationOf q) (976)) (countLit q [-61, -62, -65, -67, -68, -70, -73]) (countLit q [-74, -75, -78, -79, -82, -84, -86, -88]) (count973 q) 3 1 (meaning944 q) (meaning965 q) (meaning976 q) hs
  change valuationOf q 944 = false ∨ valuationOf q 965 = false ∨ valuationOf q 976 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1108 (q : Snake 81) (h : Conditions q) : valuation q 944 = false ∨ valuation q 965 = false ∨ valuation q 976 = true := counterClause1108 (baseVal q)

theorem counterClause1109 (q : Nat → Bool) : valuationOf q 944 = false ∨ valuationOf q 966 = false ∨ valuationOf q 977 = true := by
  have hs : count973 q = (countLit q [-61, -62, -65, -67, -68, -70, -73]) + (countLit q [-74, -75, -78, -79, -82, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -67, -68, -70, -73]) (l₂ := [-74, -75, -78, -79, -82, -84, -86, -88])
  have hm := merge_two (literal (valuationOf q) (944)) (literal (valuationOf q) (966)) (literal (valuationOf q) (977)) (countLit q [-61, -62, -65, -67, -68, -70, -73]) (countLit q [-74, -75, -78, -79, -82, -84, -86, -88]) (count973 q) 3 2 (meaning944 q) (meaning966 q) (meaning977 q) hs
  change valuationOf q 944 = false ∨ valuationOf q 966 = false ∨ valuationOf q 977 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1109 (q : Snake 81) (h : Conditions q) : valuation q 944 = false ∨ valuation q 966 = false ∨ valuation q 977 = true := counterClause1109 (baseVal q)

theorem counterClause1110 (q : Nat → Bool) : valuationOf q 944 = false ∨ valuationOf q 967 = false ∨ valuationOf q 978 = true := by
  have hs : count973 q = (countLit q [-61, -62, -65, -67, -68, -70, -73]) + (countLit q [-74, -75, -78, -79, -82, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -67, -68, -70, -73]) (l₂ := [-74, -75, -78, -79, -82, -84, -86, -88])
  have hm := merge_two (literal (valuationOf q) (944)) (literal (valuationOf q) (967)) (literal (valuationOf q) (978)) (countLit q [-61, -62, -65, -67, -68, -70, -73]) (countLit q [-74, -75, -78, -79, -82, -84, -86, -88]) (count973 q) 3 3 (meaning944 q) (meaning967 q) (meaning978 q) hs
  change valuationOf q 944 = false ∨ valuationOf q 967 = false ∨ valuationOf q 978 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1110 (q : Snake 81) (h : Conditions q) : valuation q 944 = false ∨ valuation q 967 = false ∨ valuation q 978 = true := counterClause1110 (baseVal q)

theorem counterClause1111 (q : Nat → Bool) : valuationOf q 944 = false ∨ valuationOf q 968 = false ∨ valuationOf q 979 = true := by
  have hs : count973 q = (countLit q [-61, -62, -65, -67, -68, -70, -73]) + (countLit q [-74, -75, -78, -79, -82, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -67, -68, -70, -73]) (l₂ := [-74, -75, -78, -79, -82, -84, -86, -88])
  have hm := merge_two (literal (valuationOf q) (944)) (literal (valuationOf q) (968)) (literal (valuationOf q) (979)) (countLit q [-61, -62, -65, -67, -68, -70, -73]) (countLit q [-74, -75, -78, -79, -82, -84, -86, -88]) (count973 q) 3 4 (meaning944 q) (meaning968 q) (meaning979 q) hs
  change valuationOf q 944 = false ∨ valuationOf q 968 = false ∨ valuationOf q 979 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1111 (q : Snake 81) (h : Conditions q) : valuation q 944 = false ∨ valuation q 968 = false ∨ valuation q 979 = true := counterClause1111 (baseVal q)

theorem counterClause1112 (q : Nat → Bool) : valuationOf q 944 = false ∨ valuationOf q 969 = false ∨ valuationOf q 980 = true := by
  have hs : count973 q = (countLit q [-61, -62, -65, -67, -68, -70, -73]) + (countLit q [-74, -75, -78, -79, -82, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -67, -68, -70, -73]) (l₂ := [-74, -75, -78, -79, -82, -84, -86, -88])
  have hm := merge_two (literal (valuationOf q) (944)) (literal (valuationOf q) (969)) (literal (valuationOf q) (980)) (countLit q [-61, -62, -65, -67, -68, -70, -73]) (countLit q [-74, -75, -78, -79, -82, -84, -86, -88]) (count973 q) 3 5 (meaning944 q) (meaning969 q) (meaning980 q) hs
  change valuationOf q 944 = false ∨ valuationOf q 969 = false ∨ valuationOf q 980 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1112 (q : Snake 81) (h : Conditions q) : valuation q 944 = false ∨ valuation q 969 = false ∨ valuation q 980 = true := counterClause1112 (baseVal q)

theorem counterClause1113 (q : Nat → Bool) : valuationOf q 945 = false ∨ valuationOf q 965 = false ∨ valuationOf q 977 = true := by
  have hs : count973 q = (countLit q [-61, -62, -65, -67, -68, -70, -73]) + (countLit q [-74, -75, -78, -79, -82, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -67, -68, -70, -73]) (l₂ := [-74, -75, -78, -79, -82, -84, -86, -88])
  have hm := merge_two (literal (valuationOf q) (945)) (literal (valuationOf q) (965)) (literal (valuationOf q) (977)) (countLit q [-61, -62, -65, -67, -68, -70, -73]) (countLit q [-74, -75, -78, -79, -82, -84, -86, -88]) (count973 q) 4 1 (meaning945 q) (meaning965 q) (meaning977 q) hs
  change valuationOf q 945 = false ∨ valuationOf q 965 = false ∨ valuationOf q 977 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1113 (q : Snake 81) (h : Conditions q) : valuation q 945 = false ∨ valuation q 965 = false ∨ valuation q 977 = true := counterClause1113 (baseVal q)

theorem counterClause1114 (q : Nat → Bool) : valuationOf q 945 = false ∨ valuationOf q 966 = false ∨ valuationOf q 978 = true := by
  have hs : count973 q = (countLit q [-61, -62, -65, -67, -68, -70, -73]) + (countLit q [-74, -75, -78, -79, -82, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -67, -68, -70, -73]) (l₂ := [-74, -75, -78, -79, -82, -84, -86, -88])
  have hm := merge_two (literal (valuationOf q) (945)) (literal (valuationOf q) (966)) (literal (valuationOf q) (978)) (countLit q [-61, -62, -65, -67, -68, -70, -73]) (countLit q [-74, -75, -78, -79, -82, -84, -86, -88]) (count973 q) 4 2 (meaning945 q) (meaning966 q) (meaning978 q) hs
  change valuationOf q 945 = false ∨ valuationOf q 966 = false ∨ valuationOf q 978 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1114 (q : Snake 81) (h : Conditions q) : valuation q 945 = false ∨ valuation q 966 = false ∨ valuation q 978 = true := counterClause1114 (baseVal q)

theorem counterClause1115 (q : Nat → Bool) : valuationOf q 945 = false ∨ valuationOf q 967 = false ∨ valuationOf q 979 = true := by
  have hs : count973 q = (countLit q [-61, -62, -65, -67, -68, -70, -73]) + (countLit q [-74, -75, -78, -79, -82, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -67, -68, -70, -73]) (l₂ := [-74, -75, -78, -79, -82, -84, -86, -88])
  have hm := merge_two (literal (valuationOf q) (945)) (literal (valuationOf q) (967)) (literal (valuationOf q) (979)) (countLit q [-61, -62, -65, -67, -68, -70, -73]) (countLit q [-74, -75, -78, -79, -82, -84, -86, -88]) (count973 q) 4 3 (meaning945 q) (meaning967 q) (meaning979 q) hs
  change valuationOf q 945 = false ∨ valuationOf q 967 = false ∨ valuationOf q 979 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1115 (q : Snake 81) (h : Conditions q) : valuation q 945 = false ∨ valuation q 967 = false ∨ valuation q 979 = true := counterClause1115 (baseVal q)

theorem counterClause1116 (q : Nat → Bool) : valuationOf q 945 = false ∨ valuationOf q 968 = false ∨ valuationOf q 980 = true := by
  have hs : count973 q = (countLit q [-61, -62, -65, -67, -68, -70, -73]) + (countLit q [-74, -75, -78, -79, -82, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -67, -68, -70, -73]) (l₂ := [-74, -75, -78, -79, -82, -84, -86, -88])
  have hm := merge_two (literal (valuationOf q) (945)) (literal (valuationOf q) (968)) (literal (valuationOf q) (980)) (countLit q [-61, -62, -65, -67, -68, -70, -73]) (countLit q [-74, -75, -78, -79, -82, -84, -86, -88]) (count973 q) 4 4 (meaning945 q) (meaning968 q) (meaning980 q) hs
  change valuationOf q 945 = false ∨ valuationOf q 968 = false ∨ valuationOf q 980 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1116 (q : Snake 81) (h : Conditions q) : valuation q 945 = false ∨ valuation q 968 = false ∨ valuation q 980 = true := counterClause1116 (baseVal q)

theorem counterClause1117 (q : Nat → Bool) : valuationOf q 946 = false ∨ valuationOf q 965 = false ∨ valuationOf q 978 = true := by
  have hs : count973 q = (countLit q [-61, -62, -65, -67, -68, -70, -73]) + (countLit q [-74, -75, -78, -79, -82, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -67, -68, -70, -73]) (l₂ := [-74, -75, -78, -79, -82, -84, -86, -88])
  have hm := merge_two (literal (valuationOf q) (946)) (literal (valuationOf q) (965)) (literal (valuationOf q) (978)) (countLit q [-61, -62, -65, -67, -68, -70, -73]) (countLit q [-74, -75, -78, -79, -82, -84, -86, -88]) (count973 q) 5 1 (meaning946 q) (meaning965 q) (meaning978 q) hs
  change valuationOf q 946 = false ∨ valuationOf q 965 = false ∨ valuationOf q 978 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1117 (q : Snake 81) (h : Conditions q) : valuation q 946 = false ∨ valuation q 965 = false ∨ valuation q 978 = true := counterClause1117 (baseVal q)

theorem counterClause1118 (q : Nat → Bool) : valuationOf q 946 = false ∨ valuationOf q 966 = false ∨ valuationOf q 979 = true := by
  have hs : count973 q = (countLit q [-61, -62, -65, -67, -68, -70, -73]) + (countLit q [-74, -75, -78, -79, -82, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -67, -68, -70, -73]) (l₂ := [-74, -75, -78, -79, -82, -84, -86, -88])
  have hm := merge_two (literal (valuationOf q) (946)) (literal (valuationOf q) (966)) (literal (valuationOf q) (979)) (countLit q [-61, -62, -65, -67, -68, -70, -73]) (countLit q [-74, -75, -78, -79, -82, -84, -86, -88]) (count973 q) 5 2 (meaning946 q) (meaning966 q) (meaning979 q) hs
  change valuationOf q 946 = false ∨ valuationOf q 966 = false ∨ valuationOf q 979 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1118 (q : Snake 81) (h : Conditions q) : valuation q 946 = false ∨ valuation q 966 = false ∨ valuation q 979 = true := counterClause1118 (baseVal q)

theorem counterClause1119 (q : Nat → Bool) : valuationOf q 946 = false ∨ valuationOf q 967 = false ∨ valuationOf q 980 = true := by
  have hs : count973 q = (countLit q [-61, -62, -65, -67, -68, -70, -73]) + (countLit q [-74, -75, -78, -79, -82, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -67, -68, -70, -73]) (l₂ := [-74, -75, -78, -79, -82, -84, -86, -88])
  have hm := merge_two (literal (valuationOf q) (946)) (literal (valuationOf q) (967)) (literal (valuationOf q) (980)) (countLit q [-61, -62, -65, -67, -68, -70, -73]) (countLit q [-74, -75, -78, -79, -82, -84, -86, -88]) (count973 q) 5 3 (meaning946 q) (meaning967 q) (meaning980 q) hs
  change valuationOf q 946 = false ∨ valuationOf q 967 = false ∨ valuationOf q 980 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1119 (q : Snake 81) (h : Conditions q) : valuation q 946 = false ∨ valuation q 967 = false ∨ valuation q 980 = true := counterClause1119 (baseVal q)

theorem counterClause1120 (q : Nat → Bool) : valuationOf q 947 = false ∨ valuationOf q 965 = false ∨ valuationOf q 979 = true := by
  have hs : count973 q = (countLit q [-61, -62, -65, -67, -68, -70, -73]) + (countLit q [-74, -75, -78, -79, -82, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -67, -68, -70, -73]) (l₂ := [-74, -75, -78, -79, -82, -84, -86, -88])
  have hm := merge_two (literal (valuationOf q) (947)) (literal (valuationOf q) (965)) (literal (valuationOf q) (979)) (countLit q [-61, -62, -65, -67, -68, -70, -73]) (countLit q [-74, -75, -78, -79, -82, -84, -86, -88]) (count973 q) 6 1 (meaning947 q) (meaning965 q) (meaning979 q) hs
  change valuationOf q 947 = false ∨ valuationOf q 965 = false ∨ valuationOf q 979 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1120 (q : Snake 81) (h : Conditions q) : valuation q 947 = false ∨ valuation q 965 = false ∨ valuation q 979 = true := counterClause1120 (baseVal q)

theorem block34 (q : Snake 81) (h : Conditions q) : B112E115.Block34 (valuation q) :=
  ⟨clause1089 q h, clause1090 q h, clause1091 q h, clause1092 q h, clause1093 q h, clause1094 q h, clause1095 q h, clause1096 q h, clause1097 q h, clause1098 q h, clause1099 q h, clause1100 q h, clause1101 q h, clause1102 q h, clause1103 q h, clause1104 q h, clause1105 q h, clause1106 q h, clause1107 q h, clause1108 q h, clause1109 q h, clause1110 q h, clause1111 q h, clause1112 q h, clause1113 q h, clause1114 q h, clause1115 q h, clause1116 q h, clause1117 q h, clause1118 q h, clause1119 q h, clause1120 q h⟩

end
end Snake9.Regrowth.E112115
