import E112203Semantics
import B112E203Inputs
namespace Snake9.Regrowth.E112203
noncomputable section
local instance blockDec32 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1025 (q : Nat → Bool) : valuationOf q 965 = false ∨ valuationOf q 973 = true := by
  have hs : count973 q = (countLit q [-56, -59, -61, -64, -65, -67, -68]) + (countLit q [-70, -73, -76, -77, -78, -80, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -61, -64, -65, -67, -68]) (l₂ := [-70, -73, -76, -77, -78, -80, -84, -85])
  have hm := merge_right (literal (valuationOf q) (965)) (literal (valuationOf q) (973)) (countLit q [-56, -59, -61, -64, -65, -67, -68]) (countLit q [-70, -73, -76, -77, -78, -80, -84, -85]) (count973 q) 1 (meaning965 q) (meaning973 q) hs
  change valuationOf q 965 = false ∨ valuationOf q 973 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1025 (q : Snake 81) (h : Conditions q) : valuation q 965 = false ∨ valuation q 973 = true := counterClause1025 (baseVal q)

theorem counterClause1026 (q : Nat → Bool) : valuationOf q 966 = false ∨ valuationOf q 974 = true := by
  have hs : count973 q = (countLit q [-56, -59, -61, -64, -65, -67, -68]) + (countLit q [-70, -73, -76, -77, -78, -80, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -61, -64, -65, -67, -68]) (l₂ := [-70, -73, -76, -77, -78, -80, -84, -85])
  have hm := merge_right (literal (valuationOf q) (966)) (literal (valuationOf q) (974)) (countLit q [-56, -59, -61, -64, -65, -67, -68]) (countLit q [-70, -73, -76, -77, -78, -80, -84, -85]) (count973 q) 2 (meaning966 q) (meaning974 q) hs
  change valuationOf q 966 = false ∨ valuationOf q 974 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1026 (q : Snake 81) (h : Conditions q) : valuation q 966 = false ∨ valuation q 974 = true := counterClause1026 (baseVal q)

theorem counterClause1027 (q : Nat → Bool) : valuationOf q 968 = false ∨ valuationOf q 976 = true := by
  have hs : count973 q = (countLit q [-56, -59, -61, -64, -65, -67, -68]) + (countLit q [-70, -73, -76, -77, -78, -80, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -61, -64, -65, -67, -68]) (l₂ := [-70, -73, -76, -77, -78, -80, -84, -85])
  have hm := merge_right (literal (valuationOf q) (968)) (literal (valuationOf q) (976)) (countLit q [-56, -59, -61, -64, -65, -67, -68]) (countLit q [-70, -73, -76, -77, -78, -80, -84, -85]) (count973 q) 4 (meaning968 q) (meaning976 q) hs
  change valuationOf q 968 = false ∨ valuationOf q 976 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1027 (q : Snake 81) (h : Conditions q) : valuation q 968 = false ∨ valuation q 976 = true := counterClause1027 (baseVal q)

theorem counterClause1028 (q : Nat → Bool) : valuationOf q 942 = false ∨ valuationOf q 965 = false ∨ valuationOf q 974 = true := by
  have hs : count973 q = (countLit q [-56, -59, -61, -64, -65, -67, -68]) + (countLit q [-70, -73, -76, -77, -78, -80, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -61, -64, -65, -67, -68]) (l₂ := [-70, -73, -76, -77, -78, -80, -84, -85])
  have hm := merge_two (literal (valuationOf q) (942)) (literal (valuationOf q) (965)) (literal (valuationOf q) (974)) (countLit q [-56, -59, -61, -64, -65, -67, -68]) (countLit q [-70, -73, -76, -77, -78, -80, -84, -85]) (count973 q) 1 1 (meaning942 q) (meaning965 q) (meaning974 q) hs
  change valuationOf q 942 = false ∨ valuationOf q 965 = false ∨ valuationOf q 974 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1028 (q : Snake 81) (h : Conditions q) : valuation q 942 = false ∨ valuation q 965 = false ∨ valuation q 974 = true := counterClause1028 (baseVal q)

theorem counterClause1029 (q : Nat → Bool) : valuationOf q 942 = false ∨ valuationOf q 966 = false ∨ valuationOf q 975 = true := by
  have hs : count973 q = (countLit q [-56, -59, -61, -64, -65, -67, -68]) + (countLit q [-70, -73, -76, -77, -78, -80, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -61, -64, -65, -67, -68]) (l₂ := [-70, -73, -76, -77, -78, -80, -84, -85])
  have hm := merge_two (literal (valuationOf q) (942)) (literal (valuationOf q) (966)) (literal (valuationOf q) (975)) (countLit q [-56, -59, -61, -64, -65, -67, -68]) (countLit q [-70, -73, -76, -77, -78, -80, -84, -85]) (count973 q) 1 2 (meaning942 q) (meaning966 q) (meaning975 q) hs
  change valuationOf q 942 = false ∨ valuationOf q 966 = false ∨ valuationOf q 975 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1029 (q : Snake 81) (h : Conditions q) : valuation q 942 = false ∨ valuation q 966 = false ∨ valuation q 975 = true := counterClause1029 (baseVal q)

theorem counterClause1030 (q : Nat → Bool) : valuationOf q 942 = false ∨ valuationOf q 967 = false ∨ valuationOf q 976 = true := by
  have hs : count973 q = (countLit q [-56, -59, -61, -64, -65, -67, -68]) + (countLit q [-70, -73, -76, -77, -78, -80, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -61, -64, -65, -67, -68]) (l₂ := [-70, -73, -76, -77, -78, -80, -84, -85])
  have hm := merge_two (literal (valuationOf q) (942)) (literal (valuationOf q) (967)) (literal (valuationOf q) (976)) (countLit q [-56, -59, -61, -64, -65, -67, -68]) (countLit q [-70, -73, -76, -77, -78, -80, -84, -85]) (count973 q) 1 3 (meaning942 q) (meaning967 q) (meaning976 q) hs
  change valuationOf q 942 = false ∨ valuationOf q 967 = false ∨ valuationOf q 976 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1030 (q : Snake 81) (h : Conditions q) : valuation q 942 = false ∨ valuation q 967 = false ∨ valuation q 976 = true := counterClause1030 (baseVal q)

theorem counterClause1031 (q : Nat → Bool) : valuationOf q 942 = false ∨ valuationOf q 968 = false ∨ valuationOf q 977 = true := by
  have hs : count973 q = (countLit q [-56, -59, -61, -64, -65, -67, -68]) + (countLit q [-70, -73, -76, -77, -78, -80, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -61, -64, -65, -67, -68]) (l₂ := [-70, -73, -76, -77, -78, -80, -84, -85])
  have hm := merge_two (literal (valuationOf q) (942)) (literal (valuationOf q) (968)) (literal (valuationOf q) (977)) (countLit q [-56, -59, -61, -64, -65, -67, -68]) (countLit q [-70, -73, -76, -77, -78, -80, -84, -85]) (count973 q) 1 4 (meaning942 q) (meaning968 q) (meaning977 q) hs
  change valuationOf q 942 = false ∨ valuationOf q 968 = false ∨ valuationOf q 977 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1031 (q : Snake 81) (h : Conditions q) : valuation q 942 = false ∨ valuation q 968 = false ∨ valuation q 977 = true := counterClause1031 (baseVal q)

theorem counterClause1032 (q : Nat → Bool) : valuationOf q 943 = false ∨ valuationOf q 974 = true := by
  have hs : count973 q = (countLit q [-56, -59, -61, -64, -65, -67, -68]) + (countLit q [-70, -73, -76, -77, -78, -80, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -61, -64, -65, -67, -68]) (l₂ := [-70, -73, -76, -77, -78, -80, -84, -85])
  have hm := merge_left (literal (valuationOf q) (943)) (literal (valuationOf q) (974)) (countLit q [-56, -59, -61, -64, -65, -67, -68]) (countLit q [-70, -73, -76, -77, -78, -80, -84, -85]) (count973 q) 2 (meaning943 q) (meaning974 q) hs
  change valuationOf q 943 = false ∨ valuationOf q 974 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1032 (q : Snake 81) (h : Conditions q) : valuation q 943 = false ∨ valuation q 974 = true := counterClause1032 (baseVal q)

theorem counterClause1033 (q : Nat → Bool) : valuationOf q 943 = false ∨ valuationOf q 965 = false ∨ valuationOf q 975 = true := by
  have hs : count973 q = (countLit q [-56, -59, -61, -64, -65, -67, -68]) + (countLit q [-70, -73, -76, -77, -78, -80, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -61, -64, -65, -67, -68]) (l₂ := [-70, -73, -76, -77, -78, -80, -84, -85])
  have hm := merge_two (literal (valuationOf q) (943)) (literal (valuationOf q) (965)) (literal (valuationOf q) (975)) (countLit q [-56, -59, -61, -64, -65, -67, -68]) (countLit q [-70, -73, -76, -77, -78, -80, -84, -85]) (count973 q) 2 1 (meaning943 q) (meaning965 q) (meaning975 q) hs
  change valuationOf q 943 = false ∨ valuationOf q 965 = false ∨ valuationOf q 975 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1033 (q : Snake 81) (h : Conditions q) : valuation q 943 = false ∨ valuation q 965 = false ∨ valuation q 975 = true := counterClause1033 (baseVal q)

theorem counterClause1034 (q : Nat → Bool) : valuationOf q 943 = false ∨ valuationOf q 966 = false ∨ valuationOf q 976 = true := by
  have hs : count973 q = (countLit q [-56, -59, -61, -64, -65, -67, -68]) + (countLit q [-70, -73, -76, -77, -78, -80, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -61, -64, -65, -67, -68]) (l₂ := [-70, -73, -76, -77, -78, -80, -84, -85])
  have hm := merge_two (literal (valuationOf q) (943)) (literal (valuationOf q) (966)) (literal (valuationOf q) (976)) (countLit q [-56, -59, -61, -64, -65, -67, -68]) (countLit q [-70, -73, -76, -77, -78, -80, -84, -85]) (count973 q) 2 2 (meaning943 q) (meaning966 q) (meaning976 q) hs
  change valuationOf q 943 = false ∨ valuationOf q 966 = false ∨ valuationOf q 976 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1034 (q : Snake 81) (h : Conditions q) : valuation q 943 = false ∨ valuation q 966 = false ∨ valuation q 976 = true := counterClause1034 (baseVal q)

theorem counterClause1035 (q : Nat → Bool) : valuationOf q 943 = false ∨ valuationOf q 967 = false ∨ valuationOf q 977 = true := by
  have hs : count973 q = (countLit q [-56, -59, -61, -64, -65, -67, -68]) + (countLit q [-70, -73, -76, -77, -78, -80, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -61, -64, -65, -67, -68]) (l₂ := [-70, -73, -76, -77, -78, -80, -84, -85])
  have hm := merge_two (literal (valuationOf q) (943)) (literal (valuationOf q) (967)) (literal (valuationOf q) (977)) (countLit q [-56, -59, -61, -64, -65, -67, -68]) (countLit q [-70, -73, -76, -77, -78, -80, -84, -85]) (count973 q) 2 3 (meaning943 q) (meaning967 q) (meaning977 q) hs
  change valuationOf q 943 = false ∨ valuationOf q 967 = false ∨ valuationOf q 977 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1035 (q : Snake 81) (h : Conditions q) : valuation q 943 = false ∨ valuation q 967 = false ∨ valuation q 977 = true := counterClause1035 (baseVal q)

theorem counterClause1036 (q : Nat → Bool) : valuationOf q 943 = false ∨ valuationOf q 968 = false ∨ valuationOf q 978 = true := by
  have hs : count973 q = (countLit q [-56, -59, -61, -64, -65, -67, -68]) + (countLit q [-70, -73, -76, -77, -78, -80, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -61, -64, -65, -67, -68]) (l₂ := [-70, -73, -76, -77, -78, -80, -84, -85])
  have hm := merge_two (literal (valuationOf q) (943)) (literal (valuationOf q) (968)) (literal (valuationOf q) (978)) (countLit q [-56, -59, -61, -64, -65, -67, -68]) (countLit q [-70, -73, -76, -77, -78, -80, -84, -85]) (count973 q) 2 4 (meaning943 q) (meaning968 q) (meaning978 q) hs
  change valuationOf q 943 = false ∨ valuationOf q 968 = false ∨ valuationOf q 978 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1036 (q : Snake 81) (h : Conditions q) : valuation q 943 = false ∨ valuation q 968 = false ∨ valuation q 978 = true := counterClause1036 (baseVal q)

theorem counterClause1037 (q : Nat → Bool) : valuationOf q 943 = false ∨ valuationOf q 969 = false ∨ valuationOf q 979 = true := by
  have hs : count973 q = (countLit q [-56, -59, -61, -64, -65, -67, -68]) + (countLit q [-70, -73, -76, -77, -78, -80, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -61, -64, -65, -67, -68]) (l₂ := [-70, -73, -76, -77, -78, -80, -84, -85])
  have hm := merge_two (literal (valuationOf q) (943)) (literal (valuationOf q) (969)) (literal (valuationOf q) (979)) (countLit q [-56, -59, -61, -64, -65, -67, -68]) (countLit q [-70, -73, -76, -77, -78, -80, -84, -85]) (count973 q) 2 5 (meaning943 q) (meaning969 q) (meaning979 q) hs
  change valuationOf q 943 = false ∨ valuationOf q 969 = false ∨ valuationOf q 979 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1037 (q : Snake 81) (h : Conditions q) : valuation q 943 = false ∨ valuation q 969 = false ∨ valuation q 979 = true := counterClause1037 (baseVal q)

theorem counterClause1038 (q : Nat → Bool) : valuationOf q 944 = false ∨ valuationOf q 965 = false ∨ valuationOf q 976 = true := by
  have hs : count973 q = (countLit q [-56, -59, -61, -64, -65, -67, -68]) + (countLit q [-70, -73, -76, -77, -78, -80, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -61, -64, -65, -67, -68]) (l₂ := [-70, -73, -76, -77, -78, -80, -84, -85])
  have hm := merge_two (literal (valuationOf q) (944)) (literal (valuationOf q) (965)) (literal (valuationOf q) (976)) (countLit q [-56, -59, -61, -64, -65, -67, -68]) (countLit q [-70, -73, -76, -77, -78, -80, -84, -85]) (count973 q) 3 1 (meaning944 q) (meaning965 q) (meaning976 q) hs
  change valuationOf q 944 = false ∨ valuationOf q 965 = false ∨ valuationOf q 976 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1038 (q : Snake 81) (h : Conditions q) : valuation q 944 = false ∨ valuation q 965 = false ∨ valuation q 976 = true := counterClause1038 (baseVal q)

theorem counterClause1039 (q : Nat → Bool) : valuationOf q 944 = false ∨ valuationOf q 966 = false ∨ valuationOf q 977 = true := by
  have hs : count973 q = (countLit q [-56, -59, -61, -64, -65, -67, -68]) + (countLit q [-70, -73, -76, -77, -78, -80, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -61, -64, -65, -67, -68]) (l₂ := [-70, -73, -76, -77, -78, -80, -84, -85])
  have hm := merge_two (literal (valuationOf q) (944)) (literal (valuationOf q) (966)) (literal (valuationOf q) (977)) (countLit q [-56, -59, -61, -64, -65, -67, -68]) (countLit q [-70, -73, -76, -77, -78, -80, -84, -85]) (count973 q) 3 2 (meaning944 q) (meaning966 q) (meaning977 q) hs
  change valuationOf q 944 = false ∨ valuationOf q 966 = false ∨ valuationOf q 977 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1039 (q : Snake 81) (h : Conditions q) : valuation q 944 = false ∨ valuation q 966 = false ∨ valuation q 977 = true := counterClause1039 (baseVal q)

theorem counterClause1040 (q : Nat → Bool) : valuationOf q 944 = false ∨ valuationOf q 967 = false ∨ valuationOf q 978 = true := by
  have hs : count973 q = (countLit q [-56, -59, -61, -64, -65, -67, -68]) + (countLit q [-70, -73, -76, -77, -78, -80, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -61, -64, -65, -67, -68]) (l₂ := [-70, -73, -76, -77, -78, -80, -84, -85])
  have hm := merge_two (literal (valuationOf q) (944)) (literal (valuationOf q) (967)) (literal (valuationOf q) (978)) (countLit q [-56, -59, -61, -64, -65, -67, -68]) (countLit q [-70, -73, -76, -77, -78, -80, -84, -85]) (count973 q) 3 3 (meaning944 q) (meaning967 q) (meaning978 q) hs
  change valuationOf q 944 = false ∨ valuationOf q 967 = false ∨ valuationOf q 978 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1040 (q : Snake 81) (h : Conditions q) : valuation q 944 = false ∨ valuation q 967 = false ∨ valuation q 978 = true := counterClause1040 (baseVal q)

theorem counterClause1041 (q : Nat → Bool) : valuationOf q 944 = false ∨ valuationOf q 968 = false ∨ valuationOf q 979 = true := by
  have hs : count973 q = (countLit q [-56, -59, -61, -64, -65, -67, -68]) + (countLit q [-70, -73, -76, -77, -78, -80, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -61, -64, -65, -67, -68]) (l₂ := [-70, -73, -76, -77, -78, -80, -84, -85])
  have hm := merge_two (literal (valuationOf q) (944)) (literal (valuationOf q) (968)) (literal (valuationOf q) (979)) (countLit q [-56, -59, -61, -64, -65, -67, -68]) (countLit q [-70, -73, -76, -77, -78, -80, -84, -85]) (count973 q) 3 4 (meaning944 q) (meaning968 q) (meaning979 q) hs
  change valuationOf q 944 = false ∨ valuationOf q 968 = false ∨ valuationOf q 979 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1041 (q : Snake 81) (h : Conditions q) : valuation q 944 = false ∨ valuation q 968 = false ∨ valuation q 979 = true := counterClause1041 (baseVal q)

theorem counterClause1042 (q : Nat → Bool) : valuationOf q 944 = false ∨ valuationOf q 969 = false ∨ valuationOf q 980 = true := by
  have hs : count973 q = (countLit q [-56, -59, -61, -64, -65, -67, -68]) + (countLit q [-70, -73, -76, -77, -78, -80, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -61, -64, -65, -67, -68]) (l₂ := [-70, -73, -76, -77, -78, -80, -84, -85])
  have hm := merge_two (literal (valuationOf q) (944)) (literal (valuationOf q) (969)) (literal (valuationOf q) (980)) (countLit q [-56, -59, -61, -64, -65, -67, -68]) (countLit q [-70, -73, -76, -77, -78, -80, -84, -85]) (count973 q) 3 5 (meaning944 q) (meaning969 q) (meaning980 q) hs
  change valuationOf q 944 = false ∨ valuationOf q 969 = false ∨ valuationOf q 980 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1042 (q : Snake 81) (h : Conditions q) : valuation q 944 = false ∨ valuation q 969 = false ∨ valuation q 980 = true := counterClause1042 (baseVal q)

theorem counterClause1043 (q : Nat → Bool) : valuationOf q 945 = false ∨ valuationOf q 965 = false ∨ valuationOf q 977 = true := by
  have hs : count973 q = (countLit q [-56, -59, -61, -64, -65, -67, -68]) + (countLit q [-70, -73, -76, -77, -78, -80, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -61, -64, -65, -67, -68]) (l₂ := [-70, -73, -76, -77, -78, -80, -84, -85])
  have hm := merge_two (literal (valuationOf q) (945)) (literal (valuationOf q) (965)) (literal (valuationOf q) (977)) (countLit q [-56, -59, -61, -64, -65, -67, -68]) (countLit q [-70, -73, -76, -77, -78, -80, -84, -85]) (count973 q) 4 1 (meaning945 q) (meaning965 q) (meaning977 q) hs
  change valuationOf q 945 = false ∨ valuationOf q 965 = false ∨ valuationOf q 977 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1043 (q : Snake 81) (h : Conditions q) : valuation q 945 = false ∨ valuation q 965 = false ∨ valuation q 977 = true := counterClause1043 (baseVal q)

theorem counterClause1044 (q : Nat → Bool) : valuationOf q 945 = false ∨ valuationOf q 966 = false ∨ valuationOf q 978 = true := by
  have hs : count973 q = (countLit q [-56, -59, -61, -64, -65, -67, -68]) + (countLit q [-70, -73, -76, -77, -78, -80, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -61, -64, -65, -67, -68]) (l₂ := [-70, -73, -76, -77, -78, -80, -84, -85])
  have hm := merge_two (literal (valuationOf q) (945)) (literal (valuationOf q) (966)) (literal (valuationOf q) (978)) (countLit q [-56, -59, -61, -64, -65, -67, -68]) (countLit q [-70, -73, -76, -77, -78, -80, -84, -85]) (count973 q) 4 2 (meaning945 q) (meaning966 q) (meaning978 q) hs
  change valuationOf q 945 = false ∨ valuationOf q 966 = false ∨ valuationOf q 978 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1044 (q : Snake 81) (h : Conditions q) : valuation q 945 = false ∨ valuation q 966 = false ∨ valuation q 978 = true := counterClause1044 (baseVal q)

theorem counterClause1045 (q : Nat → Bool) : valuationOf q 945 = false ∨ valuationOf q 967 = false ∨ valuationOf q 979 = true := by
  have hs : count973 q = (countLit q [-56, -59, -61, -64, -65, -67, -68]) + (countLit q [-70, -73, -76, -77, -78, -80, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -61, -64, -65, -67, -68]) (l₂ := [-70, -73, -76, -77, -78, -80, -84, -85])
  have hm := merge_two (literal (valuationOf q) (945)) (literal (valuationOf q) (967)) (literal (valuationOf q) (979)) (countLit q [-56, -59, -61, -64, -65, -67, -68]) (countLit q [-70, -73, -76, -77, -78, -80, -84, -85]) (count973 q) 4 3 (meaning945 q) (meaning967 q) (meaning979 q) hs
  change valuationOf q 945 = false ∨ valuationOf q 967 = false ∨ valuationOf q 979 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1045 (q : Snake 81) (h : Conditions q) : valuation q 945 = false ∨ valuation q 967 = false ∨ valuation q 979 = true := counterClause1045 (baseVal q)

theorem counterClause1046 (q : Nat → Bool) : valuationOf q 945 = false ∨ valuationOf q 968 = false ∨ valuationOf q 980 = true := by
  have hs : count973 q = (countLit q [-56, -59, -61, -64, -65, -67, -68]) + (countLit q [-70, -73, -76, -77, -78, -80, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -61, -64, -65, -67, -68]) (l₂ := [-70, -73, -76, -77, -78, -80, -84, -85])
  have hm := merge_two (literal (valuationOf q) (945)) (literal (valuationOf q) (968)) (literal (valuationOf q) (980)) (countLit q [-56, -59, -61, -64, -65, -67, -68]) (countLit q [-70, -73, -76, -77, -78, -80, -84, -85]) (count973 q) 4 4 (meaning945 q) (meaning968 q) (meaning980 q) hs
  change valuationOf q 945 = false ∨ valuationOf q 968 = false ∨ valuationOf q 980 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1046 (q : Snake 81) (h : Conditions q) : valuation q 945 = false ∨ valuation q 968 = false ∨ valuation q 980 = true := counterClause1046 (baseVal q)

theorem counterClause1047 (q : Nat → Bool) : valuationOf q 946 = false ∨ valuationOf q 965 = false ∨ valuationOf q 978 = true := by
  have hs : count973 q = (countLit q [-56, -59, -61, -64, -65, -67, -68]) + (countLit q [-70, -73, -76, -77, -78, -80, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -61, -64, -65, -67, -68]) (l₂ := [-70, -73, -76, -77, -78, -80, -84, -85])
  have hm := merge_two (literal (valuationOf q) (946)) (literal (valuationOf q) (965)) (literal (valuationOf q) (978)) (countLit q [-56, -59, -61, -64, -65, -67, -68]) (countLit q [-70, -73, -76, -77, -78, -80, -84, -85]) (count973 q) 5 1 (meaning946 q) (meaning965 q) (meaning978 q) hs
  change valuationOf q 946 = false ∨ valuationOf q 965 = false ∨ valuationOf q 978 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1047 (q : Snake 81) (h : Conditions q) : valuation q 946 = false ∨ valuation q 965 = false ∨ valuation q 978 = true := counterClause1047 (baseVal q)

theorem counterClause1048 (q : Nat → Bool) : valuationOf q 946 = false ∨ valuationOf q 966 = false ∨ valuationOf q 979 = true := by
  have hs : count973 q = (countLit q [-56, -59, -61, -64, -65, -67, -68]) + (countLit q [-70, -73, -76, -77, -78, -80, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -61, -64, -65, -67, -68]) (l₂ := [-70, -73, -76, -77, -78, -80, -84, -85])
  have hm := merge_two (literal (valuationOf q) (946)) (literal (valuationOf q) (966)) (literal (valuationOf q) (979)) (countLit q [-56, -59, -61, -64, -65, -67, -68]) (countLit q [-70, -73, -76, -77, -78, -80, -84, -85]) (count973 q) 5 2 (meaning946 q) (meaning966 q) (meaning979 q) hs
  change valuationOf q 946 = false ∨ valuationOf q 966 = false ∨ valuationOf q 979 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1048 (q : Snake 81) (h : Conditions q) : valuation q 946 = false ∨ valuation q 966 = false ∨ valuation q 979 = true := counterClause1048 (baseVal q)

theorem counterClause1049 (q : Nat → Bool) : valuationOf q 946 = false ∨ valuationOf q 967 = false ∨ valuationOf q 980 = true := by
  have hs : count973 q = (countLit q [-56, -59, -61, -64, -65, -67, -68]) + (countLit q [-70, -73, -76, -77, -78, -80, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -61, -64, -65, -67, -68]) (l₂ := [-70, -73, -76, -77, -78, -80, -84, -85])
  have hm := merge_two (literal (valuationOf q) (946)) (literal (valuationOf q) (967)) (literal (valuationOf q) (980)) (countLit q [-56, -59, -61, -64, -65, -67, -68]) (countLit q [-70, -73, -76, -77, -78, -80, -84, -85]) (count973 q) 5 3 (meaning946 q) (meaning967 q) (meaning980 q) hs
  change valuationOf q 946 = false ∨ valuationOf q 967 = false ∨ valuationOf q 980 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1049 (q : Snake 81) (h : Conditions q) : valuation q 946 = false ∨ valuation q 967 = false ∨ valuation q 980 = true := counterClause1049 (baseVal q)

theorem counterClause1050 (q : Nat → Bool) : valuationOf q 946 = false ∨ valuationOf q 968 = false ∨ valuationOf q 981 = true := by
  have hs : count973 q = (countLit q [-56, -59, -61, -64, -65, -67, -68]) + (countLit q [-70, -73, -76, -77, -78, -80, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -61, -64, -65, -67, -68]) (l₂ := [-70, -73, -76, -77, -78, -80, -84, -85])
  have hm := merge_two (literal (valuationOf q) (946)) (literal (valuationOf q) (968)) (literal (valuationOf q) (981)) (countLit q [-56, -59, -61, -64, -65, -67, -68]) (countLit q [-70, -73, -76, -77, -78, -80, -84, -85]) (count973 q) 5 4 (meaning946 q) (meaning968 q) (meaning981 q) hs
  change valuationOf q 946 = false ∨ valuationOf q 968 = false ∨ valuationOf q 981 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1050 (q : Snake 81) (h : Conditions q) : valuation q 946 = false ∨ valuation q 968 = false ∨ valuation q 981 = true := counterClause1050 (baseVal q)

theorem counterClause1051 (q : Nat → Bool) : valuationOf q 947 = false ∨ valuationOf q 965 = false ∨ valuationOf q 979 = true := by
  have hs : count973 q = (countLit q [-56, -59, -61, -64, -65, -67, -68]) + (countLit q [-70, -73, -76, -77, -78, -80, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -61, -64, -65, -67, -68]) (l₂ := [-70, -73, -76, -77, -78, -80, -84, -85])
  have hm := merge_two (literal (valuationOf q) (947)) (literal (valuationOf q) (965)) (literal (valuationOf q) (979)) (countLit q [-56, -59, -61, -64, -65, -67, -68]) (countLit q [-70, -73, -76, -77, -78, -80, -84, -85]) (count973 q) 6 1 (meaning947 q) (meaning965 q) (meaning979 q) hs
  change valuationOf q 947 = false ∨ valuationOf q 965 = false ∨ valuationOf q 979 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1051 (q : Snake 81) (h : Conditions q) : valuation q 947 = false ∨ valuation q 965 = false ∨ valuation q 979 = true := counterClause1051 (baseVal q)

theorem counterClause1052 (q : Nat → Bool) : valuationOf q 947 = false ∨ valuationOf q 966 = false ∨ valuationOf q 980 = true := by
  have hs : count973 q = (countLit q [-56, -59, -61, -64, -65, -67, -68]) + (countLit q [-70, -73, -76, -77, -78, -80, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -61, -64, -65, -67, -68]) (l₂ := [-70, -73, -76, -77, -78, -80, -84, -85])
  have hm := merge_two (literal (valuationOf q) (947)) (literal (valuationOf q) (966)) (literal (valuationOf q) (980)) (countLit q [-56, -59, -61, -64, -65, -67, -68]) (countLit q [-70, -73, -76, -77, -78, -80, -84, -85]) (count973 q) 6 2 (meaning947 q) (meaning966 q) (meaning980 q) hs
  change valuationOf q 947 = false ∨ valuationOf q 966 = false ∨ valuationOf q 980 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1052 (q : Snake 81) (h : Conditions q) : valuation q 947 = false ∨ valuation q 966 = false ∨ valuation q 980 = true := counterClause1052 (baseVal q)

theorem counterClause1053 (q : Nat → Bool) : valuationOf q 947 = false ∨ valuationOf q 967 = false ∨ valuationOf q 981 = true := by
  have hs : count973 q = (countLit q [-56, -59, -61, -64, -65, -67, -68]) + (countLit q [-70, -73, -76, -77, -78, -80, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -61, -64, -65, -67, -68]) (l₂ := [-70, -73, -76, -77, -78, -80, -84, -85])
  have hm := merge_two (literal (valuationOf q) (947)) (literal (valuationOf q) (967)) (literal (valuationOf q) (981)) (countLit q [-56, -59, -61, -64, -65, -67, -68]) (countLit q [-70, -73, -76, -77, -78, -80, -84, -85]) (count973 q) 6 3 (meaning947 q) (meaning967 q) (meaning981 q) hs
  change valuationOf q 947 = false ∨ valuationOf q 967 = false ∨ valuationOf q 981 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1053 (q : Snake 81) (h : Conditions q) : valuation q 947 = false ∨ valuation q 967 = false ∨ valuation q 981 = true := counterClause1053 (baseVal q)

theorem counterClause1054 (q : Nat → Bool) : valuationOf q 948 = false ∨ valuationOf q 966 = false ∨ valuationOf q 981 = true := by
  have hs : count973 q = (countLit q [-56, -59, -61, -64, -65, -67, -68]) + (countLit q [-70, -73, -76, -77, -78, -80, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -61, -64, -65, -67, -68]) (l₂ := [-70, -73, -76, -77, -78, -80, -84, -85])
  have hm := merge_two (literal (valuationOf q) (948)) (literal (valuationOf q) (966)) (literal (valuationOf q) (981)) (countLit q [-56, -59, -61, -64, -65, -67, -68]) (countLit q [-70, -73, -76, -77, -78, -80, -84, -85]) (count973 q) 7 2 (meaning948 q) (meaning966 q) (meaning981 q) hs
  change valuationOf q 948 = false ∨ valuationOf q 966 = false ∨ valuationOf q 981 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1054 (q : Snake 81) (h : Conditions q) : valuation q 948 = false ∨ valuation q 966 = false ∨ valuation q 981 = true := counterClause1054 (baseVal q)

theorem counterClause1055 (q : Nat → Bool) : valuationOf q 91 = true ∨ valuationOf q 988 = true := by
  have hs : count988 q = (countLit q [-88]) + (countLit q [-91]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-91])
  have hm := merge_right (literal (valuationOf q) (-91)) (literal (valuationOf q) (988)) (countLit q [-88]) (countLit q [-91]) (count988 q) 1 (meaningNeg91 q) (meaning988 q) hs
  change (! (valuationOf q 91)) = false ∨ valuationOf q 988 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1055 (q : Snake 81) (h : Conditions q) : valuation q 91 = true ∨ valuation q 988 = true := counterClause1055 (baseVal q)

theorem counterClause1056 (q : Nat → Bool) : valuationOf q 88 = true ∨ valuationOf q 988 = true := by
  have hs : count988 q = (countLit q [-88]) + (countLit q [-91]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-91])
  have hm := merge_left (literal (valuationOf q) (-88)) (literal (valuationOf q) (988)) (countLit q [-88]) (countLit q [-91]) (count988 q) 1 (meaningNeg88 q) (meaning988 q) hs
  change (! (valuationOf q 88)) = false ∨ valuationOf q 988 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1056 (q : Snake 81) (h : Conditions q) : valuation q 88 = true ∨ valuation q 988 = true := counterClause1056 (baseVal q)

theorem block32 (q : Snake 81) (h : Conditions q) : B112E203.Block32 (valuation q) :=
  ⟨clause1025 q h, clause1026 q h, clause1027 q h, clause1028 q h, clause1029 q h, clause1030 q h, clause1031 q h, clause1032 q h, clause1033 q h, clause1034 q h, clause1035 q h, clause1036 q h, clause1037 q h, clause1038 q h, clause1039 q h, clause1040 q h, clause1041 q h, clause1042 q h, clause1043 q h, clause1044 q h, clause1045 q h, clause1046 q h, clause1047 q h, clause1048 q h, clause1049 q h, clause1050 q h, clause1051 q h, clause1052 q h, clause1053 q h, clause1054 q h, clause1055 q h, clause1056 q h⟩

end
end Snake9.Regrowth.E112203
