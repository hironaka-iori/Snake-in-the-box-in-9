import E112153Semantics
import B112E153Inputs
namespace Snake9.Regrowth.E112153
noncomputable section
local instance blockDec33 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1057 (q : Nat → Bool) : valuationOf q 891 = false ∨ valuationOf q 953 = false ∨ valuationOf q 974 = true := by
  have hs : count966 q = (countLit q [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) + (countLit q [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) (l₂ := [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61])
  have hm := merge_two (literal (valuationOf q) (891)) (literal (valuationOf q) (953)) (literal (valuationOf q) (974)) (countLit q [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) (countLit q [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) (count966 q) 5 4 (meaning891 q) (meaning953 q) (meaning974 q) hs
  change valuationOf q 891 = false ∨ valuationOf q 953 = false ∨ valuationOf q 974 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1057 (q : Snake 81) (h : Conditions q) : valuation q 891 = false ∨ valuation q 953 = false ∨ valuation q 974 = true := counterClause1057 (baseVal q)

theorem counterClause1058 (q : Nat → Bool) : valuationOf q 891 = false ∨ valuationOf q 954 = false ∨ valuationOf q 975 = true := by
  have hs : count966 q = (countLit q [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) + (countLit q [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) (l₂ := [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61])
  have hm := merge_two (literal (valuationOf q) (891)) (literal (valuationOf q) (954)) (literal (valuationOf q) (975)) (countLit q [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) (countLit q [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) (count966 q) 5 5 (meaning891 q) (meaning954 q) (meaning975 q) hs
  change valuationOf q 891 = false ∨ valuationOf q 954 = false ∨ valuationOf q 975 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1058 (q : Snake 81) (h : Conditions q) : valuation q 891 = false ∨ valuation q 954 = false ∨ valuation q 975 = true := counterClause1058 (baseVal q)

theorem counterClause1059 (q : Nat → Bool) : valuationOf q 891 = false ∨ valuationOf q 955 = false ∨ valuationOf q 976 = true := by
  have hs : count966 q = (countLit q [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) + (countLit q [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) (l₂ := [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61])
  have hm := merge_two (literal (valuationOf q) (891)) (literal (valuationOf q) (955)) (literal (valuationOf q) (976)) (countLit q [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) (countLit q [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) (count966 q) 5 6 (meaning891 q) (meaning955 q) (meaning976 q) hs
  change valuationOf q 891 = false ∨ valuationOf q 955 = false ∨ valuationOf q 976 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1059 (q : Snake 81) (h : Conditions q) : valuation q 891 = false ∨ valuation q 955 = false ∨ valuation q 976 = true := counterClause1059 (baseVal q)

theorem counterClause1060 (q : Nat → Bool) : valuationOf q 891 = false ∨ valuationOf q 956 = false ∨ valuationOf q 977 = true := by
  have hs : count966 q = (countLit q [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) + (countLit q [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) (l₂ := [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61])
  have hm := merge_two (literal (valuationOf q) (891)) (literal (valuationOf q) (956)) (literal (valuationOf q) (977)) (countLit q [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) (countLit q [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) (count966 q) 5 7 (meaning891 q) (meaning956 q) (meaning977 q) hs
  change valuationOf q 891 = false ∨ valuationOf q 956 = false ∨ valuationOf q 977 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1060 (q : Snake 81) (h : Conditions q) : valuation q 891 = false ∨ valuation q 956 = false ∨ valuation q 977 = true := counterClause1060 (baseVal q)

theorem counterClause1061 (q : Nat → Bool) : valuationOf q 891 = false ∨ valuationOf q 957 = false ∨ valuationOf q 978 = true := by
  have hs : count966 q = (countLit q [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) + (countLit q [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) (l₂ := [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61])
  have hm := merge_two (literal (valuationOf q) (891)) (literal (valuationOf q) (957)) (literal (valuationOf q) (978)) (countLit q [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) (countLit q [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) (count966 q) 5 8 (meaning891 q) (meaning957 q) (meaning978 q) hs
  change valuationOf q 891 = false ∨ valuationOf q 957 = false ∨ valuationOf q 978 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1061 (q : Snake 81) (h : Conditions q) : valuation q 891 = false ∨ valuation q 957 = false ∨ valuation q 978 = true := counterClause1061 (baseVal q)

theorem counterClause1062 (q : Nat → Bool) : valuationOf q 892 = false ∨ valuationOf q 952 = false ∨ valuationOf q 974 = true := by
  have hs : count966 q = (countLit q [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) + (countLit q [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) (l₂ := [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61])
  have hm := merge_two (literal (valuationOf q) (892)) (literal (valuationOf q) (952)) (literal (valuationOf q) (974)) (countLit q [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) (countLit q [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) (count966 q) 6 3 (meaning892 q) (meaning952 q) (meaning974 q) hs
  change valuationOf q 892 = false ∨ valuationOf q 952 = false ∨ valuationOf q 974 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1062 (q : Snake 81) (h : Conditions q) : valuation q 892 = false ∨ valuation q 952 = false ∨ valuation q 974 = true := counterClause1062 (baseVal q)

theorem counterClause1063 (q : Nat → Bool) : valuationOf q 892 = false ∨ valuationOf q 953 = false ∨ valuationOf q 975 = true := by
  have hs : count966 q = (countLit q [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) + (countLit q [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) (l₂ := [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61])
  have hm := merge_two (literal (valuationOf q) (892)) (literal (valuationOf q) (953)) (literal (valuationOf q) (975)) (countLit q [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) (countLit q [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) (count966 q) 6 4 (meaning892 q) (meaning953 q) (meaning975 q) hs
  change valuationOf q 892 = false ∨ valuationOf q 953 = false ∨ valuationOf q 975 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1063 (q : Snake 81) (h : Conditions q) : valuation q 892 = false ∨ valuation q 953 = false ∨ valuation q 975 = true := counterClause1063 (baseVal q)

theorem counterClause1064 (q : Nat → Bool) : valuationOf q 892 = false ∨ valuationOf q 954 = false ∨ valuationOf q 976 = true := by
  have hs : count966 q = (countLit q [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) + (countLit q [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) (l₂ := [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61])
  have hm := merge_two (literal (valuationOf q) (892)) (literal (valuationOf q) (954)) (literal (valuationOf q) (976)) (countLit q [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) (countLit q [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) (count966 q) 6 5 (meaning892 q) (meaning954 q) (meaning976 q) hs
  change valuationOf q 892 = false ∨ valuationOf q 954 = false ∨ valuationOf q 976 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1064 (q : Snake 81) (h : Conditions q) : valuation q 892 = false ∨ valuation q 954 = false ∨ valuation q 976 = true := counterClause1064 (baseVal q)

theorem counterClause1065 (q : Nat → Bool) : valuationOf q 892 = false ∨ valuationOf q 955 = false ∨ valuationOf q 977 = true := by
  have hs : count966 q = (countLit q [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) + (countLit q [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) (l₂ := [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61])
  have hm := merge_two (literal (valuationOf q) (892)) (literal (valuationOf q) (955)) (literal (valuationOf q) (977)) (countLit q [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) (countLit q [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) (count966 q) 6 6 (meaning892 q) (meaning955 q) (meaning977 q) hs
  change valuationOf q 892 = false ∨ valuationOf q 955 = false ∨ valuationOf q 977 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1065 (q : Snake 81) (h : Conditions q) : valuation q 892 = false ∨ valuation q 955 = false ∨ valuation q 977 = true := counterClause1065 (baseVal q)

theorem counterClause1066 (q : Nat → Bool) : valuationOf q 68 = true ∨ valuationOf q 988 = true := by
  have hs : count988 q = (countLit q [-65]) + (countLit q [-68]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-68])
  have hm := merge_right (literal (valuationOf q) (-68)) (literal (valuationOf q) (988)) (countLit q [-65]) (countLit q [-68]) (count988 q) 1 (meaningNeg68 q) (meaning988 q) hs
  change (! (valuationOf q 68)) = false ∨ valuationOf q 988 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1066 (q : Snake 81) (h : Conditions q) : valuation q 68 = true ∨ valuation q 988 = true := counterClause1066 (baseVal q)

theorem counterClause1067 (q : Nat → Bool) : valuationOf q 65 = true ∨ valuationOf q 988 = true := by
  have hs : count988 q = (countLit q [-65]) + (countLit q [-68]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-68])
  have hm := merge_left (literal (valuationOf q) (-65)) (literal (valuationOf q) (988)) (countLit q [-65]) (countLit q [-68]) (count988 q) 1 (meaningNeg65 q) (meaning988 q) hs
  change (! (valuationOf q 65)) = false ∨ valuationOf q 988 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1067 (q : Snake 81) (h : Conditions q) : valuation q 65 = true ∨ valuation q 988 = true := counterClause1067 (baseVal q)

theorem counterClause1068 (q : Nat → Bool) : valuationOf q 65 = true ∨ valuationOf q 68 = true ∨ valuationOf q 989 = true := by
  have hs : count988 q = (countLit q [-65]) + (countLit q [-68]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-68])
  have hm := merge_two (literal (valuationOf q) (-65)) (literal (valuationOf q) (-68)) (literal (valuationOf q) (989)) (countLit q [-65]) (countLit q [-68]) (count988 q) 1 1 (meaningNeg65 q) (meaningNeg68 q) (meaning989 q) hs
  change (! (valuationOf q 65)) = false ∨ (! (valuationOf q 68)) = false ∨ valuationOf q 989 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1068 (q : Snake 81) (h : Conditions q) : valuation q 65 = true ∨ valuation q 68 = true ∨ valuation q 989 = true := counterClause1068 (baseVal q)

theorem counterClause1069 (q : Nat → Bool) : valuationOf q 988 = false ∨ valuationOf q 990 = true := by
  have hs : count990 q = (countLit q [-63]) + (countLit q [-65, -68]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-65, -68])
  have hm := merge_right (literal (valuationOf q) (988)) (literal (valuationOf q) (990)) (countLit q [-63]) (countLit q [-65, -68]) (count990 q) 1 (meaning988 q) (meaning990 q) hs
  change valuationOf q 988 = false ∨ valuationOf q 990 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1069 (q : Snake 81) (h : Conditions q) : valuation q 988 = false ∨ valuation q 990 = true := counterClause1069 (baseVal q)

theorem counterClause1070 (q : Nat → Bool) : valuationOf q 989 = false ∨ valuationOf q 991 = true := by
  have hs : count990 q = (countLit q [-63]) + (countLit q [-65, -68]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-65, -68])
  have hm := merge_right (literal (valuationOf q) (989)) (literal (valuationOf q) (991)) (countLit q [-63]) (countLit q [-65, -68]) (count990 q) 2 (meaning989 q) (meaning991 q) hs
  change valuationOf q 989 = false ∨ valuationOf q 991 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1070 (q : Snake 81) (h : Conditions q) : valuation q 989 = false ∨ valuation q 991 = true := counterClause1070 (baseVal q)

theorem counterClause1071 (q : Nat → Bool) : valuationOf q 63 = true ∨ valuationOf q 990 = true := by
  have hs : count990 q = (countLit q [-63]) + (countLit q [-65, -68]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-65, -68])
  have hm := merge_left (literal (valuationOf q) (-63)) (literal (valuationOf q) (990)) (countLit q [-63]) (countLit q [-65, -68]) (count990 q) 1 (meaningNeg63 q) (meaning990 q) hs
  change (! (valuationOf q 63)) = false ∨ valuationOf q 990 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1071 (q : Snake 81) (h : Conditions q) : valuation q 63 = true ∨ valuation q 990 = true := counterClause1071 (baseVal q)

theorem counterClause1072 (q : Nat → Bool) : valuationOf q 63 = true ∨ valuationOf q 988 = false ∨ valuationOf q 991 = true := by
  have hs : count990 q = (countLit q [-63]) + (countLit q [-65, -68]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-65, -68])
  have hm := merge_two (literal (valuationOf q) (-63)) (literal (valuationOf q) (988)) (literal (valuationOf q) (991)) (countLit q [-63]) (countLit q [-65, -68]) (count990 q) 1 1 (meaningNeg63 q) (meaning988 q) (meaning991 q) hs
  change (! (valuationOf q 63)) = false ∨ valuationOf q 988 = false ∨ valuationOf q 991 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1072 (q : Snake 81) (h : Conditions q) : valuation q 63 = true ∨ valuation q 988 = false ∨ valuation q 991 = true := counterClause1072 (baseVal q)

theorem counterClause1073 (q : Nat → Bool) : valuationOf q 63 = true ∨ valuationOf q 989 = false ∨ valuationOf q 992 = true := by
  have hs : count990 q = (countLit q [-63]) + (countLit q [-65, -68]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-65, -68])
  have hm := merge_two (literal (valuationOf q) (-63)) (literal (valuationOf q) (989)) (literal (valuationOf q) (992)) (countLit q [-63]) (countLit q [-65, -68]) (count990 q) 1 2 (meaningNeg63 q) (meaning989 q) (meaning992 q) hs
  change (! (valuationOf q 63)) = false ∨ valuationOf q 989 = false ∨ valuationOf q 992 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1073 (q : Snake 81) (h : Conditions q) : valuation q 63 = true ∨ valuation q 989 = false ∨ valuation q 992 = true := counterClause1073 (baseVal q)

theorem counterClause1074 (q : Nat → Bool) : valuationOf q 73 = true ∨ valuationOf q 993 = true := by
  have hs : count993 q = (countLit q [-71]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-71]) (l₂ := [-73])
  have hm := merge_right (literal (valuationOf q) (-73)) (literal (valuationOf q) (993)) (countLit q [-71]) (countLit q [-73]) (count993 q) 1 (meaningNeg73 q) (meaning993 q) hs
  change (! (valuationOf q 73)) = false ∨ valuationOf q 993 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1074 (q : Snake 81) (h : Conditions q) : valuation q 73 = true ∨ valuation q 993 = true := counterClause1074 (baseVal q)

theorem counterClause1075 (q : Nat → Bool) : valuationOf q 71 = true ∨ valuationOf q 993 = true := by
  have hs : count993 q = (countLit q [-71]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-71]) (l₂ := [-73])
  have hm := merge_left (literal (valuationOf q) (-71)) (literal (valuationOf q) (993)) (countLit q [-71]) (countLit q [-73]) (count993 q) 1 (meaningNeg71 q) (meaning993 q) hs
  change (! (valuationOf q 71)) = false ∨ valuationOf q 993 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1075 (q : Snake 81) (h : Conditions q) : valuation q 71 = true ∨ valuation q 993 = true := counterClause1075 (baseVal q)

theorem counterClause1076 (q : Nat → Bool) : valuationOf q 71 = true ∨ valuationOf q 73 = true ∨ valuationOf q 994 = true := by
  have hs : count993 q = (countLit q [-71]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-71]) (l₂ := [-73])
  have hm := merge_two (literal (valuationOf q) (-71)) (literal (valuationOf q) (-73)) (literal (valuationOf q) (994)) (countLit q [-71]) (countLit q [-73]) (count993 q) 1 1 (meaningNeg71 q) (meaningNeg73 q) (meaning994 q) hs
  change (! (valuationOf q 71)) = false ∨ (! (valuationOf q 73)) = false ∨ valuationOf q 994 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1076 (q : Snake 81) (h : Conditions q) : valuation q 71 = true ∨ valuation q 73 = true ∨ valuation q 994 = true := counterClause1076 (baseVal q)

theorem counterClause1077 (q : Nat → Bool) : valuationOf q 75 = true ∨ valuationOf q 995 = true := by
  have hs : count995 q = (countLit q [-74]) + (countLit q [-75]) := List.countP_append (p := literal q) (l₁ := [-74]) (l₂ := [-75])
  have hm := merge_right (literal (valuationOf q) (-75)) (literal (valuationOf q) (995)) (countLit q [-74]) (countLit q [-75]) (count995 q) 1 (meaningNeg75 q) (meaning995 q) hs
  change (! (valuationOf q 75)) = false ∨ valuationOf q 995 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1077 (q : Snake 81) (h : Conditions q) : valuation q 75 = true ∨ valuation q 995 = true := counterClause1077 (baseVal q)

theorem counterClause1078 (q : Nat → Bool) : valuationOf q 74 = true ∨ valuationOf q 995 = true := by
  have hs : count995 q = (countLit q [-74]) + (countLit q [-75]) := List.countP_append (p := literal q) (l₁ := [-74]) (l₂ := [-75])
  have hm := merge_left (literal (valuationOf q) (-74)) (literal (valuationOf q) (995)) (countLit q [-74]) (countLit q [-75]) (count995 q) 1 (meaningNeg74 q) (meaning995 q) hs
  change (! (valuationOf q 74)) = false ∨ valuationOf q 995 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1078 (q : Snake 81) (h : Conditions q) : valuation q 74 = true ∨ valuation q 995 = true := counterClause1078 (baseVal q)

theorem counterClause1079 (q : Nat → Bool) : valuationOf q 74 = true ∨ valuationOf q 75 = true ∨ valuationOf q 996 = true := by
  have hs : count995 q = (countLit q [-74]) + (countLit q [-75]) := List.countP_append (p := literal q) (l₁ := [-74]) (l₂ := [-75])
  have hm := merge_two (literal (valuationOf q) (-74)) (literal (valuationOf q) (-75)) (literal (valuationOf q) (996)) (countLit q [-74]) (countLit q [-75]) (count995 q) 1 1 (meaningNeg74 q) (meaningNeg75 q) (meaning996 q) hs
  change (! (valuationOf q 74)) = false ∨ (! (valuationOf q 75)) = false ∨ valuationOf q 996 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1079 (q : Snake 81) (h : Conditions q) : valuation q 74 = true ∨ valuation q 75 = true ∨ valuation q 996 = true := counterClause1079 (baseVal q)

theorem counterClause1080 (q : Nat → Bool) : valuationOf q 995 = false ∨ valuationOf q 997 = true := by
  have hs : count997 q = (countLit q [-71, -73]) + (countLit q [-74, -75]) := List.countP_append (p := literal q) (l₁ := [-71, -73]) (l₂ := [-74, -75])
  have hm := merge_right (literal (valuationOf q) (995)) (literal (valuationOf q) (997)) (countLit q [-71, -73]) (countLit q [-74, -75]) (count997 q) 1 (meaning995 q) (meaning997 q) hs
  change valuationOf q 995 = false ∨ valuationOf q 997 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1080 (q : Snake 81) (h : Conditions q) : valuation q 995 = false ∨ valuation q 997 = true := counterClause1080 (baseVal q)

theorem counterClause1081 (q : Nat → Bool) : valuationOf q 996 = false ∨ valuationOf q 998 = true := by
  have hs : count997 q = (countLit q [-71, -73]) + (countLit q [-74, -75]) := List.countP_append (p := literal q) (l₁ := [-71, -73]) (l₂ := [-74, -75])
  have hm := merge_right (literal (valuationOf q) (996)) (literal (valuationOf q) (998)) (countLit q [-71, -73]) (countLit q [-74, -75]) (count997 q) 2 (meaning996 q) (meaning998 q) hs
  change valuationOf q 996 = false ∨ valuationOf q 998 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1081 (q : Snake 81) (h : Conditions q) : valuation q 996 = false ∨ valuation q 998 = true := counterClause1081 (baseVal q)

theorem counterClause1082 (q : Nat → Bool) : valuationOf q 993 = false ∨ valuationOf q 997 = true := by
  have hs : count997 q = (countLit q [-71, -73]) + (countLit q [-74, -75]) := List.countP_append (p := literal q) (l₁ := [-71, -73]) (l₂ := [-74, -75])
  have hm := merge_left (literal (valuationOf q) (993)) (literal (valuationOf q) (997)) (countLit q [-71, -73]) (countLit q [-74, -75]) (count997 q) 1 (meaning993 q) (meaning997 q) hs
  change valuationOf q 993 = false ∨ valuationOf q 997 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1082 (q : Snake 81) (h : Conditions q) : valuation q 993 = false ∨ valuation q 997 = true := counterClause1082 (baseVal q)

theorem counterClause1083 (q : Nat → Bool) : valuationOf q 993 = false ∨ valuationOf q 995 = false ∨ valuationOf q 998 = true := by
  have hs : count997 q = (countLit q [-71, -73]) + (countLit q [-74, -75]) := List.countP_append (p := literal q) (l₁ := [-71, -73]) (l₂ := [-74, -75])
  have hm := merge_two (literal (valuationOf q) (993)) (literal (valuationOf q) (995)) (literal (valuationOf q) (998)) (countLit q [-71, -73]) (countLit q [-74, -75]) (count997 q) 1 1 (meaning993 q) (meaning995 q) (meaning998 q) hs
  change valuationOf q 993 = false ∨ valuationOf q 995 = false ∨ valuationOf q 998 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1083 (q : Snake 81) (h : Conditions q) : valuation q 993 = false ∨ valuation q 995 = false ∨ valuation q 998 = true := counterClause1083 (baseVal q)

theorem counterClause1084 (q : Nat → Bool) : valuationOf q 993 = false ∨ valuationOf q 996 = false ∨ valuationOf q 999 = true := by
  have hs : count997 q = (countLit q [-71, -73]) + (countLit q [-74, -75]) := List.countP_append (p := literal q) (l₁ := [-71, -73]) (l₂ := [-74, -75])
  have hm := merge_two (literal (valuationOf q) (993)) (literal (valuationOf q) (996)) (literal (valuationOf q) (999)) (countLit q [-71, -73]) (countLit q [-74, -75]) (count997 q) 1 2 (meaning993 q) (meaning996 q) (meaning999 q) hs
  change valuationOf q 993 = false ∨ valuationOf q 996 = false ∨ valuationOf q 999 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1084 (q : Snake 81) (h : Conditions q) : valuation q 993 = false ∨ valuation q 996 = false ∨ valuation q 999 = true := counterClause1084 (baseVal q)

theorem counterClause1085 (q : Nat → Bool) : valuationOf q 994 = false ∨ valuationOf q 998 = true := by
  have hs : count997 q = (countLit q [-71, -73]) + (countLit q [-74, -75]) := List.countP_append (p := literal q) (l₁ := [-71, -73]) (l₂ := [-74, -75])
  have hm := merge_left (literal (valuationOf q) (994)) (literal (valuationOf q) (998)) (countLit q [-71, -73]) (countLit q [-74, -75]) (count997 q) 2 (meaning994 q) (meaning998 q) hs
  change valuationOf q 994 = false ∨ valuationOf q 998 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1085 (q : Snake 81) (h : Conditions q) : valuation q 994 = false ∨ valuation q 998 = true := counterClause1085 (baseVal q)

theorem counterClause1086 (q : Nat → Bool) : valuationOf q 994 = false ∨ valuationOf q 995 = false ∨ valuationOf q 999 = true := by
  have hs : count997 q = (countLit q [-71, -73]) + (countLit q [-74, -75]) := List.countP_append (p := literal q) (l₁ := [-71, -73]) (l₂ := [-74, -75])
  have hm := merge_two (literal (valuationOf q) (994)) (literal (valuationOf q) (995)) (literal (valuationOf q) (999)) (countLit q [-71, -73]) (countLit q [-74, -75]) (count997 q) 2 1 (meaning994 q) (meaning995 q) (meaning999 q) hs
  change valuationOf q 994 = false ∨ valuationOf q 995 = false ∨ valuationOf q 999 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1086 (q : Snake 81) (h : Conditions q) : valuation q 994 = false ∨ valuation q 995 = false ∨ valuation q 999 = true := counterClause1086 (baseVal q)

theorem counterClause1087 (q : Nat → Bool) : valuationOf q 994 = false ∨ valuationOf q 996 = false ∨ valuationOf q 1000 = true := by
  have hs : count997 q = (countLit q [-71, -73]) + (countLit q [-74, -75]) := List.countP_append (p := literal q) (l₁ := [-71, -73]) (l₂ := [-74, -75])
  have hm := merge_two (literal (valuationOf q) (994)) (literal (valuationOf q) (996)) (literal (valuationOf q) (1000)) (countLit q [-71, -73]) (countLit q [-74, -75]) (count997 q) 2 2 (meaning994 q) (meaning996 q) (meaning1000 q) hs
  change valuationOf q 994 = false ∨ valuationOf q 996 = false ∨ valuationOf q 1000 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1087 (q : Snake 81) (h : Conditions q) : valuation q 994 = false ∨ valuation q 996 = false ∨ valuation q 1000 = true := counterClause1087 (baseVal q)

theorem counterClause1088 (q : Nat → Bool) : valuationOf q 997 = false ∨ valuationOf q 1001 = true := by
  have hs : count1001 q = (countLit q [-63, -65, -68]) + (countLit q [-71, -73, -74, -75]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68]) (l₂ := [-71, -73, -74, -75])
  have hm := merge_right (literal (valuationOf q) (997)) (literal (valuationOf q) (1001)) (countLit q [-63, -65, -68]) (countLit q [-71, -73, -74, -75]) (count1001 q) 1 (meaning997 q) (meaning1001 q) hs
  change valuationOf q 997 = false ∨ valuationOf q 1001 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1088 (q : Snake 81) (h : Conditions q) : valuation q 997 = false ∨ valuation q 1001 = true := counterClause1088 (baseVal q)

theorem block33 (q : Snake 81) (h : Conditions q) : B112E153.Block33 (valuation q) :=
  ⟨clause1057 q h, clause1058 q h, clause1059 q h, clause1060 q h, clause1061 q h, clause1062 q h, clause1063 q h, clause1064 q h, clause1065 q h, clause1066 q h, clause1067 q h, clause1068 q h, clause1069 q h, clause1070 q h, clause1071 q h, clause1072 q h, clause1073 q h, clause1074 q h, clause1075 q h, clause1076 q h, clause1077 q h, clause1078 q h, clause1079 q h, clause1080 q h, clause1081 q h, clause1082 q h, clause1083 q h, clause1084 q h, clause1085 q h, clause1086 q h, clause1087 q h, clause1088 q h⟩

end
end Snake9.Regrowth.E112153
