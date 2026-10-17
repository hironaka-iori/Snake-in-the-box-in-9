import E112097Semantics
import B112E097Inputs
namespace Snake9.Regrowth.E112097
noncomputable section
local instance blockDec33 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1057 (q : Nat → Bool) : valuationOf q 916 = false ∨ valuationOf q 924 = false ∨ valuationOf q 929 = true := by
  have hs : count928 q = (countLit q [-46, -47, -50, -53]) + (countLit q [-54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -50, -53]) (l₂ := [-54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (916)) (literal (valuationOf q) (924)) (literal (valuationOf q) (929)) (countLit q [-46, -47, -50, -53]) (countLit q [-54, -55, -57, -59]) (count928 q) 1 1 (meaning916 q) (meaning924 q) (meaning929 q) hs
  change valuationOf q 916 = false ∨ valuationOf q 924 = false ∨ valuationOf q 929 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1057 (q : Snake 81) (h : Conditions q) : valuation q 916 = false ∨ valuation q 924 = false ∨ valuation q 929 = true := counterClause1057 (baseVal q)

theorem counterClause1058 (q : Nat → Bool) : valuationOf q 916 = false ∨ valuationOf q 925 = false ∨ valuationOf q 930 = true := by
  have hs : count928 q = (countLit q [-46, -47, -50, -53]) + (countLit q [-54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -50, -53]) (l₂ := [-54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (916)) (literal (valuationOf q) (925)) (literal (valuationOf q) (930)) (countLit q [-46, -47, -50, -53]) (countLit q [-54, -55, -57, -59]) (count928 q) 1 2 (meaning916 q) (meaning925 q) (meaning930 q) hs
  change valuationOf q 916 = false ∨ valuationOf q 925 = false ∨ valuationOf q 930 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1058 (q : Snake 81) (h : Conditions q) : valuation q 916 = false ∨ valuation q 925 = false ∨ valuation q 930 = true := counterClause1058 (baseVal q)

theorem counterClause1059 (q : Nat → Bool) : valuationOf q 916 = false ∨ valuationOf q 926 = false ∨ valuationOf q 931 = true := by
  have hs : count928 q = (countLit q [-46, -47, -50, -53]) + (countLit q [-54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -50, -53]) (l₂ := [-54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (916)) (literal (valuationOf q) (926)) (literal (valuationOf q) (931)) (countLit q [-46, -47, -50, -53]) (countLit q [-54, -55, -57, -59]) (count928 q) 1 3 (meaning916 q) (meaning926 q) (meaning931 q) hs
  change valuationOf q 916 = false ∨ valuationOf q 926 = false ∨ valuationOf q 931 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1059 (q : Snake 81) (h : Conditions q) : valuation q 916 = false ∨ valuation q 926 = false ∨ valuation q 931 = true := counterClause1059 (baseVal q)

theorem counterClause1060 (q : Nat → Bool) : valuationOf q 916 = false ∨ valuationOf q 927 = false ∨ valuationOf q 932 = true := by
  have hs : count928 q = (countLit q [-46, -47, -50, -53]) + (countLit q [-54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -50, -53]) (l₂ := [-54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (916)) (literal (valuationOf q) (927)) (literal (valuationOf q) (932)) (countLit q [-46, -47, -50, -53]) (countLit q [-54, -55, -57, -59]) (count928 q) 1 4 (meaning916 q) (meaning927 q) (meaning932 q) hs
  change valuationOf q 916 = false ∨ valuationOf q 927 = false ∨ valuationOf q 932 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1060 (q : Snake 81) (h : Conditions q) : valuation q 916 = false ∨ valuation q 927 = false ∨ valuation q 932 = true := counterClause1060 (baseVal q)

theorem counterClause1061 (q : Nat → Bool) : valuationOf q 917 = false ∨ valuationOf q 929 = true := by
  have hs : count928 q = (countLit q [-46, -47, -50, -53]) + (countLit q [-54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -50, -53]) (l₂ := [-54, -55, -57, -59])
  have hm := merge_left (literal (valuationOf q) (917)) (literal (valuationOf q) (929)) (countLit q [-46, -47, -50, -53]) (countLit q [-54, -55, -57, -59]) (count928 q) 2 (meaning917 q) (meaning929 q) hs
  change valuationOf q 917 = false ∨ valuationOf q 929 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1061 (q : Snake 81) (h : Conditions q) : valuation q 917 = false ∨ valuation q 929 = true := counterClause1061 (baseVal q)

theorem counterClause1062 (q : Nat → Bool) : valuationOf q 917 = false ∨ valuationOf q 924 = false ∨ valuationOf q 930 = true := by
  have hs : count928 q = (countLit q [-46, -47, -50, -53]) + (countLit q [-54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -50, -53]) (l₂ := [-54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (917)) (literal (valuationOf q) (924)) (literal (valuationOf q) (930)) (countLit q [-46, -47, -50, -53]) (countLit q [-54, -55, -57, -59]) (count928 q) 2 1 (meaning917 q) (meaning924 q) (meaning930 q) hs
  change valuationOf q 917 = false ∨ valuationOf q 924 = false ∨ valuationOf q 930 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1062 (q : Snake 81) (h : Conditions q) : valuation q 917 = false ∨ valuation q 924 = false ∨ valuation q 930 = true := counterClause1062 (baseVal q)

theorem counterClause1063 (q : Nat → Bool) : valuationOf q 917 = false ∨ valuationOf q 925 = false ∨ valuationOf q 931 = true := by
  have hs : count928 q = (countLit q [-46, -47, -50, -53]) + (countLit q [-54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -50, -53]) (l₂ := [-54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (917)) (literal (valuationOf q) (925)) (literal (valuationOf q) (931)) (countLit q [-46, -47, -50, -53]) (countLit q [-54, -55, -57, -59]) (count928 q) 2 2 (meaning917 q) (meaning925 q) (meaning931 q) hs
  change valuationOf q 917 = false ∨ valuationOf q 925 = false ∨ valuationOf q 931 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1063 (q : Snake 81) (h : Conditions q) : valuation q 917 = false ∨ valuation q 925 = false ∨ valuation q 931 = true := counterClause1063 (baseVal q)

theorem counterClause1064 (q : Nat → Bool) : valuationOf q 917 = false ∨ valuationOf q 926 = false ∨ valuationOf q 932 = true := by
  have hs : count928 q = (countLit q [-46, -47, -50, -53]) + (countLit q [-54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -50, -53]) (l₂ := [-54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (917)) (literal (valuationOf q) (926)) (literal (valuationOf q) (932)) (countLit q [-46, -47, -50, -53]) (countLit q [-54, -55, -57, -59]) (count928 q) 2 3 (meaning917 q) (meaning926 q) (meaning932 q) hs
  change valuationOf q 917 = false ∨ valuationOf q 926 = false ∨ valuationOf q 932 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1064 (q : Snake 81) (h : Conditions q) : valuation q 917 = false ∨ valuation q 926 = false ∨ valuation q 932 = true := counterClause1064 (baseVal q)

theorem counterClause1065 (q : Nat → Bool) : valuationOf q 917 = false ∨ valuationOf q 927 = false ∨ valuationOf q 933 = true := by
  have hs : count928 q = (countLit q [-46, -47, -50, -53]) + (countLit q [-54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -50, -53]) (l₂ := [-54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (917)) (literal (valuationOf q) (927)) (literal (valuationOf q) (933)) (countLit q [-46, -47, -50, -53]) (countLit q [-54, -55, -57, -59]) (count928 q) 2 4 (meaning917 q) (meaning927 q) (meaning933 q) hs
  change valuationOf q 917 = false ∨ valuationOf q 927 = false ∨ valuationOf q 933 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1065 (q : Snake 81) (h : Conditions q) : valuation q 917 = false ∨ valuation q 927 = false ∨ valuation q 933 = true := counterClause1065 (baseVal q)

theorem counterClause1066 (q : Nat → Bool) : valuationOf q 918 = false ∨ valuationOf q 930 = true := by
  have hs : count928 q = (countLit q [-46, -47, -50, -53]) + (countLit q [-54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -50, -53]) (l₂ := [-54, -55, -57, -59])
  have hm := merge_left (literal (valuationOf q) (918)) (literal (valuationOf q) (930)) (countLit q [-46, -47, -50, -53]) (countLit q [-54, -55, -57, -59]) (count928 q) 3 (meaning918 q) (meaning930 q) hs
  change valuationOf q 918 = false ∨ valuationOf q 930 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1066 (q : Snake 81) (h : Conditions q) : valuation q 918 = false ∨ valuation q 930 = true := counterClause1066 (baseVal q)

theorem counterClause1067 (q : Nat → Bool) : valuationOf q 918 = false ∨ valuationOf q 924 = false ∨ valuationOf q 931 = true := by
  have hs : count928 q = (countLit q [-46, -47, -50, -53]) + (countLit q [-54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -50, -53]) (l₂ := [-54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (918)) (literal (valuationOf q) (924)) (literal (valuationOf q) (931)) (countLit q [-46, -47, -50, -53]) (countLit q [-54, -55, -57, -59]) (count928 q) 3 1 (meaning918 q) (meaning924 q) (meaning931 q) hs
  change valuationOf q 918 = false ∨ valuationOf q 924 = false ∨ valuationOf q 931 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1067 (q : Snake 81) (h : Conditions q) : valuation q 918 = false ∨ valuation q 924 = false ∨ valuation q 931 = true := counterClause1067 (baseVal q)

theorem counterClause1068 (q : Nat → Bool) : valuationOf q 918 = false ∨ valuationOf q 925 = false ∨ valuationOf q 932 = true := by
  have hs : count928 q = (countLit q [-46, -47, -50, -53]) + (countLit q [-54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -50, -53]) (l₂ := [-54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (918)) (literal (valuationOf q) (925)) (literal (valuationOf q) (932)) (countLit q [-46, -47, -50, -53]) (countLit q [-54, -55, -57, -59]) (count928 q) 3 2 (meaning918 q) (meaning925 q) (meaning932 q) hs
  change valuationOf q 918 = false ∨ valuationOf q 925 = false ∨ valuationOf q 932 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1068 (q : Snake 81) (h : Conditions q) : valuation q 918 = false ∨ valuation q 925 = false ∨ valuation q 932 = true := counterClause1068 (baseVal q)

theorem counterClause1069 (q : Nat → Bool) : valuationOf q 918 = false ∨ valuationOf q 926 = false ∨ valuationOf q 933 = true := by
  have hs : count928 q = (countLit q [-46, -47, -50, -53]) + (countLit q [-54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -50, -53]) (l₂ := [-54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (918)) (literal (valuationOf q) (926)) (literal (valuationOf q) (933)) (countLit q [-46, -47, -50, -53]) (countLit q [-54, -55, -57, -59]) (count928 q) 3 3 (meaning918 q) (meaning926 q) (meaning933 q) hs
  change valuationOf q 918 = false ∨ valuationOf q 926 = false ∨ valuationOf q 933 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1069 (q : Snake 81) (h : Conditions q) : valuation q 918 = false ∨ valuation q 926 = false ∨ valuation q 933 = true := counterClause1069 (baseVal q)

theorem counterClause1070 (q : Nat → Bool) : valuationOf q 919 = false ∨ valuationOf q 931 = true := by
  have hs : count928 q = (countLit q [-46, -47, -50, -53]) + (countLit q [-54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -50, -53]) (l₂ := [-54, -55, -57, -59])
  have hm := merge_left (literal (valuationOf q) (919)) (literal (valuationOf q) (931)) (countLit q [-46, -47, -50, -53]) (countLit q [-54, -55, -57, -59]) (count928 q) 4 (meaning919 q) (meaning931 q) hs
  change valuationOf q 919 = false ∨ valuationOf q 931 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1070 (q : Snake 81) (h : Conditions q) : valuation q 919 = false ∨ valuation q 931 = true := counterClause1070 (baseVal q)

theorem counterClause1071 (q : Nat → Bool) : valuationOf q 919 = false ∨ valuationOf q 924 = false ∨ valuationOf q 932 = true := by
  have hs : count928 q = (countLit q [-46, -47, -50, -53]) + (countLit q [-54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -50, -53]) (l₂ := [-54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (919)) (literal (valuationOf q) (924)) (literal (valuationOf q) (932)) (countLit q [-46, -47, -50, -53]) (countLit q [-54, -55, -57, -59]) (count928 q) 4 1 (meaning919 q) (meaning924 q) (meaning932 q) hs
  change valuationOf q 919 = false ∨ valuationOf q 924 = false ∨ valuationOf q 932 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1071 (q : Snake 81) (h : Conditions q) : valuation q 919 = false ∨ valuation q 924 = false ∨ valuation q 932 = true := counterClause1071 (baseVal q)

theorem counterClause1072 (q : Nat → Bool) : valuationOf q 919 = false ∨ valuationOf q 925 = false ∨ valuationOf q 933 = true := by
  have hs : count928 q = (countLit q [-46, -47, -50, -53]) + (countLit q [-54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -50, -53]) (l₂ := [-54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (919)) (literal (valuationOf q) (925)) (literal (valuationOf q) (933)) (countLit q [-46, -47, -50, -53]) (countLit q [-54, -55, -57, -59]) (count928 q) 4 2 (meaning919 q) (meaning925 q) (meaning933 q) hs
  change valuationOf q 919 = false ∨ valuationOf q 925 = false ∨ valuationOf q 933 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1072 (q : Snake 81) (h : Conditions q) : valuation q 919 = false ∨ valuation q 925 = false ∨ valuation q 933 = true := counterClause1072 (baseVal q)

theorem counterClause1073 (q : Nat → Bool) : valuationOf q 930 = false ∨ valuationOf q 938 = true := by
  have hs : count936 q = (countLit q [-33, -34, -36, -38, -40, -43, -44]) + (countLit q [-46, -47, -50, -53, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -38, -40, -43, -44]) (l₂ := [-46, -47, -50, -53, -54, -55, -57, -59])
  have hm := merge_right (literal (valuationOf q) (930)) (literal (valuationOf q) (938)) (countLit q [-33, -34, -36, -38, -40, -43, -44]) (countLit q [-46, -47, -50, -53, -54, -55, -57, -59]) (count936 q) 3 (meaning930 q) (meaning938 q) hs
  change valuationOf q 930 = false ∨ valuationOf q 938 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1073 (q : Snake 81) (h : Conditions q) : valuation q 930 = false ∨ valuation q 938 = true := counterClause1073 (baseVal q)

theorem counterClause1074 (q : Nat → Bool) : valuationOf q 905 = false ∨ valuationOf q 928 = false ∨ valuationOf q 937 = true := by
  have hs : count936 q = (countLit q [-33, -34, -36, -38, -40, -43, -44]) + (countLit q [-46, -47, -50, -53, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -38, -40, -43, -44]) (l₂ := [-46, -47, -50, -53, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (905)) (literal (valuationOf q) (928)) (literal (valuationOf q) (937)) (countLit q [-33, -34, -36, -38, -40, -43, -44]) (countLit q [-46, -47, -50, -53, -54, -55, -57, -59]) (count936 q) 1 1 (meaning905 q) (meaning928 q) (meaning937 q) hs
  change valuationOf q 905 = false ∨ valuationOf q 928 = false ∨ valuationOf q 937 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1074 (q : Snake 81) (h : Conditions q) : valuation q 905 = false ∨ valuation q 928 = false ∨ valuation q 937 = true := counterClause1074 (baseVal q)

theorem counterClause1075 (q : Nat → Bool) : valuationOf q 905 = false ∨ valuationOf q 929 = false ∨ valuationOf q 938 = true := by
  have hs : count936 q = (countLit q [-33, -34, -36, -38, -40, -43, -44]) + (countLit q [-46, -47, -50, -53, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -38, -40, -43, -44]) (l₂ := [-46, -47, -50, -53, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (905)) (literal (valuationOf q) (929)) (literal (valuationOf q) (938)) (countLit q [-33, -34, -36, -38, -40, -43, -44]) (countLit q [-46, -47, -50, -53, -54, -55, -57, -59]) (count936 q) 1 2 (meaning905 q) (meaning929 q) (meaning938 q) hs
  change valuationOf q 905 = false ∨ valuationOf q 929 = false ∨ valuationOf q 938 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1075 (q : Snake 81) (h : Conditions q) : valuation q 905 = false ∨ valuation q 929 = false ∨ valuation q 938 = true := counterClause1075 (baseVal q)

theorem counterClause1076 (q : Nat → Bool) : valuationOf q 905 = false ∨ valuationOf q 930 = false ∨ valuationOf q 939 = true := by
  have hs : count936 q = (countLit q [-33, -34, -36, -38, -40, -43, -44]) + (countLit q [-46, -47, -50, -53, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -38, -40, -43, -44]) (l₂ := [-46, -47, -50, -53, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (905)) (literal (valuationOf q) (930)) (literal (valuationOf q) (939)) (countLit q [-33, -34, -36, -38, -40, -43, -44]) (countLit q [-46, -47, -50, -53, -54, -55, -57, -59]) (count936 q) 1 3 (meaning905 q) (meaning930 q) (meaning939 q) hs
  change valuationOf q 905 = false ∨ valuationOf q 930 = false ∨ valuationOf q 939 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1076 (q : Snake 81) (h : Conditions q) : valuation q 905 = false ∨ valuation q 930 = false ∨ valuation q 939 = true := counterClause1076 (baseVal q)

theorem counterClause1077 (q : Nat → Bool) : valuationOf q 905 = false ∨ valuationOf q 931 = false ∨ valuationOf q 940 = true := by
  have hs : count936 q = (countLit q [-33, -34, -36, -38, -40, -43, -44]) + (countLit q [-46, -47, -50, -53, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -38, -40, -43, -44]) (l₂ := [-46, -47, -50, -53, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (905)) (literal (valuationOf q) (931)) (literal (valuationOf q) (940)) (countLit q [-33, -34, -36, -38, -40, -43, -44]) (countLit q [-46, -47, -50, -53, -54, -55, -57, -59]) (count936 q) 1 4 (meaning905 q) (meaning931 q) (meaning940 q) hs
  change valuationOf q 905 = false ∨ valuationOf q 931 = false ∨ valuationOf q 940 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1077 (q : Snake 81) (h : Conditions q) : valuation q 905 = false ∨ valuation q 931 = false ∨ valuation q 940 = true := counterClause1077 (baseVal q)

theorem counterClause1078 (q : Nat → Bool) : valuationOf q 905 = false ∨ valuationOf q 932 = false ∨ valuationOf q 941 = true := by
  have hs : count936 q = (countLit q [-33, -34, -36, -38, -40, -43, -44]) + (countLit q [-46, -47, -50, -53, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -38, -40, -43, -44]) (l₂ := [-46, -47, -50, -53, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (905)) (literal (valuationOf q) (932)) (literal (valuationOf q) (941)) (countLit q [-33, -34, -36, -38, -40, -43, -44]) (countLit q [-46, -47, -50, -53, -54, -55, -57, -59]) (count936 q) 1 5 (meaning905 q) (meaning932 q) (meaning941 q) hs
  change valuationOf q 905 = false ∨ valuationOf q 932 = false ∨ valuationOf q 941 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1078 (q : Snake 81) (h : Conditions q) : valuation q 905 = false ∨ valuation q 932 = false ∨ valuation q 941 = true := counterClause1078 (baseVal q)

theorem counterClause1079 (q : Nat → Bool) : valuationOf q 905 = false ∨ valuationOf q 933 = false ∨ valuationOf q 942 = true := by
  have hs : count936 q = (countLit q [-33, -34, -36, -38, -40, -43, -44]) + (countLit q [-46, -47, -50, -53, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -38, -40, -43, -44]) (l₂ := [-46, -47, -50, -53, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (905)) (literal (valuationOf q) (933)) (literal (valuationOf q) (942)) (countLit q [-33, -34, -36, -38, -40, -43, -44]) (countLit q [-46, -47, -50, -53, -54, -55, -57, -59]) (count936 q) 1 6 (meaning905 q) (meaning933 q) (meaning942 q) hs
  change valuationOf q 905 = false ∨ valuationOf q 933 = false ∨ valuationOf q 942 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1079 (q : Snake 81) (h : Conditions q) : valuation q 905 = false ∨ valuation q 933 = false ∨ valuation q 942 = true := counterClause1079 (baseVal q)

theorem counterClause1080 (q : Nat → Bool) : valuationOf q 906 = false ∨ valuationOf q 928 = false ∨ valuationOf q 938 = true := by
  have hs : count936 q = (countLit q [-33, -34, -36, -38, -40, -43, -44]) + (countLit q [-46, -47, -50, -53, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -38, -40, -43, -44]) (l₂ := [-46, -47, -50, -53, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (906)) (literal (valuationOf q) (928)) (literal (valuationOf q) (938)) (countLit q [-33, -34, -36, -38, -40, -43, -44]) (countLit q [-46, -47, -50, -53, -54, -55, -57, -59]) (count936 q) 2 1 (meaning906 q) (meaning928 q) (meaning938 q) hs
  change valuationOf q 906 = false ∨ valuationOf q 928 = false ∨ valuationOf q 938 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1080 (q : Snake 81) (h : Conditions q) : valuation q 906 = false ∨ valuation q 928 = false ∨ valuation q 938 = true := counterClause1080 (baseVal q)

theorem counterClause1081 (q : Nat → Bool) : valuationOf q 906 = false ∨ valuationOf q 929 = false ∨ valuationOf q 939 = true := by
  have hs : count936 q = (countLit q [-33, -34, -36, -38, -40, -43, -44]) + (countLit q [-46, -47, -50, -53, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -38, -40, -43, -44]) (l₂ := [-46, -47, -50, -53, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (906)) (literal (valuationOf q) (929)) (literal (valuationOf q) (939)) (countLit q [-33, -34, -36, -38, -40, -43, -44]) (countLit q [-46, -47, -50, -53, -54, -55, -57, -59]) (count936 q) 2 2 (meaning906 q) (meaning929 q) (meaning939 q) hs
  change valuationOf q 906 = false ∨ valuationOf q 929 = false ∨ valuationOf q 939 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1081 (q : Snake 81) (h : Conditions q) : valuation q 906 = false ∨ valuation q 929 = false ∨ valuation q 939 = true := counterClause1081 (baseVal q)

theorem counterClause1082 (q : Nat → Bool) : valuationOf q 906 = false ∨ valuationOf q 930 = false ∨ valuationOf q 940 = true := by
  have hs : count936 q = (countLit q [-33, -34, -36, -38, -40, -43, -44]) + (countLit q [-46, -47, -50, -53, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -38, -40, -43, -44]) (l₂ := [-46, -47, -50, -53, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (906)) (literal (valuationOf q) (930)) (literal (valuationOf q) (940)) (countLit q [-33, -34, -36, -38, -40, -43, -44]) (countLit q [-46, -47, -50, -53, -54, -55, -57, -59]) (count936 q) 2 3 (meaning906 q) (meaning930 q) (meaning940 q) hs
  change valuationOf q 906 = false ∨ valuationOf q 930 = false ∨ valuationOf q 940 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1082 (q : Snake 81) (h : Conditions q) : valuation q 906 = false ∨ valuation q 930 = false ∨ valuation q 940 = true := counterClause1082 (baseVal q)

theorem counterClause1083 (q : Nat → Bool) : valuationOf q 906 = false ∨ valuationOf q 931 = false ∨ valuationOf q 941 = true := by
  have hs : count936 q = (countLit q [-33, -34, -36, -38, -40, -43, -44]) + (countLit q [-46, -47, -50, -53, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -38, -40, -43, -44]) (l₂ := [-46, -47, -50, -53, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (906)) (literal (valuationOf q) (931)) (literal (valuationOf q) (941)) (countLit q [-33, -34, -36, -38, -40, -43, -44]) (countLit q [-46, -47, -50, -53, -54, -55, -57, -59]) (count936 q) 2 4 (meaning906 q) (meaning931 q) (meaning941 q) hs
  change valuationOf q 906 = false ∨ valuationOf q 931 = false ∨ valuationOf q 941 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1083 (q : Snake 81) (h : Conditions q) : valuation q 906 = false ∨ valuation q 931 = false ∨ valuation q 941 = true := counterClause1083 (baseVal q)

theorem counterClause1084 (q : Nat → Bool) : valuationOf q 906 = false ∨ valuationOf q 932 = false ∨ valuationOf q 942 = true := by
  have hs : count936 q = (countLit q [-33, -34, -36, -38, -40, -43, -44]) + (countLit q [-46, -47, -50, -53, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -38, -40, -43, -44]) (l₂ := [-46, -47, -50, -53, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (906)) (literal (valuationOf q) (932)) (literal (valuationOf q) (942)) (countLit q [-33, -34, -36, -38, -40, -43, -44]) (countLit q [-46, -47, -50, -53, -54, -55, -57, -59]) (count936 q) 2 5 (meaning906 q) (meaning932 q) (meaning942 q) hs
  change valuationOf q 906 = false ∨ valuationOf q 932 = false ∨ valuationOf q 942 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1084 (q : Snake 81) (h : Conditions q) : valuation q 906 = false ∨ valuation q 932 = false ∨ valuation q 942 = true := counterClause1084 (baseVal q)

theorem counterClause1085 (q : Nat → Bool) : valuationOf q 906 = false ∨ valuationOf q 933 = false ∨ valuationOf q 943 = true := by
  have hs : count936 q = (countLit q [-33, -34, -36, -38, -40, -43, -44]) + (countLit q [-46, -47, -50, -53, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -38, -40, -43, -44]) (l₂ := [-46, -47, -50, -53, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (906)) (literal (valuationOf q) (933)) (literal (valuationOf q) (943)) (countLit q [-33, -34, -36, -38, -40, -43, -44]) (countLit q [-46, -47, -50, -53, -54, -55, -57, -59]) (count936 q) 2 6 (meaning906 q) (meaning933 q) (meaning943 q) hs
  change valuationOf q 906 = false ∨ valuationOf q 933 = false ∨ valuationOf q 943 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1085 (q : Snake 81) (h : Conditions q) : valuation q 906 = false ∨ valuation q 933 = false ∨ valuation q 943 = true := counterClause1085 (baseVal q)

theorem counterClause1086 (q : Nat → Bool) : valuationOf q 907 = false ∨ valuationOf q 928 = false ∨ valuationOf q 939 = true := by
  have hs : count936 q = (countLit q [-33, -34, -36, -38, -40, -43, -44]) + (countLit q [-46, -47, -50, -53, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -38, -40, -43, -44]) (l₂ := [-46, -47, -50, -53, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (907)) (literal (valuationOf q) (928)) (literal (valuationOf q) (939)) (countLit q [-33, -34, -36, -38, -40, -43, -44]) (countLit q [-46, -47, -50, -53, -54, -55, -57, -59]) (count936 q) 3 1 (meaning907 q) (meaning928 q) (meaning939 q) hs
  change valuationOf q 907 = false ∨ valuationOf q 928 = false ∨ valuationOf q 939 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1086 (q : Snake 81) (h : Conditions q) : valuation q 907 = false ∨ valuation q 928 = false ∨ valuation q 939 = true := counterClause1086 (baseVal q)

theorem counterClause1087 (q : Nat → Bool) : valuationOf q 907 = false ∨ valuationOf q 929 = false ∨ valuationOf q 940 = true := by
  have hs : count936 q = (countLit q [-33, -34, -36, -38, -40, -43, -44]) + (countLit q [-46, -47, -50, -53, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -38, -40, -43, -44]) (l₂ := [-46, -47, -50, -53, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (907)) (literal (valuationOf q) (929)) (literal (valuationOf q) (940)) (countLit q [-33, -34, -36, -38, -40, -43, -44]) (countLit q [-46, -47, -50, -53, -54, -55, -57, -59]) (count936 q) 3 2 (meaning907 q) (meaning929 q) (meaning940 q) hs
  change valuationOf q 907 = false ∨ valuationOf q 929 = false ∨ valuationOf q 940 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1087 (q : Snake 81) (h : Conditions q) : valuation q 907 = false ∨ valuation q 929 = false ∨ valuation q 940 = true := counterClause1087 (baseVal q)

theorem counterClause1088 (q : Nat → Bool) : valuationOf q 907 = false ∨ valuationOf q 930 = false ∨ valuationOf q 941 = true := by
  have hs : count936 q = (countLit q [-33, -34, -36, -38, -40, -43, -44]) + (countLit q [-46, -47, -50, -53, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -38, -40, -43, -44]) (l₂ := [-46, -47, -50, -53, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (907)) (literal (valuationOf q) (930)) (literal (valuationOf q) (941)) (countLit q [-33, -34, -36, -38, -40, -43, -44]) (countLit q [-46, -47, -50, -53, -54, -55, -57, -59]) (count936 q) 3 3 (meaning907 q) (meaning930 q) (meaning941 q) hs
  change valuationOf q 907 = false ∨ valuationOf q 930 = false ∨ valuationOf q 941 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1088 (q : Snake 81) (h : Conditions q) : valuation q 907 = false ∨ valuation q 930 = false ∨ valuation q 941 = true := counterClause1088 (baseVal q)

theorem block33 (q : Snake 81) (h : Conditions q) : B112E097.Block33 (valuation q) :=
  ⟨clause1057 q h, clause1058 q h, clause1059 q h, clause1060 q h, clause1061 q h, clause1062 q h, clause1063 q h, clause1064 q h, clause1065 q h, clause1066 q h, clause1067 q h, clause1068 q h, clause1069 q h, clause1070 q h, clause1071 q h, clause1072 q h, clause1073 q h, clause1074 q h, clause1075 q h, clause1076 q h, clause1077 q h, clause1078 q h, clause1079 q h, clause1080 q h, clause1081 q h, clause1082 q h, clause1083 q h, clause1084 q h, clause1085 q h, clause1086 q h, clause1087 q h, clause1088 q h⟩

end
end Snake9.Regrowth.E112097
