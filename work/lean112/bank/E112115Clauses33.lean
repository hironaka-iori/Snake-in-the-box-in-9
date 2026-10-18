import E112115Semantics
import B112E115Inputs
namespace Snake9.Regrowth.E112115
noncomputable section
local instance blockDec33 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1057 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 79 = true ∨ valuationOf q 952 = true := by
  have hs : count951 q = (countLit q [-78]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-79])
  have hm := merge_two (literal (valuationOf q) (-78)) (literal (valuationOf q) (-79)) (literal (valuationOf q) (952)) (countLit q [-78]) (countLit q [-79]) (count951 q) 1 1 (meaningNeg78 q) (meaningNeg79 q) (meaning952 q) hs
  change (! (valuationOf q 78)) = false ∨ (! (valuationOf q 79)) = false ∨ valuationOf q 952 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1057 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 79 = true ∨ valuation q 952 = true := counterClause1057 (baseVal q)

theorem counterClause1058 (q : Nat → Bool) : valuationOf q 951 = false ∨ valuationOf q 953 = true := by
  have hs : count953 q = (countLit q [-74, -75]) + (countLit q [-78, -79]) := List.countP_append (p := literal q) (l₁ := [-74, -75]) (l₂ := [-78, -79])
  have hm := merge_right (literal (valuationOf q) (951)) (literal (valuationOf q) (953)) (countLit q [-74, -75]) (countLit q [-78, -79]) (count953 q) 1 (meaning951 q) (meaning953 q) hs
  change valuationOf q 951 = false ∨ valuationOf q 953 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1058 (q : Snake 81) (h : Conditions q) : valuation q 951 = false ∨ valuation q 953 = true := counterClause1058 (baseVal q)

theorem counterClause1059 (q : Nat → Bool) : valuationOf q 952 = false ∨ valuationOf q 954 = true := by
  have hs : count953 q = (countLit q [-74, -75]) + (countLit q [-78, -79]) := List.countP_append (p := literal q) (l₁ := [-74, -75]) (l₂ := [-78, -79])
  have hm := merge_right (literal (valuationOf q) (952)) (literal (valuationOf q) (954)) (countLit q [-74, -75]) (countLit q [-78, -79]) (count953 q) 2 (meaning952 q) (meaning954 q) hs
  change valuationOf q 952 = false ∨ valuationOf q 954 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1059 (q : Snake 81) (h : Conditions q) : valuation q 952 = false ∨ valuation q 954 = true := counterClause1059 (baseVal q)

theorem counterClause1060 (q : Nat → Bool) : valuationOf q 949 = false ∨ valuationOf q 953 = true := by
  have hs : count953 q = (countLit q [-74, -75]) + (countLit q [-78, -79]) := List.countP_append (p := literal q) (l₁ := [-74, -75]) (l₂ := [-78, -79])
  have hm := merge_left (literal (valuationOf q) (949)) (literal (valuationOf q) (953)) (countLit q [-74, -75]) (countLit q [-78, -79]) (count953 q) 1 (meaning949 q) (meaning953 q) hs
  change valuationOf q 949 = false ∨ valuationOf q 953 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1060 (q : Snake 81) (h : Conditions q) : valuation q 949 = false ∨ valuation q 953 = true := counterClause1060 (baseVal q)

theorem counterClause1061 (q : Nat → Bool) : valuationOf q 949 = false ∨ valuationOf q 951 = false ∨ valuationOf q 954 = true := by
  have hs : count953 q = (countLit q [-74, -75]) + (countLit q [-78, -79]) := List.countP_append (p := literal q) (l₁ := [-74, -75]) (l₂ := [-78, -79])
  have hm := merge_two (literal (valuationOf q) (949)) (literal (valuationOf q) (951)) (literal (valuationOf q) (954)) (countLit q [-74, -75]) (countLit q [-78, -79]) (count953 q) 1 1 (meaning949 q) (meaning951 q) (meaning954 q) hs
  change valuationOf q 949 = false ∨ valuationOf q 951 = false ∨ valuationOf q 954 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1061 (q : Snake 81) (h : Conditions q) : valuation q 949 = false ∨ valuation q 951 = false ∨ valuation q 954 = true := counterClause1061 (baseVal q)

theorem counterClause1062 (q : Nat → Bool) : valuationOf q 949 = false ∨ valuationOf q 952 = false ∨ valuationOf q 955 = true := by
  have hs : count953 q = (countLit q [-74, -75]) + (countLit q [-78, -79]) := List.countP_append (p := literal q) (l₁ := [-74, -75]) (l₂ := [-78, -79])
  have hm := merge_two (literal (valuationOf q) (949)) (literal (valuationOf q) (952)) (literal (valuationOf q) (955)) (countLit q [-74, -75]) (countLit q [-78, -79]) (count953 q) 1 2 (meaning949 q) (meaning952 q) (meaning955 q) hs
  change valuationOf q 949 = false ∨ valuationOf q 952 = false ∨ valuationOf q 955 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1062 (q : Snake 81) (h : Conditions q) : valuation q 949 = false ∨ valuation q 952 = false ∨ valuation q 955 = true := counterClause1062 (baseVal q)

theorem counterClause1063 (q : Nat → Bool) : valuationOf q 950 = false ∨ valuationOf q 954 = true := by
  have hs : count953 q = (countLit q [-74, -75]) + (countLit q [-78, -79]) := List.countP_append (p := literal q) (l₁ := [-74, -75]) (l₂ := [-78, -79])
  have hm := merge_left (literal (valuationOf q) (950)) (literal (valuationOf q) (954)) (countLit q [-74, -75]) (countLit q [-78, -79]) (count953 q) 2 (meaning950 q) (meaning954 q) hs
  change valuationOf q 950 = false ∨ valuationOf q 954 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1063 (q : Snake 81) (h : Conditions q) : valuation q 950 = false ∨ valuation q 954 = true := counterClause1063 (baseVal q)

theorem counterClause1064 (q : Nat → Bool) : valuationOf q 950 = false ∨ valuationOf q 951 = false ∨ valuationOf q 955 = true := by
  have hs : count953 q = (countLit q [-74, -75]) + (countLit q [-78, -79]) := List.countP_append (p := literal q) (l₁ := [-74, -75]) (l₂ := [-78, -79])
  have hm := merge_two (literal (valuationOf q) (950)) (literal (valuationOf q) (951)) (literal (valuationOf q) (955)) (countLit q [-74, -75]) (countLit q [-78, -79]) (count953 q) 2 1 (meaning950 q) (meaning951 q) (meaning955 q) hs
  change valuationOf q 950 = false ∨ valuationOf q 951 = false ∨ valuationOf q 955 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1064 (q : Snake 81) (h : Conditions q) : valuation q 950 = false ∨ valuation q 951 = false ∨ valuation q 955 = true := counterClause1064 (baseVal q)

theorem counterClause1065 (q : Nat → Bool) : valuationOf q 84 = true ∨ valuationOf q 957 = true := by
  have hs : count957 q = (countLit q [-82]) + (countLit q [-84]) := List.countP_append (p := literal q) (l₁ := [-82]) (l₂ := [-84])
  have hm := merge_right (literal (valuationOf q) (-84)) (literal (valuationOf q) (957)) (countLit q [-82]) (countLit q [-84]) (count957 q) 1 (meaningNeg84 q) (meaning957 q) hs
  change (! (valuationOf q 84)) = false ∨ valuationOf q 957 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1065 (q : Snake 81) (h : Conditions q) : valuation q 84 = true ∨ valuation q 957 = true := counterClause1065 (baseVal q)

theorem counterClause1066 (q : Nat → Bool) : valuationOf q 82 = true ∨ valuationOf q 957 = true := by
  have hs : count957 q = (countLit q [-82]) + (countLit q [-84]) := List.countP_append (p := literal q) (l₁ := [-82]) (l₂ := [-84])
  have hm := merge_left (literal (valuationOf q) (-82)) (literal (valuationOf q) (957)) (countLit q [-82]) (countLit q [-84]) (count957 q) 1 (meaningNeg82 q) (meaning957 q) hs
  change (! (valuationOf q 82)) = false ∨ valuationOf q 957 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1066 (q : Snake 81) (h : Conditions q) : valuation q 82 = true ∨ valuation q 957 = true := counterClause1066 (baseVal q)

theorem counterClause1067 (q : Nat → Bool) : valuationOf q 82 = true ∨ valuationOf q 84 = true ∨ valuationOf q 958 = true := by
  have hs : count957 q = (countLit q [-82]) + (countLit q [-84]) := List.countP_append (p := literal q) (l₁ := [-82]) (l₂ := [-84])
  have hm := merge_two (literal (valuationOf q) (-82)) (literal (valuationOf q) (-84)) (literal (valuationOf q) (958)) (countLit q [-82]) (countLit q [-84]) (count957 q) 1 1 (meaningNeg82 q) (meaningNeg84 q) (meaning958 q) hs
  change (! (valuationOf q 82)) = false ∨ (! (valuationOf q 84)) = false ∨ valuationOf q 958 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1067 (q : Snake 81) (h : Conditions q) : valuation q 82 = true ∨ valuation q 84 = true ∨ valuation q 958 = true := counterClause1067 (baseVal q)

theorem counterClause1068 (q : Nat → Bool) : valuationOf q 88 = true ∨ valuationOf q 959 = true := by
  have hs : count959 q = (countLit q [-86]) + (countLit q [-88]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-88])
  have hm := merge_right (literal (valuationOf q) (-88)) (literal (valuationOf q) (959)) (countLit q [-86]) (countLit q [-88]) (count959 q) 1 (meaningNeg88 q) (meaning959 q) hs
  change (! (valuationOf q 88)) = false ∨ valuationOf q 959 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1068 (q : Snake 81) (h : Conditions q) : valuation q 88 = true ∨ valuation q 959 = true := counterClause1068 (baseVal q)

theorem counterClause1069 (q : Nat → Bool) : valuationOf q 86 = true ∨ valuationOf q 959 = true := by
  have hs : count959 q = (countLit q [-86]) + (countLit q [-88]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-88])
  have hm := merge_left (literal (valuationOf q) (-86)) (literal (valuationOf q) (959)) (countLit q [-86]) (countLit q [-88]) (count959 q) 1 (meaningNeg86 q) (meaning959 q) hs
  change (! (valuationOf q 86)) = false ∨ valuationOf q 959 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1069 (q : Snake 81) (h : Conditions q) : valuation q 86 = true ∨ valuation q 959 = true := counterClause1069 (baseVal q)

theorem counterClause1070 (q : Nat → Bool) : valuationOf q 86 = true ∨ valuationOf q 88 = true ∨ valuationOf q 960 = true := by
  have hs : count959 q = (countLit q [-86]) + (countLit q [-88]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-88])
  have hm := merge_two (literal (valuationOf q) (-86)) (literal (valuationOf q) (-88)) (literal (valuationOf q) (960)) (countLit q [-86]) (countLit q [-88]) (count959 q) 1 1 (meaningNeg86 q) (meaningNeg88 q) (meaning960 q) hs
  change (! (valuationOf q 86)) = false ∨ (! (valuationOf q 88)) = false ∨ valuationOf q 960 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1070 (q : Snake 81) (h : Conditions q) : valuation q 86 = true ∨ valuation q 88 = true ∨ valuation q 960 = true := counterClause1070 (baseVal q)

theorem counterClause1071 (q : Nat → Bool) : valuationOf q 959 = false ∨ valuationOf q 961 = true := by
  have hs : count961 q = (countLit q [-82, -84]) + (countLit q [-86, -88]) := List.countP_append (p := literal q) (l₁ := [-82, -84]) (l₂ := [-86, -88])
  have hm := merge_right (literal (valuationOf q) (959)) (literal (valuationOf q) (961)) (countLit q [-82, -84]) (countLit q [-86, -88]) (count961 q) 1 (meaning959 q) (meaning961 q) hs
  change valuationOf q 959 = false ∨ valuationOf q 961 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1071 (q : Snake 81) (h : Conditions q) : valuation q 959 = false ∨ valuation q 961 = true := counterClause1071 (baseVal q)

theorem counterClause1072 (q : Nat → Bool) : valuationOf q 960 = false ∨ valuationOf q 962 = true := by
  have hs : count961 q = (countLit q [-82, -84]) + (countLit q [-86, -88]) := List.countP_append (p := literal q) (l₁ := [-82, -84]) (l₂ := [-86, -88])
  have hm := merge_right (literal (valuationOf q) (960)) (literal (valuationOf q) (962)) (countLit q [-82, -84]) (countLit q [-86, -88]) (count961 q) 2 (meaning960 q) (meaning962 q) hs
  change valuationOf q 960 = false ∨ valuationOf q 962 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1072 (q : Snake 81) (h : Conditions q) : valuation q 960 = false ∨ valuation q 962 = true := counterClause1072 (baseVal q)

theorem counterClause1073 (q : Nat → Bool) : valuationOf q 957 = false ∨ valuationOf q 961 = true := by
  have hs : count961 q = (countLit q [-82, -84]) + (countLit q [-86, -88]) := List.countP_append (p := literal q) (l₁ := [-82, -84]) (l₂ := [-86, -88])
  have hm := merge_left (literal (valuationOf q) (957)) (literal (valuationOf q) (961)) (countLit q [-82, -84]) (countLit q [-86, -88]) (count961 q) 1 (meaning957 q) (meaning961 q) hs
  change valuationOf q 957 = false ∨ valuationOf q 961 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1073 (q : Snake 81) (h : Conditions q) : valuation q 957 = false ∨ valuation q 961 = true := counterClause1073 (baseVal q)

theorem counterClause1074 (q : Nat → Bool) : valuationOf q 957 = false ∨ valuationOf q 959 = false ∨ valuationOf q 962 = true := by
  have hs : count961 q = (countLit q [-82, -84]) + (countLit q [-86, -88]) := List.countP_append (p := literal q) (l₁ := [-82, -84]) (l₂ := [-86, -88])
  have hm := merge_two (literal (valuationOf q) (957)) (literal (valuationOf q) (959)) (literal (valuationOf q) (962)) (countLit q [-82, -84]) (countLit q [-86, -88]) (count961 q) 1 1 (meaning957 q) (meaning959 q) (meaning962 q) hs
  change valuationOf q 957 = false ∨ valuationOf q 959 = false ∨ valuationOf q 962 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1074 (q : Snake 81) (h : Conditions q) : valuation q 957 = false ∨ valuation q 959 = false ∨ valuation q 962 = true := counterClause1074 (baseVal q)

theorem counterClause1075 (q : Nat → Bool) : valuationOf q 957 = false ∨ valuationOf q 960 = false ∨ valuationOf q 963 = true := by
  have hs : count961 q = (countLit q [-82, -84]) + (countLit q [-86, -88]) := List.countP_append (p := literal q) (l₁ := [-82, -84]) (l₂ := [-86, -88])
  have hm := merge_two (literal (valuationOf q) (957)) (literal (valuationOf q) (960)) (literal (valuationOf q) (963)) (countLit q [-82, -84]) (countLit q [-86, -88]) (count961 q) 1 2 (meaning957 q) (meaning960 q) (meaning963 q) hs
  change valuationOf q 957 = false ∨ valuationOf q 960 = false ∨ valuationOf q 963 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1075 (q : Snake 81) (h : Conditions q) : valuation q 957 = false ∨ valuation q 960 = false ∨ valuation q 963 = true := counterClause1075 (baseVal q)

theorem counterClause1076 (q : Nat → Bool) : valuationOf q 958 = false ∨ valuationOf q 962 = true := by
  have hs : count961 q = (countLit q [-82, -84]) + (countLit q [-86, -88]) := List.countP_append (p := literal q) (l₁ := [-82, -84]) (l₂ := [-86, -88])
  have hm := merge_left (literal (valuationOf q) (958)) (literal (valuationOf q) (962)) (countLit q [-82, -84]) (countLit q [-86, -88]) (count961 q) 2 (meaning958 q) (meaning962 q) hs
  change valuationOf q 958 = false ∨ valuationOf q 962 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1076 (q : Snake 81) (h : Conditions q) : valuation q 958 = false ∨ valuation q 962 = true := counterClause1076 (baseVal q)

theorem counterClause1077 (q : Nat → Bool) : valuationOf q 958 = false ∨ valuationOf q 959 = false ∨ valuationOf q 963 = true := by
  have hs : count961 q = (countLit q [-82, -84]) + (countLit q [-86, -88]) := List.countP_append (p := literal q) (l₁ := [-82, -84]) (l₂ := [-86, -88])
  have hm := merge_two (literal (valuationOf q) (958)) (literal (valuationOf q) (959)) (literal (valuationOf q) (963)) (countLit q [-82, -84]) (countLit q [-86, -88]) (count961 q) 2 1 (meaning958 q) (meaning959 q) (meaning963 q) hs
  change valuationOf q 958 = false ∨ valuationOf q 959 = false ∨ valuationOf q 963 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1077 (q : Snake 81) (h : Conditions q) : valuation q 958 = false ∨ valuation q 959 = false ∨ valuation q 963 = true := counterClause1077 (baseVal q)

theorem counterClause1078 (q : Nat → Bool) : valuationOf q 958 = false ∨ valuationOf q 960 = false ∨ valuationOf q 964 = true := by
  have hs : count961 q = (countLit q [-82, -84]) + (countLit q [-86, -88]) := List.countP_append (p := literal q) (l₁ := [-82, -84]) (l₂ := [-86, -88])
  have hm := merge_two (literal (valuationOf q) (958)) (literal (valuationOf q) (960)) (literal (valuationOf q) (964)) (countLit q [-82, -84]) (countLit q [-86, -88]) (count961 q) 2 2 (meaning958 q) (meaning960 q) (meaning964 q) hs
  change valuationOf q 958 = false ∨ valuationOf q 960 = false ∨ valuationOf q 964 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1078 (q : Snake 81) (h : Conditions q) : valuation q 958 = false ∨ valuation q 960 = false ∨ valuation q 964 = true := counterClause1078 (baseVal q)

theorem counterClause1079 (q : Nat → Bool) : valuationOf q 961 = false ∨ valuationOf q 965 = true := by
  have hs : count965 q = (countLit q [-74, -75, -78, -79]) + (countLit q [-82, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-74, -75, -78, -79]) (l₂ := [-82, -84, -86, -88])
  have hm := merge_right (literal (valuationOf q) (961)) (literal (valuationOf q) (965)) (countLit q [-74, -75, -78, -79]) (countLit q [-82, -84, -86, -88]) (count965 q) 1 (meaning961 q) (meaning965 q) hs
  change valuationOf q 961 = false ∨ valuationOf q 965 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1079 (q : Snake 81) (h : Conditions q) : valuation q 961 = false ∨ valuation q 965 = true := counterClause1079 (baseVal q)

theorem counterClause1080 (q : Nat → Bool) : valuationOf q 962 = false ∨ valuationOf q 966 = true := by
  have hs : count965 q = (countLit q [-74, -75, -78, -79]) + (countLit q [-82, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-74, -75, -78, -79]) (l₂ := [-82, -84, -86, -88])
  have hm := merge_right (literal (valuationOf q) (962)) (literal (valuationOf q) (966)) (countLit q [-74, -75, -78, -79]) (countLit q [-82, -84, -86, -88]) (count965 q) 2 (meaning962 q) (meaning966 q) hs
  change valuationOf q 962 = false ∨ valuationOf q 966 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1080 (q : Snake 81) (h : Conditions q) : valuation q 962 = false ∨ valuation q 966 = true := counterClause1080 (baseVal q)

theorem counterClause1081 (q : Nat → Bool) : valuationOf q 963 = false ∨ valuationOf q 967 = true := by
  have hs : count965 q = (countLit q [-74, -75, -78, -79]) + (countLit q [-82, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-74, -75, -78, -79]) (l₂ := [-82, -84, -86, -88])
  have hm := merge_right (literal (valuationOf q) (963)) (literal (valuationOf q) (967)) (countLit q [-74, -75, -78, -79]) (countLit q [-82, -84, -86, -88]) (count965 q) 3 (meaning963 q) (meaning967 q) hs
  change valuationOf q 963 = false ∨ valuationOf q 967 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1081 (q : Snake 81) (h : Conditions q) : valuation q 963 = false ∨ valuation q 967 = true := counterClause1081 (baseVal q)

theorem counterClause1082 (q : Nat → Bool) : valuationOf q 964 = false ∨ valuationOf q 968 = true := by
  have hs : count965 q = (countLit q [-74, -75, -78, -79]) + (countLit q [-82, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-74, -75, -78, -79]) (l₂ := [-82, -84, -86, -88])
  have hm := merge_right (literal (valuationOf q) (964)) (literal (valuationOf q) (968)) (countLit q [-74, -75, -78, -79]) (countLit q [-82, -84, -86, -88]) (count965 q) 4 (meaning964 q) (meaning968 q) hs
  change valuationOf q 964 = false ∨ valuationOf q 968 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1082 (q : Snake 81) (h : Conditions q) : valuation q 964 = false ∨ valuation q 968 = true := counterClause1082 (baseVal q)

theorem counterClause1083 (q : Nat → Bool) : valuationOf q 953 = false ∨ valuationOf q 965 = true := by
  have hs : count965 q = (countLit q [-74, -75, -78, -79]) + (countLit q [-82, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-74, -75, -78, -79]) (l₂ := [-82, -84, -86, -88])
  have hm := merge_left (literal (valuationOf q) (953)) (literal (valuationOf q) (965)) (countLit q [-74, -75, -78, -79]) (countLit q [-82, -84, -86, -88]) (count965 q) 1 (meaning953 q) (meaning965 q) hs
  change valuationOf q 953 = false ∨ valuationOf q 965 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1083 (q : Snake 81) (h : Conditions q) : valuation q 953 = false ∨ valuation q 965 = true := counterClause1083 (baseVal q)

theorem counterClause1084 (q : Nat → Bool) : valuationOf q 953 = false ∨ valuationOf q 961 = false ∨ valuationOf q 966 = true := by
  have hs : count965 q = (countLit q [-74, -75, -78, -79]) + (countLit q [-82, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-74, -75, -78, -79]) (l₂ := [-82, -84, -86, -88])
  have hm := merge_two (literal (valuationOf q) (953)) (literal (valuationOf q) (961)) (literal (valuationOf q) (966)) (countLit q [-74, -75, -78, -79]) (countLit q [-82, -84, -86, -88]) (count965 q) 1 1 (meaning953 q) (meaning961 q) (meaning966 q) hs
  change valuationOf q 953 = false ∨ valuationOf q 961 = false ∨ valuationOf q 966 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1084 (q : Snake 81) (h : Conditions q) : valuation q 953 = false ∨ valuation q 961 = false ∨ valuation q 966 = true := counterClause1084 (baseVal q)

theorem counterClause1085 (q : Nat → Bool) : valuationOf q 953 = false ∨ valuationOf q 962 = false ∨ valuationOf q 967 = true := by
  have hs : count965 q = (countLit q [-74, -75, -78, -79]) + (countLit q [-82, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-74, -75, -78, -79]) (l₂ := [-82, -84, -86, -88])
  have hm := merge_two (literal (valuationOf q) (953)) (literal (valuationOf q) (962)) (literal (valuationOf q) (967)) (countLit q [-74, -75, -78, -79]) (countLit q [-82, -84, -86, -88]) (count965 q) 1 2 (meaning953 q) (meaning962 q) (meaning967 q) hs
  change valuationOf q 953 = false ∨ valuationOf q 962 = false ∨ valuationOf q 967 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1085 (q : Snake 81) (h : Conditions q) : valuation q 953 = false ∨ valuation q 962 = false ∨ valuation q 967 = true := counterClause1085 (baseVal q)

theorem counterClause1086 (q : Nat → Bool) : valuationOf q 953 = false ∨ valuationOf q 963 = false ∨ valuationOf q 968 = true := by
  have hs : count965 q = (countLit q [-74, -75, -78, -79]) + (countLit q [-82, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-74, -75, -78, -79]) (l₂ := [-82, -84, -86, -88])
  have hm := merge_two (literal (valuationOf q) (953)) (literal (valuationOf q) (963)) (literal (valuationOf q) (968)) (countLit q [-74, -75, -78, -79]) (countLit q [-82, -84, -86, -88]) (count965 q) 1 3 (meaning953 q) (meaning963 q) (meaning968 q) hs
  change valuationOf q 953 = false ∨ valuationOf q 963 = false ∨ valuationOf q 968 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1086 (q : Snake 81) (h : Conditions q) : valuation q 953 = false ∨ valuation q 963 = false ∨ valuation q 968 = true := counterClause1086 (baseVal q)

theorem counterClause1087 (q : Nat → Bool) : valuationOf q 953 = false ∨ valuationOf q 964 = false ∨ valuationOf q 969 = true := by
  have hs : count965 q = (countLit q [-74, -75, -78, -79]) + (countLit q [-82, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-74, -75, -78, -79]) (l₂ := [-82, -84, -86, -88])
  have hm := merge_two (literal (valuationOf q) (953)) (literal (valuationOf q) (964)) (literal (valuationOf q) (969)) (countLit q [-74, -75, -78, -79]) (countLit q [-82, -84, -86, -88]) (count965 q) 1 4 (meaning953 q) (meaning964 q) (meaning969 q) hs
  change valuationOf q 953 = false ∨ valuationOf q 964 = false ∨ valuationOf q 969 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1087 (q : Snake 81) (h : Conditions q) : valuation q 953 = false ∨ valuation q 964 = false ∨ valuation q 969 = true := counterClause1087 (baseVal q)

theorem counterClause1088 (q : Nat → Bool) : valuationOf q 954 = false ∨ valuationOf q 966 = true := by
  have hs : count965 q = (countLit q [-74, -75, -78, -79]) + (countLit q [-82, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-74, -75, -78, -79]) (l₂ := [-82, -84, -86, -88])
  have hm := merge_left (literal (valuationOf q) (954)) (literal (valuationOf q) (966)) (countLit q [-74, -75, -78, -79]) (countLit q [-82, -84, -86, -88]) (count965 q) 2 (meaning954 q) (meaning966 q) hs
  change valuationOf q 954 = false ∨ valuationOf q 966 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1088 (q : Snake 81) (h : Conditions q) : valuation q 954 = false ∨ valuation q 966 = true := counterClause1088 (baseVal q)

theorem block33 (q : Snake 81) (h : Conditions q) : B112E115.Block33 (valuation q) :=
  ⟨clause1057 q h, clause1058 q h, clause1059 q h, clause1060 q h, clause1061 q h, clause1062 q h, clause1063 q h, clause1064 q h, clause1065 q h, clause1066 q h, clause1067 q h, clause1068 q h, clause1069 q h, clause1070 q h, clause1071 q h, clause1072 q h, clause1073 q h, clause1074 q h, clause1075 q h, clause1076 q h, clause1077 q h, clause1078 q h, clause1079 q h, clause1080 q h, clause1081 q h, clause1082 q h, clause1083 q h, clause1084 q h, clause1085 q h, clause1086 q h, clause1087 q h, clause1088 q h⟩

end
end Snake9.Regrowth.E112115
