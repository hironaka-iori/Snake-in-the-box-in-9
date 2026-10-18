import E112213Semantics
import B112E213Inputs
namespace Snake9.Regrowth.E112213
noncomputable section
local instance blockDec32 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1025 (q : Nat → Bool) : valuationOf q 949 = false ∨ valuationOf q 953 = true := by
  have hs : count953 q = (countLit q [-74, -76]) + (countLit q [-79, -81]) := List.countP_append (p := literal q) (l₁ := [-74, -76]) (l₂ := [-79, -81])
  have hm := merge_left (literal (valuationOf q) (949)) (literal (valuationOf q) (953)) (countLit q [-74, -76]) (countLit q [-79, -81]) (count953 q) 1 (meaning949 q) (meaning953 q) hs
  change valuationOf q 949 = false ∨ valuationOf q 953 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1025 (q : Snake 81) (h : Conditions q) : valuation q 949 = false ∨ valuation q 953 = true := counterClause1025 (baseVal q)

theorem counterClause1026 (q : Nat → Bool) : valuationOf q 949 = false ∨ valuationOf q 951 = false ∨ valuationOf q 954 = true := by
  have hs : count953 q = (countLit q [-74, -76]) + (countLit q [-79, -81]) := List.countP_append (p := literal q) (l₁ := [-74, -76]) (l₂ := [-79, -81])
  have hm := merge_two (literal (valuationOf q) (949)) (literal (valuationOf q) (951)) (literal (valuationOf q) (954)) (countLit q [-74, -76]) (countLit q [-79, -81]) (count953 q) 1 1 (meaning949 q) (meaning951 q) (meaning954 q) hs
  change valuationOf q 949 = false ∨ valuationOf q 951 = false ∨ valuationOf q 954 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1026 (q : Snake 81) (h : Conditions q) : valuation q 949 = false ∨ valuation q 951 = false ∨ valuation q 954 = true := counterClause1026 (baseVal q)

theorem counterClause1027 (q : Nat → Bool) : valuationOf q 949 = false ∨ valuationOf q 952 = false ∨ valuationOf q 955 = true := by
  have hs : count953 q = (countLit q [-74, -76]) + (countLit q [-79, -81]) := List.countP_append (p := literal q) (l₁ := [-74, -76]) (l₂ := [-79, -81])
  have hm := merge_two (literal (valuationOf q) (949)) (literal (valuationOf q) (952)) (literal (valuationOf q) (955)) (countLit q [-74, -76]) (countLit q [-79, -81]) (count953 q) 1 2 (meaning949 q) (meaning952 q) (meaning955 q) hs
  change valuationOf q 949 = false ∨ valuationOf q 952 = false ∨ valuationOf q 955 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1027 (q : Snake 81) (h : Conditions q) : valuation q 949 = false ∨ valuation q 952 = false ∨ valuation q 955 = true := counterClause1027 (baseVal q)

theorem counterClause1028 (q : Nat → Bool) : valuationOf q 950 = false ∨ valuationOf q 954 = true := by
  have hs : count953 q = (countLit q [-74, -76]) + (countLit q [-79, -81]) := List.countP_append (p := literal q) (l₁ := [-74, -76]) (l₂ := [-79, -81])
  have hm := merge_left (literal (valuationOf q) (950)) (literal (valuationOf q) (954)) (countLit q [-74, -76]) (countLit q [-79, -81]) (count953 q) 2 (meaning950 q) (meaning954 q) hs
  change valuationOf q 950 = false ∨ valuationOf q 954 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1028 (q : Snake 81) (h : Conditions q) : valuation q 950 = false ∨ valuation q 954 = true := counterClause1028 (baseVal q)

theorem counterClause1029 (q : Nat → Bool) : valuationOf q 950 = false ∨ valuationOf q 951 = false ∨ valuationOf q 955 = true := by
  have hs : count953 q = (countLit q [-74, -76]) + (countLit q [-79, -81]) := List.countP_append (p := literal q) (l₁ := [-74, -76]) (l₂ := [-79, -81])
  have hm := merge_two (literal (valuationOf q) (950)) (literal (valuationOf q) (951)) (literal (valuationOf q) (955)) (countLit q [-74, -76]) (countLit q [-79, -81]) (count953 q) 2 1 (meaning950 q) (meaning951 q) (meaning955 q) hs
  change valuationOf q 950 = false ∨ valuationOf q 951 = false ∨ valuationOf q 955 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1029 (q : Snake 81) (h : Conditions q) : valuation q 950 = false ∨ valuation q 951 = false ∨ valuation q 955 = true := counterClause1029 (baseVal q)

theorem counterClause1030 (q : Nat → Bool) : valuationOf q 84 = true ∨ valuationOf q 957 = true := by
  have hs : count957 q = (countLit q [-83]) + (countLit q [-84]) := List.countP_append (p := literal q) (l₁ := [-83]) (l₂ := [-84])
  have hm := merge_right (literal (valuationOf q) (-84)) (literal (valuationOf q) (957)) (countLit q [-83]) (countLit q [-84]) (count957 q) 1 (meaningNeg84 q) (meaning957 q) hs
  change (! (valuationOf q 84)) = false ∨ valuationOf q 957 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1030 (q : Snake 81) (h : Conditions q) : valuation q 84 = true ∨ valuation q 957 = true := counterClause1030 (baseVal q)

theorem counterClause1031 (q : Nat → Bool) : valuationOf q 83 = true ∨ valuationOf q 957 = true := by
  have hs : count957 q = (countLit q [-83]) + (countLit q [-84]) := List.countP_append (p := literal q) (l₁ := [-83]) (l₂ := [-84])
  have hm := merge_left (literal (valuationOf q) (-83)) (literal (valuationOf q) (957)) (countLit q [-83]) (countLit q [-84]) (count957 q) 1 (meaningNeg83 q) (meaning957 q) hs
  change (! (valuationOf q 83)) = false ∨ valuationOf q 957 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1031 (q : Snake 81) (h : Conditions q) : valuation q 83 = true ∨ valuation q 957 = true := counterClause1031 (baseVal q)

theorem counterClause1032 (q : Nat → Bool) : valuationOf q 83 = true ∨ valuationOf q 84 = true ∨ valuationOf q 958 = true := by
  have hs : count957 q = (countLit q [-83]) + (countLit q [-84]) := List.countP_append (p := literal q) (l₁ := [-83]) (l₂ := [-84])
  have hm := merge_two (literal (valuationOf q) (-83)) (literal (valuationOf q) (-84)) (literal (valuationOf q) (958)) (countLit q [-83]) (countLit q [-84]) (count957 q) 1 1 (meaningNeg83 q) (meaningNeg84 q) (meaning958 q) hs
  change (! (valuationOf q 83)) = false ∨ (! (valuationOf q 84)) = false ∨ valuationOf q 958 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1032 (q : Snake 81) (h : Conditions q) : valuation q 83 = true ∨ valuation q 84 = true ∨ valuation q 958 = true := counterClause1032 (baseVal q)

theorem counterClause1033 (q : Nat → Bool) : valuationOf q 90 = true ∨ valuationOf q 959 = true := by
  have hs : count959 q = (countLit q [-87]) + (countLit q [-90]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-90])
  have hm := merge_right (literal (valuationOf q) (-90)) (literal (valuationOf q) (959)) (countLit q [-87]) (countLit q [-90]) (count959 q) 1 (meaningNeg90 q) (meaning959 q) hs
  change (! (valuationOf q 90)) = false ∨ valuationOf q 959 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1033 (q : Snake 81) (h : Conditions q) : valuation q 90 = true ∨ valuation q 959 = true := counterClause1033 (baseVal q)

theorem counterClause1034 (q : Nat → Bool) : valuationOf q 87 = true ∨ valuationOf q 959 = true := by
  have hs : count959 q = (countLit q [-87]) + (countLit q [-90]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-90])
  have hm := merge_left (literal (valuationOf q) (-87)) (literal (valuationOf q) (959)) (countLit q [-87]) (countLit q [-90]) (count959 q) 1 (meaningNeg87 q) (meaning959 q) hs
  change (! (valuationOf q 87)) = false ∨ valuationOf q 959 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1034 (q : Snake 81) (h : Conditions q) : valuation q 87 = true ∨ valuation q 959 = true := counterClause1034 (baseVal q)

theorem counterClause1035 (q : Nat → Bool) : valuationOf q 87 = true ∨ valuationOf q 90 = true ∨ valuationOf q 960 = true := by
  have hs : count959 q = (countLit q [-87]) + (countLit q [-90]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-90])
  have hm := merge_two (literal (valuationOf q) (-87)) (literal (valuationOf q) (-90)) (literal (valuationOf q) (960)) (countLit q [-87]) (countLit q [-90]) (count959 q) 1 1 (meaningNeg87 q) (meaningNeg90 q) (meaning960 q) hs
  change (! (valuationOf q 87)) = false ∨ (! (valuationOf q 90)) = false ∨ valuationOf q 960 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1035 (q : Snake 81) (h : Conditions q) : valuation q 87 = true ∨ valuation q 90 = true ∨ valuation q 960 = true := counterClause1035 (baseVal q)

theorem counterClause1036 (q : Nat → Bool) : valuationOf q 959 = false ∨ valuationOf q 961 = true := by
  have hs : count961 q = (countLit q [-83, -84]) + (countLit q [-87, -90]) := List.countP_append (p := literal q) (l₁ := [-83, -84]) (l₂ := [-87, -90])
  have hm := merge_right (literal (valuationOf q) (959)) (literal (valuationOf q) (961)) (countLit q [-83, -84]) (countLit q [-87, -90]) (count961 q) 1 (meaning959 q) (meaning961 q) hs
  change valuationOf q 959 = false ∨ valuationOf q 961 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1036 (q : Snake 81) (h : Conditions q) : valuation q 959 = false ∨ valuation q 961 = true := counterClause1036 (baseVal q)

theorem counterClause1037 (q : Nat → Bool) : valuationOf q 960 = false ∨ valuationOf q 962 = true := by
  have hs : count961 q = (countLit q [-83, -84]) + (countLit q [-87, -90]) := List.countP_append (p := literal q) (l₁ := [-83, -84]) (l₂ := [-87, -90])
  have hm := merge_right (literal (valuationOf q) (960)) (literal (valuationOf q) (962)) (countLit q [-83, -84]) (countLit q [-87, -90]) (count961 q) 2 (meaning960 q) (meaning962 q) hs
  change valuationOf q 960 = false ∨ valuationOf q 962 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1037 (q : Snake 81) (h : Conditions q) : valuation q 960 = false ∨ valuation q 962 = true := counterClause1037 (baseVal q)

theorem counterClause1038 (q : Nat → Bool) : valuationOf q 957 = false ∨ valuationOf q 961 = true := by
  have hs : count961 q = (countLit q [-83, -84]) + (countLit q [-87, -90]) := List.countP_append (p := literal q) (l₁ := [-83, -84]) (l₂ := [-87, -90])
  have hm := merge_left (literal (valuationOf q) (957)) (literal (valuationOf q) (961)) (countLit q [-83, -84]) (countLit q [-87, -90]) (count961 q) 1 (meaning957 q) (meaning961 q) hs
  change valuationOf q 957 = false ∨ valuationOf q 961 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1038 (q : Snake 81) (h : Conditions q) : valuation q 957 = false ∨ valuation q 961 = true := counterClause1038 (baseVal q)

theorem counterClause1039 (q : Nat → Bool) : valuationOf q 957 = false ∨ valuationOf q 959 = false ∨ valuationOf q 962 = true := by
  have hs : count961 q = (countLit q [-83, -84]) + (countLit q [-87, -90]) := List.countP_append (p := literal q) (l₁ := [-83, -84]) (l₂ := [-87, -90])
  have hm := merge_two (literal (valuationOf q) (957)) (literal (valuationOf q) (959)) (literal (valuationOf q) (962)) (countLit q [-83, -84]) (countLit q [-87, -90]) (count961 q) 1 1 (meaning957 q) (meaning959 q) (meaning962 q) hs
  change valuationOf q 957 = false ∨ valuationOf q 959 = false ∨ valuationOf q 962 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1039 (q : Snake 81) (h : Conditions q) : valuation q 957 = false ∨ valuation q 959 = false ∨ valuation q 962 = true := counterClause1039 (baseVal q)

theorem counterClause1040 (q : Nat → Bool) : valuationOf q 958 = false ∨ valuationOf q 962 = true := by
  have hs : count961 q = (countLit q [-83, -84]) + (countLit q [-87, -90]) := List.countP_append (p := literal q) (l₁ := [-83, -84]) (l₂ := [-87, -90])
  have hm := merge_left (literal (valuationOf q) (958)) (literal (valuationOf q) (962)) (countLit q [-83, -84]) (countLit q [-87, -90]) (count961 q) 2 (meaning958 q) (meaning962 q) hs
  change valuationOf q 958 = false ∨ valuationOf q 962 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1040 (q : Snake 81) (h : Conditions q) : valuation q 958 = false ∨ valuation q 962 = true := counterClause1040 (baseVal q)

theorem counterClause1041 (q : Nat → Bool) : valuationOf q 958 = false ∨ valuationOf q 959 = false ∨ valuationOf q 963 = true := by
  have hs : count961 q = (countLit q [-83, -84]) + (countLit q [-87, -90]) := List.countP_append (p := literal q) (l₁ := [-83, -84]) (l₂ := [-87, -90])
  have hm := merge_two (literal (valuationOf q) (958)) (literal (valuationOf q) (959)) (literal (valuationOf q) (963)) (countLit q [-83, -84]) (countLit q [-87, -90]) (count961 q) 2 1 (meaning958 q) (meaning959 q) (meaning963 q) hs
  change valuationOf q 958 = false ∨ valuationOf q 959 = false ∨ valuationOf q 963 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1041 (q : Snake 81) (h : Conditions q) : valuation q 958 = false ∨ valuation q 959 = false ∨ valuation q 963 = true := counterClause1041 (baseVal q)

theorem counterClause1042 (q : Nat → Bool) : valuationOf q 961 = false ∨ valuationOf q 965 = true := by
  have hs : count965 q = (countLit q [-74, -76, -79, -81]) + (countLit q [-83, -84, -87, -90]) := List.countP_append (p := literal q) (l₁ := [-74, -76, -79, -81]) (l₂ := [-83, -84, -87, -90])
  have hm := merge_right (literal (valuationOf q) (961)) (literal (valuationOf q) (965)) (countLit q [-74, -76, -79, -81]) (countLit q [-83, -84, -87, -90]) (count965 q) 1 (meaning961 q) (meaning965 q) hs
  change valuationOf q 961 = false ∨ valuationOf q 965 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1042 (q : Snake 81) (h : Conditions q) : valuation q 961 = false ∨ valuation q 965 = true := counterClause1042 (baseVal q)

theorem counterClause1043 (q : Nat → Bool) : valuationOf q 962 = false ∨ valuationOf q 966 = true := by
  have hs : count965 q = (countLit q [-74, -76, -79, -81]) + (countLit q [-83, -84, -87, -90]) := List.countP_append (p := literal q) (l₁ := [-74, -76, -79, -81]) (l₂ := [-83, -84, -87, -90])
  have hm := merge_right (literal (valuationOf q) (962)) (literal (valuationOf q) (966)) (countLit q [-74, -76, -79, -81]) (countLit q [-83, -84, -87, -90]) (count965 q) 2 (meaning962 q) (meaning966 q) hs
  change valuationOf q 962 = false ∨ valuationOf q 966 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1043 (q : Snake 81) (h : Conditions q) : valuation q 962 = false ∨ valuation q 966 = true := counterClause1043 (baseVal q)

theorem counterClause1044 (q : Nat → Bool) : valuationOf q 963 = false ∨ valuationOf q 967 = true := by
  have hs : count965 q = (countLit q [-74, -76, -79, -81]) + (countLit q [-83, -84, -87, -90]) := List.countP_append (p := literal q) (l₁ := [-74, -76, -79, -81]) (l₂ := [-83, -84, -87, -90])
  have hm := merge_right (literal (valuationOf q) (963)) (literal (valuationOf q) (967)) (countLit q [-74, -76, -79, -81]) (countLit q [-83, -84, -87, -90]) (count965 q) 3 (meaning963 q) (meaning967 q) hs
  change valuationOf q 963 = false ∨ valuationOf q 967 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1044 (q : Snake 81) (h : Conditions q) : valuation q 963 = false ∨ valuation q 967 = true := counterClause1044 (baseVal q)

theorem counterClause1045 (q : Nat → Bool) : valuationOf q 953 = false ∨ valuationOf q 965 = true := by
  have hs : count965 q = (countLit q [-74, -76, -79, -81]) + (countLit q [-83, -84, -87, -90]) := List.countP_append (p := literal q) (l₁ := [-74, -76, -79, -81]) (l₂ := [-83, -84, -87, -90])
  have hm := merge_left (literal (valuationOf q) (953)) (literal (valuationOf q) (965)) (countLit q [-74, -76, -79, -81]) (countLit q [-83, -84, -87, -90]) (count965 q) 1 (meaning953 q) (meaning965 q) hs
  change valuationOf q 953 = false ∨ valuationOf q 965 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1045 (q : Snake 81) (h : Conditions q) : valuation q 953 = false ∨ valuation q 965 = true := counterClause1045 (baseVal q)

theorem counterClause1046 (q : Nat → Bool) : valuationOf q 953 = false ∨ valuationOf q 961 = false ∨ valuationOf q 966 = true := by
  have hs : count965 q = (countLit q [-74, -76, -79, -81]) + (countLit q [-83, -84, -87, -90]) := List.countP_append (p := literal q) (l₁ := [-74, -76, -79, -81]) (l₂ := [-83, -84, -87, -90])
  have hm := merge_two (literal (valuationOf q) (953)) (literal (valuationOf q) (961)) (literal (valuationOf q) (966)) (countLit q [-74, -76, -79, -81]) (countLit q [-83, -84, -87, -90]) (count965 q) 1 1 (meaning953 q) (meaning961 q) (meaning966 q) hs
  change valuationOf q 953 = false ∨ valuationOf q 961 = false ∨ valuationOf q 966 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1046 (q : Snake 81) (h : Conditions q) : valuation q 953 = false ∨ valuation q 961 = false ∨ valuation q 966 = true := counterClause1046 (baseVal q)

theorem counterClause1047 (q : Nat → Bool) : valuationOf q 953 = false ∨ valuationOf q 962 = false ∨ valuationOf q 967 = true := by
  have hs : count965 q = (countLit q [-74, -76, -79, -81]) + (countLit q [-83, -84, -87, -90]) := List.countP_append (p := literal q) (l₁ := [-74, -76, -79, -81]) (l₂ := [-83, -84, -87, -90])
  have hm := merge_two (literal (valuationOf q) (953)) (literal (valuationOf q) (962)) (literal (valuationOf q) (967)) (countLit q [-74, -76, -79, -81]) (countLit q [-83, -84, -87, -90]) (count965 q) 1 2 (meaning953 q) (meaning962 q) (meaning967 q) hs
  change valuationOf q 953 = false ∨ valuationOf q 962 = false ∨ valuationOf q 967 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1047 (q : Snake 81) (h : Conditions q) : valuation q 953 = false ∨ valuation q 962 = false ∨ valuation q 967 = true := counterClause1047 (baseVal q)

theorem counterClause1048 (q : Nat → Bool) : valuationOf q 953 = false ∨ valuationOf q 963 = false ∨ valuationOf q 968 = true := by
  have hs : count965 q = (countLit q [-74, -76, -79, -81]) + (countLit q [-83, -84, -87, -90]) := List.countP_append (p := literal q) (l₁ := [-74, -76, -79, -81]) (l₂ := [-83, -84, -87, -90])
  have hm := merge_two (literal (valuationOf q) (953)) (literal (valuationOf q) (963)) (literal (valuationOf q) (968)) (countLit q [-74, -76, -79, -81]) (countLit q [-83, -84, -87, -90]) (count965 q) 1 3 (meaning953 q) (meaning963 q) (meaning968 q) hs
  change valuationOf q 953 = false ∨ valuationOf q 963 = false ∨ valuationOf q 968 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1048 (q : Snake 81) (h : Conditions q) : valuation q 953 = false ∨ valuation q 963 = false ∨ valuation q 968 = true := counterClause1048 (baseVal q)

theorem counterClause1049 (q : Nat → Bool) : valuationOf q 954 = false ∨ valuationOf q 966 = true := by
  have hs : count965 q = (countLit q [-74, -76, -79, -81]) + (countLit q [-83, -84, -87, -90]) := List.countP_append (p := literal q) (l₁ := [-74, -76, -79, -81]) (l₂ := [-83, -84, -87, -90])
  have hm := merge_left (literal (valuationOf q) (954)) (literal (valuationOf q) (966)) (countLit q [-74, -76, -79, -81]) (countLit q [-83, -84, -87, -90]) (count965 q) 2 (meaning954 q) (meaning966 q) hs
  change valuationOf q 954 = false ∨ valuationOf q 966 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1049 (q : Snake 81) (h : Conditions q) : valuation q 954 = false ∨ valuation q 966 = true := counterClause1049 (baseVal q)

theorem counterClause1050 (q : Nat → Bool) : valuationOf q 954 = false ∨ valuationOf q 961 = false ∨ valuationOf q 967 = true := by
  have hs : count965 q = (countLit q [-74, -76, -79, -81]) + (countLit q [-83, -84, -87, -90]) := List.countP_append (p := literal q) (l₁ := [-74, -76, -79, -81]) (l₂ := [-83, -84, -87, -90])
  have hm := merge_two (literal (valuationOf q) (954)) (literal (valuationOf q) (961)) (literal (valuationOf q) (967)) (countLit q [-74, -76, -79, -81]) (countLit q [-83, -84, -87, -90]) (count965 q) 2 1 (meaning954 q) (meaning961 q) (meaning967 q) hs
  change valuationOf q 954 = false ∨ valuationOf q 961 = false ∨ valuationOf q 967 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1050 (q : Snake 81) (h : Conditions q) : valuation q 954 = false ∨ valuation q 961 = false ∨ valuation q 967 = true := counterClause1050 (baseVal q)

theorem counterClause1051 (q : Nat → Bool) : valuationOf q 954 = false ∨ valuationOf q 962 = false ∨ valuationOf q 968 = true := by
  have hs : count965 q = (countLit q [-74, -76, -79, -81]) + (countLit q [-83, -84, -87, -90]) := List.countP_append (p := literal q) (l₁ := [-74, -76, -79, -81]) (l₂ := [-83, -84, -87, -90])
  have hm := merge_two (literal (valuationOf q) (954)) (literal (valuationOf q) (962)) (literal (valuationOf q) (968)) (countLit q [-74, -76, -79, -81]) (countLit q [-83, -84, -87, -90]) (count965 q) 2 2 (meaning954 q) (meaning962 q) (meaning968 q) hs
  change valuationOf q 954 = false ∨ valuationOf q 962 = false ∨ valuationOf q 968 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1051 (q : Snake 81) (h : Conditions q) : valuation q 954 = false ∨ valuation q 962 = false ∨ valuation q 968 = true := counterClause1051 (baseVal q)

theorem counterClause1052 (q : Nat → Bool) : valuationOf q 955 = false ∨ valuationOf q 967 = true := by
  have hs : count965 q = (countLit q [-74, -76, -79, -81]) + (countLit q [-83, -84, -87, -90]) := List.countP_append (p := literal q) (l₁ := [-74, -76, -79, -81]) (l₂ := [-83, -84, -87, -90])
  have hm := merge_left (literal (valuationOf q) (955)) (literal (valuationOf q) (967)) (countLit q [-74, -76, -79, -81]) (countLit q [-83, -84, -87, -90]) (count965 q) 3 (meaning955 q) (meaning967 q) hs
  change valuationOf q 955 = false ∨ valuationOf q 967 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1052 (q : Snake 81) (h : Conditions q) : valuation q 955 = false ∨ valuation q 967 = true := counterClause1052 (baseVal q)

theorem counterClause1053 (q : Nat → Bool) : valuationOf q 965 = false ∨ valuationOf q 973 = true := by
  have hs : count973 q = (countLit q [-59, -62, -64, -66, -69, -72, -73]) + (countLit q [-74, -76, -79, -81, -83, -84, -87, -90]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -64, -66, -69, -72, -73]) (l₂ := [-74, -76, -79, -81, -83, -84, -87, -90])
  have hm := merge_right (literal (valuationOf q) (965)) (literal (valuationOf q) (973)) (countLit q [-59, -62, -64, -66, -69, -72, -73]) (countLit q [-74, -76, -79, -81, -83, -84, -87, -90]) (count973 q) 1 (meaning965 q) (meaning973 q) hs
  change valuationOf q 965 = false ∨ valuationOf q 973 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1053 (q : Snake 81) (h : Conditions q) : valuation q 965 = false ∨ valuation q 973 = true := counterClause1053 (baseVal q)

theorem counterClause1054 (q : Nat → Bool) : valuationOf q 966 = false ∨ valuationOf q 974 = true := by
  have hs : count973 q = (countLit q [-59, -62, -64, -66, -69, -72, -73]) + (countLit q [-74, -76, -79, -81, -83, -84, -87, -90]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -64, -66, -69, -72, -73]) (l₂ := [-74, -76, -79, -81, -83, -84, -87, -90])
  have hm := merge_right (literal (valuationOf q) (966)) (literal (valuationOf q) (974)) (countLit q [-59, -62, -64, -66, -69, -72, -73]) (countLit q [-74, -76, -79, -81, -83, -84, -87, -90]) (count973 q) 2 (meaning966 q) (meaning974 q) hs
  change valuationOf q 966 = false ∨ valuationOf q 974 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1054 (q : Snake 81) (h : Conditions q) : valuation q 966 = false ∨ valuation q 974 = true := counterClause1054 (baseVal q)

theorem counterClause1055 (q : Nat → Bool) : valuationOf q 967 = false ∨ valuationOf q 975 = true := by
  have hs : count973 q = (countLit q [-59, -62, -64, -66, -69, -72, -73]) + (countLit q [-74, -76, -79, -81, -83, -84, -87, -90]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -64, -66, -69, -72, -73]) (l₂ := [-74, -76, -79, -81, -83, -84, -87, -90])
  have hm := merge_right (literal (valuationOf q) (967)) (literal (valuationOf q) (975)) (countLit q [-59, -62, -64, -66, -69, -72, -73]) (countLit q [-74, -76, -79, -81, -83, -84, -87, -90]) (count973 q) 3 (meaning967 q) (meaning975 q) hs
  change valuationOf q 967 = false ∨ valuationOf q 975 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1055 (q : Snake 81) (h : Conditions q) : valuation q 967 = false ∨ valuation q 975 = true := counterClause1055 (baseVal q)

theorem counterClause1056 (q : Nat → Bool) : valuationOf q 942 = false ∨ valuationOf q 973 = true := by
  have hs : count973 q = (countLit q [-59, -62, -64, -66, -69, -72, -73]) + (countLit q [-74, -76, -79, -81, -83, -84, -87, -90]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -64, -66, -69, -72, -73]) (l₂ := [-74, -76, -79, -81, -83, -84, -87, -90])
  have hm := merge_left (literal (valuationOf q) (942)) (literal (valuationOf q) (973)) (countLit q [-59, -62, -64, -66, -69, -72, -73]) (countLit q [-74, -76, -79, -81, -83, -84, -87, -90]) (count973 q) 1 (meaning942 q) (meaning973 q) hs
  change valuationOf q 942 = false ∨ valuationOf q 973 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1056 (q : Snake 81) (h : Conditions q) : valuation q 942 = false ∨ valuation q 973 = true := counterClause1056 (baseVal q)

theorem block32 (q : Snake 81) (h : Conditions q) : B112E213.Block32 (valuation q) :=
  ⟨clause1025 q h, clause1026 q h, clause1027 q h, clause1028 q h, clause1029 q h, clause1030 q h, clause1031 q h, clause1032 q h, clause1033 q h, clause1034 q h, clause1035 q h, clause1036 q h, clause1037 q h, clause1038 q h, clause1039 q h, clause1040 q h, clause1041 q h, clause1042 q h, clause1043 q h, clause1044 q h, clause1045 q h, clause1046 q h, clause1047 q h, clause1048 q h, clause1049 q h, clause1050 q h, clause1051 q h, clause1052 q h, clause1053 q h, clause1054 q h, clause1055 q h, clause1056 q h⟩

end
end Snake9.Regrowth.E112213
