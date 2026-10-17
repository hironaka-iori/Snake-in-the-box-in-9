import E112153Semantics
import B112E153Inputs
namespace Snake9.Regrowth.E112153
noncomputable section
local instance blockDec35 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1121 (q : Nat → Bool) : valuationOf q 87 = true ∨ valuationOf q 1016 = true := by
  have hs : count1016 q = (countLit q [-87]) + (countLit q [-88]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-88])
  have hm := merge_left (literal (valuationOf q) (-87)) (literal (valuationOf q) (1016)) (countLit q [-87]) (countLit q [-88]) (count1016 q) 1 (meaningNeg87 q) (meaning1016 q) hs
  change (! (valuationOf q 87)) = false ∨ valuationOf q 1016 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1121 (q : Snake 81) (h : Conditions q) : valuation q 87 = true ∨ valuation q 1016 = true := counterClause1121 (baseVal q)

theorem counterClause1122 (q : Nat → Bool) : valuationOf q 87 = true ∨ valuationOf q 88 = true ∨ valuationOf q 1017 = true := by
  have hs : count1016 q = (countLit q [-87]) + (countLit q [-88]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-88])
  have hm := merge_two (literal (valuationOf q) (-87)) (literal (valuationOf q) (-88)) (literal (valuationOf q) (1017)) (countLit q [-87]) (countLit q [-88]) (count1016 q) 1 1 (meaningNeg87 q) (meaningNeg88 q) (meaning1017 q) hs
  change (! (valuationOf q 87)) = false ∨ (! (valuationOf q 88)) = false ∨ valuationOf q 1017 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1122 (q : Snake 81) (h : Conditions q) : valuation q 87 = true ∨ valuation q 88 = true ∨ valuation q 1017 = true := counterClause1122 (baseVal q)

theorem counterClause1123 (q : Nat → Bool) : valuationOf q 93 = true ∨ valuationOf q 1018 = true := by
  have hs : count1018 q = (countLit q [-91]) + (countLit q [-93]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-93])
  have hm := merge_right (literal (valuationOf q) (-93)) (literal (valuationOf q) (1018)) (countLit q [-91]) (countLit q [-93]) (count1018 q) 1 (meaningNeg93 q) (meaning1018 q) hs
  change (! (valuationOf q 93)) = false ∨ valuationOf q 1018 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1123 (q : Snake 81) (h : Conditions q) : valuation q 93 = true ∨ valuation q 1018 = true := counterClause1123 (baseVal q)

theorem counterClause1124 (q : Nat → Bool) : valuationOf q 91 = true ∨ valuationOf q 1018 = true := by
  have hs : count1018 q = (countLit q [-91]) + (countLit q [-93]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-93])
  have hm := merge_left (literal (valuationOf q) (-91)) (literal (valuationOf q) (1018)) (countLit q [-91]) (countLit q [-93]) (count1018 q) 1 (meaningNeg91 q) (meaning1018 q) hs
  change (! (valuationOf q 91)) = false ∨ valuationOf q 1018 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1124 (q : Snake 81) (h : Conditions q) : valuation q 91 = true ∨ valuation q 1018 = true := counterClause1124 (baseVal q)

theorem counterClause1125 (q : Nat → Bool) : valuationOf q 91 = true ∨ valuationOf q 93 = true ∨ valuationOf q 1019 = true := by
  have hs : count1018 q = (countLit q [-91]) + (countLit q [-93]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-93])
  have hm := merge_two (literal (valuationOf q) (-91)) (literal (valuationOf q) (-93)) (literal (valuationOf q) (1019)) (countLit q [-91]) (countLit q [-93]) (count1018 q) 1 1 (meaningNeg91 q) (meaningNeg93 q) (meaning1019 q) hs
  change (! (valuationOf q 91)) = false ∨ (! (valuationOf q 93)) = false ∨ valuationOf q 1019 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1125 (q : Snake 81) (h : Conditions q) : valuation q 91 = true ∨ valuation q 93 = true ∨ valuation q 1019 = true := counterClause1125 (baseVal q)

theorem counterClause1126 (q : Nat → Bool) : valuationOf q 1018 = false ∨ valuationOf q 1020 = true := by
  have hs : count1020 q = (countLit q [-87, -88]) + (countLit q [-91, -93]) := List.countP_append (p := literal q) (l₁ := [-87, -88]) (l₂ := [-91, -93])
  have hm := merge_right (literal (valuationOf q) (1018)) (literal (valuationOf q) (1020)) (countLit q [-87, -88]) (countLit q [-91, -93]) (count1020 q) 1 (meaning1018 q) (meaning1020 q) hs
  change valuationOf q 1018 = false ∨ valuationOf q 1020 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1126 (q : Snake 81) (h : Conditions q) : valuation q 1018 = false ∨ valuation q 1020 = true := counterClause1126 (baseVal q)

theorem counterClause1127 (q : Nat → Bool) : valuationOf q 1019 = false ∨ valuationOf q 1021 = true := by
  have hs : count1020 q = (countLit q [-87, -88]) + (countLit q [-91, -93]) := List.countP_append (p := literal q) (l₁ := [-87, -88]) (l₂ := [-91, -93])
  have hm := merge_right (literal (valuationOf q) (1019)) (literal (valuationOf q) (1021)) (countLit q [-87, -88]) (countLit q [-91, -93]) (count1020 q) 2 (meaning1019 q) (meaning1021 q) hs
  change valuationOf q 1019 = false ∨ valuationOf q 1021 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1127 (q : Snake 81) (h : Conditions q) : valuation q 1019 = false ∨ valuation q 1021 = true := counterClause1127 (baseVal q)

theorem counterClause1128 (q : Nat → Bool) : valuationOf q 1016 = false ∨ valuationOf q 1020 = true := by
  have hs : count1020 q = (countLit q [-87, -88]) + (countLit q [-91, -93]) := List.countP_append (p := literal q) (l₁ := [-87, -88]) (l₂ := [-91, -93])
  have hm := merge_left (literal (valuationOf q) (1016)) (literal (valuationOf q) (1020)) (countLit q [-87, -88]) (countLit q [-91, -93]) (count1020 q) 1 (meaning1016 q) (meaning1020 q) hs
  change valuationOf q 1016 = false ∨ valuationOf q 1020 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1128 (q : Snake 81) (h : Conditions q) : valuation q 1016 = false ∨ valuation q 1020 = true := counterClause1128 (baseVal q)

theorem counterClause1129 (q : Nat → Bool) : valuationOf q 1016 = false ∨ valuationOf q 1018 = false ∨ valuationOf q 1021 = true := by
  have hs : count1020 q = (countLit q [-87, -88]) + (countLit q [-91, -93]) := List.countP_append (p := literal q) (l₁ := [-87, -88]) (l₂ := [-91, -93])
  have hm := merge_two (literal (valuationOf q) (1016)) (literal (valuationOf q) (1018)) (literal (valuationOf q) (1021)) (countLit q [-87, -88]) (countLit q [-91, -93]) (count1020 q) 1 1 (meaning1016 q) (meaning1018 q) (meaning1021 q) hs
  change valuationOf q 1016 = false ∨ valuationOf q 1018 = false ∨ valuationOf q 1021 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1129 (q : Snake 81) (h : Conditions q) : valuation q 1016 = false ∨ valuation q 1018 = false ∨ valuation q 1021 = true := counterClause1129 (baseVal q)

theorem counterClause1130 (q : Nat → Bool) : valuationOf q 1016 = false ∨ valuationOf q 1019 = false ∨ valuationOf q 1022 = true := by
  have hs : count1020 q = (countLit q [-87, -88]) + (countLit q [-91, -93]) := List.countP_append (p := literal q) (l₁ := [-87, -88]) (l₂ := [-91, -93])
  have hm := merge_two (literal (valuationOf q) (1016)) (literal (valuationOf q) (1019)) (literal (valuationOf q) (1022)) (countLit q [-87, -88]) (countLit q [-91, -93]) (count1020 q) 1 2 (meaning1016 q) (meaning1019 q) (meaning1022 q) hs
  change valuationOf q 1016 = false ∨ valuationOf q 1019 = false ∨ valuationOf q 1022 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1130 (q : Snake 81) (h : Conditions q) : valuation q 1016 = false ∨ valuation q 1019 = false ∨ valuation q 1022 = true := counterClause1130 (baseVal q)

theorem counterClause1131 (q : Nat → Bool) : valuationOf q 1017 = false ∨ valuationOf q 1021 = true := by
  have hs : count1020 q = (countLit q [-87, -88]) + (countLit q [-91, -93]) := List.countP_append (p := literal q) (l₁ := [-87, -88]) (l₂ := [-91, -93])
  have hm := merge_left (literal (valuationOf q) (1017)) (literal (valuationOf q) (1021)) (countLit q [-87, -88]) (countLit q [-91, -93]) (count1020 q) 2 (meaning1017 q) (meaning1021 q) hs
  change valuationOf q 1017 = false ∨ valuationOf q 1021 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1131 (q : Snake 81) (h : Conditions q) : valuation q 1017 = false ∨ valuation q 1021 = true := counterClause1131 (baseVal q)

theorem counterClause1132 (q : Nat → Bool) : valuationOf q 1017 = false ∨ valuationOf q 1018 = false ∨ valuationOf q 1022 = true := by
  have hs : count1020 q = (countLit q [-87, -88]) + (countLit q [-91, -93]) := List.countP_append (p := literal q) (l₁ := [-87, -88]) (l₂ := [-91, -93])
  have hm := merge_two (literal (valuationOf q) (1017)) (literal (valuationOf q) (1018)) (literal (valuationOf q) (1022)) (countLit q [-87, -88]) (countLit q [-91, -93]) (count1020 q) 2 1 (meaning1017 q) (meaning1018 q) (meaning1022 q) hs
  change valuationOf q 1017 = false ∨ valuationOf q 1018 = false ∨ valuationOf q 1022 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1132 (q : Snake 81) (h : Conditions q) : valuation q 1017 = false ∨ valuation q 1018 = false ∨ valuation q 1022 = true := counterClause1132 (baseVal q)

theorem counterClause1133 (q : Nat → Bool) : valuationOf q 1017 = false ∨ valuationOf q 1019 = false ∨ valuationOf q 1023 = true := by
  have hs : count1020 q = (countLit q [-87, -88]) + (countLit q [-91, -93]) := List.countP_append (p := literal q) (l₁ := [-87, -88]) (l₂ := [-91, -93])
  have hm := merge_two (literal (valuationOf q) (1017)) (literal (valuationOf q) (1019)) (literal (valuationOf q) (1023)) (countLit q [-87, -88]) (countLit q [-91, -93]) (count1020 q) 2 2 (meaning1017 q) (meaning1019 q) (meaning1023 q) hs
  change valuationOf q 1017 = false ∨ valuationOf q 1019 = false ∨ valuationOf q 1023 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1133 (q : Snake 81) (h : Conditions q) : valuation q 1017 = false ∨ valuation q 1019 = false ∨ valuation q 1023 = true := counterClause1133 (baseVal q)

theorem counterClause1134 (q : Nat → Bool) : valuationOf q 1020 = false ∨ valuationOf q 1024 = true := by
  have hs : count1024 q = (countLit q [-80, -81, -82, -86]) + (countLit q [-87, -88, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-80, -81, -82, -86]) (l₂ := [-87, -88, -91, -93])
  have hm := merge_right (literal (valuationOf q) (1020)) (literal (valuationOf q) (1024)) (countLit q [-80, -81, -82, -86]) (countLit q [-87, -88, -91, -93]) (count1024 q) 1 (meaning1020 q) (meaning1024 q) hs
  change valuationOf q 1020 = false ∨ valuationOf q 1024 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1134 (q : Snake 81) (h : Conditions q) : valuation q 1020 = false ∨ valuation q 1024 = true := counterClause1134 (baseVal q)

theorem counterClause1135 (q : Nat → Bool) : valuationOf q 1021 = false ∨ valuationOf q 1025 = true := by
  have hs : count1024 q = (countLit q [-80, -81, -82, -86]) + (countLit q [-87, -88, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-80, -81, -82, -86]) (l₂ := [-87, -88, -91, -93])
  have hm := merge_right (literal (valuationOf q) (1021)) (literal (valuationOf q) (1025)) (countLit q [-80, -81, -82, -86]) (countLit q [-87, -88, -91, -93]) (count1024 q) 2 (meaning1021 q) (meaning1025 q) hs
  change valuationOf q 1021 = false ∨ valuationOf q 1025 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1135 (q : Snake 81) (h : Conditions q) : valuation q 1021 = false ∨ valuation q 1025 = true := counterClause1135 (baseVal q)

theorem counterClause1136 (q : Nat → Bool) : valuationOf q 1022 = false ∨ valuationOf q 1026 = true := by
  have hs : count1024 q = (countLit q [-80, -81, -82, -86]) + (countLit q [-87, -88, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-80, -81, -82, -86]) (l₂ := [-87, -88, -91, -93])
  have hm := merge_right (literal (valuationOf q) (1022)) (literal (valuationOf q) (1026)) (countLit q [-80, -81, -82, -86]) (countLit q [-87, -88, -91, -93]) (count1024 q) 3 (meaning1022 q) (meaning1026 q) hs
  change valuationOf q 1022 = false ∨ valuationOf q 1026 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1136 (q : Snake 81) (h : Conditions q) : valuation q 1022 = false ∨ valuation q 1026 = true := counterClause1136 (baseVal q)

theorem counterClause1137 (q : Nat → Bool) : valuationOf q 1023 = false ∨ valuationOf q 1027 = true := by
  have hs : count1024 q = (countLit q [-80, -81, -82, -86]) + (countLit q [-87, -88, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-80, -81, -82, -86]) (l₂ := [-87, -88, -91, -93])
  have hm := merge_right (literal (valuationOf q) (1023)) (literal (valuationOf q) (1027)) (countLit q [-80, -81, -82, -86]) (countLit q [-87, -88, -91, -93]) (count1024 q) 4 (meaning1023 q) (meaning1027 q) hs
  change valuationOf q 1023 = false ∨ valuationOf q 1027 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1137 (q : Snake 81) (h : Conditions q) : valuation q 1023 = false ∨ valuation q 1027 = true := counterClause1137 (baseVal q)

theorem counterClause1138 (q : Nat → Bool) : valuationOf q 1012 = false ∨ valuationOf q 1024 = true := by
  have hs : count1024 q = (countLit q [-80, -81, -82, -86]) + (countLit q [-87, -88, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-80, -81, -82, -86]) (l₂ := [-87, -88, -91, -93])
  have hm := merge_left (literal (valuationOf q) (1012)) (literal (valuationOf q) (1024)) (countLit q [-80, -81, -82, -86]) (countLit q [-87, -88, -91, -93]) (count1024 q) 1 (meaning1012 q) (meaning1024 q) hs
  change valuationOf q 1012 = false ∨ valuationOf q 1024 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1138 (q : Snake 81) (h : Conditions q) : valuation q 1012 = false ∨ valuation q 1024 = true := counterClause1138 (baseVal q)

theorem counterClause1139 (q : Nat → Bool) : valuationOf q 1012 = false ∨ valuationOf q 1020 = false ∨ valuationOf q 1025 = true := by
  have hs : count1024 q = (countLit q [-80, -81, -82, -86]) + (countLit q [-87, -88, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-80, -81, -82, -86]) (l₂ := [-87, -88, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1012)) (literal (valuationOf q) (1020)) (literal (valuationOf q) (1025)) (countLit q [-80, -81, -82, -86]) (countLit q [-87, -88, -91, -93]) (count1024 q) 1 1 (meaning1012 q) (meaning1020 q) (meaning1025 q) hs
  change valuationOf q 1012 = false ∨ valuationOf q 1020 = false ∨ valuationOf q 1025 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1139 (q : Snake 81) (h : Conditions q) : valuation q 1012 = false ∨ valuation q 1020 = false ∨ valuation q 1025 = true := counterClause1139 (baseVal q)

theorem counterClause1140 (q : Nat → Bool) : valuationOf q 1012 = false ∨ valuationOf q 1021 = false ∨ valuationOf q 1026 = true := by
  have hs : count1024 q = (countLit q [-80, -81, -82, -86]) + (countLit q [-87, -88, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-80, -81, -82, -86]) (l₂ := [-87, -88, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1012)) (literal (valuationOf q) (1021)) (literal (valuationOf q) (1026)) (countLit q [-80, -81, -82, -86]) (countLit q [-87, -88, -91, -93]) (count1024 q) 1 2 (meaning1012 q) (meaning1021 q) (meaning1026 q) hs
  change valuationOf q 1012 = false ∨ valuationOf q 1021 = false ∨ valuationOf q 1026 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1140 (q : Snake 81) (h : Conditions q) : valuation q 1012 = false ∨ valuation q 1021 = false ∨ valuation q 1026 = true := counterClause1140 (baseVal q)

theorem counterClause1141 (q : Nat → Bool) : valuationOf q 1012 = false ∨ valuationOf q 1022 = false ∨ valuationOf q 1027 = true := by
  have hs : count1024 q = (countLit q [-80, -81, -82, -86]) + (countLit q [-87, -88, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-80, -81, -82, -86]) (l₂ := [-87, -88, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1012)) (literal (valuationOf q) (1022)) (literal (valuationOf q) (1027)) (countLit q [-80, -81, -82, -86]) (countLit q [-87, -88, -91, -93]) (count1024 q) 1 3 (meaning1012 q) (meaning1022 q) (meaning1027 q) hs
  change valuationOf q 1012 = false ∨ valuationOf q 1022 = false ∨ valuationOf q 1027 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1141 (q : Snake 81) (h : Conditions q) : valuation q 1012 = false ∨ valuation q 1022 = false ∨ valuation q 1027 = true := counterClause1141 (baseVal q)

theorem counterClause1142 (q : Nat → Bool) : valuationOf q 1012 = false ∨ valuationOf q 1023 = false ∨ valuationOf q 1028 = true := by
  have hs : count1024 q = (countLit q [-80, -81, -82, -86]) + (countLit q [-87, -88, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-80, -81, -82, -86]) (l₂ := [-87, -88, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1012)) (literal (valuationOf q) (1023)) (literal (valuationOf q) (1028)) (countLit q [-80, -81, -82, -86]) (countLit q [-87, -88, -91, -93]) (count1024 q) 1 4 (meaning1012 q) (meaning1023 q) (meaning1028 q) hs
  change valuationOf q 1012 = false ∨ valuationOf q 1023 = false ∨ valuationOf q 1028 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1142 (q : Snake 81) (h : Conditions q) : valuation q 1012 = false ∨ valuation q 1023 = false ∨ valuation q 1028 = true := counterClause1142 (baseVal q)

theorem counterClause1143 (q : Nat → Bool) : valuationOf q 1013 = false ∨ valuationOf q 1025 = true := by
  have hs : count1024 q = (countLit q [-80, -81, -82, -86]) + (countLit q [-87, -88, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-80, -81, -82, -86]) (l₂ := [-87, -88, -91, -93])
  have hm := merge_left (literal (valuationOf q) (1013)) (literal (valuationOf q) (1025)) (countLit q [-80, -81, -82, -86]) (countLit q [-87, -88, -91, -93]) (count1024 q) 2 (meaning1013 q) (meaning1025 q) hs
  change valuationOf q 1013 = false ∨ valuationOf q 1025 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1143 (q : Snake 81) (h : Conditions q) : valuation q 1013 = false ∨ valuation q 1025 = true := counterClause1143 (baseVal q)

theorem counterClause1144 (q : Nat → Bool) : valuationOf q 1013 = false ∨ valuationOf q 1020 = false ∨ valuationOf q 1026 = true := by
  have hs : count1024 q = (countLit q [-80, -81, -82, -86]) + (countLit q [-87, -88, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-80, -81, -82, -86]) (l₂ := [-87, -88, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1013)) (literal (valuationOf q) (1020)) (literal (valuationOf q) (1026)) (countLit q [-80, -81, -82, -86]) (countLit q [-87, -88, -91, -93]) (count1024 q) 2 1 (meaning1013 q) (meaning1020 q) (meaning1026 q) hs
  change valuationOf q 1013 = false ∨ valuationOf q 1020 = false ∨ valuationOf q 1026 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1144 (q : Snake 81) (h : Conditions q) : valuation q 1013 = false ∨ valuation q 1020 = false ∨ valuation q 1026 = true := counterClause1144 (baseVal q)

theorem counterClause1145 (q : Nat → Bool) : valuationOf q 1013 = false ∨ valuationOf q 1021 = false ∨ valuationOf q 1027 = true := by
  have hs : count1024 q = (countLit q [-80, -81, -82, -86]) + (countLit q [-87, -88, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-80, -81, -82, -86]) (l₂ := [-87, -88, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1013)) (literal (valuationOf q) (1021)) (literal (valuationOf q) (1027)) (countLit q [-80, -81, -82, -86]) (countLit q [-87, -88, -91, -93]) (count1024 q) 2 2 (meaning1013 q) (meaning1021 q) (meaning1027 q) hs
  change valuationOf q 1013 = false ∨ valuationOf q 1021 = false ∨ valuationOf q 1027 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1145 (q : Snake 81) (h : Conditions q) : valuation q 1013 = false ∨ valuation q 1021 = false ∨ valuation q 1027 = true := counterClause1145 (baseVal q)

theorem counterClause1146 (q : Nat → Bool) : valuationOf q 1013 = false ∨ valuationOf q 1022 = false ∨ valuationOf q 1028 = true := by
  have hs : count1024 q = (countLit q [-80, -81, -82, -86]) + (countLit q [-87, -88, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-80, -81, -82, -86]) (l₂ := [-87, -88, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1013)) (literal (valuationOf q) (1022)) (literal (valuationOf q) (1028)) (countLit q [-80, -81, -82, -86]) (countLit q [-87, -88, -91, -93]) (count1024 q) 2 3 (meaning1013 q) (meaning1022 q) (meaning1028 q) hs
  change valuationOf q 1013 = false ∨ valuationOf q 1022 = false ∨ valuationOf q 1028 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1146 (q : Snake 81) (h : Conditions q) : valuation q 1013 = false ∨ valuation q 1022 = false ∨ valuation q 1028 = true := counterClause1146 (baseVal q)

theorem counterClause1147 (q : Nat → Bool) : valuationOf q 1013 = false ∨ valuationOf q 1023 = false ∨ valuationOf q 1029 = true := by
  have hs : count1024 q = (countLit q [-80, -81, -82, -86]) + (countLit q [-87, -88, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-80, -81, -82, -86]) (l₂ := [-87, -88, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1013)) (literal (valuationOf q) (1023)) (literal (valuationOf q) (1029)) (countLit q [-80, -81, -82, -86]) (countLit q [-87, -88, -91, -93]) (count1024 q) 2 4 (meaning1013 q) (meaning1023 q) (meaning1029 q) hs
  change valuationOf q 1013 = false ∨ valuationOf q 1023 = false ∨ valuationOf q 1029 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1147 (q : Snake 81) (h : Conditions q) : valuation q 1013 = false ∨ valuation q 1023 = false ∨ valuation q 1029 = true := counterClause1147 (baseVal q)

theorem counterClause1148 (q : Nat → Bool) : valuationOf q 1014 = false ∨ valuationOf q 1026 = true := by
  have hs : count1024 q = (countLit q [-80, -81, -82, -86]) + (countLit q [-87, -88, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-80, -81, -82, -86]) (l₂ := [-87, -88, -91, -93])
  have hm := merge_left (literal (valuationOf q) (1014)) (literal (valuationOf q) (1026)) (countLit q [-80, -81, -82, -86]) (countLit q [-87, -88, -91, -93]) (count1024 q) 3 (meaning1014 q) (meaning1026 q) hs
  change valuationOf q 1014 = false ∨ valuationOf q 1026 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1148 (q : Snake 81) (h : Conditions q) : valuation q 1014 = false ∨ valuation q 1026 = true := counterClause1148 (baseVal q)

theorem counterClause1149 (q : Nat → Bool) : valuationOf q 1014 = false ∨ valuationOf q 1020 = false ∨ valuationOf q 1027 = true := by
  have hs : count1024 q = (countLit q [-80, -81, -82, -86]) + (countLit q [-87, -88, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-80, -81, -82, -86]) (l₂ := [-87, -88, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1014)) (literal (valuationOf q) (1020)) (literal (valuationOf q) (1027)) (countLit q [-80, -81, -82, -86]) (countLit q [-87, -88, -91, -93]) (count1024 q) 3 1 (meaning1014 q) (meaning1020 q) (meaning1027 q) hs
  change valuationOf q 1014 = false ∨ valuationOf q 1020 = false ∨ valuationOf q 1027 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1149 (q : Snake 81) (h : Conditions q) : valuation q 1014 = false ∨ valuation q 1020 = false ∨ valuation q 1027 = true := counterClause1149 (baseVal q)

theorem counterClause1150 (q : Nat → Bool) : valuationOf q 1014 = false ∨ valuationOf q 1021 = false ∨ valuationOf q 1028 = true := by
  have hs : count1024 q = (countLit q [-80, -81, -82, -86]) + (countLit q [-87, -88, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-80, -81, -82, -86]) (l₂ := [-87, -88, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1014)) (literal (valuationOf q) (1021)) (literal (valuationOf q) (1028)) (countLit q [-80, -81, -82, -86]) (countLit q [-87, -88, -91, -93]) (count1024 q) 3 2 (meaning1014 q) (meaning1021 q) (meaning1028 q) hs
  change valuationOf q 1014 = false ∨ valuationOf q 1021 = false ∨ valuationOf q 1028 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1150 (q : Snake 81) (h : Conditions q) : valuation q 1014 = false ∨ valuation q 1021 = false ∨ valuation q 1028 = true := counterClause1150 (baseVal q)

theorem counterClause1151 (q : Nat → Bool) : valuationOf q 1014 = false ∨ valuationOf q 1022 = false ∨ valuationOf q 1029 = true := by
  have hs : count1024 q = (countLit q [-80, -81, -82, -86]) + (countLit q [-87, -88, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-80, -81, -82, -86]) (l₂ := [-87, -88, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1014)) (literal (valuationOf q) (1022)) (literal (valuationOf q) (1029)) (countLit q [-80, -81, -82, -86]) (countLit q [-87, -88, -91, -93]) (count1024 q) 3 3 (meaning1014 q) (meaning1022 q) (meaning1029 q) hs
  change valuationOf q 1014 = false ∨ valuationOf q 1022 = false ∨ valuationOf q 1029 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1151 (q : Snake 81) (h : Conditions q) : valuation q 1014 = false ∨ valuation q 1022 = false ∨ valuation q 1029 = true := counterClause1151 (baseVal q)

theorem counterClause1152 (q : Nat → Bool) : valuationOf q 1014 = false ∨ valuationOf q 1023 = false ∨ valuationOf q 1030 = true := by
  have hs : count1024 q = (countLit q [-80, -81, -82, -86]) + (countLit q [-87, -88, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-80, -81, -82, -86]) (l₂ := [-87, -88, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1014)) (literal (valuationOf q) (1023)) (literal (valuationOf q) (1030)) (countLit q [-80, -81, -82, -86]) (countLit q [-87, -88, -91, -93]) (count1024 q) 3 4 (meaning1014 q) (meaning1023 q) (meaning1030 q) hs
  change valuationOf q 1014 = false ∨ valuationOf q 1023 = false ∨ valuationOf q 1030 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1152 (q : Snake 81) (h : Conditions q) : valuation q 1014 = false ∨ valuation q 1023 = false ∨ valuation q 1030 = true := counterClause1152 (baseVal q)

theorem block35 (q : Snake 81) (h : Conditions q) : B112E153.Block35 (valuation q) :=
  ⟨clause1121 q h, clause1122 q h, clause1123 q h, clause1124 q h, clause1125 q h, clause1126 q h, clause1127 q h, clause1128 q h, clause1129 q h, clause1130 q h, clause1131 q h, clause1132 q h, clause1133 q h, clause1134 q h, clause1135 q h, clause1136 q h, clause1137 q h, clause1138 q h, clause1139 q h, clause1140 q h, clause1141 q h, clause1142 q h, clause1143 q h, clause1144 q h, clause1145 q h, clause1146 q h, clause1147 q h, clause1148 q h, clause1149 q h, clause1150 q h, clause1151 q h, clause1152 q h⟩

end
end Snake9.Regrowth.E112153
