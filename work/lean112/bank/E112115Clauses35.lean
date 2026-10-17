import E112115Semantics
import B112E115Inputs
namespace Snake9.Regrowth.E112115
noncomputable section
local instance blockDec35 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1121 (q : Nat → Bool) : valuationOf q 947 = false ∨ valuationOf q 966 = false ∨ valuationOf q 980 = true := by
  have hs : count973 q = (countLit q [-61, -62, -65, -67, -68, -70, -73]) + (countLit q [-74, -75, -78, -79, -82, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -67, -68, -70, -73]) (l₂ := [-74, -75, -78, -79, -82, -84, -86, -88])
  have hm := merge_two (literal (valuationOf q) (947)) (literal (valuationOf q) (966)) (literal (valuationOf q) (980)) (countLit q [-61, -62, -65, -67, -68, -70, -73]) (countLit q [-74, -75, -78, -79, -82, -84, -86, -88]) (count973 q) 6 2 (meaning947 q) (meaning966 q) (meaning980 q) hs
  change valuationOf q 947 = false ∨ valuationOf q 966 = false ∨ valuationOf q 980 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1121 (q : Snake 81) (h : Conditions q) : valuation q 947 = false ∨ valuation q 966 = false ∨ valuation q 980 = true := counterClause1121 (baseVal q)

theorem counterClause1122 (q : Nat → Bool) : valuationOf q 947 = false ∨ valuationOf q 967 = false ∨ valuationOf q 981 = true := by
  have hs : count973 q = (countLit q [-61, -62, -65, -67, -68, -70, -73]) + (countLit q [-74, -75, -78, -79, -82, -84, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -67, -68, -70, -73]) (l₂ := [-74, -75, -78, -79, -82, -84, -86, -88])
  have hm := merge_two (literal (valuationOf q) (947)) (literal (valuationOf q) (967)) (literal (valuationOf q) (981)) (countLit q [-61, -62, -65, -67, -68, -70, -73]) (countLit q [-74, -75, -78, -79, -82, -84, -86, -88]) (count973 q) 6 3 (meaning947 q) (meaning967 q) (meaning981 q) hs
  change valuationOf q 947 = false ∨ valuationOf q 967 = false ∨ valuationOf q 981 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1122 (q : Snake 81) (h : Conditions q) : valuation q 947 = false ∨ valuation q 967 = false ∨ valuation q 981 = true := counterClause1122 (baseVal q)

theorem counterClause1123 (q : Nat → Bool) : valuationOf q 93 = true ∨ valuationOf q 988 = true := by
  have hs : count988 q = (countLit q [-92]) + (countLit q [-93]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-93])
  have hm := merge_right (literal (valuationOf q) (-93)) (literal (valuationOf q) (988)) (countLit q [-92]) (countLit q [-93]) (count988 q) 1 (meaningNeg93 q) (meaning988 q) hs
  change (! (valuationOf q 93)) = false ∨ valuationOf q 988 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1123 (q : Snake 81) (h : Conditions q) : valuation q 93 = true ∨ valuation q 988 = true := counterClause1123 (baseVal q)

theorem counterClause1124 (q : Nat → Bool) : valuationOf q 92 = true ∨ valuationOf q 988 = true := by
  have hs : count988 q = (countLit q [-92]) + (countLit q [-93]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-93])
  have hm := merge_left (literal (valuationOf q) (-92)) (literal (valuationOf q) (988)) (countLit q [-92]) (countLit q [-93]) (count988 q) 1 (meaningNeg92 q) (meaning988 q) hs
  change (! (valuationOf q 92)) = false ∨ valuationOf q 988 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1124 (q : Snake 81) (h : Conditions q) : valuation q 92 = true ∨ valuation q 988 = true := counterClause1124 (baseVal q)

theorem counterClause1125 (q : Nat → Bool) : valuationOf q 988 = false ∨ valuationOf q 990 = true := by
  have hs : count990 q = (countLit q [-91]) + (countLit q [-92, -93]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-92, -93])
  have hm := merge_right (literal (valuationOf q) (988)) (literal (valuationOf q) (990)) (countLit q [-91]) (countLit q [-92, -93]) (count990 q) 1 (meaning988 q) (meaning990 q) hs
  change valuationOf q 988 = false ∨ valuationOf q 990 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1125 (q : Snake 81) (h : Conditions q) : valuation q 988 = false ∨ valuation q 990 = true := counterClause1125 (baseVal q)

theorem counterClause1126 (q : Nat → Bool) : valuationOf q 91 = true ∨ valuationOf q 990 = true := by
  have hs : count990 q = (countLit q [-91]) + (countLit q [-92, -93]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-92, -93])
  have hm := merge_left (literal (valuationOf q) (-91)) (literal (valuationOf q) (990)) (countLit q [-91]) (countLit q [-92, -93]) (count990 q) 1 (meaningNeg91 q) (meaning990 q) hs
  change (! (valuationOf q 91)) = false ∨ valuationOf q 990 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1126 (q : Snake 81) (h : Conditions q) : valuation q 91 = true ∨ valuation q 990 = true := counterClause1126 (baseVal q)

theorem counterClause1127 (q : Nat → Bool) : valuationOf q 102 = true ∨ valuationOf q 995 = true := by
  have hs : count995 q = (countLit q [-100]) + (countLit q [-102]) := List.countP_append (p := literal q) (l₁ := [-100]) (l₂ := [-102])
  have hm := merge_right (literal (valuationOf q) (-102)) (literal (valuationOf q) (995)) (countLit q [-100]) (countLit q [-102]) (count995 q) 1 (meaningNeg102 q) (meaning995 q) hs
  change (! (valuationOf q 102)) = false ∨ valuationOf q 995 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1127 (q : Snake 81) (h : Conditions q) : valuation q 102 = true ∨ valuation q 995 = true := counterClause1127 (baseVal q)

theorem counterClause1128 (q : Nat → Bool) : valuationOf q 995 = false ∨ valuationOf q 997 = true := by
  have hs : count997 q = (countLit q [-96, -99]) + (countLit q [-100, -102]) := List.countP_append (p := literal q) (l₁ := [-96, -99]) (l₂ := [-100, -102])
  have hm := merge_right (literal (valuationOf q) (995)) (literal (valuationOf q) (997)) (countLit q [-96, -99]) (countLit q [-100, -102]) (count997 q) 1 (meaning995 q) (meaning997 q) hs
  change valuationOf q 995 = false ∨ valuationOf q 997 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1128 (q : Snake 81) (h : Conditions q) : valuation q 995 = false ∨ valuation q 997 = true := counterClause1128 (baseVal q)

theorem counterClause1129 (q : Nat → Bool) : valuationOf q 997 = false ∨ valuationOf q 1001 = true := by
  have hs : count1001 q = (countLit q [-91, -92, -93]) + (countLit q [-96, -99, -100, -102]) := List.countP_append (p := literal q) (l₁ := [-91, -92, -93]) (l₂ := [-96, -99, -100, -102])
  have hm := merge_right (literal (valuationOf q) (997)) (literal (valuationOf q) (1001)) (countLit q [-91, -92, -93]) (countLit q [-96, -99, -100, -102]) (count1001 q) 1 (meaning997 q) (meaning1001 q) hs
  change valuationOf q 997 = false ∨ valuationOf q 1001 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1129 (q : Snake 81) (h : Conditions q) : valuation q 997 = false ∨ valuation q 1001 = true := counterClause1129 (baseVal q)

theorem counterClause1130 (q : Nat → Bool) : valuationOf q 990 = false ∨ valuationOf q 1001 = true := by
  have hs : count1001 q = (countLit q [-91, -92, -93]) + (countLit q [-96, -99, -100, -102]) := List.countP_append (p := literal q) (l₁ := [-91, -92, -93]) (l₂ := [-96, -99, -100, -102])
  have hm := merge_left (literal (valuationOf q) (990)) (literal (valuationOf q) (1001)) (countLit q [-91, -92, -93]) (countLit q [-96, -99, -100, -102]) (count1001 q) 1 (meaning990 q) (meaning1001 q) hs
  change valuationOf q 990 = false ∨ valuationOf q 1001 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1130 (q : Snake 81) (h : Conditions q) : valuation q 990 = false ∨ valuation q 1001 = true := counterClause1130 (baseVal q)

theorem counterClause1131 (q : Nat → Bool) : valuationOf q 106 = true ∨ valuationOf q 1008 = true := by
  have hs : count1008 q = (countLit q [-105]) + (countLit q [-106]) := List.countP_append (p := literal q) (l₁ := [-105]) (l₂ := [-106])
  have hm := merge_right (literal (valuationOf q) (-106)) (literal (valuationOf q) (1008)) (countLit q [-105]) (countLit q [-106]) (count1008 q) 1 (meaningNeg106 q) (meaning1008 q) hs
  change (! (valuationOf q 106)) = false ∨ valuationOf q 1008 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1131 (q : Snake 81) (h : Conditions q) : valuation q 106 = true ∨ valuation q 1008 = true := counterClause1131 (baseVal q)

theorem counterClause1132 (q : Nat → Bool) : valuationOf q 110 = true ∨ valuationOf q 1010 = true := by
  have hs : count1010 q = (countLit q [-107]) + (countLit q [-110]) := List.countP_append (p := literal q) (l₁ := [-107]) (l₂ := [-110])
  have hm := merge_right (literal (valuationOf q) (-110)) (literal (valuationOf q) (1010)) (countLit q [-107]) (countLit q [-110]) (count1010 q) 1 (meaningNeg110 q) (meaning1010 q) hs
  change (! (valuationOf q 110)) = false ∨ valuationOf q 1010 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1132 (q : Snake 81) (h : Conditions q) : valuation q 110 = true ∨ valuation q 1010 = true := counterClause1132 (baseVal q)

theorem counterClause1133 (q : Nat → Bool) : valuationOf q 107 = true ∨ valuationOf q 110 = true ∨ valuationOf q 1011 = true := by
  have hs : count1010 q = (countLit q [-107]) + (countLit q [-110]) := List.countP_append (p := literal q) (l₁ := [-107]) (l₂ := [-110])
  have hm := merge_two (literal (valuationOf q) (-107)) (literal (valuationOf q) (-110)) (literal (valuationOf q) (1011)) (countLit q [-107]) (countLit q [-110]) (count1010 q) 1 1 (meaningNeg107 q) (meaningNeg110 q) (meaning1011 q) hs
  change (! (valuationOf q 107)) = false ∨ (! (valuationOf q 110)) = false ∨ valuationOf q 1011 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1133 (q : Snake 81) (h : Conditions q) : valuation q 107 = true ∨ valuation q 110 = true ∨ valuation q 1011 = true := counterClause1133 (baseVal q)

theorem counterClause1134 (q : Nat → Bool) : valuationOf q 1010 = false ∨ valuationOf q 1012 = true := by
  have hs : count1012 q = (countLit q [-105, -106]) + (countLit q [-107, -110]) := List.countP_append (p := literal q) (l₁ := [-105, -106]) (l₂ := [-107, -110])
  have hm := merge_right (literal (valuationOf q) (1010)) (literal (valuationOf q) (1012)) (countLit q [-105, -106]) (countLit q [-107, -110]) (count1012 q) 1 (meaning1010 q) (meaning1012 q) hs
  change valuationOf q 1010 = false ∨ valuationOf q 1012 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1134 (q : Snake 81) (h : Conditions q) : valuation q 1010 = false ∨ valuation q 1012 = true := counterClause1134 (baseVal q)

theorem counterClause1135 (q : Nat → Bool) : valuationOf q 1011 = false ∨ valuationOf q 1013 = true := by
  have hs : count1012 q = (countLit q [-105, -106]) + (countLit q [-107, -110]) := List.countP_append (p := literal q) (l₁ := [-105, -106]) (l₂ := [-107, -110])
  have hm := merge_right (literal (valuationOf q) (1011)) (literal (valuationOf q) (1013)) (countLit q [-105, -106]) (countLit q [-107, -110]) (count1012 q) 2 (meaning1011 q) (meaning1013 q) hs
  change valuationOf q 1011 = false ∨ valuationOf q 1013 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1135 (q : Snake 81) (h : Conditions q) : valuation q 1011 = false ∨ valuation q 1013 = true := counterClause1135 (baseVal q)

theorem counterClause1136 (q : Nat → Bool) : valuationOf q 1008 = false ∨ valuationOf q 1010 = false ∨ valuationOf q 1013 = true := by
  have hs : count1012 q = (countLit q [-105, -106]) + (countLit q [-107, -110]) := List.countP_append (p := literal q) (l₁ := [-105, -106]) (l₂ := [-107, -110])
  have hm := merge_two (literal (valuationOf q) (1008)) (literal (valuationOf q) (1010)) (literal (valuationOf q) (1013)) (countLit q [-105, -106]) (countLit q [-107, -110]) (count1012 q) 1 1 (meaning1008 q) (meaning1010 q) (meaning1013 q) hs
  change valuationOf q 1008 = false ∨ valuationOf q 1010 = false ∨ valuationOf q 1013 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1136 (q : Snake 81) (h : Conditions q) : valuation q 1008 = false ∨ valuation q 1010 = false ∨ valuation q 1013 = true := counterClause1136 (baseVal q)

theorem counterClause1137 (q : Nat → Bool) : valuationOf q 1008 = false ∨ valuationOf q 1011 = false ∨ valuationOf q 1014 = true := by
  have hs : count1012 q = (countLit q [-105, -106]) + (countLit q [-107, -110]) := List.countP_append (p := literal q) (l₁ := [-105, -106]) (l₂ := [-107, -110])
  have hm := merge_two (literal (valuationOf q) (1008)) (literal (valuationOf q) (1011)) (literal (valuationOf q) (1014)) (countLit q [-105, -106]) (countLit q [-107, -110]) (count1012 q) 1 2 (meaning1008 q) (meaning1011 q) (meaning1014 q) hs
  change valuationOf q 1008 = false ∨ valuationOf q 1011 = false ∨ valuationOf q 1014 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1137 (q : Snake 81) (h : Conditions q) : valuation q 1008 = false ∨ valuation q 1011 = false ∨ valuation q 1014 = true := counterClause1137 (baseVal q)

theorem counterClause1138 (q : Nat → Bool) : valuationOf q 114 = true ∨ valuationOf q 1016 = true := by
  have hs : count1016 q = (countLit q [-112]) + (countLit q [-114]) := List.countP_append (p := literal q) (l₁ := [-112]) (l₂ := [-114])
  have hm := merge_right (literal (valuationOf q) (-114)) (literal (valuationOf q) (1016)) (countLit q [-112]) (countLit q [-114]) (count1016 q) 1 (meaningNeg114 q) (meaning1016 q) hs
  change (! (valuationOf q 114)) = false ∨ valuationOf q 1016 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1138 (q : Snake 81) (h : Conditions q) : valuation q 114 = true ∨ valuation q 1016 = true := counterClause1138 (baseVal q)

theorem counterClause1139 (q : Nat → Bool) : valuationOf q 112 = true ∨ valuationOf q 1016 = true := by
  have hs : count1016 q = (countLit q [-112]) + (countLit q [-114]) := List.countP_append (p := literal q) (l₁ := [-112]) (l₂ := [-114])
  have hm := merge_left (literal (valuationOf q) (-112)) (literal (valuationOf q) (1016)) (countLit q [-112]) (countLit q [-114]) (count1016 q) 1 (meaningNeg112 q) (meaning1016 q) hs
  change (! (valuationOf q 112)) = false ∨ valuationOf q 1016 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1139 (q : Snake 81) (h : Conditions q) : valuation q 112 = true ∨ valuation q 1016 = true := counterClause1139 (baseVal q)

theorem counterClause1140 (q : Nat → Bool) : valuationOf q 112 = true ∨ valuationOf q 114 = true ∨ valuationOf q 1017 = true := by
  have hs : count1016 q = (countLit q [-112]) + (countLit q [-114]) := List.countP_append (p := literal q) (l₁ := [-112]) (l₂ := [-114])
  have hm := merge_two (literal (valuationOf q) (-112)) (literal (valuationOf q) (-114)) (literal (valuationOf q) (1017)) (countLit q [-112]) (countLit q [-114]) (count1016 q) 1 1 (meaningNeg112 q) (meaningNeg114 q) (meaning1017 q) hs
  change (! (valuationOf q 112)) = false ∨ (! (valuationOf q 114)) = false ∨ valuationOf q 1017 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1140 (q : Snake 81) (h : Conditions q) : valuation q 112 = true ∨ valuation q 114 = true ∨ valuation q 1017 = true := counterClause1140 (baseVal q)

theorem counterClause1141 (q : Nat → Bool) : valuationOf q 115 = true ∨ valuationOf q 117 = true ∨ valuationOf q 1019 = true := by
  have hs : count1018 q = (countLit q [-115]) + (countLit q [-117]) := List.countP_append (p := literal q) (l₁ := [-115]) (l₂ := [-117])
  have hm := merge_two (literal (valuationOf q) (-115)) (literal (valuationOf q) (-117)) (literal (valuationOf q) (1019)) (countLit q [-115]) (countLit q [-117]) (count1018 q) 1 1 (meaningNeg115 q) (meaningNeg117 q) (meaning1019 q) hs
  change (! (valuationOf q 115)) = false ∨ (! (valuationOf q 117)) = false ∨ valuationOf q 1019 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1141 (q : Snake 81) (h : Conditions q) : valuation q 115 = true ∨ valuation q 117 = true ∨ valuation q 1019 = true := counterClause1141 (baseVal q)

theorem counterClause1142 (q : Nat → Bool) : valuationOf q 1019 = false ∨ valuationOf q 1021 = true := by
  have hs : count1020 q = (countLit q [-112, -114]) + (countLit q [-115, -117]) := List.countP_append (p := literal q) (l₁ := [-112, -114]) (l₂ := [-115, -117])
  have hm := merge_right (literal (valuationOf q) (1019)) (literal (valuationOf q) (1021)) (countLit q [-112, -114]) (countLit q [-115, -117]) (count1020 q) 2 (meaning1019 q) (meaning1021 q) hs
  change valuationOf q 1019 = false ∨ valuationOf q 1021 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1142 (q : Snake 81) (h : Conditions q) : valuation q 1019 = false ∨ valuation q 1021 = true := counterClause1142 (baseVal q)

theorem counterClause1143 (q : Nat → Bool) : valuationOf q 1016 = false ∨ valuationOf q 1019 = false ∨ valuationOf q 1022 = true := by
  have hs : count1020 q = (countLit q [-112, -114]) + (countLit q [-115, -117]) := List.countP_append (p := literal q) (l₁ := [-112, -114]) (l₂ := [-115, -117])
  have hm := merge_two (literal (valuationOf q) (1016)) (literal (valuationOf q) (1019)) (literal (valuationOf q) (1022)) (countLit q [-112, -114]) (countLit q [-115, -117]) (count1020 q) 1 2 (meaning1016 q) (meaning1019 q) (meaning1022 q) hs
  change valuationOf q 1016 = false ∨ valuationOf q 1019 = false ∨ valuationOf q 1022 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1143 (q : Snake 81) (h : Conditions q) : valuation q 1016 = false ∨ valuation q 1019 = false ∨ valuation q 1022 = true := counterClause1143 (baseVal q)

theorem counterClause1144 (q : Nat → Bool) : valuationOf q 1017 = false ∨ valuationOf q 1019 = false ∨ valuationOf q 1023 = true := by
  have hs : count1020 q = (countLit q [-112, -114]) + (countLit q [-115, -117]) := List.countP_append (p := literal q) (l₁ := [-112, -114]) (l₂ := [-115, -117])
  have hm := merge_two (literal (valuationOf q) (1017)) (literal (valuationOf q) (1019)) (literal (valuationOf q) (1023)) (countLit q [-112, -114]) (countLit q [-115, -117]) (count1020 q) 2 2 (meaning1017 q) (meaning1019 q) (meaning1023 q) hs
  change valuationOf q 1017 = false ∨ valuationOf q 1019 = false ∨ valuationOf q 1023 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1144 (q : Snake 81) (h : Conditions q) : valuation q 1017 = false ∨ valuation q 1019 = false ∨ valuation q 1023 = true := counterClause1144 (baseVal q)

theorem counterClause1145 (q : Nat → Bool) : valuationOf q 1012 = false ∨ valuationOf q 1021 = false ∨ valuationOf q 1026 = true := by
  have hs : count1024 q = (countLit q [-105, -106, -107, -110]) + (countLit q [-112, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-105, -106, -107, -110]) (l₂ := [-112, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1012)) (literal (valuationOf q) (1021)) (literal (valuationOf q) (1026)) (countLit q [-105, -106, -107, -110]) (countLit q [-112, -114, -115, -117]) (count1024 q) 1 2 (meaning1012 q) (meaning1021 q) (meaning1026 q) hs
  change valuationOf q 1012 = false ∨ valuationOf q 1021 = false ∨ valuationOf q 1026 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1145 (q : Snake 81) (h : Conditions q) : valuation q 1012 = false ∨ valuation q 1021 = false ∨ valuation q 1026 = true := counterClause1145 (baseVal q)

theorem counterClause1146 (q : Nat → Bool) : valuationOf q 1012 = false ∨ valuationOf q 1022 = false ∨ valuationOf q 1027 = true := by
  have hs : count1024 q = (countLit q [-105, -106, -107, -110]) + (countLit q [-112, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-105, -106, -107, -110]) (l₂ := [-112, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1012)) (literal (valuationOf q) (1022)) (literal (valuationOf q) (1027)) (countLit q [-105, -106, -107, -110]) (countLit q [-112, -114, -115, -117]) (count1024 q) 1 3 (meaning1012 q) (meaning1022 q) (meaning1027 q) hs
  change valuationOf q 1012 = false ∨ valuationOf q 1022 = false ∨ valuationOf q 1027 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1146 (q : Snake 81) (h : Conditions q) : valuation q 1012 = false ∨ valuation q 1022 = false ∨ valuation q 1027 = true := counterClause1146 (baseVal q)

theorem counterClause1147 (q : Nat → Bool) : valuationOf q 1012 = false ∨ valuationOf q 1023 = false ∨ valuationOf q 1028 = true := by
  have hs : count1024 q = (countLit q [-105, -106, -107, -110]) + (countLit q [-112, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-105, -106, -107, -110]) (l₂ := [-112, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1012)) (literal (valuationOf q) (1023)) (literal (valuationOf q) (1028)) (countLit q [-105, -106, -107, -110]) (countLit q [-112, -114, -115, -117]) (count1024 q) 1 4 (meaning1012 q) (meaning1023 q) (meaning1028 q) hs
  change valuationOf q 1012 = false ∨ valuationOf q 1023 = false ∨ valuationOf q 1028 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1147 (q : Snake 81) (h : Conditions q) : valuation q 1012 = false ∨ valuation q 1023 = false ∨ valuation q 1028 = true := counterClause1147 (baseVal q)

theorem counterClause1148 (q : Nat → Bool) : valuationOf q 1013 = false ∨ valuationOf q 1021 = false ∨ valuationOf q 1027 = true := by
  have hs : count1024 q = (countLit q [-105, -106, -107, -110]) + (countLit q [-112, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-105, -106, -107, -110]) (l₂ := [-112, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1013)) (literal (valuationOf q) (1021)) (literal (valuationOf q) (1027)) (countLit q [-105, -106, -107, -110]) (countLit q [-112, -114, -115, -117]) (count1024 q) 2 2 (meaning1013 q) (meaning1021 q) (meaning1027 q) hs
  change valuationOf q 1013 = false ∨ valuationOf q 1021 = false ∨ valuationOf q 1027 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1148 (q : Snake 81) (h : Conditions q) : valuation q 1013 = false ∨ valuation q 1021 = false ∨ valuation q 1027 = true := counterClause1148 (baseVal q)

theorem counterClause1149 (q : Nat → Bool) : valuationOf q 1013 = false ∨ valuationOf q 1022 = false ∨ valuationOf q 1028 = true := by
  have hs : count1024 q = (countLit q [-105, -106, -107, -110]) + (countLit q [-112, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-105, -106, -107, -110]) (l₂ := [-112, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1013)) (literal (valuationOf q) (1022)) (literal (valuationOf q) (1028)) (countLit q [-105, -106, -107, -110]) (countLit q [-112, -114, -115, -117]) (count1024 q) 2 3 (meaning1013 q) (meaning1022 q) (meaning1028 q) hs
  change valuationOf q 1013 = false ∨ valuationOf q 1022 = false ∨ valuationOf q 1028 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1149 (q : Snake 81) (h : Conditions q) : valuation q 1013 = false ∨ valuation q 1022 = false ∨ valuation q 1028 = true := counterClause1149 (baseVal q)

theorem counterClause1150 (q : Nat → Bool) : valuationOf q 1013 = false ∨ valuationOf q 1023 = false ∨ valuationOf q 1029 = true := by
  have hs : count1024 q = (countLit q [-105, -106, -107, -110]) + (countLit q [-112, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-105, -106, -107, -110]) (l₂ := [-112, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1013)) (literal (valuationOf q) (1023)) (literal (valuationOf q) (1029)) (countLit q [-105, -106, -107, -110]) (countLit q [-112, -114, -115, -117]) (count1024 q) 2 4 (meaning1013 q) (meaning1023 q) (meaning1029 q) hs
  change valuationOf q 1013 = false ∨ valuationOf q 1023 = false ∨ valuationOf q 1029 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1150 (q : Snake 81) (h : Conditions q) : valuation q 1013 = false ∨ valuation q 1023 = false ∨ valuation q 1029 = true := counterClause1150 (baseVal q)

theorem counterClause1151 (q : Nat → Bool) : valuationOf q 1014 = false ∨ valuationOf q 1021 = false ∨ valuationOf q 1028 = true := by
  have hs : count1024 q = (countLit q [-105, -106, -107, -110]) + (countLit q [-112, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-105, -106, -107, -110]) (l₂ := [-112, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1014)) (literal (valuationOf q) (1021)) (literal (valuationOf q) (1028)) (countLit q [-105, -106, -107, -110]) (countLit q [-112, -114, -115, -117]) (count1024 q) 3 2 (meaning1014 q) (meaning1021 q) (meaning1028 q) hs
  change valuationOf q 1014 = false ∨ valuationOf q 1021 = false ∨ valuationOf q 1028 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1151 (q : Snake 81) (h : Conditions q) : valuation q 1014 = false ∨ valuation q 1021 = false ∨ valuation q 1028 = true := counterClause1151 (baseVal q)

theorem counterClause1152 (q : Nat → Bool) : valuationOf q 1014 = false ∨ valuationOf q 1022 = false ∨ valuationOf q 1029 = true := by
  have hs : count1024 q = (countLit q [-105, -106, -107, -110]) + (countLit q [-112, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-105, -106, -107, -110]) (l₂ := [-112, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1014)) (literal (valuationOf q) (1022)) (literal (valuationOf q) (1029)) (countLit q [-105, -106, -107, -110]) (countLit q [-112, -114, -115, -117]) (count1024 q) 3 3 (meaning1014 q) (meaning1022 q) (meaning1029 q) hs
  change valuationOf q 1014 = false ∨ valuationOf q 1022 = false ∨ valuationOf q 1029 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1152 (q : Snake 81) (h : Conditions q) : valuation q 1014 = false ∨ valuation q 1022 = false ∨ valuation q 1029 = true := counterClause1152 (baseVal q)

theorem block35 (q : Snake 81) (h : Conditions q) : B112E115.Block35 (valuation q) :=
  ⟨clause1121 q h, clause1122 q h, clause1123 q h, clause1124 q h, clause1125 q h, clause1126 q h, clause1127 q h, clause1128 q h, clause1129 q h, clause1130 q h, clause1131 q h, clause1132 q h, clause1133 q h, clause1134 q h, clause1135 q h, clause1136 q h, clause1137 q h, clause1138 q h, clause1139 q h, clause1140 q h, clause1141 q h, clause1142 q h, clause1143 q h, clause1144 q h, clause1145 q h, clause1146 q h, clause1147 q h, clause1148 q h, clause1149 q h, clause1150 q h, clause1151 q h, clause1152 q h⟩

end
end Snake9.Regrowth.E112115
