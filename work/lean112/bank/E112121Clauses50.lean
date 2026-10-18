import E112121Semantics
import B112E121Inputs
namespace Snake9.Regrowth.E112121
noncomputable section
local instance blockDec50 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1601 (q : Nat → Bool) : valuationOf q 1064 = false ∨ valuationOf q 1134 = false ∨ valuationOf q 1152 = true := by
  have hs : count1143 q = (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) + (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (l₂ := [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1064)) (literal (valuationOf q) (1134)) (literal (valuationOf q) (1152)) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) (count1143 q) 2 8 (meaning1064 q) (meaning1134 q) (meaning1152 q) hs
  change valuationOf q 1064 = false ∨ valuationOf q 1134 = false ∨ valuationOf q 1152 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1601 (q : Snake 81) (h : Conditions q) : valuation q 1064 = false ∨ valuation q 1134 = false ∨ valuation q 1152 = true := counterClause1601 (baseVal q)

theorem counterClause1602 (q : Nat → Bool) : valuationOf q 1064 = false ∨ valuationOf q 1135 = false ∨ valuationOf q 1153 = true := by
  have hs : count1143 q = (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) + (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (l₂ := [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1064)) (literal (valuationOf q) (1135)) (literal (valuationOf q) (1153)) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) (count1143 q) 2 9 (meaning1064 q) (meaning1135 q) (meaning1153 q) hs
  change valuationOf q 1064 = false ∨ valuationOf q 1135 = false ∨ valuationOf q 1153 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1602 (q : Snake 81) (h : Conditions q) : valuation q 1064 = false ∨ valuation q 1135 = false ∨ valuation q 1153 = true := counterClause1602 (baseVal q)

theorem counterClause1603 (q : Nat → Bool) : valuationOf q 1065 = false ∨ valuationOf q 1129 = false ∨ valuationOf q 1148 = true := by
  have hs : count1143 q = (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) + (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (l₂ := [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1065)) (literal (valuationOf q) (1129)) (literal (valuationOf q) (1148)) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) (count1143 q) 3 3 (meaning1065 q) (meaning1129 q) (meaning1148 q) hs
  change valuationOf q 1065 = false ∨ valuationOf q 1129 = false ∨ valuationOf q 1148 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1603 (q : Snake 81) (h : Conditions q) : valuation q 1065 = false ∨ valuation q 1129 = false ∨ valuation q 1148 = true := counterClause1603 (baseVal q)

theorem counterClause1604 (q : Nat → Bool) : valuationOf q 1065 = false ∨ valuationOf q 1130 = false ∨ valuationOf q 1149 = true := by
  have hs : count1143 q = (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) + (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (l₂ := [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1065)) (literal (valuationOf q) (1130)) (literal (valuationOf q) (1149)) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) (count1143 q) 3 4 (meaning1065 q) (meaning1130 q) (meaning1149 q) hs
  change valuationOf q 1065 = false ∨ valuationOf q 1130 = false ∨ valuationOf q 1149 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1604 (q : Snake 81) (h : Conditions q) : valuation q 1065 = false ∨ valuation q 1130 = false ∨ valuation q 1149 = true := counterClause1604 (baseVal q)

theorem counterClause1605 (q : Nat → Bool) : valuationOf q 1065 = false ∨ valuationOf q 1131 = false ∨ valuationOf q 1150 = true := by
  have hs : count1143 q = (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) + (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (l₂ := [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1065)) (literal (valuationOf q) (1131)) (literal (valuationOf q) (1150)) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) (count1143 q) 3 5 (meaning1065 q) (meaning1131 q) (meaning1150 q) hs
  change valuationOf q 1065 = false ∨ valuationOf q 1131 = false ∨ valuationOf q 1150 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1605 (q : Snake 81) (h : Conditions q) : valuation q 1065 = false ∨ valuation q 1131 = false ∨ valuation q 1150 = true := counterClause1605 (baseVal q)

theorem counterClause1606 (q : Nat → Bool) : valuationOf q 1065 = false ∨ valuationOf q 1132 = false ∨ valuationOf q 1151 = true := by
  have hs : count1143 q = (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) + (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (l₂ := [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1065)) (literal (valuationOf q) (1132)) (literal (valuationOf q) (1151)) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) (count1143 q) 3 6 (meaning1065 q) (meaning1132 q) (meaning1151 q) hs
  change valuationOf q 1065 = false ∨ valuationOf q 1132 = false ∨ valuationOf q 1151 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1606 (q : Snake 81) (h : Conditions q) : valuation q 1065 = false ∨ valuation q 1132 = false ∨ valuation q 1151 = true := counterClause1606 (baseVal q)

theorem counterClause1607 (q : Nat → Bool) : valuationOf q 1065 = false ∨ valuationOf q 1133 = false ∨ valuationOf q 1152 = true := by
  have hs : count1143 q = (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) + (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (l₂ := [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1065)) (literal (valuationOf q) (1133)) (literal (valuationOf q) (1152)) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) (count1143 q) 3 7 (meaning1065 q) (meaning1133 q) (meaning1152 q) hs
  change valuationOf q 1065 = false ∨ valuationOf q 1133 = false ∨ valuationOf q 1152 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1607 (q : Snake 81) (h : Conditions q) : valuation q 1065 = false ∨ valuation q 1133 = false ∨ valuation q 1152 = true := counterClause1607 (baseVal q)

theorem counterClause1608 (q : Nat → Bool) : valuationOf q 1065 = false ∨ valuationOf q 1134 = false ∨ valuationOf q 1153 = true := by
  have hs : count1143 q = (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) + (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (l₂ := [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1065)) (literal (valuationOf q) (1134)) (literal (valuationOf q) (1153)) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) (count1143 q) 3 8 (meaning1065 q) (meaning1134 q) (meaning1153 q) hs
  change valuationOf q 1065 = false ∨ valuationOf q 1134 = false ∨ valuationOf q 1153 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1608 (q : Snake 81) (h : Conditions q) : valuation q 1065 = false ∨ valuation q 1134 = false ∨ valuation q 1153 = true := counterClause1608 (baseVal q)

theorem counterClause1609 (q : Nat → Bool) : valuationOf q 1065 = false ∨ valuationOf q 1135 = false ∨ valuationOf q 1154 = true := by
  have hs : count1143 q = (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) + (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (l₂ := [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1065)) (literal (valuationOf q) (1135)) (literal (valuationOf q) (1154)) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) (count1143 q) 3 9 (meaning1065 q) (meaning1135 q) (meaning1154 q) hs
  change valuationOf q 1065 = false ∨ valuationOf q 1135 = false ∨ valuationOf q 1154 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1609 (q : Snake 81) (h : Conditions q) : valuation q 1065 = false ∨ valuation q 1135 = false ∨ valuation q 1154 = true := counterClause1609 (baseVal q)

theorem counterClause1610 (q : Nat → Bool) : valuationOf q 1066 = false ∨ valuationOf q 1129 = false ∨ valuationOf q 1149 = true := by
  have hs : count1143 q = (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) + (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (l₂ := [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1066)) (literal (valuationOf q) (1129)) (literal (valuationOf q) (1149)) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) (count1143 q) 4 3 (meaning1066 q) (meaning1129 q) (meaning1149 q) hs
  change valuationOf q 1066 = false ∨ valuationOf q 1129 = false ∨ valuationOf q 1149 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1610 (q : Snake 81) (h : Conditions q) : valuation q 1066 = false ∨ valuation q 1129 = false ∨ valuation q 1149 = true := counterClause1610 (baseVal q)

theorem counterClause1611 (q : Nat → Bool) : valuationOf q 1066 = false ∨ valuationOf q 1130 = false ∨ valuationOf q 1150 = true := by
  have hs : count1143 q = (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) + (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (l₂ := [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1066)) (literal (valuationOf q) (1130)) (literal (valuationOf q) (1150)) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) (count1143 q) 4 4 (meaning1066 q) (meaning1130 q) (meaning1150 q) hs
  change valuationOf q 1066 = false ∨ valuationOf q 1130 = false ∨ valuationOf q 1150 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1611 (q : Snake 81) (h : Conditions q) : valuation q 1066 = false ∨ valuation q 1130 = false ∨ valuation q 1150 = true := counterClause1611 (baseVal q)

theorem counterClause1612 (q : Nat → Bool) : valuationOf q 1066 = false ∨ valuationOf q 1131 = false ∨ valuationOf q 1151 = true := by
  have hs : count1143 q = (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) + (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (l₂ := [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1066)) (literal (valuationOf q) (1131)) (literal (valuationOf q) (1151)) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) (count1143 q) 4 5 (meaning1066 q) (meaning1131 q) (meaning1151 q) hs
  change valuationOf q 1066 = false ∨ valuationOf q 1131 = false ∨ valuationOf q 1151 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1612 (q : Snake 81) (h : Conditions q) : valuation q 1066 = false ∨ valuation q 1131 = false ∨ valuation q 1151 = true := counterClause1612 (baseVal q)

theorem counterClause1613 (q : Nat → Bool) : valuationOf q 1066 = false ∨ valuationOf q 1132 = false ∨ valuationOf q 1152 = true := by
  have hs : count1143 q = (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) + (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (l₂ := [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1066)) (literal (valuationOf q) (1132)) (literal (valuationOf q) (1152)) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) (count1143 q) 4 6 (meaning1066 q) (meaning1132 q) (meaning1152 q) hs
  change valuationOf q 1066 = false ∨ valuationOf q 1132 = false ∨ valuationOf q 1152 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1613 (q : Snake 81) (h : Conditions q) : valuation q 1066 = false ∨ valuation q 1132 = false ∨ valuation q 1152 = true := counterClause1613 (baseVal q)

theorem counterClause1614 (q : Nat → Bool) : valuationOf q 1066 = false ∨ valuationOf q 1133 = false ∨ valuationOf q 1153 = true := by
  have hs : count1143 q = (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) + (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (l₂ := [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1066)) (literal (valuationOf q) (1133)) (literal (valuationOf q) (1153)) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) (count1143 q) 4 7 (meaning1066 q) (meaning1133 q) (meaning1153 q) hs
  change valuationOf q 1066 = false ∨ valuationOf q 1133 = false ∨ valuationOf q 1153 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1614 (q : Snake 81) (h : Conditions q) : valuation q 1066 = false ∨ valuation q 1133 = false ∨ valuation q 1153 = true := counterClause1614 (baseVal q)

theorem counterClause1615 (q : Nat → Bool) : valuationOf q 1066 = false ∨ valuationOf q 1134 = false ∨ valuationOf q 1154 = true := by
  have hs : count1143 q = (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) + (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (l₂ := [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1066)) (literal (valuationOf q) (1134)) (literal (valuationOf q) (1154)) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) (count1143 q) 4 8 (meaning1066 q) (meaning1134 q) (meaning1154 q) hs
  change valuationOf q 1066 = false ∨ valuationOf q 1134 = false ∨ valuationOf q 1154 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1615 (q : Snake 81) (h : Conditions q) : valuation q 1066 = false ∨ valuation q 1134 = false ∨ valuation q 1154 = true := counterClause1615 (baseVal q)

theorem counterClause1616 (q : Nat → Bool) : valuationOf q 1066 = false ∨ valuationOf q 1135 = false ∨ valuationOf q 1155 = true := by
  have hs : count1143 q = (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) + (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (l₂ := [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1066)) (literal (valuationOf q) (1135)) (literal (valuationOf q) (1155)) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) (count1143 q) 4 9 (meaning1066 q) (meaning1135 q) (meaning1155 q) hs
  change valuationOf q 1066 = false ∨ valuationOf q 1135 = false ∨ valuationOf q 1155 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1616 (q : Snake 81) (h : Conditions q) : valuation q 1066 = false ∨ valuation q 1135 = false ∨ valuation q 1155 = true := counterClause1616 (baseVal q)

theorem counterClause1617 (q : Nat → Bool) : valuationOf q 1067 = false ∨ valuationOf q 1129 = false ∨ valuationOf q 1150 = true := by
  have hs : count1143 q = (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) + (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (l₂ := [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1067)) (literal (valuationOf q) (1129)) (literal (valuationOf q) (1150)) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) (count1143 q) 5 3 (meaning1067 q) (meaning1129 q) (meaning1150 q) hs
  change valuationOf q 1067 = false ∨ valuationOf q 1129 = false ∨ valuationOf q 1150 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1617 (q : Snake 81) (h : Conditions q) : valuation q 1067 = false ∨ valuation q 1129 = false ∨ valuation q 1150 = true := counterClause1617 (baseVal q)

theorem counterClause1618 (q : Nat → Bool) : valuationOf q 1067 = false ∨ valuationOf q 1130 = false ∨ valuationOf q 1151 = true := by
  have hs : count1143 q = (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) + (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (l₂ := [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1067)) (literal (valuationOf q) (1130)) (literal (valuationOf q) (1151)) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) (count1143 q) 5 4 (meaning1067 q) (meaning1130 q) (meaning1151 q) hs
  change valuationOf q 1067 = false ∨ valuationOf q 1130 = false ∨ valuationOf q 1151 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1618 (q : Snake 81) (h : Conditions q) : valuation q 1067 = false ∨ valuation q 1130 = false ∨ valuation q 1151 = true := counterClause1618 (baseVal q)

theorem counterClause1619 (q : Nat → Bool) : valuationOf q 1067 = false ∨ valuationOf q 1131 = false ∨ valuationOf q 1152 = true := by
  have hs : count1143 q = (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) + (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (l₂ := [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1067)) (literal (valuationOf q) (1131)) (literal (valuationOf q) (1152)) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) (count1143 q) 5 5 (meaning1067 q) (meaning1131 q) (meaning1152 q) hs
  change valuationOf q 1067 = false ∨ valuationOf q 1131 = false ∨ valuationOf q 1152 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1619 (q : Snake 81) (h : Conditions q) : valuation q 1067 = false ∨ valuation q 1131 = false ∨ valuation q 1152 = true := counterClause1619 (baseVal q)

theorem counterClause1620 (q : Nat → Bool) : valuationOf q 1067 = false ∨ valuationOf q 1132 = false ∨ valuationOf q 1153 = true := by
  have hs : count1143 q = (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) + (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (l₂ := [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1067)) (literal (valuationOf q) (1132)) (literal (valuationOf q) (1153)) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) (count1143 q) 5 6 (meaning1067 q) (meaning1132 q) (meaning1153 q) hs
  change valuationOf q 1067 = false ∨ valuationOf q 1132 = false ∨ valuationOf q 1153 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1620 (q : Snake 81) (h : Conditions q) : valuation q 1067 = false ∨ valuation q 1132 = false ∨ valuation q 1153 = true := counterClause1620 (baseVal q)

theorem counterClause1621 (q : Nat → Bool) : valuationOf q 1067 = false ∨ valuationOf q 1133 = false ∨ valuationOf q 1154 = true := by
  have hs : count1143 q = (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) + (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (l₂ := [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1067)) (literal (valuationOf q) (1133)) (literal (valuationOf q) (1154)) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) (count1143 q) 5 7 (meaning1067 q) (meaning1133 q) (meaning1154 q) hs
  change valuationOf q 1067 = false ∨ valuationOf q 1133 = false ∨ valuationOf q 1154 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1621 (q : Snake 81) (h : Conditions q) : valuation q 1067 = false ∨ valuation q 1133 = false ∨ valuation q 1154 = true := counterClause1621 (baseVal q)

theorem counterClause1622 (q : Nat → Bool) : valuationOf q 1067 = false ∨ valuationOf q 1134 = false ∨ valuationOf q 1155 = true := by
  have hs : count1143 q = (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) + (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (l₂ := [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1067)) (literal (valuationOf q) (1134)) (literal (valuationOf q) (1155)) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) (count1143 q) 5 8 (meaning1067 q) (meaning1134 q) (meaning1155 q) hs
  change valuationOf q 1067 = false ∨ valuationOf q 1134 = false ∨ valuationOf q 1155 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1622 (q : Snake 81) (h : Conditions q) : valuation q 1067 = false ∨ valuation q 1134 = false ∨ valuation q 1155 = true := counterClause1622 (baseVal q)

theorem counterClause1623 (q : Nat → Bool) : valuationOf q 1068 = false ∨ valuationOf q 1129 = false ∨ valuationOf q 1151 = true := by
  have hs : count1143 q = (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) + (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (l₂ := [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1068)) (literal (valuationOf q) (1129)) (literal (valuationOf q) (1151)) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) (count1143 q) 6 3 (meaning1068 q) (meaning1129 q) (meaning1151 q) hs
  change valuationOf q 1068 = false ∨ valuationOf q 1129 = false ∨ valuationOf q 1151 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1623 (q : Snake 81) (h : Conditions q) : valuation q 1068 = false ∨ valuation q 1129 = false ∨ valuation q 1151 = true := counterClause1623 (baseVal q)

theorem counterClause1624 (q : Nat → Bool) : valuationOf q 1068 = false ∨ valuationOf q 1130 = false ∨ valuationOf q 1152 = true := by
  have hs : count1143 q = (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) + (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (l₂ := [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1068)) (literal (valuationOf q) (1130)) (literal (valuationOf q) (1152)) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) (count1143 q) 6 4 (meaning1068 q) (meaning1130 q) (meaning1152 q) hs
  change valuationOf q 1068 = false ∨ valuationOf q 1130 = false ∨ valuationOf q 1152 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1624 (q : Snake 81) (h : Conditions q) : valuation q 1068 = false ∨ valuation q 1130 = false ∨ valuation q 1152 = true := counterClause1624 (baseVal q)

theorem counterClause1625 (q : Nat → Bool) : valuationOf q 1068 = false ∨ valuationOf q 1131 = false ∨ valuationOf q 1153 = true := by
  have hs : count1143 q = (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) + (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (l₂ := [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1068)) (literal (valuationOf q) (1131)) (literal (valuationOf q) (1153)) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) (count1143 q) 6 5 (meaning1068 q) (meaning1131 q) (meaning1153 q) hs
  change valuationOf q 1068 = false ∨ valuationOf q 1131 = false ∨ valuationOf q 1153 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1625 (q : Snake 81) (h : Conditions q) : valuation q 1068 = false ∨ valuation q 1131 = false ∨ valuation q 1153 = true := counterClause1625 (baseVal q)

theorem counterClause1626 (q : Nat → Bool) : valuationOf q 1068 = false ∨ valuationOf q 1132 = false ∨ valuationOf q 1154 = true := by
  have hs : count1143 q = (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) + (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (l₂ := [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1068)) (literal (valuationOf q) (1132)) (literal (valuationOf q) (1154)) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) (count1143 q) 6 6 (meaning1068 q) (meaning1132 q) (meaning1154 q) hs
  change valuationOf q 1068 = false ∨ valuationOf q 1132 = false ∨ valuationOf q 1154 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1626 (q : Snake 81) (h : Conditions q) : valuation q 1068 = false ∨ valuation q 1132 = false ∨ valuation q 1154 = true := counterClause1626 (baseVal q)

theorem counterClause1627 (q : Nat → Bool) : valuationOf q 1068 = false ∨ valuationOf q 1133 = false ∨ valuationOf q 1155 = true := by
  have hs : count1143 q = (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) + (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (l₂ := [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1068)) (literal (valuationOf q) (1133)) (literal (valuationOf q) (1155)) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) (count1143 q) 6 7 (meaning1068 q) (meaning1133 q) (meaning1155 q) hs
  change valuationOf q 1068 = false ∨ valuationOf q 1133 = false ∨ valuationOf q 1155 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1627 (q : Snake 81) (h : Conditions q) : valuation q 1068 = false ∨ valuation q 1133 = false ∨ valuation q 1155 = true := counterClause1627 (baseVal q)

theorem counterClause1628 (q : Nat → Bool) : valuationOf q 1068 = false ∨ valuationOf q 1134 = false ∨ valuationOf q 1156 = true := by
  have hs : count1143 q = (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) + (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (l₂ := [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1068)) (literal (valuationOf q) (1134)) (literal (valuationOf q) (1156)) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) (count1143 q) 6 8 (meaning1068 q) (meaning1134 q) (meaning1156 q) hs
  change valuationOf q 1068 = false ∨ valuationOf q 1134 = false ∨ valuationOf q 1156 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1628 (q : Snake 81) (h : Conditions q) : valuation q 1068 = false ∨ valuation q 1134 = false ∨ valuation q 1156 = true := counterClause1628 (baseVal q)

theorem counterClause1629 (q : Nat → Bool) : valuationOf q 1069 = false ∨ valuationOf q 1129 = false ∨ valuationOf q 1152 = true := by
  have hs : count1143 q = (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) + (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (l₂ := [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1069)) (literal (valuationOf q) (1129)) (literal (valuationOf q) (1152)) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) (count1143 q) 7 3 (meaning1069 q) (meaning1129 q) (meaning1152 q) hs
  change valuationOf q 1069 = false ∨ valuationOf q 1129 = false ∨ valuationOf q 1152 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1629 (q : Snake 81) (h : Conditions q) : valuation q 1069 = false ∨ valuation q 1129 = false ∨ valuation q 1152 = true := counterClause1629 (baseVal q)

theorem counterClause1630 (q : Nat → Bool) : valuationOf q 1069 = false ∨ valuationOf q 1130 = false ∨ valuationOf q 1153 = true := by
  have hs : count1143 q = (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) + (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (l₂ := [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1069)) (literal (valuationOf q) (1130)) (literal (valuationOf q) (1153)) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) (count1143 q) 7 4 (meaning1069 q) (meaning1130 q) (meaning1153 q) hs
  change valuationOf q 1069 = false ∨ valuationOf q 1130 = false ∨ valuationOf q 1153 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1630 (q : Snake 81) (h : Conditions q) : valuation q 1069 = false ∨ valuation q 1130 = false ∨ valuation q 1153 = true := counterClause1630 (baseVal q)

theorem counterClause1631 (q : Nat → Bool) : valuationOf q 1069 = false ∨ valuationOf q 1131 = false ∨ valuationOf q 1154 = true := by
  have hs : count1143 q = (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) + (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (l₂ := [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1069)) (literal (valuationOf q) (1131)) (literal (valuationOf q) (1154)) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) (count1143 q) 7 5 (meaning1069 q) (meaning1131 q) (meaning1154 q) hs
  change valuationOf q 1069 = false ∨ valuationOf q 1131 = false ∨ valuationOf q 1154 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1631 (q : Snake 81) (h : Conditions q) : valuation q 1069 = false ∨ valuation q 1131 = false ∨ valuation q 1154 = true := counterClause1631 (baseVal q)

theorem counterClause1632 (q : Nat → Bool) : valuationOf q 1069 = false ∨ valuationOf q 1132 = false ∨ valuationOf q 1155 = true := by
  have hs : count1143 q = (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) + (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (l₂ := [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1069)) (literal (valuationOf q) (1132)) (literal (valuationOf q) (1155)) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) (count1143 q) 7 6 (meaning1069 q) (meaning1132 q) (meaning1155 q) hs
  change valuationOf q 1069 = false ∨ valuationOf q 1132 = false ∨ valuationOf q 1155 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1632 (q : Snake 81) (h : Conditions q) : valuation q 1069 = false ∨ valuation q 1132 = false ∨ valuation q 1155 = true := counterClause1632 (baseVal q)

theorem block50 (q : Snake 81) (h : Conditions q) : B112E121.Block50 (valuation q) :=
  ⟨clause1601 q h, clause1602 q h, clause1603 q h, clause1604 q h, clause1605 q h, clause1606 q h, clause1607 q h, clause1608 q h, clause1609 q h, clause1610 q h, clause1611 q h, clause1612 q h, clause1613 q h, clause1614 q h, clause1615 q h, clause1616 q h, clause1617 q h, clause1618 q h, clause1619 q h, clause1620 q h, clause1621 q h, clause1622 q h, clause1623 q h, clause1624 q h, clause1625 q h, clause1626 q h, clause1627 q h, clause1628 q h, clause1629 q h, clause1630 q h, clause1631 q h, clause1632 q h⟩

end
end Snake9.Regrowth.E112121
