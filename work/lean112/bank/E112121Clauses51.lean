import E112121Semantics
import B112E121Inputs
namespace Snake9.Regrowth.E112121
noncomputable section
local instance blockDec51 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1633 (q : Nat → Bool) : valuationOf q 1069 = false ∨ valuationOf q 1133 = false ∨ valuationOf q 1156 = true := by
  have hs : count1143 q = (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) + (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (l₂ := [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1069)) (literal (valuationOf q) (1133)) (literal (valuationOf q) (1156)) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) (count1143 q) 7 7 (meaning1069 q) (meaning1133 q) (meaning1156 q) hs
  change valuationOf q 1069 = false ∨ valuationOf q 1133 = false ∨ valuationOf q 1156 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1633 (q : Snake 81) (h : Conditions q) : valuation q 1069 = false ∨ valuation q 1133 = false ∨ valuation q 1156 = true := counterClause1633 (baseVal q)

theorem counterClause1634 (q : Nat → Bool) : valuationOf q 1070 = false ∨ valuationOf q 1129 = false ∨ valuationOf q 1153 = true := by
  have hs : count1143 q = (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) + (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (l₂ := [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1070)) (literal (valuationOf q) (1129)) (literal (valuationOf q) (1153)) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) (count1143 q) 8 3 (meaning1070 q) (meaning1129 q) (meaning1153 q) hs
  change valuationOf q 1070 = false ∨ valuationOf q 1129 = false ∨ valuationOf q 1153 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1634 (q : Snake 81) (h : Conditions q) : valuation q 1070 = false ∨ valuation q 1129 = false ∨ valuation q 1153 = true := counterClause1634 (baseVal q)

theorem counterClause1635 (q : Nat → Bool) : valuationOf q 1070 = false ∨ valuationOf q 1130 = false ∨ valuationOf q 1154 = true := by
  have hs : count1143 q = (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) + (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (l₂ := [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1070)) (literal (valuationOf q) (1130)) (literal (valuationOf q) (1154)) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) (count1143 q) 8 4 (meaning1070 q) (meaning1130 q) (meaning1154 q) hs
  change valuationOf q 1070 = false ∨ valuationOf q 1130 = false ∨ valuationOf q 1154 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1635 (q : Snake 81) (h : Conditions q) : valuation q 1070 = false ∨ valuation q 1130 = false ∨ valuation q 1154 = true := counterClause1635 (baseVal q)

theorem counterClause1636 (q : Nat → Bool) : valuationOf q 1070 = false ∨ valuationOf q 1131 = false ∨ valuationOf q 1155 = true := by
  have hs : count1143 q = (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) + (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (l₂ := [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1070)) (literal (valuationOf q) (1131)) (literal (valuationOf q) (1155)) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) (count1143 q) 8 5 (meaning1070 q) (meaning1131 q) (meaning1155 q) hs
  change valuationOf q 1070 = false ∨ valuationOf q 1131 = false ∨ valuationOf q 1155 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1636 (q : Snake 81) (h : Conditions q) : valuation q 1070 = false ∨ valuation q 1131 = false ∨ valuation q 1155 = true := counterClause1636 (baseVal q)

theorem counterClause1637 (q : Nat → Bool) : valuationOf q 1070 = false ∨ valuationOf q 1132 = false ∨ valuationOf q 1156 = true := by
  have hs : count1143 q = (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) + (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (l₂ := [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1070)) (literal (valuationOf q) (1132)) (literal (valuationOf q) (1156)) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) (count1143 q) 8 6 (meaning1070 q) (meaning1132 q) (meaning1156 q) hs
  change valuationOf q 1070 = false ∨ valuationOf q 1132 = false ∨ valuationOf q 1156 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1637 (q : Snake 81) (h : Conditions q) : valuation q 1070 = false ∨ valuation q 1132 = false ∨ valuation q 1156 = true := counterClause1637 (baseVal q)

theorem counterClause1638 (q : Nat → Bool) : valuationOf q 1070 = false ∨ valuationOf q 1133 = false ∨ valuationOf q 1157 = true := by
  have hs : count1143 q = (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) + (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (l₂ := [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1070)) (literal (valuationOf q) (1133)) (literal (valuationOf q) (1157)) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) (count1143 q) 8 7 (meaning1070 q) (meaning1133 q) (meaning1157 q) hs
  change valuationOf q 1070 = false ∨ valuationOf q 1133 = false ∨ valuationOf q 1157 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1638 (q : Snake 81) (h : Conditions q) : valuation q 1070 = false ∨ valuation q 1133 = false ∨ valuation q 1157 = true := counterClause1638 (baseVal q)

theorem counterClause1639 (q : Nat → Bool) : valuationOf q 999 = false ∨ valuationOf q 1157 = false ∨ valuationOf q 1190 = true := by
  have hs : count1167 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31, -32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) + (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93, -94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31, -32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) (l₂ := [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93, -94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (999)) (literal (valuationOf q) (1157)) (literal (valuationOf q) (1190)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31, -32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93, -94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) (count1167 q) 9 15 (meaning999 q) (meaning1157 q) (meaning1190 q) hs
  change valuationOf q 999 = false ∨ valuationOf q 1157 = false ∨ valuationOf q 1190 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1639 (q : Snake 81) (h : Conditions q) : valuation q 999 = false ∨ valuation q 1157 = false ∨ valuation q 1190 = true := counterClause1639 (baseVal q)

theorem counterClause1640 (q : Nat → Bool) : valuationOf q 1000 = false ∨ valuationOf q 1156 = false ∨ valuationOf q 1190 = true := by
  have hs : count1167 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31, -32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) + (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93, -94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31, -32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) (l₂ := [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93, -94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1000)) (literal (valuationOf q) (1156)) (literal (valuationOf q) (1190)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31, -32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93, -94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) (count1167 q) 10 14 (meaning1000 q) (meaning1156 q) (meaning1190 q) hs
  change valuationOf q 1000 = false ∨ valuationOf q 1156 = false ∨ valuationOf q 1190 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1640 (q : Snake 81) (h : Conditions q) : valuation q 1000 = false ∨ valuation q 1156 = false ∨ valuation q 1190 = true := counterClause1640 (baseVal q)

theorem counterClause1641 (q : Nat → Bool) : valuationOf q 1001 = false ∨ valuationOf q 1155 = false ∨ valuationOf q 1190 = true := by
  have hs : count1167 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31, -32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) + (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93, -94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31, -32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) (l₂ := [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93, -94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1001)) (literal (valuationOf q) (1155)) (literal (valuationOf q) (1190)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31, -32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93, -94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) (count1167 q) 11 13 (meaning1001 q) (meaning1155 q) (meaning1190 q) hs
  change valuationOf q 1001 = false ∨ valuationOf q 1155 = false ∨ valuationOf q 1190 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1641 (q : Snake 81) (h : Conditions q) : valuation q 1001 = false ∨ valuation q 1155 = false ∨ valuation q 1190 = true := counterClause1641 (baseVal q)

theorem counterClause1642 (q : Nat → Bool) : valuationOf q 1002 = false ∨ valuationOf q 1154 = false ∨ valuationOf q 1190 = true := by
  have hs : count1167 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31, -32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) + (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93, -94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31, -32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) (l₂ := [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93, -94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1002)) (literal (valuationOf q) (1154)) (literal (valuationOf q) (1190)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31, -32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93, -94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) (count1167 q) 12 12 (meaning1002 q) (meaning1154 q) (meaning1190 q) hs
  change valuationOf q 1002 = false ∨ valuationOf q 1154 = false ∨ valuationOf q 1190 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1642 (q : Snake 81) (h : Conditions q) : valuation q 1002 = false ∨ valuation q 1154 = false ∨ valuation q 1190 = true := counterClause1642 (baseVal q)

theorem counterClause1643 (q : Nat → Bool) : valuationOf q 1003 = false ∨ valuationOf q 1153 = false ∨ valuationOf q 1190 = true := by
  have hs : count1167 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31, -32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) + (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93, -94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31, -32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) (l₂ := [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93, -94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1003)) (literal (valuationOf q) (1153)) (literal (valuationOf q) (1190)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31, -32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93, -94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) (count1167 q) 13 11 (meaning1003 q) (meaning1153 q) (meaning1190 q) hs
  change valuationOf q 1003 = false ∨ valuationOf q 1153 = false ∨ valuationOf q 1190 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1643 (q : Snake 81) (h : Conditions q) : valuation q 1003 = false ∨ valuation q 1153 = false ∨ valuation q 1190 = true := counterClause1643 (baseVal q)

theorem counterClause1644 (q : Nat → Bool) : valuationOf q 1004 = false ∨ valuationOf q 1152 = false ∨ valuationOf q 1190 = true := by
  have hs : count1167 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31, -32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) + (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93, -94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31, -32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) (l₂ := [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93, -94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1004)) (literal (valuationOf q) (1152)) (literal (valuationOf q) (1190)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31, -32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93, -94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) (count1167 q) 14 10 (meaning1004 q) (meaning1152 q) (meaning1190 q) hs
  change valuationOf q 1004 = false ∨ valuationOf q 1152 = false ∨ valuationOf q 1190 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1644 (q : Snake 81) (h : Conditions q) : valuation q 1004 = false ∨ valuation q 1152 = false ∨ valuation q 1190 = true := counterClause1644 (baseVal q)

theorem counterClause1645 (q : Nat → Bool) : valuationOf q 1005 = false ∨ valuationOf q 1151 = false ∨ valuationOf q 1190 = true := by
  have hs : count1167 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31, -32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) + (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93, -94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31, -32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) (l₂ := [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93, -94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1005)) (literal (valuationOf q) (1151)) (literal (valuationOf q) (1190)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31, -32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93, -94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) (count1167 q) 15 9 (meaning1005 q) (meaning1151 q) (meaning1190 q) hs
  change valuationOf q 1005 = false ∨ valuationOf q 1151 = false ∨ valuationOf q 1190 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1645 (q : Snake 81) (h : Conditions q) : valuation q 1005 = false ∨ valuation q 1151 = false ∨ valuation q 1190 = true := counterClause1645 (baseVal q)

theorem counterClause1646 (q : Nat → Bool) : valuationOf q 1006 = false ∨ valuationOf q 1150 = false ∨ valuationOf q 1190 = true := by
  have hs : count1167 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31, -32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) + (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93, -94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31, -32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) (l₂ := [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93, -94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1006)) (literal (valuationOf q) (1150)) (literal (valuationOf q) (1190)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31, -32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93, -94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) (count1167 q) 16 8 (meaning1006 q) (meaning1150 q) (meaning1190 q) hs
  change valuationOf q 1006 = false ∨ valuationOf q 1150 = false ∨ valuationOf q 1190 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1646 (q : Snake 81) (h : Conditions q) : valuation q 1006 = false ∨ valuation q 1150 = false ∨ valuation q 1190 = true := counterClause1646 (baseVal q)

theorem counterClause1647 (q : Nat → Bool) : valuationOf q 1007 = false ∨ valuationOf q 1149 = false ∨ valuationOf q 1190 = true := by
  have hs : count1167 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31, -32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) + (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93, -94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31, -32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) (l₂ := [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93, -94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1007)) (literal (valuationOf q) (1149)) (literal (valuationOf q) (1190)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31, -32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93, -94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) (count1167 q) 17 7 (meaning1007 q) (meaning1149 q) (meaning1190 q) hs
  change valuationOf q 1007 = false ∨ valuationOf q 1149 = false ∨ valuationOf q 1190 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1647 (q : Snake 81) (h : Conditions q) : valuation q 1007 = false ∨ valuation q 1149 = false ∨ valuation q 1190 = true := counterClause1647 (baseVal q)

theorem counterClause1648 (q : Nat → Bool) : valuationOf q 1008 = false ∨ valuationOf q 1148 = false ∨ valuationOf q 1190 = true := by
  have hs : count1167 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31, -32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) + (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93, -94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31, -32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) (l₂ := [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93, -94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1008)) (literal (valuationOf q) (1148)) (literal (valuationOf q) (1190)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31, -32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93, -94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) (count1167 q) 18 6 (meaning1008 q) (meaning1148 q) (meaning1190 q) hs
  change valuationOf q 1008 = false ∨ valuationOf q 1148 = false ∨ valuationOf q 1190 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1648 (q : Snake 81) (h : Conditions q) : valuation q 1008 = false ∨ valuation q 1148 = false ∨ valuation q 1190 = true := counterClause1648 (baseVal q)

theorem clause1649 (q : Snake 81) (h : Conditions q) : valuation q 1190 = false := by
  rw [value1190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1167 (baseVal q) = (evenSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_even_bound q h
  rw [evenSide_length] at hb
  rw [he]
  omega

theorem clause1650 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 2 = false ∨ valuation q 8 = false ∨ valuation q 9 = false := by
  rw [value1, value2, value8, value9]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (0 : Vertex) (1 : Vertex) (32 : Vertex) (33 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1651 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 4 = false ∨ valuation q 9 = false ∨ valuation q 20 = false := by
  rw [value2, value4, value9, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (1 : Vertex) (17 : Vertex) (33 : Vertex) (49 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1652 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 7 = false ∨ valuation q 13 = false ∨ valuation q 25 = false := by
  rw [value3, value7, value13, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (6 : Vertex) (22 : Vertex) (38 : Vertex) (54 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1653 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 13 = false ∨ valuation q 33 = false ∨ valuation q 35 = false := by
  rw [value3, value13, value33, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (6 : Vertex) (38 : Vertex) (70 : Vertex) (102 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1654 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 6 = false ∨ valuation q 20 = false ∨ valuation q 22 = false := by
  rw [value4, value6, value20, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (17 : Vertex) (19 : Vertex) (49 : Vertex) (51 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1655 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 6 = false ∨ valuation q 21 = false ∨ valuation q 22 = false := by
  rw [value5, value6, value21, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (18 : Vertex) (19 : Vertex) (50 : Vertex) (51 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1656 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 7 = false ∨ valuation q 21 = false ∨ valuation q 25 = false := by
  rw [value5, value7, value21, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (18 : Vertex) (22 : Vertex) (50 : Vertex) (54 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1657 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 9 = false ∨ valuation q 11 = false ∨ valuation q 12 = false := by
  rw [value8, value9, value11, value12]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (32 : Vertex) (33 : Vertex) (36 : Vertex) (37 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1658 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 9 = false ∨ valuation q 44 = false ∨ valuation q 45 = false := by
  rw [value8, value9, value44, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (32 : Vertex) (33 : Vertex) (160 : Vertex) (161 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1659 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 9 = false ∨ valuation q 69 = false ∨ valuation q 70 = false := by
  rw [value8, value9, value69, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (32 : Vertex) (33 : Vertex) (288 : Vertex) (289 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1660 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 10 = false ∨ valuation q 15 = false ∨ valuation q 17 = false := by
  rw [value8, value10, value15, value17]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (32 : Vertex) (34 : Vertex) (40 : Vertex) (42 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1661 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 11 = false ∨ valuation q 15 = false ∨ valuation q 18 = false := by
  rw [value8, value11, value15, value18]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (32 : Vertex) (36 : Vertex) (40 : Vertex) (44 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1662 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 15 = false ∨ valuation q 44 = false ∨ valuation q 48 = false := by
  rw [value8, value15, value44, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (32 : Vertex) (40 : Vertex) (160 : Vertex) (168 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1663 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 15 = false ∨ valuation q 69 = false ∨ valuation q 73 = false := by
  rw [value8, value15, value69, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (32 : Vertex) (40 : Vertex) (288 : Vertex) (296 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1664 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 44 = false ∨ valuation q 69 = false ∨ valuation q 87 = false := by
  rw [value8, value44, value69, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (32 : Vertex) (160 : Vertex) (288 : Vertex) (416 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block51 (q : Snake 81) (h : Conditions q) : B112E121.Block51 (valuation q) :=
  ⟨clause1633 q h, clause1634 q h, clause1635 q h, clause1636 q h, clause1637 q h, clause1638 q h, clause1639 q h, clause1640 q h, clause1641 q h, clause1642 q h, clause1643 q h, clause1644 q h, clause1645 q h, clause1646 q h, clause1647 q h, clause1648 q h, clause1649 q h, clause1650 q h, clause1651 q h, clause1652 q h, clause1653 q h, clause1654 q h, clause1655 q h, clause1656 q h, clause1657 q h, clause1658 q h, clause1659 q h, clause1660 q h, clause1661 q h, clause1662 q h, clause1663 q h, clause1664 q h⟩

end
end Snake9.Regrowth.E112121
