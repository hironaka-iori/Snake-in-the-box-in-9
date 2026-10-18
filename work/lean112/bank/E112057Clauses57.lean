import E112057Semantics
import B112E057Inputs
namespace Snake9.Regrowth.E112057
noncomputable section
local instance blockDec57 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1825 (q : Nat → Bool) : valuationOf q 1079 = false ∨ valuationOf q 1131 = false ∨ valuationOf q 1160 = true := by
  have hs : count1147 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) + (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (l₂ := [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1079)) (literal (valuationOf q) (1131)) (literal (valuationOf q) (1160)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) (count1147 q) 13 1 (meaning1079 q) (meaning1131 q) (meaning1160 q) hs
  change valuationOf q 1079 = false ∨ valuationOf q 1131 = false ∨ valuationOf q 1160 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1825 (q : Snake 81) (h : Conditions q) : valuation q 1079 = false ∨ valuation q 1131 = false ∨ valuation q 1160 = true := counterClause1825 (baseVal q)

theorem counterClause1826 (q : Nat → Bool) : valuationOf q 1079 = false ∨ valuationOf q 1132 = false ∨ valuationOf q 1161 = true := by
  have hs : count1147 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) + (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (l₂ := [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1079)) (literal (valuationOf q) (1132)) (literal (valuationOf q) (1161)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) (count1147 q) 13 2 (meaning1079 q) (meaning1132 q) (meaning1161 q) hs
  change valuationOf q 1079 = false ∨ valuationOf q 1132 = false ∨ valuationOf q 1161 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1826 (q : Snake 81) (h : Conditions q) : valuation q 1079 = false ∨ valuation q 1132 = false ∨ valuation q 1161 = true := counterClause1826 (baseVal q)

theorem counterClause1827 (q : Nat → Bool) : valuationOf q 1003 = false ∨ valuationOf q 1161 = false ∨ valuationOf q 1194 = true := by
  have hs : count1171 q = (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33, -35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) + (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94, -95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33, -35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) (l₂ := [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94, -95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1003)) (literal (valuationOf q) (1161)) (literal (valuationOf q) (1194)) (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33, -35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94, -95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) (count1171 q) 9 15 (meaning1003 q) (meaning1161 q) (meaning1194 q) hs
  change valuationOf q 1003 = false ∨ valuationOf q 1161 = false ∨ valuationOf q 1194 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1827 (q : Snake 81) (h : Conditions q) : valuation q 1003 = false ∨ valuation q 1161 = false ∨ valuation q 1194 = true := counterClause1827 (baseVal q)

theorem counterClause1828 (q : Nat → Bool) : valuationOf q 1004 = false ∨ valuationOf q 1160 = false ∨ valuationOf q 1194 = true := by
  have hs : count1171 q = (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33, -35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) + (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94, -95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33, -35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) (l₂ := [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94, -95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1004)) (literal (valuationOf q) (1160)) (literal (valuationOf q) (1194)) (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33, -35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94, -95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) (count1171 q) 10 14 (meaning1004 q) (meaning1160 q) (meaning1194 q) hs
  change valuationOf q 1004 = false ∨ valuationOf q 1160 = false ∨ valuationOf q 1194 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1828 (q : Snake 81) (h : Conditions q) : valuation q 1004 = false ∨ valuation q 1160 = false ∨ valuation q 1194 = true := counterClause1828 (baseVal q)

theorem counterClause1829 (q : Nat → Bool) : valuationOf q 1005 = false ∨ valuationOf q 1159 = false ∨ valuationOf q 1194 = true := by
  have hs : count1171 q = (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33, -35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) + (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94, -95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33, -35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) (l₂ := [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94, -95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1005)) (literal (valuationOf q) (1159)) (literal (valuationOf q) (1194)) (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33, -35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94, -95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) (count1171 q) 11 13 (meaning1005 q) (meaning1159 q) (meaning1194 q) hs
  change valuationOf q 1005 = false ∨ valuationOf q 1159 = false ∨ valuationOf q 1194 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1829 (q : Snake 81) (h : Conditions q) : valuation q 1005 = false ∨ valuation q 1159 = false ∨ valuation q 1194 = true := counterClause1829 (baseVal q)

theorem counterClause1830 (q : Nat → Bool) : valuationOf q 1006 = false ∨ valuationOf q 1158 = false ∨ valuationOf q 1194 = true := by
  have hs : count1171 q = (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33, -35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) + (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94, -95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33, -35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) (l₂ := [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94, -95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1006)) (literal (valuationOf q) (1158)) (literal (valuationOf q) (1194)) (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33, -35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94, -95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) (count1171 q) 12 12 (meaning1006 q) (meaning1158 q) (meaning1194 q) hs
  change valuationOf q 1006 = false ∨ valuationOf q 1158 = false ∨ valuationOf q 1194 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1830 (q : Snake 81) (h : Conditions q) : valuation q 1006 = false ∨ valuation q 1158 = false ∨ valuation q 1194 = true := counterClause1830 (baseVal q)

theorem counterClause1831 (q : Nat → Bool) : valuationOf q 1007 = false ∨ valuationOf q 1157 = false ∨ valuationOf q 1194 = true := by
  have hs : count1171 q = (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33, -35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) + (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94, -95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33, -35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) (l₂ := [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94, -95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1007)) (literal (valuationOf q) (1157)) (literal (valuationOf q) (1194)) (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33, -35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94, -95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) (count1171 q) 13 11 (meaning1007 q) (meaning1157 q) (meaning1194 q) hs
  change valuationOf q 1007 = false ∨ valuationOf q 1157 = false ∨ valuationOf q 1194 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1831 (q : Snake 81) (h : Conditions q) : valuation q 1007 = false ∨ valuation q 1157 = false ∨ valuation q 1194 = true := counterClause1831 (baseVal q)

theorem counterClause1832 (q : Nat → Bool) : valuationOf q 1008 = false ∨ valuationOf q 1156 = false ∨ valuationOf q 1194 = true := by
  have hs : count1171 q = (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33, -35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) + (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94, -95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33, -35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) (l₂ := [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94, -95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1008)) (literal (valuationOf q) (1156)) (literal (valuationOf q) (1194)) (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33, -35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94, -95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) (count1171 q) 14 10 (meaning1008 q) (meaning1156 q) (meaning1194 q) hs
  change valuationOf q 1008 = false ∨ valuationOf q 1156 = false ∨ valuationOf q 1194 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1832 (q : Snake 81) (h : Conditions q) : valuation q 1008 = false ∨ valuation q 1156 = false ∨ valuation q 1194 = true := counterClause1832 (baseVal q)

theorem counterClause1833 (q : Nat → Bool) : valuationOf q 1009 = false ∨ valuationOf q 1155 = false ∨ valuationOf q 1194 = true := by
  have hs : count1171 q = (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33, -35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) + (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94, -95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33, -35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) (l₂ := [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94, -95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1009)) (literal (valuationOf q) (1155)) (literal (valuationOf q) (1194)) (countLit q [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33, -35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94, -95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) (count1171 q) 15 9 (meaning1009 q) (meaning1155 q) (meaning1194 q) hs
  change valuationOf q 1009 = false ∨ valuationOf q 1155 = false ∨ valuationOf q 1194 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1833 (q : Snake 81) (h : Conditions q) : valuation q 1009 = false ∨ valuation q 1155 = false ∨ valuation q 1194 = true := counterClause1833 (baseVal q)

theorem clause1834 (q : Snake 81) (h : Conditions q) : valuation q 1194 = false := by
  rw [value1194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1171 (baseVal q) = (evenSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_even_bound q h
  rw [evenSide_length] at hb
  rw [he]
  omega

theorem counterClause1835 (q : Nat → Bool) : valuationOf q 5 = true ∨ valuationOf q 1551 = true := by
  have hs : count1551 q = (countLit q [-3]) + (countLit q [-5]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-5])
  have hm := merge_right (literal (valuationOf q) (-5)) (literal (valuationOf q) (1551)) (countLit q [-3]) (countLit q [-5]) (count1551 q) 1 (meaningNeg5 q) (meaning1551 q) hs
  change (! (valuationOf q 5)) = false ∨ valuationOf q 1551 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1835 (q : Snake 81) (h : Conditions q) : valuation q 5 = true ∨ valuation q 1551 = true := counterClause1835 (baseVal q)

theorem counterClause1836 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 1551 = true := by
  have hs : count1551 q = (countLit q [-3]) + (countLit q [-5]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-5])
  have hm := merge_left (literal (valuationOf q) (-3)) (literal (valuationOf q) (1551)) (countLit q [-3]) (countLit q [-5]) (count1551 q) 1 (meaningNeg3 q) (meaning1551 q) hs
  change (! (valuationOf q 3)) = false ∨ valuationOf q 1551 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1836 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 1551 = true := counterClause1836 (baseVal q)

theorem counterClause1837 (q : Nat → Bool) : valuationOf q 1551 = false ∨ valuationOf q 1553 = true := by
  have hs : count1553 q = (countLit q [-2]) + (countLit q [-3, -5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-3, -5])
  have hm := merge_right (literal (valuationOf q) (1551)) (literal (valuationOf q) (1553)) (countLit q [-2]) (countLit q [-3, -5]) (count1553 q) 1 (meaning1551 q) (meaning1553 q) hs
  change valuationOf q 1551 = false ∨ valuationOf q 1553 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1837 (q : Snake 81) (h : Conditions q) : valuation q 1551 = false ∨ valuation q 1553 = true := counterClause1837 (baseVal q)

theorem counterClause1838 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1553 = true := by
  have hs : count1553 q = (countLit q [-2]) + (countLit q [-3, -5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-3, -5])
  have hm := merge_left (literal (valuationOf q) (-2)) (literal (valuationOf q) (1553)) (countLit q [-2]) (countLit q [-3, -5]) (count1553 q) 1 (meaningNeg2 q) (meaning1553 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1553 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1838 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1553 = true := counterClause1838 (baseVal q)

theorem counterClause1839 (q : Nat → Bool) : valuationOf q 12 = true ∨ valuationOf q 1556 = true := by
  have hs : count1556 q = (countLit q [-8]) + (countLit q [-12]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-12])
  have hm := merge_right (literal (valuationOf q) (-12)) (literal (valuationOf q) (1556)) (countLit q [-8]) (countLit q [-12]) (count1556 q) 1 (meaningNeg12 q) (meaning1556 q) hs
  change (! (valuationOf q 12)) = false ∨ valuationOf q 1556 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1839 (q : Snake 81) (h : Conditions q) : valuation q 12 = true ∨ valuation q 1556 = true := counterClause1839 (baseVal q)

theorem counterClause1840 (q : Nat → Bool) : valuationOf q 8 = true ∨ valuationOf q 1556 = true := by
  have hs : count1556 q = (countLit q [-8]) + (countLit q [-12]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-12])
  have hm := merge_left (literal (valuationOf q) (-8)) (literal (valuationOf q) (1556)) (countLit q [-8]) (countLit q [-12]) (count1556 q) 1 (meaningNeg8 q) (meaning1556 q) hs
  change (! (valuationOf q 8)) = false ∨ valuationOf q 1556 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1840 (q : Snake 81) (h : Conditions q) : valuation q 8 = true ∨ valuation q 1556 = true := counterClause1840 (baseVal q)

theorem counterClause1841 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 1558 = true := by
  have hs : count1558 q = (countLit q [-13]) + (countLit q [-14]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-14])
  have hm := merge_right (literal (valuationOf q) (-14)) (literal (valuationOf q) (1558)) (countLit q [-13]) (countLit q [-14]) (count1558 q) 1 (meaningNeg14 q) (meaning1558 q) hs
  change (! (valuationOf q 14)) = false ∨ valuationOf q 1558 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1841 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 1558 = true := counterClause1841 (baseVal q)

theorem counterClause1842 (q : Nat → Bool) : valuationOf q 13 = true ∨ valuationOf q 14 = true ∨ valuationOf q 1559 = true := by
  have hs : count1558 q = (countLit q [-13]) + (countLit q [-14]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-14])
  have hm := merge_two (literal (valuationOf q) (-13)) (literal (valuationOf q) (-14)) (literal (valuationOf q) (1559)) (countLit q [-13]) (countLit q [-14]) (count1558 q) 1 1 (meaningNeg13 q) (meaningNeg14 q) (meaning1559 q) hs
  change (! (valuationOf q 13)) = false ∨ (! (valuationOf q 14)) = false ∨ valuationOf q 1559 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1842 (q : Snake 81) (h : Conditions q) : valuation q 13 = true ∨ valuation q 14 = true ∨ valuation q 1559 = true := counterClause1842 (baseVal q)

theorem counterClause1843 (q : Nat → Bool) : valuationOf q 1558 = false ∨ valuationOf q 1560 = true := by
  have hs : count1560 q = (countLit q [-8, -12]) + (countLit q [-13, -14]) := List.countP_append (p := literal q) (l₁ := [-8, -12]) (l₂ := [-13, -14])
  have hm := merge_right (literal (valuationOf q) (1558)) (literal (valuationOf q) (1560)) (countLit q [-8, -12]) (countLit q [-13, -14]) (count1560 q) 1 (meaning1558 q) (meaning1560 q) hs
  change valuationOf q 1558 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1843 (q : Snake 81) (h : Conditions q) : valuation q 1558 = false ∨ valuation q 1560 = true := counterClause1843 (baseVal q)

theorem counterClause1844 (q : Nat → Bool) : valuationOf q 1559 = false ∨ valuationOf q 1561 = true := by
  have hs : count1560 q = (countLit q [-8, -12]) + (countLit q [-13, -14]) := List.countP_append (p := literal q) (l₁ := [-8, -12]) (l₂ := [-13, -14])
  have hm := merge_right (literal (valuationOf q) (1559)) (literal (valuationOf q) (1561)) (countLit q [-8, -12]) (countLit q [-13, -14]) (count1560 q) 2 (meaning1559 q) (meaning1561 q) hs
  change valuationOf q 1559 = false ∨ valuationOf q 1561 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1844 (q : Snake 81) (h : Conditions q) : valuation q 1559 = false ∨ valuation q 1561 = true := counterClause1844 (baseVal q)

theorem counterClause1845 (q : Nat → Bool) : valuationOf q 1556 = false ∨ valuationOf q 1560 = true := by
  have hs : count1560 q = (countLit q [-8, -12]) + (countLit q [-13, -14]) := List.countP_append (p := literal q) (l₁ := [-8, -12]) (l₂ := [-13, -14])
  have hm := merge_left (literal (valuationOf q) (1556)) (literal (valuationOf q) (1560)) (countLit q [-8, -12]) (countLit q [-13, -14]) (count1560 q) 1 (meaning1556 q) (meaning1560 q) hs
  change valuationOf q 1556 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1845 (q : Snake 81) (h : Conditions q) : valuation q 1556 = false ∨ valuation q 1560 = true := counterClause1845 (baseVal q)

theorem counterClause1846 (q : Nat → Bool) : valuationOf q 1556 = false ∨ valuationOf q 1558 = false ∨ valuationOf q 1561 = true := by
  have hs : count1560 q = (countLit q [-8, -12]) + (countLit q [-13, -14]) := List.countP_append (p := literal q) (l₁ := [-8, -12]) (l₂ := [-13, -14])
  have hm := merge_two (literal (valuationOf q) (1556)) (literal (valuationOf q) (1558)) (literal (valuationOf q) (1561)) (countLit q [-8, -12]) (countLit q [-13, -14]) (count1560 q) 1 1 (meaning1556 q) (meaning1558 q) (meaning1561 q) hs
  change valuationOf q 1556 = false ∨ valuationOf q 1558 = false ∨ valuationOf q 1561 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1846 (q : Snake 81) (h : Conditions q) : valuation q 1556 = false ∨ valuation q 1558 = false ∨ valuation q 1561 = true := counterClause1846 (baseVal q)

theorem counterClause1847 (q : Nat → Bool) : valuationOf q 1560 = false ∨ valuationOf q 1564 = true := by
  have hs : count1564 q = (countLit q [-2, -3, -5]) + (countLit q [-8, -12, -13, -14]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-8, -12, -13, -14])
  have hm := merge_right (literal (valuationOf q) (1560)) (literal (valuationOf q) (1564)) (countLit q [-2, -3, -5]) (countLit q [-8, -12, -13, -14]) (count1564 q) 1 (meaning1560 q) (meaning1564 q) hs
  change valuationOf q 1560 = false ∨ valuationOf q 1564 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1847 (q : Snake 81) (h : Conditions q) : valuation q 1560 = false ∨ valuation q 1564 = true := counterClause1847 (baseVal q)

theorem counterClause1848 (q : Nat → Bool) : valuationOf q 1561 = false ∨ valuationOf q 1565 = true := by
  have hs : count1564 q = (countLit q [-2, -3, -5]) + (countLit q [-8, -12, -13, -14]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-8, -12, -13, -14])
  have hm := merge_right (literal (valuationOf q) (1561)) (literal (valuationOf q) (1565)) (countLit q [-2, -3, -5]) (countLit q [-8, -12, -13, -14]) (count1564 q) 2 (meaning1561 q) (meaning1565 q) hs
  change valuationOf q 1561 = false ∨ valuationOf q 1565 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1848 (q : Snake 81) (h : Conditions q) : valuation q 1561 = false ∨ valuation q 1565 = true := counterClause1848 (baseVal q)

theorem counterClause1849 (q : Nat → Bool) : valuationOf q 1553 = false ∨ valuationOf q 1564 = true := by
  have hs : count1564 q = (countLit q [-2, -3, -5]) + (countLit q [-8, -12, -13, -14]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-8, -12, -13, -14])
  have hm := merge_left (literal (valuationOf q) (1553)) (literal (valuationOf q) (1564)) (countLit q [-2, -3, -5]) (countLit q [-8, -12, -13, -14]) (count1564 q) 1 (meaning1553 q) (meaning1564 q) hs
  change valuationOf q 1553 = false ∨ valuationOf q 1564 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1849 (q : Snake 81) (h : Conditions q) : valuation q 1553 = false ∨ valuation q 1564 = true := counterClause1849 (baseVal q)

theorem counterClause1850 (q : Nat → Bool) : valuationOf q 1553 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1565 = true := by
  have hs : count1564 q = (countLit q [-2, -3, -5]) + (countLit q [-8, -12, -13, -14]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-8, -12, -13, -14])
  have hm := merge_two (literal (valuationOf q) (1553)) (literal (valuationOf q) (1560)) (literal (valuationOf q) (1565)) (countLit q [-2, -3, -5]) (countLit q [-8, -12, -13, -14]) (count1564 q) 1 1 (meaning1553 q) (meaning1560 q) (meaning1565 q) hs
  change valuationOf q 1553 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1565 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1850 (q : Snake 81) (h : Conditions q) : valuation q 1553 = false ∨ valuation q 1560 = false ∨ valuation q 1565 = true := counterClause1850 (baseVal q)

theorem counterClause1851 (q : Nat → Bool) : valuationOf q 16 = true ∨ valuationOf q 1571 = true := by
  have hs : count1571 q = (countLit q [-16]) + (countLit q [-18]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-18])
  have hm := merge_left (literal (valuationOf q) (-16)) (literal (valuationOf q) (1571)) (countLit q [-16]) (countLit q [-18]) (count1571 q) 1 (meaningNeg16 q) (meaning1571 q) hs
  change (! (valuationOf q 16)) = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1851 (q : Snake 81) (h : Conditions q) : valuation q 16 = true ∨ valuation q 1571 = true := counterClause1851 (baseVal q)

theorem counterClause1852 (q : Nat → Bool) : valuationOf q 21 = true ∨ valuationOf q 1573 = true := by
  have hs : count1573 q = (countLit q [-20]) + (countLit q [-21]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-21])
  have hm := merge_right (literal (valuationOf q) (-21)) (literal (valuationOf q) (1573)) (countLit q [-20]) (countLit q [-21]) (count1573 q) 1 (meaningNeg21 q) (meaning1573 q) hs
  change (! (valuationOf q 21)) = false ∨ valuationOf q 1573 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1852 (q : Snake 81) (h : Conditions q) : valuation q 21 = true ∨ valuation q 1573 = true := counterClause1852 (baseVal q)

theorem counterClause1853 (q : Nat → Bool) : valuationOf q 20 = true ∨ valuationOf q 1573 = true := by
  have hs : count1573 q = (countLit q [-20]) + (countLit q [-21]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-21])
  have hm := merge_left (literal (valuationOf q) (-20)) (literal (valuationOf q) (1573)) (countLit q [-20]) (countLit q [-21]) (count1573 q) 1 (meaningNeg20 q) (meaning1573 q) hs
  change (! (valuationOf q 20)) = false ∨ valuationOf q 1573 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1853 (q : Snake 81) (h : Conditions q) : valuation q 20 = true ∨ valuation q 1573 = true := counterClause1853 (baseVal q)

theorem counterClause1854 (q : Nat → Bool) : valuationOf q 1571 = false ∨ valuationOf q 1573 = false ∨ valuationOf q 1576 = true := by
  have hs : count1575 q = (countLit q [-16, -18]) + (countLit q [-20, -21]) := List.countP_append (p := literal q) (l₁ := [-16, -18]) (l₂ := [-20, -21])
  have hm := merge_two (literal (valuationOf q) (1571)) (literal (valuationOf q) (1573)) (literal (valuationOf q) (1576)) (countLit q [-16, -18]) (countLit q [-20, -21]) (count1575 q) 1 1 (meaning1571 q) (meaning1573 q) (meaning1576 q) hs
  change valuationOf q 1571 = false ∨ valuationOf q 1573 = false ∨ valuationOf q 1576 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1854 (q : Snake 81) (h : Conditions q) : valuation q 1571 = false ∨ valuation q 1573 = false ∨ valuation q 1576 = true := counterClause1854 (baseVal q)

theorem counterClause1855 (q : Nat → Bool) : valuationOf q 24 = true ∨ valuationOf q 1579 = true := by
  have hs : count1579 q = (countLit q [-23]) + (countLit q [-24]) := List.countP_append (p := literal q) (l₁ := [-23]) (l₂ := [-24])
  have hm := merge_right (literal (valuationOf q) (-24)) (literal (valuationOf q) (1579)) (countLit q [-23]) (countLit q [-24]) (count1579 q) 1 (meaningNeg24 q) (meaning1579 q) hs
  change (! (valuationOf q 24)) = false ∨ valuationOf q 1579 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1855 (q : Snake 81) (h : Conditions q) : valuation q 24 = true ∨ valuation q 1579 = true := counterClause1855 (baseVal q)

theorem counterClause1856 (q : Nat → Bool) : valuationOf q 23 = true ∨ valuationOf q 1579 = true := by
  have hs : count1579 q = (countLit q [-23]) + (countLit q [-24]) := List.countP_append (p := literal q) (l₁ := [-23]) (l₂ := [-24])
  have hm := merge_left (literal (valuationOf q) (-23)) (literal (valuationOf q) (1579)) (countLit q [-23]) (countLit q [-24]) (count1579 q) 1 (meaningNeg23 q) (meaning1579 q) hs
  change (! (valuationOf q 23)) = false ∨ valuationOf q 1579 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1856 (q : Snake 81) (h : Conditions q) : valuation q 23 = true ∨ valuation q 1579 = true := counterClause1856 (baseVal q)

theorem block57 (q : Snake 81) (h : Conditions q) : B112E057.Block57 (valuation q) :=
  ⟨clause1825 q h, clause1826 q h, clause1827 q h, clause1828 q h, clause1829 q h, clause1830 q h, clause1831 q h, clause1832 q h, clause1833 q h, clause1834 q h, clause1835 q h, clause1836 q h, clause1837 q h, clause1838 q h, clause1839 q h, clause1840 q h, clause1841 q h, clause1842 q h, clause1843 q h, clause1844 q h, clause1845 q h, clause1846 q h, clause1847 q h, clause1848 q h, clause1849 q h, clause1850 q h, clause1851 q h, clause1852 q h, clause1853 q h, clause1854 q h, clause1855 q h, clause1856 q h⟩

end
end Snake9.Regrowth.E112057
