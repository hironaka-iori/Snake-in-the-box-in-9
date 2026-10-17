import E112081Semantics
import B112E081Inputs
namespace Snake9.Regrowth.E112081
noncomputable section
local instance blockDec36 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1153 (q : Nat → Bool) : valuationOf q 924 = false ∨ valuationOf q 1050 = false ∨ valuationOf q 1084 = true := by
  have hs : count1066 q = (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29, -30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) + (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29, -30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) (l₂ := [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_two (literal (valuationOf q) (924)) (literal (valuationOf q) (1050)) (literal (valuationOf q) (1084)) (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29, -30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) (count1066 q) 15 4 (meaning924 q) (meaning1050 q) (meaning1084 q) hs
  change valuationOf q 924 = false ∨ valuationOf q 1050 = false ∨ valuationOf q 1084 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1153 (q : Snake 81) (h : Conditions q) : valuation q 924 = false ∨ valuation q 1050 = false ∨ valuation q 1084 = true := counterClause1153 (baseVal q)

theorem counterClause1154 (q : Nat → Bool) : valuationOf q 925 = false ∨ valuationOf q 1049 = false ∨ valuationOf q 1084 = true := by
  have hs : count1066 q = (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29, -30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) + (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29, -30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) (l₂ := [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_two (literal (valuationOf q) (925)) (literal (valuationOf q) (1049)) (literal (valuationOf q) (1084)) (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29, -30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) (count1066 q) 16 3 (meaning925 q) (meaning1049 q) (meaning1084 q) hs
  change valuationOf q 925 = false ∨ valuationOf q 1049 = false ∨ valuationOf q 1084 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1154 (q : Snake 81) (h : Conditions q) : valuation q 925 = false ∨ valuation q 1049 = false ∨ valuation q 1084 = true := counterClause1154 (baseVal q)

theorem counterClause1155 (q : Nat → Bool) : valuationOf q 926 = false ∨ valuationOf q 1048 = false ∨ valuationOf q 1084 = true := by
  have hs : count1066 q = (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29, -30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) + (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29, -30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) (l₂ := [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117])
  have hm := merge_two (literal (valuationOf q) (926)) (literal (valuationOf q) (1048)) (literal (valuationOf q) (1084)) (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29, -30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) (countLit q [-57, -60, -62, -65, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -87, -89, -92, -95, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]) (count1066 q) 17 2 (meaning926 q) (meaning1048 q) (meaning1084 q) hs
  change valuationOf q 926 = false ∨ valuationOf q 1048 = false ∨ valuationOf q 1084 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1155 (q : Snake 81) (h : Conditions q) : valuation q 926 = false ∨ valuation q 1048 = false ∨ valuation q 1084 = true := counterClause1155 (baseVal q)

theorem clause1156 (q : Snake 81) (h : Conditions q) : valuation q 1084 = false := by
  rw [value1084]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1066 (baseVal q) = (evenSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_even_bound q h
  rw [evenSide_length] at hb
  rw [he]
  omega

theorem clause1157 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 2 = false ∨ valuation q 8 = false ∨ valuation q 9 = false := by
  rw [value1, value2, value8, value9]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (0 : Vertex) (1 : Vertex) (16 : Vertex) (17 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1158 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 2 = false ∨ valuation q 46 = false ∨ valuation q 47 = false := by
  rw [value1, value2, value46, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (0 : Vertex) (1 : Vertex) (256 : Vertex) (257 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1159 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 19 = false ∨ valuation q 51 = false ∨ valuation q 89 = false := by
  rw [value3, value19, value51, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (6 : Vertex) (134 : Vertex) (262 : Vertex) (390 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1160 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 7 = false ∨ valuation q 55 = false ∨ valuation q 58 = false := by
  rw [value5, value7, value55, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (11 : Vertex) (15 : Vertex) (267 : Vertex) (271 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1161 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 9 = false ∨ valuation q 10 = false ∨ valuation q 11 = false := by
  rw [value8, value9, value10, value11]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (16 : Vertex) (17 : Vertex) (18 : Vertex) (19 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1162 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 11 = false ∨ valuation q 59 = false ∨ valuation q 60 = false := by
  rw [value9, value11, value59, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (17 : Vertex) (19 : Vertex) (273 : Vertex) (275 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1163 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 17 = false ∨ valuation q 18 = false ∨ valuation q 19 = false := by
  rw [value16, value17, value18, value19]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (128 : Vertex) (130 : Vertex) (132 : Vertex) (134 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1164 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 19 = false ∨ valuation q 24 = false ∨ valuation q 25 = false := by
  rw [value18, value19, value24, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (132 : Vertex) (134 : Vertex) (140 : Vertex) (142 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1165 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 23 = false ∨ valuation q 24 = false ∨ valuation q 25 = false := by
  rw [value21, value23, value24, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (136 : Vertex) (138 : Vertex) (140 : Vertex) (142 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1166 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 47 = false ∨ valuation q 69 = false ∨ valuation q 70 = false := by
  rw [value46, value47, value69, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (256 : Vertex) (257 : Vertex) (320 : Vertex) (321 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1167 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 48 = false ∨ valuation q 49 = false ∨ valuation q 51 = false := by
  rw [value46, value48, value49, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (256 : Vertex) (258 : Vertex) (260 : Vertex) (262 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1168 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 48 = false ∨ valuation q 53 = false ∨ valuation q 54 = false := by
  rw [value46, value48, value53, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (256 : Vertex) (258 : Vertex) (264 : Vertex) (266 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1169 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 53 = false ∨ valuation q 69 = false ∨ valuation q 73 = false := by
  rw [value46, value53, value69, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (256 : Vertex) (264 : Vertex) (320 : Vertex) (328 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1170 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 59 = false ∨ valuation q 70 = false ∨ valuation q 78 = false := by
  rw [value47, value59, value70, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (257 : Vertex) (273 : Vertex) (321 : Vertex) (337 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1171 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 59 = false ∨ valuation q 88 = false ∨ valuation q 96 = false := by
  rw [value47, value59, value88, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (257 : Vertex) (273 : Vertex) (385 : Vertex) (401 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1172 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 51 = false ∨ valuation q 54 = false ∨ valuation q 57 = false := by
  rw [value48, value51, value54, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (258 : Vertex) (262 : Vertex) (266 : Vertex) (270 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1173 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 50 = false ∨ valuation q 51 = false ∨ valuation q 52 = false := by
  rw [value49, value50, value51, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (260 : Vertex) (261 : Vertex) (262 : Vertex) (263 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1174 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 50 = false ∨ valuation q 61 = false ∨ valuation q 62 = false := by
  rw [value49, value50, value61, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (260 : Vertex) (261 : Vertex) (276 : Vertex) (277 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1175 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 51 = false ∨ valuation q 56 = false ∨ valuation q 57 = false := by
  rw [value49, value51, value56, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (260 : Vertex) (262 : Vertex) (268 : Vertex) (270 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1176 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 52 = false ∨ valuation q 57 = false ∨ valuation q 58 = false := by
  rw [value51, value52, value57, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (262 : Vertex) (263 : Vertex) (270 : Vertex) (271 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1177 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 52 = false ∨ valuation q 71 = false ∨ valuation q 72 = false := by
  rw [value51, value52, value71, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (262 : Vertex) (263 : Vertex) (326 : Vertex) (327 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1178 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 52 = false ∨ valuation q 89 = false ∨ valuation q 90 = false := by
  rw [value51, value52, value89, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (262 : Vertex) (263 : Vertex) (390 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1179 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 58 = false ∨ valuation q 63 = false ∨ valuation q 68 = false := by
  rw [value52, value58, value63, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (263 : Vertex) (271 : Vertex) (279 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1180 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 54 = false ∨ valuation q 56 = false ∨ valuation q 57 = false := by
  rw [value53, value54, value56, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (264 : Vertex) (266 : Vertex) (268 : Vertex) (270 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1181 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 55 = false ∨ valuation q 57 = false ∨ valuation q 58 = false := by
  rw [value54, value55, value57, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (266 : Vertex) (267 : Vertex) (270 : Vertex) (271 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1182 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 58 = false ∨ valuation q 67 = false ∨ valuation q 68 = false := by
  rw [value55, value58, value67, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (267 : Vertex) (271 : Vertex) (283 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1183 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 58 = false ∨ valuation q 75 = false ∨ valuation q 77 = false := by
  rw [value55, value58, value75, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (267 : Vertex) (271 : Vertex) (331 : Vertex) (335 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1184 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 60 = false ∨ valuation q 62 = false ∨ valuation q 63 = false := by
  rw [value59, value60, value62, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (273 : Vertex) (275 : Vertex) (277 : Vertex) (279 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block36 (q : Snake 81) (h : Conditions q) : B112E081.Block36 (valuation q) :=
  ⟨clause1153 q h, clause1154 q h, clause1155 q h, clause1156 q h, clause1157 q h, clause1158 q h, clause1159 q h, clause1160 q h, clause1161 q h, clause1162 q h, clause1163 q h, clause1164 q h, clause1165 q h, clause1166 q h, clause1167 q h, clause1168 q h, clause1169 q h, clause1170 q h, clause1171 q h, clause1172 q h, clause1173 q h, clause1174 q h, clause1175 q h, clause1176 q h, clause1177 q h, clause1178 q h, clause1179 q h, clause1180 q h, clause1181 q h, clause1182 q h, clause1183 q h, clause1184 q h⟩

end
end Snake9.Regrowth.E112081
