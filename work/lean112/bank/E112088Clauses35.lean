import E112088Semantics
import B112E088Inputs
namespace Snake9.Regrowth.E112088
noncomputable section
local instance blockDec35 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1121 (q : Nat → Bool) : valuationOf q 1509 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1672 = true := by
  have hs : count1654 q = (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28, -29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) + (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87, -88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28, -29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) (l₂ := [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87, -88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116])
  have hm := merge_two (literal (valuationOf q) (1509)) (literal (valuationOf q) (1641)) (literal (valuationOf q) (1672)) (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28, -29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87, -88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) (count1654 q) 12 7 (meaning1509 q) (meaning1641 q) (meaning1672 q) hs
  change valuationOf q 1509 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1121 (q : Snake 81) (h : Conditions q) : valuation q 1509 = false ∨ valuation q 1641 = false ∨ valuation q 1672 = true := counterClause1121 (baseVal q)

theorem counterClause1122 (q : Nat → Bool) : valuationOf q 1510 = false ∨ valuationOf q 1640 = false ∨ valuationOf q 1672 = true := by
  have hs : count1654 q = (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28, -29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) + (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87, -88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28, -29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) (l₂ := [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87, -88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116])
  have hm := merge_two (literal (valuationOf q) (1510)) (literal (valuationOf q) (1640)) (literal (valuationOf q) (1672)) (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28, -29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87, -88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) (count1654 q) 13 6 (meaning1510 q) (meaning1640 q) (meaning1672 q) hs
  change valuationOf q 1510 = false ∨ valuationOf q 1640 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1122 (q : Snake 81) (h : Conditions q) : valuation q 1510 = false ∨ valuation q 1640 = false ∨ valuation q 1672 = true := counterClause1122 (baseVal q)

theorem counterClause1123 (q : Nat → Bool) : valuationOf q 1512 = false ∨ valuationOf q 1638 = false ∨ valuationOf q 1672 = true := by
  have hs : count1654 q = (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28, -29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) + (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87, -88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28, -29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) (l₂ := [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87, -88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116])
  have hm := merge_two (literal (valuationOf q) (1512)) (literal (valuationOf q) (1638)) (literal (valuationOf q) (1672)) (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28, -29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87, -88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) (count1654 q) 15 4 (meaning1512 q) (meaning1638 q) (meaning1672 q) hs
  change valuationOf q 1512 = false ∨ valuationOf q 1638 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1123 (q : Snake 81) (h : Conditions q) : valuation q 1512 = false ∨ valuation q 1638 = false ∨ valuation q 1672 = true := counterClause1123 (baseVal q)

theorem clause1124 (q : Snake 81) (h : Conditions q) : valuation q 1672 = false := by
  rw [value1672]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1654 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem clause1125 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 3 = false ∨ valuation q 5 = false ∨ valuation q 7 = false := by
  rw [value1, value3, value5, value7]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (99 : Vertex) (103 : Vertex) (107 : Vertex) (111 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1126 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 3 = false ∨ valuation q 33 = false ∨ valuation q 37 = false := by
  rw [value1, value3, value33, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (99 : Vertex) (103 : Vertex) (227 : Vertex) (231 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1127 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 5 = false ∨ valuation q 33 = false ∨ valuation q 41 = false := by
  rw [value1, value5, value33, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (99 : Vertex) (107 : Vertex) (227 : Vertex) (235 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1128 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 5 = false ∨ valuation q 40 = false ∨ valuation q 41 = false := by
  rw [value4, value5, value40, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (106 : Vertex) (107 : Vertex) (234 : Vertex) (235 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1129 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 32 = false ∨ valuation q 82 = false ∨ valuation q 99 = false := by
  rw [value12, value32, value82, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (160 : Vertex) (224 : Vertex) (416 : Vertex) (480 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1130 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 14 = false ∨ valuation q 17 = false ∨ valuation q 19 = false := by
  rw [value13, value14, value17, value19]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (161 : Vertex) (163 : Vertex) (169 : Vertex) (171 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1131 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 15 = false ∨ valuation q 17 = false ∨ valuation q 20 = false := by
  rw [value13, value15, value17, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (161 : Vertex) (165 : Vertex) (169 : Vertex) (173 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1132 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 16 = false ∨ valuation q 19 = false ∨ valuation q 22 = false := by
  rw [value14, value16, value19, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (163 : Vertex) (167 : Vertex) (171 : Vertex) (175 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1133 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 19 = false ∨ valuation q 33 = false ∨ valuation q 41 = false := by
  rw [value14, value19, value33, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (163 : Vertex) (171 : Vertex) (227 : Vertex) (235 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1134 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 25 = false ∨ valuation q 33 = false ∨ valuation q 44 = false := by
  rw [value14, value25, value33, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (163 : Vertex) (179 : Vertex) (227 : Vertex) (243 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1135 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 16 = false ∨ valuation q 35 = false ∨ valuation q 37 = false := by
  rw [value15, value16, value35, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (165 : Vertex) (167 : Vertex) (229 : Vertex) (231 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1136 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 19 = false ∨ valuation q 20 = false ∨ valuation q 22 = false := by
  rw [value17, value19, value20, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (169 : Vertex) (171 : Vertex) (173 : Vertex) (175 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1137 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 19 = false ∨ valuation q 39 = false ∨ valuation q 41 = false := by
  rw [value17, value19, value39, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (169 : Vertex) (171 : Vertex) (233 : Vertex) (235 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1138 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 20 = false ∨ valuation q 28 = false ∨ valuation q 30 = false := by
  rw [value17, value20, value28, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (169 : Vertex) (173 : Vertex) (185 : Vertex) (189 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1139 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 28 = false ∨ valuation q 39 = false ∨ valuation q 49 = false := by
  rw [value17, value28, value39, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (169 : Vertex) (185 : Vertex) (233 : Vertex) (249 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1140 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 19 = false ∨ valuation q 21 = false ∨ valuation q 22 = false := by
  rw [value18, value19, value21, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (170 : Vertex) (171 : Vertex) (174 : Vertex) (175 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1141 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 19 = false ∨ valuation q 40 = false ∨ valuation q 41 = false := by
  rw [value18, value19, value40, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (170 : Vertex) (171 : Vertex) (234 : Vertex) (235 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1142 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 24 = false ∨ valuation q 26 = false ∨ valuation q 27 = false := by
  rw [value23, value24, value26, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (176 : Vertex) (178 : Vertex) (180 : Vertex) (182 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1143 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 27 = false ∨ valuation q 29 = false ∨ valuation q 31 = false := by
  rw [value26, value27, value29, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (180 : Vertex) (182 : Vertex) (188 : Vertex) (190 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1144 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 41 = false ∨ valuation q 101 = false ∨ valuation q 105 = false := by
  rw [value33, value41, value101, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (227 : Vertex) (235 : Vertex) (483 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1145 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 35 = false ∨ valuation q 36 = false ∨ valuation q 37 = false := by
  rw [value34, value35, value36, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (228 : Vertex) (229 : Vertex) (230 : Vertex) (231 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1146 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 35 = false ∨ valuation q 45 = false ∨ valuation q 46 = false := by
  rw [value34, value35, value45, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (228 : Vertex) (229 : Vertex) (244 : Vertex) (245 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1147 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 36 = false ∨ valuation q 42 = false ∨ valuation q 43 = false := by
  rw [value34, value36, value42, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (228 : Vertex) (230 : Vertex) (236 : Vertex) (238 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1148 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 37 = false ∨ valuation q 46 = false ∨ valuation q 47 = false := by
  rw [value35, value37, value46, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (229 : Vertex) (231 : Vertex) (245 : Vertex) (247 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1149 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 39 = false ∨ valuation q 40 = false ∨ valuation q 41 = false := by
  rw [value38, value39, value40, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (232 : Vertex) (233 : Vertex) (234 : Vertex) (235 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1150 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 39 = false ∨ valuation q 48 = false ∨ valuation q 49 = false := by
  rw [value38, value39, value48, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (232 : Vertex) (233 : Vertex) (248 : Vertex) (249 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1151 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 41 = false ∨ valuation q 49 = false ∨ valuation q 51 = false := by
  rw [value39, value41, value49, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (233 : Vertex) (235 : Vertex) (249 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1152 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 41 = false ∨ valuation q 104 = false ∨ valuation q 105 = false := by
  rw [value40, value41, value104, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (234 : Vertex) (235 : Vertex) (490 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block35 (q : Snake 81) (h : Conditions q) : B112E088.Block35 (valuation q) :=
  ⟨clause1121 q h, clause1122 q h, clause1123 q h, clause1124 q h, clause1125 q h, clause1126 q h, clause1127 q h, clause1128 q h, clause1129 q h, clause1130 q h, clause1131 q h, clause1132 q h, clause1133 q h, clause1134 q h, clause1135 q h, clause1136 q h, clause1137 q h, clause1138 q h, clause1139 q h, clause1140 q h, clause1141 q h, clause1142 q h, clause1143 q h, clause1144 q h, clause1145 q h, clause1146 q h, clause1147 q h, clause1148 q h, clause1149 q h, clause1150 q h, clause1151 q h, clause1152 q h⟩

end
end Snake9.Regrowth.E112088
