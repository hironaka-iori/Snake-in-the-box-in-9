import E112078Semantics
import B112E078Inputs
namespace Snake9.Regrowth.E112078
noncomputable section
local instance blockDec37 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1185 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 22 = false ∨ valuation q 26 = false ∨ valuation q 28 = false := by
  rw [value19, value22, value26, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (130 : Vertex) (134 : Vertex) (138 : Vertex) (142 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1186 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 23 = false ∨ valuation q 40 = false ∨ valuation q 42 = false := by
  rw [value20, value23, value40, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (131 : Vertex) (135 : Vertex) (195 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1187 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 22 = false ∨ valuation q 27 = false ∨ valuation q 28 = false := by
  rw [value21, value22, value27, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (132 : Vertex) (134 : Vertex) (140 : Vertex) (142 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1188 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 23 = false ∨ valuation q 88 = false ∨ valuation q 89 = false := by
  rw [value22, value23, value88, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (134 : Vertex) (135 : Vertex) (390 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1189 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 25 = false ∨ valuation q 90 = false ∨ valuation q 91 = false := by
  rw [value24, value25, value90, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (136 : Vertex) (137 : Vertex) (392 : Vertex) (393 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1190 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 33 = false ∨ valuation q 43 = false ∨ valuation q 55 = false := by
  rw [value25, value33, value43, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (137 : Vertex) (153 : Vertex) (201 : Vertex) (217 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1191 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 28 = false ∨ valuation q 45 = false ∨ valuation q 47 = false := by
  rw [value27, value28, value45, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (140 : Vertex) (142 : Vertex) (204 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1192 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 38 = false ∨ valuation q 39 = false ∨ valuation q 40 = false := by
  rw [value37, value38, value39, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (192 : Vertex) (193 : Vertex) (194 : Vertex) (195 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1193 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 40 = false ∨ valuation q 41 = false ∨ valuation q 42 = false := by
  rw [value38, value40, value41, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (193 : Vertex) (195 : Vertex) (197 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1194 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 40 = false ∨ valuation q 50 = false ∨ valuation q 52 = false := by
  rw [value38, value40, value50, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (193 : Vertex) (195 : Vertex) (209 : Vertex) (211 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1195 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 40 = false ∨ valuation q 51 = false ∨ valuation q 52 = false := by
  rw [value39, value40, value51, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (194 : Vertex) (195 : Vertex) (210 : Vertex) (211 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1196 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 40 = false ∨ valuation q 102 = false ∨ valuation q 103 = false := by
  rw [value39, value40, value102, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (194 : Vertex) (195 : Vertex) (450 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1197 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 42 = false ∨ valuation q 46 = false ∨ valuation q 48 = false := by
  rw [value41, value42, value46, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (197 : Vertex) (199 : Vertex) (205 : Vertex) (207 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1198 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 46 = false ∨ valuation q 55 = false ∨ valuation q 58 = false := by
  rw [value43, value46, value55, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (201 : Vertex) (205 : Vertex) (217 : Vertex) (221 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1199 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 55 = false ∨ valuation q 106 = false ∨ valuation q 117 = false := by
  rw [value43, value55, value106, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (201 : Vertex) (217 : Vertex) (457 : Vertex) (473 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1200 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 46 = false ∨ valuation q 47 = false ∨ valuation q 48 = false := by
  rw [value45, value46, value47, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (204 : Vertex) (205 : Vertex) (206 : Vertex) (207 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1201 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 46 = false ∨ valuation q 57 = false ∨ valuation q 58 = false := by
  rw [value45, value46, value57, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (204 : Vertex) (205 : Vertex) (220 : Vertex) (221 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1202 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 47 = false ∨ valuation q 57 = false ∨ valuation q 59 = false := by
  rw [value45, value47, value57, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (204 : Vertex) (206 : Vertex) (220 : Vertex) (222 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1203 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 47 = false ∨ valuation q 109 = false ∨ valuation q 110 = false := by
  rw [value45, value47, value109, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (204 : Vertex) (206 : Vertex) (460 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1204 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 50 = false ∨ valuation q 51 = false ∨ valuation q 52 = false := by
  rw [value49, value50, value51, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (208 : Vertex) (209 : Vertex) (210 : Vertex) (211 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1205 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 54 = false ∨ valuation q 111 = false ∨ valuation q 116 = false := by
  rw [value49, value54, value111, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (208 : Vertex) (216 : Vertex) (464 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1206 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 53 = false ∨ valuation q 56 = false ∨ valuation q 59 = false := by
  rw [value51, value53, value56, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (210 : Vertex) (214 : Vertex) (218 : Vertex) (222 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1207 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 55 = false ∨ valuation q 57 = false ∨ valuation q 58 = false := by
  rw [value54, value55, value57, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (216 : Vertex) (217 : Vertex) (220 : Vertex) (221 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1208 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 103 = false ∨ valuation q 107 = false ∨ valuation q 108 = false := by
  rw [value102, value103, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (450 : Vertex) (451 : Vertex) (458 : Vertex) (459 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1209 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 105 = false ∨ valuation q 112 = false ∨ valuation q 113 = false := by
  rw [value104, value105, value112, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (452 : Vertex) (453 : Vertex) (468 : Vertex) (469 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1210 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 108 = false ∨ valuation q 117 = false ∨ valuation q 118 = false := by
  rw [value106, value108, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (457 : Vertex) (459 : Vertex) (473 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1211 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 113 = false ∨ valuation q 114 = false ∨ valuation q 115 = false := by
  rw [value112, value113, value114, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (468 : Vertex) (469 : Vertex) (470 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block37 (q : Snake 81) (h : Conditions q) : B112E078.Block37 (valuation q) :=
  ⟨clause1185 q h, clause1186 q h, clause1187 q h, clause1188 q h, clause1189 q h, clause1190 q h, clause1191 q h, clause1192 q h, clause1193 q h, clause1194 q h, clause1195 q h, clause1196 q h, clause1197 q h, clause1198 q h, clause1199 q h, clause1200 q h, clause1201 q h, clause1202 q h, clause1203 q h, clause1204 q h, clause1205 q h, clause1206 q h, clause1207 q h, clause1208 q h, clause1209 q h, clause1210 q h, clause1211 q h⟩

end
end Snake9.Regrowth.E112078
