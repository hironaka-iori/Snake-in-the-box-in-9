import E112168Semantics
import B112E168Inputs
namespace Snake9.Regrowth.E112168
noncomputable section
local instance blockDec35 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1121 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 37 = false ∨ valuation q 48 = false ∨ valuation q 60 = false := by
  rw [value29, value37, value48, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (137 : Vertex) (153 : Vertex) (201 : Vertex) (217 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1122 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 36 = false ∨ valuation q 40 = false ∨ valuation q 41 = false := by
  rw [value35, value36, value40, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (149 : Vertex) (151 : Vertex) (157 : Vertex) (159 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1123 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 39 = false ∨ valuation q 40 = false ∨ valuation q 41 = false := by
  rw [value37, value39, value40, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (153 : Vertex) (155 : Vertex) (157 : Vertex) (159 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1124 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 45 = false ∨ valuation q 46 = false ∨ valuation q 47 = false := by
  rw [value43, value45, value46, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (193 : Vertex) (195 : Vertex) (197 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1125 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 45 = false ∨ valuation q 55 = false ∨ valuation q 57 = false := by
  rw [value43, value45, value55, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (193 : Vertex) (195 : Vertex) (209 : Vertex) (211 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1126 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 46 = false ∨ valuation q 48 = false ∨ valuation q 51 = false := by
  rw [value43, value46, value48, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (193 : Vertex) (197 : Vertex) (201 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1127 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 48 = false ∨ valuation q 55 = false ∨ valuation q 60 = false := by
  rw [value43, value48, value55, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (193 : Vertex) (201 : Vertex) (209 : Vertex) (217 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1128 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 45 = false ∨ valuation q 97 = false ∨ valuation q 98 = false := by
  rw [value44, value45, value97, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (194 : Vertex) (195 : Vertex) (450 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1129 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 60 = false ∨ valuation q 101 = false ∨ valuation q 112 = false := by
  rw [value48, value60, value101, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (201 : Vertex) (217 : Vertex) (457 : Vertex) (473 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1130 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 51 = false ∨ valuation q 62 = false ∨ valuation q 63 = false := by
  rw [value50, value51, value62, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (204 : Vertex) (205 : Vertex) (220 : Vertex) (221 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1131 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 52 = false ∨ valuation q 62 = false ∨ valuation q 64 = false := by
  rw [value50, value52, value62, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (204 : Vertex) (206 : Vertex) (220 : Vertex) (222 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1132 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 52 = false ∨ valuation q 104 = false ∨ valuation q 105 = false := by
  rw [value50, value52, value104, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (204 : Vertex) (206 : Vertex) (460 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1133 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 55 = false ∨ valuation q 56 = false ∨ valuation q 57 = false := by
  rw [value54, value55, value56, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (208 : Vertex) (209 : Vertex) (210 : Vertex) (211 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1134 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 61 = false ∨ valuation q 62 = false ∨ valuation q 64 = false := by
  rw [value59, value61, value62, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (216 : Vertex) (218 : Vertex) (220 : Vertex) (222 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1135 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 84 = false ∨ valuation q 87 = false ∨ valuation q 88 = false := by
  rw [value83, value84, value87, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (389 : Vertex) (391 : Vertex) (397 : Vertex) (399 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1136 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 98 = false ∨ valuation q 102 = false ∨ valuation q 103 = false := by
  rw [value97, value98, value102, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (450 : Vertex) (451 : Vertex) (458 : Vertex) (459 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1137 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 100 = false ∨ valuation q 107 = false ∨ valuation q 108 = false := by
  rw [value99, value100, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (452 : Vertex) (453 : Vertex) (468 : Vertex) (469 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block35 (q : Snake 81) (h : Conditions q) : B112E168.Block35 (valuation q) :=
  ⟨clause1121 q h, clause1122 q h, clause1123 q h, clause1124 q h, clause1125 q h, clause1126 q h, clause1127 q h, clause1128 q h, clause1129 q h, clause1130 q h, clause1131 q h, clause1132 q h, clause1133 q h, clause1134 q h, clause1135 q h, clause1136 q h, clause1137 q h⟩

end
end Snake9.Regrowth.E112168
