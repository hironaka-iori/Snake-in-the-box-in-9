import E112169Semantics
import B112E169Inputs
namespace Snake9.Regrowth.E112169
noncomputable section
local instance blockDec35 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1121 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 16 = false ∨ valuation q 23 = false ∨ valuation q 25 = false := by
  rw [value13, value16, value23, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (162 : Vertex) (166 : Vertex) (178 : Vertex) (182 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1122 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 26 = false ∨ valuation q 37 = false ∨ valuation q 46 = false := by
  rw [value17, value26, value37, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (168 : Vertex) (184 : Vertex) (232 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1123 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 39 = false ∨ valuation q 87 = false ∨ valuation q 105 = false := by
  rw [value18, value39, value87, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (171 : Vertex) (235 : Vertex) (427 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1124 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 28 = false ∨ valuation q 29 = false ∨ valuation q 30 = false := by
  rw [value27, value28, value29, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (188 : Vertex) (189 : Vertex) (190 : Vertex) (191 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1125 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 37 = false ∨ valuation q 99 = false ∨ valuation q 103 = false := by
  rw [value31, value37, value99, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (224 : Vertex) (232 : Vertex) (480 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1126 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 36 = false ∨ valuation q 40 = false ∨ valuation q 41 = false := by
  rw [value34, value36, value40, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (228 : Vertex) (230 : Vertex) (236 : Vertex) (238 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1127 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 38 = false ∨ valuation q 40 = false ∨ valuation q 41 = false := by
  rw [value37, value38, value40, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (232 : Vertex) (234 : Vertex) (236 : Vertex) (238 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1128 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 38 = false ∨ valuation q 46 = false ∨ valuation q 48 = false := by
  rw [value37, value38, value46, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (232 : Vertex) (234 : Vertex) (248 : Vertex) (250 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1129 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 39 = false ∨ valuation q 48 = false ∨ valuation q 49 = false := by
  rw [value38, value39, value48, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (234 : Vertex) (235 : Vertex) (250 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1130 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 47 = false ∨ valuation q 48 = false ∨ valuation q 49 = false := by
  rw [value46, value47, value48, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (248 : Vertex) (249 : Vertex) (250 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1131 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 85 = false ∨ valuation q 91 = false ∨ valuation q 92 = false := by
  rw [value84, value85, value91, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (420 : Vertex) (421 : Vertex) (436 : Vertex) (437 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1132 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 100 = false ∨ valuation q 103 = false ∨ valuation q 104 = false := by
  rw [value99, value100, value103, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (480 : Vertex) (481 : Vertex) (488 : Vertex) (489 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1133 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 112 = false ∨ valuation q 114 = false ∨ valuation q 116 = false := by
  rw [value111, value112, value114, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (500 : Vertex) (502 : Vertex) (508 : Vertex) (510 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block35 (q : Snake 81) (h : Conditions q) : B112E169.Block35 (valuation q) :=
  ⟨clause1121 q h, clause1122 q h, clause1123 q h, clause1124 q h, clause1125 q h, clause1126 q h, clause1127 q h, clause1128 q h, clause1129 q h, clause1130 q h, clause1131 q h, clause1132 q h, clause1133 q h⟩

end
end Snake9.Regrowth.E112169
