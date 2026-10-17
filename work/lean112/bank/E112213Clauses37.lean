import E112213Semantics
import B112E213Inputs
namespace Snake9.Regrowth.E112213
noncomputable section
local instance blockDec37 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1185 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 25 = false ∨ valuation q 64 = false ∨ valuation q 65 = false := by
  rw [value23, value25, value64, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (76 : Vertex) (78 : Vertex) (204 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1186 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 25 = false ∨ valuation q 81 = false ∨ valuation q 82 = false := by
  rw [value23, value25, value81, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (76 : Vertex) (78 : Vertex) (332 : Vertex) (334 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1187 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 26 = false ∨ valuation q 36 = false ∨ valuation q 37 = false := by
  rw [value25, value26, value36, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (78 : Vertex) (79 : Vertex) (94 : Vertex) (95 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1188 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 28 = false ∨ valuation q 29 = false ∨ valuation q 30 = false := by
  rw [value27, value28, value29, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (80 : Vertex) (81 : Vertex) (82 : Vertex) (83 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1189 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 29 = false ∨ valuation q 32 = false ∨ valuation q 33 = false := by
  rw [value27, value29, value32, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (80 : Vertex) (82 : Vertex) (88 : Vertex) (90 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1190 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 31 = false ∨ valuation q 32 = false ∨ valuation q 35 = false := by
  rw [value27, value31, value32, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (80 : Vertex) (84 : Vertex) (88 : Vertex) (92 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1191 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 30 = false ∨ valuation q 33 = false ∨ valuation q 34 = false := by
  rw [value29, value30, value33, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (82 : Vertex) (83 : Vertex) (90 : Vertex) (91 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1192 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 33 = false ∨ valuation q 83 = false ∨ valuation q 89 = false := by
  rw [value29, value33, value83, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (82 : Vertex) (90 : Vertex) (338 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1193 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 39 = false ∨ valuation q 40 = false ∨ valuation q 41 = false := by
  rw [value38, value39, value40, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (128 : Vertex) (129 : Vertex) (130 : Vertex) (131 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1194 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 40 = false ∨ valuation q 46 = false ∨ valuation q 48 = false := by
  rw [value38, value40, value46, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (128 : Vertex) (130 : Vertex) (144 : Vertex) (146 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1195 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 41 = false ∨ valuation q 47 = false ∨ valuation q 49 = false := by
  rw [value39, value41, value47, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (129 : Vertex) (131 : Vertex) (145 : Vertex) (147 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1196 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 43 = false ∨ valuation q 57 = false ∨ valuation q 62 = false := by
  rw [value39, value43, value57, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (129 : Vertex) (137 : Vertex) (193 : Vertex) (201 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1197 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 41 = false ∨ valuation q 48 = false ∨ valuation q 49 = false := by
  rw [value40, value41, value48, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (130 : Vertex) (131 : Vertex) (146 : Vertex) (147 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1198 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 47 = false ∨ valuation q 48 = false ∨ valuation q 49 = false := by
  rw [value46, value47, value48, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (144 : Vertex) (145 : Vertex) (146 : Vertex) (147 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1199 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 51 = false ∨ valuation q 66 = false ∨ valuation q 71 = false := by
  rw [value48, value51, value66, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (146 : Vertex) (154 : Vertex) (210 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1200 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 58 = false ∨ valuation q 61 = false ∨ valuation q 64 = false := by
  rw [value56, value58, value61, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (192 : Vertex) (196 : Vertex) (200 : Vertex) (204 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1201 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 59 = false ∨ valuation q 64 = false ∨ valuation q 65 = false := by
  rw [value58, value59, value64, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (196 : Vertex) (198 : Vertex) (204 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1202 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 60 = false ∨ valuation q 68 = false ∨ valuation q 69 = false := by
  rw [value59, value60, value68, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (198 : Vertex) (199 : Vertex) (214 : Vertex) (215 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1203 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 75 = false ∨ valuation q 78 = false ∨ valuation q 79 = false := by
  rw [value74, value75, value78, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (320 : Vertex) (321 : Vertex) (328 : Vertex) (329 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block37 (q : Snake 81) (h : Conditions q) : B112E213.Block37 (valuation q) :=
  ⟨clause1185 q h, clause1186 q h, clause1187 q h, clause1188 q h, clause1189 q h, clause1190 q h, clause1191 q h, clause1192 q h, clause1193 q h, clause1194 q h, clause1195 q h, clause1196 q h, clause1197 q h, clause1198 q h, clause1199 q h, clause1200 q h, clause1201 q h, clause1202 q h, clause1203 q h⟩

end
end Snake9.Regrowth.E112213
