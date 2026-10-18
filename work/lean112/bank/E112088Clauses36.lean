import E112088Semantics
import B112E088Inputs
namespace Snake9.Regrowth.E112088
noncomputable section
local instance blockDec36 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1153 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 47 = false ∨ valuation q 51 = false ∨ valuation q 52 = false := by
  rw [value44, value47, value51, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (243 : Vertex) (247 : Vertex) (251 : Vertex) (255 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1154 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 49 = false ∨ valuation q 50 = false ∨ valuation q 51 = false := by
  rw [value48, value49, value50, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (248 : Vertex) (249 : Vertex) (250 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1155 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 67 = false ∨ valuation q 70 = false ∨ valuation q 71 = false := by
  rw [value66, value67, value70, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (352 : Vertex) (353 : Vertex) (360 : Vertex) (361 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1156 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 83 = false ∨ valuation q 86 = false ∨ valuation q 87 = false := by
  rw [value82, value83, value86, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (416 : Vertex) (417 : Vertex) (424 : Vertex) (425 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1157 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 85 = false ∨ valuation q 88 = false ∨ valuation q 89 = false := by
  rw [value84, value85, value88, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (420 : Vertex) (422 : Vertex) (428 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1158 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 94 = false ∨ valuation q 97 = false ∨ valuation q 98 = false := by
  rw [value91, value94, value97, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (435 : Vertex) (439 : Vertex) (443 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1159 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 101 = false ∨ valuation q 104 = false ∨ valuation q 105 = false := by
  rw [value100, value101, value104, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (482 : Vertex) (483 : Vertex) (490 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block36 (q : Snake 81) (h : Conditions q) : B112E088.Block36 (valuation q) :=
  ⟨clause1153 q h, clause1154 q h, clause1155 q h, clause1156 q h, clause1157 q h, clause1158 q h, clause1159 q h⟩

end
end Snake9.Regrowth.E112088
