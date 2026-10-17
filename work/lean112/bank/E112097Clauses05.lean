import E112097Semantics
import B112E097Inputs
namespace Snake9.Regrowth.E112097
noncomputable section
local instance blockDec5 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause161 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 47 = false ∨ valuation q 50 = false ∨ valuation q 59 = false := by
  rw [value47, value49, value50, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (292 : Vertex) (288 : Vertex) (294 : Vertex) (308 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause162 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 47 = false ∨ valuation q 55 = false ∨ valuation q 59 = false := by
  rw [value47, value49, value55, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (292 : Vertex) (288 : Vertex) (300 : Vertex) (308 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause163 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 50 = false ∨ valuation q 55 = false ∨ valuation q 59 = false := by
  rw [value49, value50, value55, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (292 : Vertex) (294 : Vertex) (300 : Vertex) (308 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause164 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 172 = true ∨ valuation q 50 = true ∨ valuation q 55 = true ∨ valuation q 59 = true := by
  rw [value49, value50, value55, value59, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (292 : Vertex) w → w ∈ region → w ≠ (288 : Vertex) → w ∈ [(294 : Vertex), (300 : Vertex), (308 : Vertex)] := by decide
  have hg := other_cover q (292 : Vertex) (288 : Vertex) [(294 : Vertex), (300 : Vertex), (308 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause165 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 172 = true ∨ valuation q 47 = true ∨ valuation q 50 = true ∨ valuation q 55 = true := by
  rw [value47, value49, value50, value55, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (292 : Vertex) w → w ∈ region → w ≠ (308 : Vertex) → w ∈ [(288 : Vertex), (294 : Vertex), (300 : Vertex)] := by decide
  have hg := other_cover q (292 : Vertex) (308 : Vertex) [(288 : Vertex), (294 : Vertex), (300 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause166 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 48 = false ∨ valuation q 49 = false ∨ valuation q 51 = false := by
  rw [value48, value49, value50, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (294 : Vertex) (290 : Vertex) (292 : Vertex) (295 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause167 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 48 = false ∨ valuation q 51 = false ∨ valuation q 56 = false := by
  rw [value48, value50, value51, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (294 : Vertex) (290 : Vertex) (295 : Vertex) (302 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause168 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 6 = false ∨ valuation q 50 = false ∨ valuation q 61 = false := by
  rw [value6, value50, value51, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (295 : Vertex) (39 : Vertex) (294 : Vertex) (311 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause169 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 6 = false ∨ valuation q 50 = false ∨ valuation q 69 = false := by
  rw [value6, value50, value51, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (295 : Vertex) (39 : Vertex) (294 : Vertex) (359 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause170 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 6 = false ∨ valuation q 61 = false ∨ valuation q 69 = false := by
  rw [value6, value51, value61, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (295 : Vertex) (39 : Vertex) (311 : Vertex) (359 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause171 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 50 = false ∨ valuation q 61 = false ∨ valuation q 69 = false := by
  rw [value50, value51, value61, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (295 : Vertex) (294 : Vertex) (311 : Vertex) (359 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause172 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 7 = false ∨ valuation q 47 = false ∨ valuation q 53 = false := by
  rw [value7, value47, value52, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (296 : Vertex) (40 : Vertex) (288 : Vertex) (297 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause173 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 7 = false ∨ valuation q 47 = false ∨ valuation q 54 = false := by
  rw [value7, value47, value52, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (296 : Vertex) (40 : Vertex) (288 : Vertex) (298 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause174 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 7 = false ∨ valuation q 47 = false ∨ valuation q 55 = false := by
  rw [value7, value47, value52, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (296 : Vertex) (40 : Vertex) (288 : Vertex) (300 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause175 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 7 = false ∨ valuation q 47 = false ∨ valuation q 70 = false := by
  rw [value7, value47, value52, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (296 : Vertex) (40 : Vertex) (288 : Vertex) (360 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause176 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 7 = false ∨ valuation q 47 = false ∨ valuation q 86 = false := by
  rw [value7, value47, value52, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (296 : Vertex) (40 : Vertex) (288 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause177 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 7 = false ∨ valuation q 53 = false ∨ valuation q 54 = false := by
  rw [value7, value52, value53, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (296 : Vertex) (40 : Vertex) (297 : Vertex) (298 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause178 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 7 = false ∨ valuation q 53 = false ∨ valuation q 55 = false := by
  rw [value7, value52, value53, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (296 : Vertex) (40 : Vertex) (297 : Vertex) (300 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause179 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 7 = false ∨ valuation q 53 = false ∨ valuation q 70 = false := by
  rw [value7, value52, value53, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (296 : Vertex) (40 : Vertex) (297 : Vertex) (360 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause180 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 7 = false ∨ valuation q 53 = false ∨ valuation q 86 = false := by
  rw [value7, value52, value53, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (296 : Vertex) (40 : Vertex) (297 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause181 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 7 = false ∨ valuation q 54 = false ∨ valuation q 55 = false := by
  rw [value7, value52, value54, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (296 : Vertex) (40 : Vertex) (298 : Vertex) (300 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause182 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 7 = false ∨ valuation q 54 = false ∨ valuation q 70 = false := by
  rw [value7, value52, value54, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (296 : Vertex) (40 : Vertex) (298 : Vertex) (360 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause183 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 7 = false ∨ valuation q 54 = false ∨ valuation q 86 = false := by
  rw [value7, value52, value54, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (296 : Vertex) (40 : Vertex) (298 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause184 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 7 = false ∨ valuation q 55 = false ∨ valuation q 70 = false := by
  rw [value7, value52, value55, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (296 : Vertex) (40 : Vertex) (300 : Vertex) (360 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause185 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 7 = false ∨ valuation q 55 = false ∨ valuation q 86 = false := by
  rw [value7, value52, value55, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (296 : Vertex) (40 : Vertex) (300 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause186 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 7 = false ∨ valuation q 70 = false ∨ valuation q 86 = false := by
  rw [value7, value52, value70, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (296 : Vertex) (40 : Vertex) (360 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause187 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 47 = false ∨ valuation q 53 = false ∨ valuation q 54 = false := by
  rw [value47, value52, value53, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (296 : Vertex) (288 : Vertex) (297 : Vertex) (298 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause188 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 47 = false ∨ valuation q 53 = false ∨ valuation q 55 = false := by
  rw [value47, value52, value53, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (296 : Vertex) (288 : Vertex) (297 : Vertex) (300 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause189 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 47 = false ∨ valuation q 53 = false ∨ valuation q 70 = false := by
  rw [value47, value52, value53, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (296 : Vertex) (288 : Vertex) (297 : Vertex) (360 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause190 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 47 = false ∨ valuation q 53 = false ∨ valuation q 86 = false := by
  rw [value47, value52, value53, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (296 : Vertex) (288 : Vertex) (297 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause191 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 47 = false ∨ valuation q 54 = false ∨ valuation q 55 = false := by
  rw [value47, value52, value54, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (296 : Vertex) (288 : Vertex) (298 : Vertex) (300 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause192 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 47 = false ∨ valuation q 54 = false ∨ valuation q 70 = false := by
  rw [value47, value52, value54, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (296 : Vertex) (288 : Vertex) (298 : Vertex) (360 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block5 (q : Snake 81) (h : Conditions q) : B112E097.Block5 (valuation q) :=
  ⟨clause161 q h, clause162 q h, clause163 q h, clause164 q h, clause165 q h, clause166 q h, clause167 q h, clause168 q h, clause169 q h, clause170 q h, clause171 q h, clause172 q h, clause173 q h, clause174 q h, clause175 q h, clause176 q h, clause177 q h, clause178 q h, clause179 q h, clause180 q h, clause181 q h, clause182 q h, clause183 q h, clause184 q h, clause185 q h, clause186 q h, clause187 q h, clause188 q h, clause189 q h, clause190 q h, clause191 q h, clause192 q h⟩

end
end Snake9.Regrowth.E112097
