import E112120Semantics
import B112E120Inputs
namespace Snake9.Regrowth.E112120
noncomputable section
local instance blockDec5 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause161 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 44 = false ∨ valuation q 77 = false ∨ valuation q 100 = false := by
  rw [value44, value77, value79, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (259 : Vertex) (385 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause162 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 44 = false ∨ valuation q 78 = false ∨ valuation q 81 = false := by
  rw [value44, value78, value79, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (259 : Vertex) (386 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause163 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 44 = false ∨ valuation q 78 = false ∨ valuation q 91 = false := by
  rw [value44, value78, value79, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (259 : Vertex) (386 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause164 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 44 = false ∨ valuation q 78 = false ∨ valuation q 100 = false := by
  rw [value44, value78, value79, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (259 : Vertex) (386 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause165 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 44 = false ∨ valuation q 81 = false ∨ valuation q 91 = false := by
  rw [value44, value79, value81, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (259 : Vertex) (391 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause166 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 44 = false ∨ valuation q 81 = false ∨ valuation q 100 = false := by
  rw [value44, value79, value81, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (259 : Vertex) (391 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause167 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 44 = false ∨ valuation q 91 = false ∨ valuation q 100 = false := by
  rw [value44, value79, value91, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (259 : Vertex) (403 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause168 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 77 = false ∨ valuation q 78 = false ∨ valuation q 81 = false := by
  rw [value77, value78, value79, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (385 : Vertex) (386 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause169 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 77 = false ∨ valuation q 78 = false ∨ valuation q 91 = false := by
  rw [value77, value78, value79, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (385 : Vertex) (386 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause170 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 77 = false ∨ valuation q 78 = false ∨ valuation q 100 = false := by
  rw [value77, value78, value79, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (385 : Vertex) (386 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause171 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 77 = false ∨ valuation q 81 = false ∨ valuation q 91 = false := by
  rw [value77, value79, value81, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (385 : Vertex) (391 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause172 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 77 = false ∨ valuation q 81 = false ∨ valuation q 100 = false := by
  rw [value77, value79, value81, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (385 : Vertex) (391 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause173 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 77 = false ∨ valuation q 91 = false ∨ valuation q 100 = false := by
  rw [value77, value79, value91, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (385 : Vertex) (403 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause174 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 78 = false ∨ valuation q 81 = false ∨ valuation q 91 = false := by
  rw [value78, value79, value81, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (386 : Vertex) (391 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause175 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 78 = false ∨ valuation q 81 = false ∨ valuation q 100 = false := by
  rw [value78, value79, value81, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (386 : Vertex) (391 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause176 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 78 = false ∨ valuation q 91 = false ∨ valuation q 100 = false := by
  rw [value78, value79, value91, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (386 : Vertex) (403 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause177 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 81 = false ∨ valuation q 91 = false ∨ valuation q 100 = false := by
  rw [value79, value81, value91, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (391 : Vertex) (403 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause178 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 46 = false ∨ valuation q 77 = false ∨ valuation q 81 = false := by
  rw [value46, value77, value80, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (261 : Vertex) (385 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause179 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 46 = false ∨ valuation q 77 = false ∨ valuation q 85 = false := by
  rw [value46, value77, value80, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (261 : Vertex) (385 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause180 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 46 = false ∨ valuation q 77 = false ∨ valuation q 102 = false := by
  rw [value46, value77, value80, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (261 : Vertex) (385 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause181 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 46 = false ∨ valuation q 81 = false ∨ valuation q 85 = false := by
  rw [value46, value80, value81, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (261 : Vertex) (391 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause182 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 46 = false ∨ valuation q 85 = false ∨ valuation q 102 = false := by
  rw [value46, value80, value85, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (261 : Vertex) (397 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause183 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 77 = false ∨ valuation q 81 = false ∨ valuation q 85 = false := by
  rw [value77, value80, value81, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (385 : Vertex) (391 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause184 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 77 = false ∨ valuation q 81 = false ∨ valuation q 102 = false := by
  rw [value77, value80, value81, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (385 : Vertex) (391 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause185 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 77 = false ∨ valuation q 85 = false ∨ valuation q 102 = false := by
  rw [value77, value80, value85, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (385 : Vertex) (397 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause186 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 81 = false ∨ valuation q 85 = false ∨ valuation q 102 = false := by
  rw [value80, value81, value85, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (391 : Vertex) (397 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause187 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 197 = true ∨ valuation q 79 = true ∨ valuation q 80 = true ∨ valuation q 87 = true := by
  rw [value79, value80, value81, value87, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (391 : Vertex) w → w ∈ region → w ≠ (135 : Vertex) → w ∈ [(387 : Vertex), (389 : Vertex), (399 : Vertex)] := by decide
  have hg := other_cover q (391 : Vertex) (135 : Vertex) [(387 : Vertex), (389 : Vertex), (399 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause188 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 197 = true ∨ valuation q 12 = true ∨ valuation q 80 = true ∨ valuation q 87 = true := by
  rw [value12, value80, value81, value87, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (391 : Vertex) w → w ∈ region → w ≠ (387 : Vertex) → w ∈ [(135 : Vertex), (389 : Vertex), (399 : Vertex)] := by decide
  have hg := other_cover q (391 : Vertex) (387 : Vertex) [(135 : Vertex), (389 : Vertex), (399 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause189 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 197 = true ∨ valuation q 12 = true ∨ valuation q 79 = true ∨ valuation q 87 = true := by
  rw [value12, value79, value81, value87, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (391 : Vertex) w → w ∈ region → w ≠ (389 : Vertex) → w ∈ [(135 : Vertex), (387 : Vertex), (399 : Vertex)] := by decide
  have hg := other_cover q (391 : Vertex) (389 : Vertex) [(135 : Vertex), (387 : Vertex), (399 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause190 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 197 = true ∨ valuation q 12 = true ∨ valuation q 79 = true ∨ valuation q 80 = true := by
  rw [value12, value79, value80, value81, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (391 : Vertex) w → w ∈ region → w ≠ (399 : Vertex) → w ∈ [(135 : Vertex), (387 : Vertex), (389 : Vertex)] := by decide
  have hg := other_cover q (391 : Vertex) (399 : Vertex) [(135 : Vertex), (387 : Vertex), (389 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause191 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 14 = false ∨ valuation q 47 = false ∨ valuation q 77 = false := by
  rw [value14, value47, value77, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (393 : Vertex) (137 : Vertex) (265 : Vertex) (385 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause192 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 14 = false ∨ valuation q 47 = false ∨ valuation q 85 = false := by
  rw [value14, value47, value82, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (393 : Vertex) (137 : Vertex) (265 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block5 (q : Snake 81) (h : Conditions q) : B112E120.Block5 (valuation q) :=
  ⟨clause161 q h, clause162 q h, clause163 q h, clause164 q h, clause165 q h, clause166 q h, clause167 q h, clause168 q h, clause169 q h, clause170 q h, clause171 q h, clause172 q h, clause173 q h, clause174 q h, clause175 q h, clause176 q h, clause177 q h, clause178 q h, clause179 q h, clause180 q h, clause181 q h, clause182 q h, clause183 q h, clause184 q h, clause185 q h, clause186 q h, clause187 q h, clause188 q h, clause189 q h, clause190 q h, clause191 q h, clause192 q h⟩

end
end Snake9.Regrowth.E112120
