import E112186Semantics
import B112E186Inputs
namespace Snake9.Regrowth.E112186
noncomputable section
local instance blockDec7 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause225 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 47 = false ∨ valuation q 64 = false ∨ valuation q 106 = false := by
  rw [value47, value64, value66, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (322 : Vertex) (258 : Vertex) (320 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause226 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 47 = false ∨ valuation q 74 = false ∨ valuation q 106 = false := by
  rw [value47, value66, value74, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (322 : Vertex) (258 : Vertex) (338 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause227 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 190 = true ∨ valuation q 64 = true ∨ valuation q 67 = true ∨ valuation q 74 = true ∨ valuation q 106 = true := by
  rw [value64, value66, value67, value74, value106, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (322 : Vertex) w → w ∈ region → w ≠ (258 : Vertex) → w ∈ [(320 : Vertex), (323 : Vertex), (338 : Vertex), (450 : Vertex)] := by decide
  have hg := other_cover q (322 : Vertex) (258 : Vertex) [(320 : Vertex), (323 : Vertex), (338 : Vertex), (450 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause228 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 190 = true ∨ valuation q 47 = true ∨ valuation q 67 = true ∨ valuation q 74 = true ∨ valuation q 106 = true := by
  rw [value47, value66, value67, value74, value106, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (322 : Vertex) w → w ∈ region → w ≠ (320 : Vertex) → w ∈ [(258 : Vertex), (323 : Vertex), (338 : Vertex), (450 : Vertex)] := by decide
  have hg := other_cover q (322 : Vertex) (320 : Vertex) [(258 : Vertex), (323 : Vertex), (338 : Vertex), (450 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause229 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 190 = true ∨ valuation q 47 = true ∨ valuation q 64 = true ∨ valuation q 67 = true ∨ valuation q 106 = true := by
  rw [value47, value64, value66, value67, value106, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (322 : Vertex) w → w ∈ region → w ≠ (338 : Vertex) → w ∈ [(258 : Vertex), (320 : Vertex), (323 : Vertex), (450 : Vertex)] := by decide
  have hg := other_cover q (322 : Vertex) (338 : Vertex) [(258 : Vertex), (320 : Vertex), (323 : Vertex), (450 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause230 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 48 = false ∨ valuation q 65 = false ∨ valuation q 66 = false := by
  rw [value48, value65, value66, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (323 : Vertex) (259 : Vertex) (321 : Vertex) (322 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause231 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 48 = false ∨ valuation q 65 = false ∨ valuation q 70 = false := by
  rw [value48, value65, value67, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (323 : Vertex) (259 : Vertex) (321 : Vertex) (331 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause232 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 48 = false ∨ valuation q 65 = false ∨ valuation q 75 = false := by
  rw [value48, value65, value67, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (323 : Vertex) (259 : Vertex) (321 : Vertex) (339 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause233 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 48 = false ∨ valuation q 65 = false ∨ valuation q 107 = false := by
  rw [value48, value65, value67, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (323 : Vertex) (259 : Vertex) (321 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause234 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 48 = false ∨ valuation q 66 = false ∨ valuation q 70 = false := by
  rw [value48, value66, value67, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (323 : Vertex) (259 : Vertex) (322 : Vertex) (331 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause235 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 48 = false ∨ valuation q 66 = false ∨ valuation q 75 = false := by
  rw [value48, value66, value67, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (323 : Vertex) (259 : Vertex) (322 : Vertex) (339 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause236 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 48 = false ∨ valuation q 66 = false ∨ valuation q 107 = false := by
  rw [value48, value66, value67, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (323 : Vertex) (259 : Vertex) (322 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause237 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 48 = false ∨ valuation q 70 = false ∨ valuation q 75 = false := by
  rw [value48, value67, value70, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (323 : Vertex) (259 : Vertex) (331 : Vertex) (339 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause238 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 48 = false ∨ valuation q 70 = false ∨ valuation q 107 = false := by
  rw [value48, value67, value70, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (323 : Vertex) (259 : Vertex) (331 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause239 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 48 = false ∨ valuation q 75 = false ∨ valuation q 107 = false := by
  rw [value48, value67, value75, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (323 : Vertex) (259 : Vertex) (339 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause240 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 65 = false ∨ valuation q 66 = false ∨ valuation q 70 = false := by
  rw [value65, value66, value67, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (323 : Vertex) (321 : Vertex) (322 : Vertex) (331 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause241 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 65 = false ∨ valuation q 66 = false ∨ valuation q 75 = false := by
  rw [value65, value66, value67, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (323 : Vertex) (321 : Vertex) (322 : Vertex) (339 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause242 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 65 = false ∨ valuation q 66 = false ∨ valuation q 107 = false := by
  rw [value65, value66, value67, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (323 : Vertex) (321 : Vertex) (322 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause243 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 65 = false ∨ valuation q 70 = false ∨ valuation q 75 = false := by
  rw [value65, value67, value70, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (323 : Vertex) (321 : Vertex) (331 : Vertex) (339 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause244 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 65 = false ∨ valuation q 70 = false ∨ valuation q 107 = false := by
  rw [value65, value67, value70, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (323 : Vertex) (321 : Vertex) (331 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause245 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 65 = false ∨ valuation q 75 = false ∨ valuation q 107 = false := by
  rw [value65, value67, value75, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (323 : Vertex) (321 : Vertex) (339 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause246 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 66 = false ∨ valuation q 70 = false ∨ valuation q 75 = false := by
  rw [value66, value67, value70, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (323 : Vertex) (322 : Vertex) (331 : Vertex) (339 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause247 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 66 = false ∨ valuation q 70 = false ∨ valuation q 107 = false := by
  rw [value66, value67, value70, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (323 : Vertex) (322 : Vertex) (331 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause248 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 66 = false ∨ valuation q 75 = false ∨ valuation q 107 = false := by
  rw [value66, value67, value75, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (323 : Vertex) (322 : Vertex) (339 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause249 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 70 = false ∨ valuation q 75 = false ∨ valuation q 107 = false := by
  rw [value67, value70, value75, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (323 : Vertex) (331 : Vertex) (339 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause250 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 1 = false ∨ valuation q 65 = false ∨ valuation q 71 = false := by
  rw [value1, value65, value68, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (325 : Vertex) (69 : Vertex) (321 : Vertex) (333 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause251 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 50 = false ∨ valuation q 65 = false ∨ valuation q 71 = false := by
  rw [value50, value65, value68, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (325 : Vertex) (261 : Vertex) (321 : Vertex) (333 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause252 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 192 = true ∨ valuation q 1 = true ∨ valuation q 50 = true ∨ valuation q 65 = true := by
  rw [value1, value50, value65, value68, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (325 : Vertex) w → w ∈ region → w ≠ (333 : Vertex) → w ∈ [(69 : Vertex), (261 : Vertex), (321 : Vertex)] := by decide
  have hg := other_cover q (325 : Vertex) (333 : Vertex) [(69 : Vertex), (261 : Vertex), (321 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause253 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 2 = false ∨ valuation q 64 = false ∨ valuation q 77 = false := by
  rw [value2, value64, value69, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (328 : Vertex) (72 : Vertex) (320 : Vertex) (344 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause254 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 193 = true ∨ valuation q 64 = true ∨ valuation q 77 = true ∨ valuation q 111 = true := by
  rw [value64, value69, value77, value111, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (328 : Vertex) w → w ∈ region → w ≠ (72 : Vertex) → w ∈ [(320 : Vertex), (344 : Vertex), (456 : Vertex)] := by decide
  have hg := other_cover q (328 : Vertex) (72 : Vertex) [(320 : Vertex), (344 : Vertex), (456 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause255 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 193 = true ∨ valuation q 2 = true ∨ valuation q 64 = true ∨ valuation q 111 = true := by
  rw [value2, value64, value69, value111, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (328 : Vertex) w → w ∈ region → w ≠ (344 : Vertex) → w ∈ [(72 : Vertex), (320 : Vertex), (456 : Vertex)] := by decide
  have hg := other_cover q (328 : Vertex) (344 : Vertex) [(72 : Vertex), (320 : Vertex), (456 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause256 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 193 = true ∨ valuation q 2 = true ∨ valuation q 64 = true ∨ valuation q 77 = true := by
  rw [value2, value64, value69, value77, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (328 : Vertex) w → w ∈ region → w ≠ (456 : Vertex) → w ∈ [(72 : Vertex), (320 : Vertex), (344 : Vertex)] := by decide
  have hg := other_cover q (328 : Vertex) (456 : Vertex) [(72 : Vertex), (320 : Vertex), (344 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block7 (q : Snake 81) (h : Conditions q) : B112E186.Block7 (valuation q) :=
  ⟨clause225 q h, clause226 q h, clause227 q h, clause228 q h, clause229 q h, clause230 q h, clause231 q h, clause232 q h, clause233 q h, clause234 q h, clause235 q h, clause236 q h, clause237 q h, clause238 q h, clause239 q h, clause240 q h, clause241 q h, clause242 q h, clause243 q h, clause244 q h, clause245 q h, clause246 q h, clause247 q h, clause248 q h, clause249 q h, clause250 q h, clause251 q h, clause252 q h, clause253 q h, clause254 q h, clause255 q h, clause256 q h⟩

end
end Snake9.Regrowth.E112186
