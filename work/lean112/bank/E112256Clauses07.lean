import E112256Semantics
import B112E256Inputs
namespace Snake9.Regrowth.E112256
noncomputable section
local instance blockDec7 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause225 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 37 = false ∨ valuation q 38 = false ∨ valuation q 40 = false := by
  rw [value36, value37, value38, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (192 : Vertex) (193 : Vertex) (194 : Vertex) (200 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause226 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 37 = false ∨ valuation q 38 = false ∨ valuation q 55 = false := by
  rw [value36, value37, value38, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (192 : Vertex) (193 : Vertex) (194 : Vertex) (224 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause227 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 37 = false ∨ valuation q 39 = false ∨ valuation q 40 = false := by
  rw [value36, value37, value39, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (192 : Vertex) (193 : Vertex) (196 : Vertex) (200 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause228 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 37 = false ∨ valuation q 39 = false ∨ valuation q 55 = false := by
  rw [value36, value37, value39, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (192 : Vertex) (193 : Vertex) (196 : Vertex) (224 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause229 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 37 = false ∨ valuation q 40 = false ∨ valuation q 55 = false := by
  rw [value36, value37, value40, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (192 : Vertex) (193 : Vertex) (200 : Vertex) (224 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause230 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 38 = false ∨ valuation q 39 = false ∨ valuation q 40 = false := by
  rw [value36, value38, value39, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (192 : Vertex) (194 : Vertex) (196 : Vertex) (200 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause231 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 38 = false ∨ valuation q 39 = false ∨ valuation q 55 = false := by
  rw [value36, value38, value39, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (192 : Vertex) (194 : Vertex) (196 : Vertex) (224 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause232 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 38 = false ∨ valuation q 40 = false ∨ valuation q 55 = false := by
  rw [value36, value38, value40, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (192 : Vertex) (194 : Vertex) (200 : Vertex) (224 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause233 (q : Snake 81) (h : Conditions q) : valuation q 163 = false ∨ valuation q 37 = false ∨ valuation q 55 = false := by
  rw [value37, value55, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (192 : Vertex) (193 : Vertex) (224 : Vertex) (by decide) (by decide) (by decide)

theorem clause234 (q : Snake 81) (h : Conditions q) : valuation q 163 = false ∨ valuation q 38 = false ∨ valuation q 55 = false := by
  rw [value38, value55, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (192 : Vertex) (194 : Vertex) (224 : Vertex) (by decide) (by decide) (by decide)

theorem clause235 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 163 = true ∨ valuation q 38 = true ∨ valuation q 39 = true ∨ valuation q 40 = true ∨ valuation q 55 = true := by
  rw [value36, value38, value39, value40, value55, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (192 : Vertex) w → w ∈ region → w ≠ (193 : Vertex) → w ∈ [(194 : Vertex), (196 : Vertex), (200 : Vertex), (224 : Vertex)] := by decide
  have hg := other_cover q (192 : Vertex) (193 : Vertex) [(194 : Vertex), (196 : Vertex), (200 : Vertex), (224 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause236 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 163 = true ∨ valuation q 37 = true ∨ valuation q 39 = true ∨ valuation q 40 = true ∨ valuation q 55 = true := by
  rw [value36, value37, value39, value40, value55, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (192 : Vertex) w → w ∈ region → w ≠ (194 : Vertex) → w ∈ [(193 : Vertex), (196 : Vertex), (200 : Vertex), (224 : Vertex)] := by decide
  have hg := other_cover q (192 : Vertex) (194 : Vertex) [(193 : Vertex), (196 : Vertex), (200 : Vertex), (224 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause237 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 163 = true ∨ valuation q 37 = true ∨ valuation q 38 = true ∨ valuation q 40 = true ∨ valuation q 55 = true := by
  rw [value36, value37, value38, value40, value55, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (192 : Vertex) w → w ∈ region → w ≠ (196 : Vertex) → w ∈ [(193 : Vertex), (194 : Vertex), (200 : Vertex), (224 : Vertex)] := by decide
  have hg := other_cover q (192 : Vertex) (196 : Vertex) [(193 : Vertex), (194 : Vertex), (200 : Vertex), (224 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause238 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 163 = true ∨ valuation q 37 = true ∨ valuation q 38 = true ∨ valuation q 39 = true ∨ valuation q 40 = true := by
  rw [value36, value37, value38, value39, value40, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (192 : Vertex) w → w ∈ region → w ≠ (224 : Vertex) → w ∈ [(193 : Vertex), (194 : Vertex), (196 : Vertex), (200 : Vertex)] := by decide
  have hg := other_cover q (192 : Vertex) (224 : Vertex) [(193 : Vertex), (194 : Vertex), (196 : Vertex), (200 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause239 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 1 = false ∨ valuation q 36 = false ∨ valuation q 41 = false := by
  rw [value1, value36, value37, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (193 : Vertex) (65 : Vertex) (192 : Vertex) (201 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause240 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 164 = true ∨ valuation q 36 = true ∨ valuation q 41 = true := by
  rw [value36, value37, value41, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (193 : Vertex) w → w ∈ region → w ≠ (65 : Vertex) → w ∈ [(192 : Vertex), (201 : Vertex)] := by decide
  have hg := other_cover q (193 : Vertex) (65 : Vertex) [(192 : Vertex), (201 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause241 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 164 = true ∨ valuation q 1 = true ∨ valuation q 41 = true := by
  rw [value1, value37, value41, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (193 : Vertex) w → w ∈ region → w ≠ (192 : Vertex) → w ∈ [(65 : Vertex), (201 : Vertex)] := by decide
  have hg := other_cover q (193 : Vertex) (192 : Vertex) [(65 : Vertex), (201 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause242 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 164 = true ∨ valuation q 1 = true ∨ valuation q 36 = true := by
  rw [value1, value36, value37, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (193 : Vertex) w → w ∈ region → w ≠ (201 : Vertex) → w ∈ [(65 : Vertex), (192 : Vertex)] := by decide
  have hg := other_cover q (193 : Vertex) (201 : Vertex) [(65 : Vertex), (192 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause243 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 2 = false ∨ valuation q 36 = false ∨ valuation q 42 = false := by
  rw [value2, value36, value38, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (194 : Vertex) (66 : Vertex) (192 : Vertex) (202 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause244 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 2 = false ∨ valuation q 36 = false ∨ valuation q 45 = false := by
  rw [value2, value36, value38, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (194 : Vertex) (66 : Vertex) (192 : Vertex) (210 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause245 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 2 = false ∨ valuation q 42 = false ∨ valuation q 45 = false := by
  rw [value2, value38, value42, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (194 : Vertex) (66 : Vertex) (202 : Vertex) (210 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause246 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 36 = false ∨ valuation q 42 = false ∨ valuation q 45 = false := by
  rw [value36, value38, value42, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (194 : Vertex) (192 : Vertex) (202 : Vertex) (210 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause247 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 165 = true ∨ valuation q 36 = true ∨ valuation q 42 = true ∨ valuation q 45 = true := by
  rw [value36, value38, value42, value45, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (194 : Vertex) w → w ∈ region → w ≠ (66 : Vertex) → w ∈ [(192 : Vertex), (202 : Vertex), (210 : Vertex)] := by decide
  have hg := other_cover q (194 : Vertex) (66 : Vertex) [(192 : Vertex), (202 : Vertex), (210 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause248 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 165 = true ∨ valuation q 2 = true ∨ valuation q 42 = true ∨ valuation q 45 = true := by
  rw [value2, value38, value42, value45, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (194 : Vertex) w → w ∈ region → w ≠ (192 : Vertex) → w ∈ [(66 : Vertex), (202 : Vertex), (210 : Vertex)] := by decide
  have hg := other_cover q (194 : Vertex) (192 : Vertex) [(66 : Vertex), (202 : Vertex), (210 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause249 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 165 = true ∨ valuation q 2 = true ∨ valuation q 36 = true ∨ valuation q 45 = true := by
  rw [value2, value36, value38, value45, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (194 : Vertex) w → w ∈ region → w ≠ (202 : Vertex) → w ∈ [(66 : Vertex), (192 : Vertex), (210 : Vertex)] := by decide
  have hg := other_cover q (194 : Vertex) (202 : Vertex) [(66 : Vertex), (192 : Vertex), (210 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause250 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 165 = true ∨ valuation q 2 = true ∨ valuation q 36 = true ∨ valuation q 42 = true := by
  rw [value2, value36, value38, value42, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (194 : Vertex) w → w ∈ region → w ≠ (210 : Vertex) → w ∈ [(66 : Vertex), (192 : Vertex), (202 : Vertex)] := by decide
  have hg := other_cover q (194 : Vertex) (210 : Vertex) [(66 : Vertex), (192 : Vertex), (202 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause251 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 36 = false ∨ valuation q 43 = false ∨ valuation q 47 = false := by
  rw [value36, value39, value43, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (196 : Vertex) (192 : Vertex) (204 : Vertex) (212 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause252 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 36 = false ∨ valuation q 43 = false ∨ valuation q 57 = false := by
  rw [value36, value39, value43, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (196 : Vertex) (192 : Vertex) (204 : Vertex) (228 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause253 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 36 = false ∨ valuation q 47 = false ∨ valuation q 57 = false := by
  rw [value36, value39, value47, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (196 : Vertex) (192 : Vertex) (212 : Vertex) (228 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause254 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 43 = false ∨ valuation q 47 = false ∨ valuation q 57 = false := by
  rw [value39, value43, value47, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (196 : Vertex) (204 : Vertex) (212 : Vertex) (228 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause255 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 166 = true ∨ valuation q 43 = true ∨ valuation q 47 = true ∨ valuation q 57 = true := by
  rw [value39, value43, value47, value57, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (196 : Vertex) w → w ∈ region → w ≠ (192 : Vertex) → w ∈ [(204 : Vertex), (212 : Vertex), (228 : Vertex)] := by decide
  have hg := other_cover q (196 : Vertex) (192 : Vertex) [(204 : Vertex), (212 : Vertex), (228 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause256 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 166 = true ∨ valuation q 36 = true ∨ valuation q 43 = true ∨ valuation q 57 = true := by
  rw [value36, value39, value43, value57, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (196 : Vertex) w → w ∈ region → w ≠ (212 : Vertex) → w ∈ [(192 : Vertex), (204 : Vertex), (228 : Vertex)] := by decide
  have hg := other_cover q (196 : Vertex) (212 : Vertex) [(192 : Vertex), (204 : Vertex), (228 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block7 (q : Snake 81) (h : Conditions q) : B112E256.Block7 (valuation q) :=
  ⟨clause225 q h, clause226 q h, clause227 q h, clause228 q h, clause229 q h, clause230 q h, clause231 q h, clause232 q h, clause233 q h, clause234 q h, clause235 q h, clause236 q h, clause237 q h, clause238 q h, clause239 q h, clause240 q h, clause241 q h, clause242 q h, clause243 q h, clause244 q h, clause245 q h, clause246 q h, clause247 q h, clause248 q h, clause249 q h, clause250 q h, clause251 q h, clause252 q h, clause253 q h, clause254 q h, clause255 q h, clause256 q h⟩

end
end Snake9.Regrowth.E112256
