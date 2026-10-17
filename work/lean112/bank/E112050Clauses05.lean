import E112050Semantics
import B112E050Inputs
namespace Snake9.Regrowth.E112050
noncomputable section
local instance blockDec5 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause161 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 174 = true ∨ valuation q 37 = true ∨ valuation q 47 = true := by
  rw [value37, value46, value47, value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (218 : Vertex) w → w ∈ region → w ≠ (474 : Vertex) → w ∈ [(202 : Vertex), (219 : Vertex)] := by decide
  have hg := other_cover q (218 : Vertex) (474 : Vertex) [(202 : Vertex), (219 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause162 (q : Snake 81) (h : Conditions q) : valuation q 175 = false ∨ valuation q 45 = false ∨ valuation q 46 = false := by
  rw [value45, value46, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (219 : Vertex) (217 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide)

theorem clause163 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 175 = true ∨ valuation q 46 = true := by
  rw [value46, value47, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (219 : Vertex) w → w ∈ region → w ≠ (217 : Vertex) → w ∈ [(218 : Vertex)] := by decide
  have hg := other_cover q (219 : Vertex) (217 : Vertex) [(218 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause164 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 175 = true ∨ valuation q 45 = true := by
  rw [value45, value47, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (219 : Vertex) w → w ∈ region → w ≠ (218 : Vertex) → w ∈ [(217 : Vertex)] := by decide
  have hg := other_cover q (219 : Vertex) (218 : Vertex) [(217 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause165 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 10 = false ∨ valuation q 42 = false ∨ valuation q 45 = false := by
  rw [value10, value42, value45, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (221 : Vertex) (93 : Vertex) (213 : Vertex) (217 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause166 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 42 = false ∨ valuation q 45 = false ∨ valuation q 127 = false := by
  rw [value42, value45, value48, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (221 : Vertex) (213 : Vertex) (217 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause167 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 51 = false ∨ valuation q 53 = false ∨ valuation q 54 = false := by
  rw [value49, value51, value53, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (257 : Vertex) (259 : Vertex) (261 : Vertex) (265 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause168 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 177 = true ∨ valuation q 53 = true ∨ valuation q 54 = true := by
  rw [value49, value53, value54, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (257 : Vertex) w → w ∈ region → w ≠ (259 : Vertex) → w ∈ [(261 : Vertex), (265 : Vertex)] := by decide
  have hg := other_cover q (257 : Vertex) (259 : Vertex) [(261 : Vertex), (265 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause169 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 177 = true ∨ valuation q 51 = true ∨ valuation q 53 = true := by
  rw [value49, value51, value53, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (257 : Vertex) w → w ∈ region → w ≠ (265 : Vertex) → w ∈ [(259 : Vertex), (261 : Vertex)] := by decide
  have hg := other_cover q (257 : Vertex) (265 : Vertex) [(259 : Vertex), (261 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause170 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 51 = false ∨ valuation q 60 = false ∨ valuation q 68 = false := by
  rw [value50, value51, value60, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (258 : Vertex) (259 : Vertex) (274 : Vertex) (322 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause171 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 51 = false ∨ valuation q 60 = false ∨ valuation q 87 = false := by
  rw [value50, value51, value60, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (258 : Vertex) (259 : Vertex) (274 : Vertex) (386 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause172 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 51 = false ∨ valuation q 68 = false ∨ valuation q 87 = false := by
  rw [value50, value51, value68, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (258 : Vertex) (259 : Vertex) (322 : Vertex) (386 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause173 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 60 = false ∨ valuation q 68 = false ∨ valuation q 87 = false := by
  rw [value50, value60, value68, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (258 : Vertex) (274 : Vertex) (322 : Vertex) (386 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause174 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 49 = false ∨ valuation q 50 = false ∨ valuation q 55 = false := by
  rw [value49, value50, value51, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (259 : Vertex) (257 : Vertex) (258 : Vertex) (267 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause175 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 179 = true ∨ valuation q 49 = true ∨ valuation q 55 = true ∨ valuation q 61 = true := by
  rw [value49, value51, value55, value61, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (259 : Vertex) w → w ∈ region → w ≠ (258 : Vertex) → w ∈ [(257 : Vertex), (267 : Vertex), (275 : Vertex)] := by decide
  have hg := other_cover q (259 : Vertex) (258 : Vertex) [(257 : Vertex), (267 : Vertex), (275 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause176 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 179 = true ∨ valuation q 49 = true ∨ valuation q 50 = true ∨ valuation q 61 = true := by
  rw [value49, value50, value51, value61, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (259 : Vertex) w → w ∈ region → w ≠ (267 : Vertex) → w ∈ [(257 : Vertex), (258 : Vertex), (275 : Vertex)] := by decide
  have hg := other_cover q (259 : Vertex) (267 : Vertex) [(257 : Vertex), (258 : Vertex), (275 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause177 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 179 = true ∨ valuation q 49 = true ∨ valuation q 50 = true ∨ valuation q 55 = true := by
  rw [value49, value50, value51, value55, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (259 : Vertex) w → w ∈ region → w ≠ (275 : Vertex) → w ∈ [(257 : Vertex), (258 : Vertex), (267 : Vertex)] := by decide
  have hg := other_cover q (259 : Vertex) (275 : Vertex) [(257 : Vertex), (258 : Vertex), (267 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause178 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 53 = false ∨ valuation q 56 = false ∨ valuation q 69 = false := by
  rw [value52, value53, value56, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (260 : Vertex) (261 : Vertex) (268 : Vertex) (324 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause179 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 53 = false ∨ valuation q 56 = false ∨ valuation q 88 = false := by
  rw [value52, value53, value56, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (260 : Vertex) (261 : Vertex) (268 : Vertex) (388 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause180 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 53 = false ∨ valuation q 69 = false ∨ valuation q 88 = false := by
  rw [value52, value53, value69, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (260 : Vertex) (261 : Vertex) (324 : Vertex) (388 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause181 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 181 = true ∨ valuation q 52 = true ∨ valuation q 57 = true ∨ valuation q 70 = true ∨ valuation q 89 = true := by
  rw [value52, value53, value57, value70, value89, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (261 : Vertex) w → w ∈ region → w ≠ (257 : Vertex) → w ∈ [(260 : Vertex), (269 : Vertex), (325 : Vertex), (389 : Vertex)] := by decide
  have hg := other_cover q (261 : Vertex) (257 : Vertex) [(260 : Vertex), (269 : Vertex), (325 : Vertex), (389 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause182 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 181 = true ∨ valuation q 49 = true ∨ valuation q 57 = true ∨ valuation q 70 = true ∨ valuation q 89 = true := by
  rw [value49, value53, value57, value70, value89, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (261 : Vertex) w → w ∈ region → w ≠ (260 : Vertex) → w ∈ [(257 : Vertex), (269 : Vertex), (325 : Vertex), (389 : Vertex)] := by decide
  have hg := other_cover q (261 : Vertex) (260 : Vertex) [(257 : Vertex), (269 : Vertex), (325 : Vertex), (389 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause183 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 181 = true ∨ valuation q 49 = true ∨ valuation q 52 = true ∨ valuation q 70 = true ∨ valuation q 89 = true := by
  rw [value49, value52, value53, value70, value89, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (261 : Vertex) w → w ∈ region → w ≠ (269 : Vertex) → w ∈ [(257 : Vertex), (260 : Vertex), (325 : Vertex), (389 : Vertex)] := by decide
  have hg := other_cover q (261 : Vertex) (269 : Vertex) [(257 : Vertex), (260 : Vertex), (325 : Vertex), (389 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause184 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 181 = true ∨ valuation q 49 = true ∨ valuation q 52 = true ∨ valuation q 57 = true ∨ valuation q 89 = true := by
  rw [value49, value52, value53, value57, value89, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (261 : Vertex) w → w ∈ region → w ≠ (325 : Vertex) → w ∈ [(257 : Vertex), (260 : Vertex), (269 : Vertex), (389 : Vertex)] := by decide
  have hg := other_cover q (261 : Vertex) (325 : Vertex) [(257 : Vertex), (260 : Vertex), (269 : Vertex), (389 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause185 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 181 = true ∨ valuation q 49 = true ∨ valuation q 52 = true ∨ valuation q 57 = true ∨ valuation q 70 = true := by
  rw [value49, value52, value53, value57, value70, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (261 : Vertex) w → w ∈ region → w ≠ (389 : Vertex) → w ∈ [(257 : Vertex), (260 : Vertex), (269 : Vertex), (325 : Vertex)] := by decide
  have hg := other_cover q (261 : Vertex) (389 : Vertex) [(257 : Vertex), (260 : Vertex), (269 : Vertex), (325 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause186 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 55 = false ∨ valuation q 57 = false ∨ valuation q 93 = false := by
  rw [value54, value55, value57, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (265 : Vertex) (267 : Vertex) (269 : Vertex) (393 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause187 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 182 = true ∨ valuation q 55 = true ∨ valuation q 57 = true ∨ valuation q 93 = true := by
  rw [value54, value55, value57, value93, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (265 : Vertex) w → w ∈ region → w ≠ (257 : Vertex) → w ∈ [(267 : Vertex), (269 : Vertex), (393 : Vertex)] := by decide
  have hg := other_cover q (265 : Vertex) (257 : Vertex) [(267 : Vertex), (269 : Vertex), (393 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause188 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 182 = true ∨ valuation q 49 = true ∨ valuation q 57 = true ∨ valuation q 93 = true := by
  rw [value49, value54, value57, value93, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (265 : Vertex) w → w ∈ region → w ≠ (267 : Vertex) → w ∈ [(257 : Vertex), (269 : Vertex), (393 : Vertex)] := by decide
  have hg := other_cover q (265 : Vertex) (267 : Vertex) [(257 : Vertex), (269 : Vertex), (393 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause189 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 182 = true ∨ valuation q 49 = true ∨ valuation q 55 = true ∨ valuation q 93 = true := by
  rw [value49, value54, value55, value93, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (265 : Vertex) w → w ∈ region → w ≠ (269 : Vertex) → w ∈ [(257 : Vertex), (267 : Vertex), (393 : Vertex)] := by decide
  have hg := other_cover q (265 : Vertex) (269 : Vertex) [(257 : Vertex), (267 : Vertex), (393 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause190 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 182 = true ∨ valuation q 49 = true ∨ valuation q 55 = true ∨ valuation q 57 = true := by
  rw [value49, value54, value55, value57, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (265 : Vertex) w → w ∈ region → w ≠ (393 : Vertex) → w ∈ [(257 : Vertex), (267 : Vertex), (269 : Vertex)] := by decide
  have hg := other_cover q (265 : Vertex) (393 : Vertex) [(257 : Vertex), (267 : Vertex), (269 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause191 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 51 = false ∨ valuation q 54 = false ∨ valuation q 95 = false := by
  rw [value51, value54, value55, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (267 : Vertex) (259 : Vertex) (265 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause192 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 183 = true ∨ valuation q 54 = true ∨ valuation q 95 = true := by
  rw [value54, value55, value95, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (267 : Vertex) w → w ∈ region → w ≠ (259 : Vertex) → w ∈ [(265 : Vertex), (395 : Vertex)] := by decide
  have hg := other_cover q (267 : Vertex) (259 : Vertex) [(265 : Vertex), (395 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block5 (q : Snake 81) (h : Conditions q) : B112E050.Block5 (valuation q) :=
  ⟨clause161 q h, clause162 q h, clause163 q h, clause164 q h, clause165 q h, clause166 q h, clause167 q h, clause168 q h, clause169 q h, clause170 q h, clause171 q h, clause172 q h, clause173 q h, clause174 q h, clause175 q h, clause176 q h, clause177 q h, clause178 q h, clause179 q h, clause180 q h, clause181 q h, clause182 q h, clause183 q h, clause184 q h, clause185 q h, clause186 q h, clause187 q h, clause188 q h, clause189 q h, clause190 q h, clause191 q h, clause192 q h⟩

end
end Snake9.Regrowth.E112050
